(* TODO
   (decreasing importance)
   - Interprocedural
   - generalise variable freshening
   - track breaking of soundness assumptions eg reentrancy
   - static fields?
   - include only public methods in check
*)


open! IStd
open! PermsDomain

module F = Format
module L = Logging

(* stuff stolen from ThreadSafety due to mli *)
type lock_model =
  | Lock
  | Unlock
  | NoEffect

let get_lock_model = function
  | Procname.Java java_pname ->
      begin
        match Procname.java_get_class_name java_pname, Procname.java_get_method java_pname with
        | "java.util.concurrent.locks.Lock", "lock" ->
            Lock
        | ("java.util.concurrent.locks.ReentrantLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$ReadLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$WriteLock"),
          ("lock" | "tryLock" | "lockInterruptibly") ->
            Lock
        | ("java.util.concurrent.locks.Lock"
          |"java.util.concurrent.locks.ReentrantLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$ReadLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$WriteLock"),
          "unlock" ->
            Unlock
        | _ ->
            NoEffect
      end
  | pname when Procname.equal pname BuiltinDecl.__set_locked_attribute ->
      Lock
  | pname when Procname.equal pname BuiltinDecl.__delete_locked_attribute ->
      Unlock
  | _ ->
      NoEffect

let should_analyze_proc pdesc _ =
  let pn = Procdesc.get_proc_name pdesc in
  not (Procname.is_constructor pn) &&
  not (Procname.is_class_initializer pn) &&
  not (FbThreadSafety.is_logging_method pn)
  (* not (is_call_to_builder_class_method pn) &&
  not (is_call_to_immutable_collection_method tenv pn) &&
  not (runs_on_ui_thread pdesc) &&
  not (is_thread_confined_method tenv pdesc) &&
  not (pdesc_is_assumed_thread_safe pdesc tenv) *)

let should_report_on_proc (_, _, proc_name, proc_desc) =
  not (Procname.java_is_autogen_method proc_name) &&
  Procdesc.get_access proc_desc <> PredSymb.Private &&
  not (Annotations.pdesc_return_annot_ends_with proc_desc Annotations.visibleForTesting)

let get_class = function
  | Procname.Java java_pname -> Procname.java_get_class_type_name java_pname
  | _ -> assert false

module ClassMap = PrettyPrintable.MakePPMap(Typename)

module Summary = struct
  include Summary.Make (struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
    end)

  let of_state { pre; inv; curr; constraints; locked } =
    {
      sum_pre = pre;
      sum_inv = inv;
      sum_post = curr;
      sum_constraints = constraints;
      sum_locked = locked;
    }

  let subst theta { sum_pre; sum_inv; sum_post; sum_locked; sum_constraints } =
    {
      sum_pre = Field.Map.map (Ident.subst theta) sum_pre;
      sum_inv = Field.Map.map (Ident.subst theta) sum_inv;
      sum_post = Field.Map.map (Ident.subst theta) sum_post;
      sum_locked;
      sum_constraints = Constr.Set.map (Constr.subst theta) sum_constraints
    }

  let pp fmt { sum_pre; sum_inv; sum_post; sum_locked; sum_constraints } =
    F.fprintf fmt "{ sum_pre=%a; sum_inv=%a; sum_post=%a; sum_locked=%a sum_constraints=%a }"
      (Field.Map.pp ~pp_value:Ident.pp) sum_pre
      (Field.Map.pp ~pp_value:Ident.pp) sum_inv
      (Field.Map.pp ~pp_value:Ident.pp) sum_post
      F.pp_print_bool sum_locked
      Constr.Set.pp sum_constraints

(* send variables of
     sum_constraints U sum_post \ (sum_pre U sum_inv)
   to variables fresh in astate *)
(* optimised currently only for the case where there are none *)
  let freshen summary _ =
    let vars_of_map m =
      Field.Map.fold (fun _ v a -> Ident.Set.add v a) m Ident.Set.empty in
    let prevars = vars_of_map summary.sum_pre in
    let invvars = vars_of_map summary.sum_inv in
    let rhs_vars = Ident.Set.union prevars invvars in
    let cvars = Constr.Set.vars summary.sum_constraints in
    let postvars = vars_of_map summary.sum_post in
    let lhs_vars = Ident.Set.union cvars postvars in
    let evars = Ident.Set.diff lhs_vars rhs_vars in
    if Ident.Set.is_empty evars then summary else assert false

end


(* Make a transfer functions module given the fields of a class *)
module MakeTransferFunctions(CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = PermsDomain.Domain
  type extras = ProcData.no_extras

  let do_mem mk_constr fieldname astate =
    let fld_var = Field.Map.find fieldname astate.curr in
    let args =
      (if astate.locked then [Field.Map.find fieldname astate.inv] else []) @ [fld_var] in
    Domain.NonBottom (State.add_constr (mk_constr args) astate)
  let do_store fieldname astate =
    do_mem Constr.mk_eq_one fieldname astate
  let do_load fieldname astate =
    do_mem Constr.mk_gt_zero fieldname astate

  let lock_unlock astate to_lock =
    if phys_equal astate.locked to_lock then
      Domain.Bottom
    else
      Domain.NonBottom { astate with locked = to_lock }

  let is_lock_unlock pn args astate =
    let this_arg =
      match args with
      | (l, _)::_ -> ExpSet.mem l astate.this_refs
      | _ -> false in
    if not this_arg then false else
    match get_lock_model pn with
    | NoEffect -> false
    | _ -> true

  let do_call pdesc pn args astate =
    if is_lock_unlock pn args astate then
      begin
        match get_lock_model pn with
        | Lock -> lock_unlock astate true
        | Unlock -> lock_unlock astate false
        | NoEffect -> assert false
      end
    else
      (* method call other than lock/unlock *)
      match Summary.read_summary pdesc pn with
      | None ->
          L.out "Couldn't find summary for %a@." Procname.pp pn ;
          Domain.NonBottom astate
      | Some summary ->
          if astate.locked && summary.sum_locked then Domain.Bottom else
          let summary = Summary.freshen summary astate in
          let theta = Field.Map.mk_theta Ident.Map.empty summary.sum_pre astate.pre in
          let theta = Field.Map.mk_theta theta summary.sum_inv astate.inv in
          let summary = Summary.subst theta summary in
          Domain.NonBottom
            { astate with
              locked = astate.locked || summary.sum_locked;
              constraints = Constr.Set.union astate.constraints summary.sum_constraints;
              curr = summary.sum_post;
            }

  (* actual transfer function *)
  let _exec_instr astate { ProcData.pdesc; ProcData.tenv } _ cmd =
    let classname = get_class (Procdesc.get_proc_name pdesc) in
    L.out "Analysing instruction %a@." (Sil.pp_instr Pp.text) cmd ;
    match cmd with
    | Sil.Store (Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _, _)
      when PatternMatch.is_subtype tenv classname tname ->
      do_store fieldname astate
    | Sil.Store (l', _, l, _) when Exp.is_this l || ExpSet.mem l astate.this_refs ->
      Domain.NonBottom (State.add_ref l' astate)
    | Sil.Load (_, Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _)
      when PatternMatch.is_subtype tenv classname tname ->
        do_load fieldname astate
    | Sil.Load (v,l,_,_) when Exp.is_this l || ExpSet.mem l astate.this_refs ->
      Domain.NonBottom (State.add_ref (Exp.Var v) astate)
    | Sil.Load (v,_,_,_) ->
      Domain.NonBottom (State.remove_ref (Exp.Var v) astate)
    | Sil.Remove_temps (idents, _) ->
        Domain.NonBottom
          (List.fold ~f:(fun a v -> State.remove_ref (Exp.Var v) a) ~init:astate idents)
    (* | Sil.Load (_,l,_,_) ->
      L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
      L.out "***Root is = %a***@." Exp.pp (Exp.root_of_lexp l) ;
      astate *)
    | Sil.Call (_, Const (Cfun pn), (((l,_)::_) as args), _, _)
      when Exp.is_this l || ExpSet.mem l astate.this_refs ->
        L.out "***about to analyse call %a***@." (Sil.pp_instr Pp.text) cmd ;
        do_call pdesc pn args astate
    | Sil.Call (_, Const (Cfun pn), (((_, Typ.Tstruct tname)::_) as args), _, _)
      when PatternMatch.is_subtype tenv classname tname ->
        L.out "***about to analyse call %a***@." (Sil.pp_instr Pp.text) cmd ;
        do_call pdesc pn args astate
    | _ -> Domain.NonBottom astate

  let exec_instr astate pdata x cmd =
    match astate with
    | Domain.Bottom -> Domain.Bottom
    | Domain.NonBottom astate' -> _exec_instr astate' pdata x cmd

end

module Analyzer = AbstractInterpreter.Make(ProcCfg.Normal)(MakeTransferFunctions)
module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* compute the summary of a method *)
let compute_and_store_post callback =
  L.out "Analyzing method %a@." Procname.pp callback.Callbacks.proc_name ;
  (* retrieve the fields of a given class *)
  let get_fields pdesc =
    match Tenv.lookup pdesc.ProcData.tenv (get_class callback.Callbacks.proc_name) with
    | None -> assert false
    | Some { StructTyp.fields } ->
      Field.Set.of_list (List.map ~f:(fun (fld, _, _) -> fld) fields) in
  let compute_post pdesc =
    let fields = get_fields pdesc in
    let initial =
      let m = Field.Map.mk fields in
      Domain.NonBottom { State.empty with pre = m; curr = m; inv = Field.Map.mk fields } in
    let pdata = ProcData.make_default pdesc.ProcData.pdesc pdesc.ProcData.tenv in
    match Analyzer.compute_post ~initial pdata with
    | None -> L.out "No spec found@." ; None
    | Some Domain.Bottom -> L.out "Bottom spec found@." ; None
    | Some ((Domain.NonBottom s) as a) ->
        L.out "Found spec: %a@." Analyzer.TransferFunctions.Domain.pp a ;
        Some (Summary.of_state s) in
  Interprocedural.compute_and_store_post
    ~compute_post
    ~make_extras:ProcData.make_empty_extras
    callback

(* compute all pairs (as lists) but disregarding order within the pair *)
let all_pairs =
  let rec aux = function
    | [] -> []
    | (x::xs) as all ->
      let with_x = List.map ~f:(fun y -> [x;y]) all in
      with_x @ (aux xs) in
  aux


(* create a list of substitutions from all inv variables of a list of lists of summaries
   to the same targets *)
let mk_inv_thetas ss =
  let vs =
    Field.Map.fold
      (fun f _ a -> Field.Map.add f (Ident.mk ()) a)
      ((List.hd_exn ss).sum_inv)
      Field.Map.empty in
  let mk s =
    Field.Map.fold
      (fun f v acc -> Ident.Map.add v (Field.Map.find f vs) acc)
      s.sum_inv
      Ident.Map.empty in
  List.map ~f:mk ss

let extend_with_pres thetas ss =
  let extend_with_pre theta sum =
    Field.Map.fold
      (fun _ v acc -> Ident.Map.add v (Ident.mk ()) acc)
      sum.sum_pre
      theta in
  List.map2_exn ~f:extend_with_pre thetas ss

let extend_with_exists thetas ss =
  let extend_with_exist theta sum =
    let vars = Constr.Set.vars sum.sum_constraints in
    let evars = Ident.Set.filter (fun v -> not (Ident.Map.mem v theta)) vars in
    Ident.Set.fold (fun v acc -> Ident.Map.add v (Ident.mk ()) acc) evars theta in
  List.map2_exn ~f:extend_with_exist thetas ss

let apply_substs thetas ss =
  List.map2_exn ~f:Summary.subst thetas ss

let add_splits_and_flatten sums =
  let aux sums =
    let s = List.hd_exn sums in
    let new_pre = Field.Map.map (fun _ -> Ident.mk ()) s.sum_pre in
    let constrs =
      List.fold
        ~f:(fun acc s' -> Constr.Set.union s'.sum_constraints acc)
        ~init:Constr.Set.empty
        sums in
    let constrs =
      Field.Map.fold
        (fun f v acc ->
           let vs = List.map ~f:(fun s' -> Field.Map.find f s'.sum_pre) sums in
           (* add all pre variables plus the resource invariant *)
           let i = Field.Map.find f s.sum_inv in
           let c = Constr.mk_sum v (i::vs) in
           Constr.Set.add c acc
        )
        new_pre
        constrs in
    {
      sum_inv = s.sum_inv;
      sum_pre = new_pre;
      sum_post = Field.Map.empty; (* we don't use posts for || rule *)
      sum_locked = false;
      sum_constraints = constrs
    }
  in
  aux sums

let file_analysis _ _ get_proc_desc file_env =
  (* outsource checks for ctrs/public etc to ThreadSafety *)
  let should_analyze ((_,tenv,_,pdesc) as p) =
    should_analyze_proc pdesc tenv && should_report_on_proc p
  in

  (* run actual analysis, remembering proc info *)
  let summarise ((idenv, tenv, proc_name, proc_desc) as p) =
    let callback =
      {Callbacks.get_proc_desc; get_procs_in_file = (fun _ -> []);
       idenv; tenv; proc_name; proc_desc} in
    (p, compute_and_store_post callback)
  in

  (* combine list of summaries of methods called in parallel,
     currently expects a pair of summaries as we only consider two threads --
    this is meant to be generalised in the future to n threads *)
  let process_case = function
    | [ ((_,_,p1,_), Some sum1); ((_,_,p2,_), Some sum2)] -> ([p1; p2], [sum1; sum2])
    | _ -> assert false
  in

  (* take a list of (proc info, summary) pairs *)
  let merge (pinfos, summaries) =
    let thetas = mk_inv_thetas summaries in
    let thetas = extend_with_pres thetas summaries in
    let thetas = extend_with_exists thetas summaries in
    let sums = apply_substs thetas summaries in
    let merged_summary = add_splits_and_flatten sums in
    let constraints = merged_summary.sum_constraints in
    let bounded =
      Ident.Set.fold
        (fun v a -> Constr.Set.add (Constr.mk_lb v) a |> Constr.Set.add (Constr.mk_ub v))
        (Constr.Set.vars constraints)
        constraints in
    (pinfos, bounded)
  in

  (* run z3 on a set of constraints
     and return the output as a list of strings/lines *)
  let run_z3 merged =
    let read_process_lines in_channel =
      let rec aux acc =
        let inp = try Some (input_line in_channel) with End_of_file -> None in
        match inp with
        | None -> acc
        | Some l -> aux (l::acc)
      in
      List.rev (aux [])
    in

    let in_ch,out_ch = Unix.open_process "z3 -in" in
    let fmt = F.formatter_of_out_channel out_ch in
    L.out "Passing to Z3:@.%a@." Constr.Set.pp merged ;
    (* ask for a satisfying model if sat *)
    F.fprintf fmt "(set-option :dump-models true)@." ;
    (* request decimals, not fractions, may append "?" if imprecise *)
    F.fprintf fmt "(set-option :pp.decimal true)@." ;
    F.fprintf fmt "%a@." Constr.Set.to_z3 merged ;
    F.fprintf fmt "(check-sat)@." ;
    (* need to close out_ch before reading z3's output, for reasons *)
    Out_channel.close out_ch ;
    let output = read_process_lines in_ch in
    (* kill z3 *)
    ignore (Unix.close_process (in_ch, out_ch)) ;
    output
  in

  let run_check (pinfos, merged) =
    L.out "Analysing case: %a@." (Pp.or_seq Pp.text Procname.pp) pinfos ;
    (* parse a z3 model (without the enclosing braces and model statement) *)
    let parse_z3_model varmap =
      let rec aux acc = function
        | [] | [_] -> acc
        | l1::l2::ls ->
          let varstr = Scanf.sscanf l1 "  (define-fun %s () Real" (fun v -> v) in
          let var = String.Map.find_exn varmap varstr in
          let value = Scanf.sscanf l2 " %f" (fun v -> v) in
          aux (Ident.Map.add var value acc) ls in
        aux Ident.Map.empty
      in
      match run_z3 merged with
      | "unsat" :: _ ->
        L.out "Z3 says: unsat@.@."
      | "sat" :: _ :: output -> (* drop first "(model" line as _ *)
        begin
          let varmap = Ident.Set.mk_string_map (Constr.Set.vars merged) in
          let model = parse_z3_model varmap output in
          L.out "Z3 model: %a@.@." (Ident.Map.pp ~pp_value:F.pp_print_float) model
        end
      | _ -> assert false
    in

  let classmap =
    List.fold
      ~f:(fun a ((_,_,pname,_) as p) ->
         let c = get_class pname in
         let procs = try ClassMap.find c a with Not_found -> [] in
         ClassMap.add c (p::procs) a
      )
      ~init:ClassMap.empty
      file_env
  in

  let analyse_class _ procs =
    let procs = List.filter ~f:should_analyze procs in
    let proc_sums = List.map ~f:summarise procs in
    let pairs = all_pairs proc_sums in
    let cases = List.map ~f:process_case pairs in
    let merged_cases = List.map ~f:merge cases in
    List.iter ~f:run_check merged_cases
  in
  ClassMap.iter analyse_class classmap
