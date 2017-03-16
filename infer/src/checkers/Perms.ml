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
  | Typ.Procname.Java java_pname ->
      begin
        match Typ.Procname.java_get_class_name java_pname, Typ.Procname.java_get_method java_pname with
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
  | pname when Typ.Procname.equal pname BuiltinDecl.__set_locked_attribute ->
      Lock
  | pname when Typ.Procname.equal pname BuiltinDecl.__delete_locked_attribute ->
      Unlock
  | _ ->
      NoEffect

let should_analyze_proc pdesc _ =
  let pn = Procdesc.get_proc_name pdesc in
  not (Typ.Procname.is_constructor pn) &&
  not (Typ.Procname.is_class_initializer pn) &&
  not (FbThreadSafety.is_logging_method pn)
  (* not (is_call_to_builder_class_method pn) &&
  not (is_call_to_immutable_collection_method tenv pn) &&
  not (runs_on_ui_thread pdesc) &&
  not (is_thread_confined_method tenv pdesc) &&
  not (pdesc_is_assumed_thread_safe pdesc tenv) *)

let should_report_on_proc (_, _, proc_name, proc_desc) =
  not (Typ.Procname.java_is_autogen_method proc_name) &&
  Procdesc.get_access proc_desc <> PredSymb.Private &&
  not (Annotations.pdesc_return_annot_ends_with proc_desc Annotations.visibleForTesting)

let get_class = function
  | Typ.Procname.Java java_pname -> Typ.Procname.java_get_class_type_name java_pname
  | _ -> assert false

let get_fields tenv pname =
  match Tenv.lookup tenv (get_class pname) with
  | None -> assert false
  | Some { Typ.Struct.fields } ->
      List.fold
        fields
        ~init:Field.Set.empty
        ~f:(fun acc (fld, _, _) -> Field.Set.add fld acc)

module ClassMap = PrettyPrintable.MakePPMap(Typename)

module Summary = struct
  include Summary.Make (struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
    end)

  let of_state { atoms; locks_held } =
    { sum_atoms = atoms; sum_locks = locks_held; }

  let pp fmt { sum_atoms; sum_locks } =
    F.fprintf fmt "{ sum_atoms=%a; sum_locks=%a }"
      Atom.Set.pp sum_atoms
      Lock.MultiSet.pp sum_locks

(* return set of locks that is used in accesses
   (does not include other locks held)*)
  let get_lockset s =
    Atom.Set.map_to
      (fun a -> Lock.MultiSet.to_set a.Atom.locks)
      Lock.Set.union
      Lock.Set.empty
      s.sum_atoms
end


(* Make a transfer functions module given the fields of a class *)
module MakeTransferFunctions(CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = PermsDomain.Domain
  type extras = ProcData.no_extras

  let is_un_lock pn =
    match get_lock_model pn with
    | NoEffect -> false
    | _ -> true

  let is_lock pn =
    match get_lock_model pn with
    | Lock -> true
    | _ -> false

  let get_lock pn _ =
    if Typ.Procname.equal pn BuiltinDecl.__set_locked_attribute ||
       Typ.Procname.equal pn BuiltinDecl.__delete_locked_attribute then
      Lock.This
    else
      (*FIXME!! we pretend everything is this *)
      Lock.This

  let do_call pdesc pn astate site =
      match Summary.read_summary pdesc pn with
      | None ->
          L.out "Couldn't find summary for %a@." Typ.Procname.pp pn ;
          astate
      | Some { sum_atoms; sum_locks } ->
          let new_atoms =
            Atom.Set.endomap
              (fun l -> Atom.adapt l astate.locks_held site)
              sum_atoms
          in
          let new_locks = Lock.MultiSet.union sum_locks astate.locks_held in
          {astate with atoms=new_atoms; locks_held=new_locks}

  (* actual transfer function *)
  let exec_instr astate { ProcData.pdesc; tenv } _ cmd =
    let classname = get_class (Procdesc.get_proc_name pdesc) in
    let procname = Procdesc.get_proc_name pdesc in
    match cmd with
    | Sil.Store (Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _, location)
      when PatternMatch.is_subtype tenv classname tname ->
        let site = CallSite.make procname location in
        State.add_write fieldname site astate

    | Sil.Store (Exp.Lvar lhs_pvar, lhs_typ, rhs_exp, _)
      when Pvar.is_frontend_tmp lhs_pvar (*&& not (is_constant rhs_exp)*) ->
        State.update_pvar lhs_pvar rhs_exp lhs_typ astate

    | Sil.Load (lhs_id, rhs_exp, rhs_typ, location) ->
        let astate = State.update_id lhs_id rhs_exp rhs_typ astate in
        begin
          match rhs_exp with
            | Exp.Lfield(_, fieldname, Typ.Tstruct tname)
              when PatternMatch.is_subtype tenv classname tname ->
                let site = CallSite.make procname location in
                State.add_read fieldname site astate
            | _ -> astate
        end

    | Sil.Remove_temps (ids, _) ->
        State.remove_ids ids astate

    | Sil.Call (_, Const (Cfun pn), args, _, _)
      when is_un_lock pn ->
        let to_lock = is_lock pn in
        let lock = get_lock pn args in
        let f = if to_lock then Lock.MultiSet.add else Lock.MultiSet.remove in
        { astate with locks_held = f lock astate.locks_held }

(* FIXME - not tracking references to fields *)

    | Sil.Call (_, Const (Cfun pn), l::_, location, _) ->
        if match l with
          | (Exp.Lvar pvar, _) when State.may_be_this (Var.of_pvar pvar) astate -> true
          | (Exp.Var id, _) when State.may_be_this (Var.of_id id) astate -> true
          | (_, Typ.Tstruct tname) -> PatternMatch.is_subtype tenv classname tname
          | _ -> false
        then
          let site = CallSite.make procname location in
          do_call pdesc pn astate site
        else
          astate

    | _ -> astate

(* | Sil.Load (_,l,_,_) ->
   L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
   L.out "***Root is = %a***@." Exp.pp (Exp.root_of_lexp l) ;
   astate *)

end

module Analyzer = AbstractInterpreter.Make(ProcCfg.Normal)(MakeTransferFunctions)
module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* compute the summary of a method *)
let compute_and_store_post callback =
  L.out "Analyzing method %a@." Typ.Procname.pp callback.Callbacks.proc_name ;
  let compute_post pdesc =
    let initial = State.empty in
    let pdata = ProcData.make_default pdesc.ProcData.pdesc pdesc.ProcData.tenv in
    match Analyzer.compute_post ~initial pdata with
    | None -> L.out "No spec found@." ; None
    | Some ((s) as a) ->
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

(* run z3 on a set of constraints
   and return the output as a list of strings/lines *)
let run_z3 vars merged =
  let read_process_lines in_channel =
    let rec aux acc =
      let inp = try Some (input_line in_channel) with End_of_file -> None in
      match inp with
      | None -> acc
      | Some l -> aux (l::acc)
    in
    List.rev (aux [])
  in
  let z3assert fmt (id, e) =
    match id with
    | -1 -> F.fprintf fmt "(assert %a)" Constr.to_z3 e
    | n -> F.fprintf fmt "(assert (! %a :named C%i))" Constr.to_z3 e n
  in

  let in_ch,out_ch = Unix.open_process "z3 -in" in
  let fmt = F.formatter_of_out_channel out_ch in
  L.out "Passing to Z3:@." ;
  List.iter ~f:(fun id_c -> L.out "%a@." z3assert id_c) merged ;
  (* ask for a satisfying model if sat *)
  F.fprintf fmt "(set-option :dump-models true)@." ;
  (* ask for an unsat core if unsat *)
  F.fprintf fmt "(set-option :unsat_core true)@." ;
  (* request decimals, not fractions, may append "?" if imprecise *)
  F.fprintf fmt "(set-option :pp.decimal true)@." ;
  F.fprintf fmt "%a@." Ident.Set.to_z3 vars ;
  List.iter ~f:(fun id_c -> F.fprintf fmt "%a@." z3assert id_c) merged ;
  F.fprintf fmt "(check-sat)@." ;
  F.fprintf fmt "(get-unsat-core)@." ;
  (* need to close out_ch before reading z3's output, for reasons *)
  Out_channel.close out_ch ;
  let output = read_process_lines in_ch in
  (* kill z3 *)
  ignore (Unix.close_process (in_ch, out_ch)) ;
  output

module IntMap = PrettyPrintable.MakePPMap(Int)


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
    | [ (_, Some sum1); (_, Some sum2)] -> [sum1; sum2]
    | _ -> assert false
  in

  (* take a list of (proc info, summary) pairs *)
  let compile_case fields locks invmap summaries =
    let mk_sum_constr (premaps, ctr_map) { sum_atoms } =
      let premap = Field.Map.of_fields fields in
      let ctr_map =
        Atom.Set.fold
          (fun a acc ->
             let c = Atom.compile premap invmap a in
             IntMap.add (Hashtbl.hash c) (c, a) acc
          )
          sum_atoms
          ctr_map
      in
      (premap::premaps, ctr_map)
    in
    let (premaps, ctr_map) =
      List.fold summaries
        ~init:([], IntMap.empty)
        ~f:mk_sum_constr in
    let premaps = List.rev premaps in
    let split f =
      let pres = List.map premaps ~f:(fun premap -> Field.Map.find f premap) in
      let invs = Field.Map.find f invmap in
      let lockinvs = List.map locks ~f:(fun l -> Lock.Map.find l invs) in
      Constr.mk_eq_one (pres @ lockinvs)
    in
    let extra_ctrs = Field.Set.map_to split List.cons [] fields in
    let vars =
      IntMap.fold
        (fun _ (c,_) acc -> Ident.Set.union (Constr.vars c) acc)
        ctr_map
        Ident.Set.empty
    in
    let vars =
      List.fold
        extra_ctrs
        ~init:vars
        ~f:(fun a c -> Ident.Set.union (Constr.vars c) a)
      in
    let extra_ctrs =
      Ident.Set.fold
        (fun v a -> (Constr.mk_lb [v])::(Constr.mk_ub [v])::a)
        vars
        extra_ctrs in
    (vars, ctr_map, extra_ctrs)
  in

  let merge compiled =
    let aux (vars, ctr_map, extra_ctrs) (vars_, ctr_map_, extra_ctrs_) =
      let vars' = Ident.Set.union vars vars_ in
      let extra_ctrs' = extra_ctrs_ @ extra_ctrs in
      let ctr_map' =
        IntMap.merge
          (fun _ c1 c2 ->
             match c1, c2 with
             | None, None | Some _, Some _ -> assert false
             | None, Some c | Some c, None -> Some c
          )
          ctr_map
          ctr_map_
      in
      (vars', ctr_map', extra_ctrs')
    in
    List.fold
      compiled
      ~init:(Ident.Set.empty, IntMap.empty, [])
      ~f:aux
  in



  let run_check (vars, ctr_map, extra_ctrs) =
    (* let pnames = List.map pinfos ~f:(fun (_,_,pn,_) -> pn) in
    L.out "Analysing case: %a@." (Pp.or_seq Pp.text Procname.pp) pnames ; *)
    (* parse a z3 model (without the enclosing braces and model statement) *)
    (* let parse_z3_model varmap =
      let rec aux acc = function
        | [] | [_] -> acc
        | l1::l2::ls ->
          let varstr = Scanf.sscanf l1 "  (define-fun %s () Real" (fun v -> v) in
          let var = String.Map.find_exn varmap varstr in
          let value = Scanf.sscanf l2 " %f" (fun v -> v) in
          aux (Ident.Map.add var value acc) ls in
      aux Ident.Map.empty
       in *)

    let rec parse_unsat_core = function
      | "sat"::_ -> ()
      | "unsat"::rest -> parse_unsat_core rest
      | l::_ ->
          (* L.out "to analyze %s" l ; *)
          let l = String.slice l 1 ((String.length l) - 1) in
          let ls = String.split l ~on:' ' in
          let ls = List.map ls ~f:(fun l -> String.slice l 1 (String.length l)) in
          let is = List.map ls ~f:Int.of_string in
          let atoms = List.map is
              ~f:(fun i -> snd (IntMap.find i ctr_map)) in
          let atoms = Atom.Set.of_list atoms in
          let () =
            Atom.Set.iter (fun c -> L.out "Z3: unsat core: %a@." Atom.pp c) atoms in
          let w = Atom.Set.choose (Atom.Set.filter Atom.is_write atoms) in
          let atoms = Atom.Set.elements (Atom.Set.remove w atoms) in
          let loc = CallSite.loc (List.last_exn w.path) in
          let pname = CallSite.pname (List.last_exn w.path) in
          let msg = Localise.to_string Localise.thread_safety_violation in
          let description =
            match atoms with
            | [] -> F.asprintf "The <%a> is a potential self-race." Atom.pp w
            | _ -> F.asprintf "The <%a> potentially races with:@.%a" Atom.pp w
                     (Pp.comma_seq Atom.pp) atoms
          in
          let ltr =
            List.mapi w.path
              ~f:(fun i s -> Errlog.make_trace_element i (CallSite.loc s) "" []) in
          let exn = Exceptions.Checkers (msg, Localise.verbatim_desc description) in
          Reporting.log_error pname ~loc ~ltr exn
      | _ -> ()
    in
    let merged = List.map extra_ctrs ~f:(fun c -> (-1, c)) in
    let merged = IntMap.fold (fun i (c,_) acc -> (i,c)::acc) ctr_map merged in
    let output = run_z3 vars merged in
    List.iter output ~f:(fun s -> L.out "Z3 says: %s.@." s) ;
    parse_unsat_core output
      (* | "sat" :: _ :: output -> (* drop first "(model" line as _ *) *)
        (* begin
          let varmap = Ident.Set.mk_string_map vars in
          let model = parse_z3_model varmap output in
          L.out "Z3 model: %a@.@." (Ident.Map.pp ~pp_value:F.pp_print_float) model
        end *)
      (* | _ -> assert false *)
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
    let fields =
      let (_,tenv,pn1,_) = List.hd_exn procs in
      get_fields tenv pn1
    in
    let procs = List.filter ~f:should_analyze procs in
    let proc_sums = List.map ~f:summarise procs in
    let locks =
      let lks =
        List.fold proc_sums ~init:Lock.Set.empty
          ~f:(fun acc (_,s) ->
              match s with
              | None -> acc
              | Some s -> Lock.Set.union (Summary.get_lockset s) acc
            ) in
      Lock.Set.fold List.cons lks []
    in
    let invmap =
      let mk_lockmap () =
        List.fold
          ~f:(fun acc l -> Lock.Map.add l (Ident.mk ()) acc)
          locks
          ~init:Lock.Map.empty
      in
      Field.Set.fold
        (fun f acc -> Field.Map.add f (mk_lockmap ()) acc)
        fields
        Field.Map.empty
    in
    let pairs = all_pairs proc_sums in
    let cases = List.map ~f:process_case pairs in
    let compiled = List.map ~f:(compile_case fields locks invmap) cases in
    let merged = merge compiled in
    run_check merged
  in
  ClassMap.iter analyse_class classmap
