(* TODO
   (decreasing importance)
   - track breaking of soundness assumptions eg reentrancy
   - static fields?
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

  let of_state { atoms; locks_held } =
    { sum_atoms = atoms; sum_locks = locks_held; }

  let pp fmt { sum_atoms; sum_locks } =
    F.fprintf fmt "{ sum_atoms=%a; sum_locks=%a }"
      Atom.Set.pp sum_atoms
      Lock.MultiSet.pp sum_locks

(* return set of locks that is used in accesses
   (does not include other locks held)*)
  let get_lockset s =
    Atom.Set.fold
      (fun a acc -> Lock.Set.union (Lock.MultiSet.to_set a.Atom.locks) acc)
      s.sum_atoms
      Lock.Set.empty
end


(* Make a transfer functions module given the fields of a class *)
module MakeTransferFunctions(CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = PermsDomain.Domain
  type extras = ProcData.no_extras

  let do_mem acc fieldname astate =
    Domain.NonBottom (State.add_atom acc fieldname astate)
  let do_store fieldname astate =
    do_mem Atom.Access.Write fieldname astate
  let do_load fieldname astate =
    do_mem Atom.Access.Read fieldname astate

  let is_un_lock pn =
    match get_lock_model pn with
    | NoEffect -> false
    | _ -> true

  let is_lock pn =
    match get_lock_model pn with
    | Lock -> true
    | _ -> false

  let get_lock pn _ =
    if Procname.equal pn BuiltinDecl.__set_locked_attribute ||
       Procname.equal pn BuiltinDecl.__delete_locked_attribute then
      Lock.This
    else
      (*FIXME!! we pretend everything is this *)
      Lock.This

  let do_call pdesc pn astate =
      match Summary.read_summary pdesc pn with
      | None ->
          L.out "Couldn't find summary for %a@." Procname.pp pn ;
          Domain.NonBottom astate
      | Some { sum_atoms; sum_locks } ->
          let new_atoms =
            Atom.Set.fold
              (fun l acc -> Atom.Set.add (Atom.add_locks l astate.locks_held) acc)
              sum_atoms
              Atom.Set.empty in
          let new_locks =
            Lock.MultiSet.union sum_locks astate.locks_held in
          Domain.NonBottom {astate with atoms=new_atoms; locks_held=new_locks}

  (* actual transfer function *)
  let _exec_instr astate { ProcData.pdesc; ProcData.tenv } _ cmd =
    let classname = get_class (Procdesc.get_proc_name pdesc) in
    (* L.out "Analysing instruction %a@." (Sil.pp_instr Pp.text) cmd ; *)
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

    | Sil.Call (_, Const (Cfun pn), args, _, _)
      when is_un_lock pn ->
        let to_lock = is_lock pn in
        let lock = get_lock pn args in
        let f = if to_lock then Lock.MultiSet.add else Lock.MultiSet.remove in
        Domain.NonBottom { astate with locks_held = f lock astate.locks_held }

(* FIXME - not tracking references to fields *)

    | Sil.Call (_, Const (Cfun pn), ((l,_)::_), _, _)
      when Exp.is_this l || ExpSet.mem l astate.this_refs ->
        (* L.out "***about to analyse call %a***@." (Sil.pp_instr Pp.text) cmd ; *)
        do_call pdesc pn astate

    | Sil.Call (_, Const (Cfun pn), ((_, Typ.Tstruct tname)::_), _, _)
      when PatternMatch.is_subtype tenv classname tname ->
        (* L.out "***about to analyse call %a***@." (Sil.pp_instr Pp.text) cmd ; *)
        do_call pdesc pn astate

    | _ -> Domain.NonBottom astate

(* | Sil.Load (_,l,_,_) ->
   L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
   L.out "***Root is = %a***@." Exp.pp (Exp.root_of_lexp l) ;
   astate *)

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
  let compute_post pdesc =
    let initial = Domain.NonBottom State.empty in
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
    | [ (p1, Some sum1); (p2, Some sum2)] -> ([p1; p2], [sum1; sum2])
    | _ -> assert false
  in

  (* take a list of (proc info, summary) pairs *)
  let merge (pinfos, summaries) =
    let locks = List.fold summaries ~init:Lock.Set.empty
        ~f:(fun acc s -> Lock.Set.union (Summary.get_lockset s) acc) in
    let locks_lst = Lock.Set.fold (fun l acc -> l::acc) locks [] in
    let get_fields tenv pname =
      match Tenv.lookup tenv (get_class pname) with
      | None -> assert false
      | Some { StructTyp.fields } ->
          List.fold
            fields
            ~init:Field.Set.empty
            ~f:(fun acc (fld, _, _) -> Field.Set.add fld acc) in
    let (_,tenv,pname,_) = List.hd_exn pinfos in
    let fields = get_fields tenv pname in
    let mk_lockmap () =
      Lock.Set.fold (fun l acc -> Lock.Map.add l (Ident.mk ()) acc) locks Lock.Map.empty in
    let invmap =
      Field.Set.fold
        (fun f acc -> Field.Map.add f (mk_lockmap ()) acc)
        fields
        Field.Map.empty in
    let atom_to_expr premap { Atom.access; field; locks } =
      let lmap = Field.Map.find field invmap in
      let lks = Lock.MultiSet.to_set locks in
      let invs =
        Lock.Set.fold (fun l acc -> (Lock.Map.find l lmap)::acc) lks [] in
      let p = Field.Map.find field premap in
      match access with
      | Atom.Access.Read -> Constr.mk_gt_zero (p::invs)
      | Atom.Access.Write -> Constr.mk_eq_one (p::invs)
    in
    let mk_sum_constr { sum_atoms } =
      let premap = Field.Map.of_fields fields in
      let ctrs =
        Atom.Set.fold
          (fun a acc -> Constr.Set.add (atom_to_expr premap a) acc)
          sum_atoms
          Constr.Set.empty in
      (premap, ctrs)
    in
    let (premaps, ctrs) = List.fold summaries ~init:([], Constr.Set.empty)
        ~f:(fun (premaps, acc) s ->
            let (p, cs) = mk_sum_constr s in
            (p::premaps, Constr.Set.union cs acc)
          ) in
    let premaps = List.rev premaps in
    let split_pres = Field.Map.of_fields fields in
    let split f =
      let pres = List.map premaps ~f:(fun premap -> Field.Map.find f premap) in
      let invs = Field.Map.find f invmap in
      let lockinvs = List.map locks_lst ~f:(fun l -> Lock.Map.find l invs) in
      Constr.mk_sum (Field.Map.find f split_pres) (pres @ lockinvs)
    in
    let ctrs =
      Field.Set.fold
        (fun f acc -> Constr.Set.add (split f) acc)
        fields
        ctrs
    in
    let bounded =
      Ident.Set.fold
        (fun v a ->
           Constr.Set.add (Constr.mk_lb [v]) a |>
           Constr.Set.add (Constr.mk_ub [v]))
        (Constr.Set.vars ctrs)
        ctrs in
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
    let pnames = List.map pinfos ~f:(fun (_,_,pn,_) -> pn) in
    L.out "Analysing case: %a@." (Pp.or_seq Pp.text Procname.pp) pnames ;
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
