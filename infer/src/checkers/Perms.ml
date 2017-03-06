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

let get_fields tenv pname =
  match Tenv.lookup tenv (get_class pname) with
  | None -> assert false
  | Some { StructTyp.fields } ->
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
            Atom.Set.endomap
              (fun l -> Atom.add_locks l astate.locks_held)
              sum_atoms
          in
          let new_locks = Lock.MultiSet.union sum_locks astate.locks_held in
          Domain.NonBottom {astate with atoms=new_atoms; locks_held=new_locks}

  (* actual transfer function *)
  let _exec_instr astate { ProcData.pdesc; ProcData.tenv } _ cmd =
    let classname = get_class (Procdesc.get_proc_name pdesc) in
    let procname = Procdesc.get_proc_name pdesc in
    (* L.out "Analysing instruction %a@." (Sil.pp_instr Pp.text) cmd ; *)
    match cmd with
    | Sil.Store (Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _, location)
      when PatternMatch.is_subtype tenv classname tname ->
        Domain.NonBottom (State.add_write fieldname procname location astate)

    | Sil.Store (l', _, l, _) when Exp.is_this l || ExpSet.mem l astate.this_refs ->
        Domain.NonBottom (State.add_ref l' astate)

    | Sil.Load (_, Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, location)
      when PatternMatch.is_subtype tenv classname tname ->
        Domain.NonBottom (State.add_read fieldname procname location astate)

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
  let merge fields locks invmap (pinfos, summaries) =
    let mk_sum_constr { sum_atoms } =
      let premap = Field.Map.of_fields fields in
      let ctrs =
        Atom.Set.fold
          (fun a acc ->
             let c = Atom.compile premap invmap a in
             (Hashtbl.hash c, c)::acc
          )
          sum_atoms
          [] in
      (premap, ctrs)
    in
    let (premaps, ctrs) =
      List.fold summaries
        ~init:([], [])
        ~f:(fun (premaps, acc) s ->
            let (p, cs) = mk_sum_constr s in
            (p::premaps, cs @ acc)
          ) in
    let (premaps, ctrs) = (List.rev premaps, List.rev ctrs) in
    let split f =
      let pres = List.map premaps ~f:(fun premap -> Field.Map.find f premap) in
      let invs = Field.Map.find f invmap in
      let lockinvs = List.map locks ~f:(fun l -> Lock.Map.find l invs) in
      (-1, Constr.mk_eq_one (pres @ lockinvs))
    in
    let ctrs =
      Field.Set.fold
        (fun f acc -> (split f)::acc)
        fields
        ctrs
    in
    let vars =
      List.fold
        ctrs
        ~init:Ident.Set.empty
        ~f:(fun a (_,c) -> Ident.Set.union (Constr.vars c) a)
      in
    let bounded =
      Ident.Set.fold
        (fun v a -> (-1, Constr.mk_lb [v])::(-1, Constr.mk_ub [v])::a)
        vars
        ctrs in
    (vars, pinfos, bounded)
  in

  let run_check (vars, pinfos, merged) =
    let pnames = List.map pinfos ~f:(fun (_,_,pn,_) -> pn) in
    L.out "Analysing case: %a@." (Pp.or_seq Pp.text Procname.pp) pnames ;
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
    List.iter (run_z3 vars merged) ~f:(fun s -> L.out "Z3 says: %s.@." s)
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
    let merged_cases = List.map ~f:(merge fields locks invmap) cases in
    List.iter ~f:run_check merged_cases
  in
  ClassMap.iter analyse_class classmap
