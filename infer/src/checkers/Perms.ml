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

module ClassMap = PrettyPrintable.MakePPMap(Typename)

module Summary = struct
  module S = struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
  end
  include Summary.Make (S)

  let get_summary callee_pname =
    match Specs.get_summary callee_pname with
    | None -> None
    | Some summary -> S.read_from_payload summary.Specs.payload

  let of_state pdata { atoms; locks_held } =
    let pdesc = pdata.ProcData.pdesc in
    let pname = Procdesc.get_proc_name pdesc in
    let attrs = Procdesc.get_attributes pdesc in
    let tenv = pdata.ProcData.tenv in
    let formals =
      List.map
        ~f:(fun (name, _) -> Pvar.mk name pname)
        attrs.ProcAttributes.formals in
    (* demand that every atom refers to an lvalue (so no naked root vars)
       and which is rooted at a formal *)
    let () =
      Atom.Set.iter
        (function
          | { Atom.lvalue=((Var.ProgramVar p, _), _::_) } ->
              assert (List.mem ~equal:Pvar.equal formals p)
          | _ -> assert false
        )
        atoms
    in
    (atoms, locks_held, formals, tenv)

  let pp fmt (sum_atoms, sum_locks, _) =
    F.fprintf fmt "{ sum_atoms=%a; sum_locks=%a }"
      Atom.Set.pp sum_atoms
      Lock.MultiSet.pp sum_locks

(* return set of locks that is used in accesses
   (does not include other locks held)*)
  let get_lockset (sum_atoms, _, _, _) =
    Atom.Set.map_to
      (fun a -> Lock.MultiSet.to_set a.Atom.locks)
      Lock.Set.union
      Lock.Set.empty
      sum_atoms
end

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

  let do_call caller_pdesc callee_pname args astate site =
    match Summary.read_summary caller_pdesc callee_pname with
    | None ->
        L.out "Couldn't find summary for %a@." Typ.Procname.pp callee_pname ;
        astate
    | Some (sum_atoms, sum_locks, formals, _) ->
        let f_resolve_id = IdMap.resolve astate.must_point in
        let args = List.map args
            ~f:(fun (arg, typ) -> AccessPath.of_lhs_exp arg typ ~f_resolve_id) in
        let theta = List.fold2_exn formals args ~init:PvarMap.empty
            ~f:(fun acc formal arg -> PvarMap.add formal arg acc) in
        let new_atoms =
          Atom.Set.endomap (Atom.adapt astate.locks_held site theta) sum_atoms in
        let new_locks = Lock.MultiSet.union sum_locks astate.locks_held in
        {astate with atoms=new_atoms; locks_held=new_locks}

  (* actual transfer function *)
  let exec_instr astate pdata _ cmd =
    let curr_pdesc = pdata.ProcData.pdesc in
    let procname = Procdesc.get_proc_name curr_pdesc in
    match cmd with
    | Sil.Load (lhs_id, rhs_exp, rhs_typ, location) ->
        let site = CallSite.make procname location in
        (* below we should be using a may-resolve FIXME *)
        let lvalue = State.must_resolve rhs_exp rhs_typ astate in
        let astate =
          match rhs_exp with
          | Exp.Lfield _ | Exp.Lindex _ -> State.add_read lvalue site astate
          | _ -> astate
        in
        State.update_id lhs_id rhs_exp rhs_typ astate

    | Sil.Store (lhs_exp, lhs_typ, rhs_exp, location) ->
        let site = CallSite.make procname location in
        let astate =
          match lhs_exp with
          | Exp.Lfield _ | Exp.Lindex _ ->
              (* below we should be using a may-resolve FIXME *)
              let lvalue = State.must_resolve lhs_exp lhs_typ astate in
              State.add_write lvalue site astate
          | Exp.Lvar lhs_pvar ->
              if Pvar.is_frontend_tmp lhs_pvar then
                State.update_pvar lhs_pvar rhs_exp lhs_typ astate
              else
                astate
          | _ -> assert false in
        let () =
          match rhs_exp with
          | Exp.Lfield _ | Exp.Lindex _ -> assert false
          | _ -> () in
        astate

    | Sil.Remove_temps (ids, _) ->
        State.remove_ids ids astate

    | Sil.Call (_, Const (Cfun pn), [(exp, typ)], _, _) when is_un_lock pn ->
        let lock = State.must_resolve exp typ astate in
        let f = if is_lock pn then Lock.MultiSet.add else Lock.MultiSet.remove in
        { astate with locks_held = f lock astate.locks_held }

    | Sil.Call (_, Const (Cfun pn), args, location, _) ->
        let site = CallSite.make procname location in
        do_call curr_pdesc pn args astate site

    | Sil.Declare_locals _ | Sil.Prune _ -> astate

    | _ ->
       L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
       astate

end

module Analyzer = AbstractInterpreter.Make(ProcCfg.Normal)(MakeTransferFunctions)
module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* compute the summary of a method *)
let compute_and_store_post callback =
  L.out "Analyzing method %a@." Typ.Procname.pp callback.Callbacks.proc_name ;
  let compute_post pdata =
    let initial = State.empty in
    let pdata = ProcData.make_default pdata.ProcData.pdesc pdata.ProcData.tenv in
    match Analyzer.compute_post ~initial pdata with
    | None -> L.out "No spec found@." ; None
    | Some ((s) as a) ->
        L.out "Found spec: %a@." Analyzer.TransferFunctions.Domain.pp a ;
        Some (Summary.of_state pdata s) in
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

let may_alias a1 a2 =
  let open AccessPath in
  let p1, p2 = a1.Atom.lvalue, a2.Atom.lvalue in
  let unrelated_types () =
    let get_type a =
      let p = a.Atom.lvalue in
      let (_,_,_,tenv) =
        Option.value_exn (List.last_exn a.Atom.path |> CallSite.pname |> Summary.get_summary) in
      (Option.value_exn(Raw.get_typ p tenv), tenv)
    in
    let (typ1, tenv1), (typ2, tenv2) = get_type a1, get_type a2 in
    match typ1, typ2 with
    | Typ.Tptr (Typ.Tstruct tn1, _), Typ.Tptr (Typ.Tstruct tn2, _) ->
        not (PatternMatch.is_subtype tenv1 tn1 tn2) &&
        not (PatternMatch.is_subtype tenv2 tn2 tn1)
    | _, Typ.Tstruct _ | Typ.Tstruct _, _ -> assert false
    | _, _ -> false
  in
  let res = match List.last_exn (snd p1), List.last_exn (snd p2) with
    | FieldAccess _, ArrayAccess _ | ArrayAccess _, FieldAccess _ -> false
    | ArrayAccess _, ArrayAccess _ -> assert false (*FIXME*)
    (* fields in Infer contain class name *)
    | FieldAccess f1, FieldAccess f2 when
        not (String.equal
          (Ident.java_fieldname_get_field f1)
          (Ident.java_fieldname_get_field f2))
        ||
        unrelated_types ()
      -> false
    | _, _ -> true
(* if type of lvalue is primitive then the lvalues may alias
   if the types are equal and the enclosing types may alias
   | Typ.Tint _, _ | Typ.Tfloat _, _ ->
    Typ.equal typ1 typ2 &&
    may_alias_ tenv1 (Raw.truncate p1) tenv2 (Raw.truncate p2) *)
(* | _ ->
        let pre1, pre2 = Raw.truncate p1, Raw.truncate p2 in
        not (Typ.equal typ1 typ2) *)
        (* match typ1, typ2 with
        (* if type of lvalue is primitive then the lvalues may alias
           if the types are equal and the enclosing types may alias *)
        | Typ.Tint _, _ | Typ.Tfloat _, _ ->
            Typ.equal typ1 typ2 &&
            may_alias_ tenv1 (Raw.truncate p1) tenv2 (Raw.truncate p2)
        | Typ.Tptr (Typ.Tstruct tn1, _), Typ.Tptr (Typ.Tstruct tn2, _)
        | Typ.Tstruct tn1, Typ.Tstruct tn2 ->
        | Typ.Tvoid , _ | _, Typ.Tvoid
        | Typ.Tfun _, _ | _, Typ.Tfun _
        | Typ.Tptr _, _ | _, Typ.Tptr _
        | Typ.Tarray _, _ | _, Typ.Tarray _ -> assert false (* FIXME *)
        | _, _ -> false *)
  in
  L.out "MAY_ALIAS? (%a <~> %a) = %b@." Atom.pp a1 Atom.pp a2 res ;
  res


(* let may_alias _ _ = true *)




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
  let to_z3 fmt s =
    Ident.IdentSet.iter (F.fprintf fmt "(declare-const %a Real)@." (Ident.pp Pp.text)) s in
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
  F.fprintf fmt "%a@." to_z3 vars ;
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


let should_analyze ((_,tenv,_,pdesc) as p) =
  should_analyze_proc pdesc tenv && should_report_on_proc p

(* run actual analysis, remembering proc info *)
let summarise get_proc_desc ((idenv, tenv, proc_name, proc_desc) as p) =
  let callback =
    {Callbacks.get_proc_desc; get_procs_in_file = (fun _ -> []);
     idenv; tenv; proc_name; proc_desc} in
  match compute_and_store_post callback with
  | Some sum -> Some (p, sum)
  | None -> None

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

(* merge sets of variables, constraint maps and extra constraints for each method pair,
   and bound every permission variable along the way *)
let merge compiled =
  let aux (vars, ctr_map, star_intro_ctrs) (ctr_map_, star_intro_ctr_) =
    let vars_ =
      IntMap.fold
        (fun _ (c,_) acc -> Ident.IdentSet.union (Constr.vars c) acc)
        ctr_map
        (Constr.vars star_intro_ctr_)
    in
    let vars' = Ident.IdentSet.union vars vars_ in
    let star_intro_ctrs' = star_intro_ctr_ :: star_intro_ctrs in
    let ctr_map' =
      IntMap.merge
        (fun _ c1 c2 ->
           match c1, c2 with
           (* int key is the hash of a constraint so we must never have a conflict *)
           | None, None | Some _, Some _ -> assert false
           | None, Some c | Some c, None -> Some c
        )
        ctr_map
        ctr_map_
    in
    (vars', ctr_map', star_intro_ctrs')
  in
  let vars, ctr_map, star_intro_ctrs =
    List.fold compiled ~init:(Ident.IdentSet.empty, IntMap.empty, []) ~f:aux in
  let bounded_ctrs =
    Ident.IdentSet.fold
      (fun v acc -> (Constr.mk_lb [v])::(Constr.mk_ub [v])::acc)
      vars
      star_intro_ctrs in
  (vars, ctr_map, bounded_ctrs @ star_intro_ctrs)

(* for a given pair of methods, generate appropriate constraints *)
let compile_case partition locks invmap summaries =
  (* for each method create a precondition permission variable for the given location *)
  let pres = List.map summaries ~f:(fun _ -> mk_permvar ()) in
  (* for a given summary and precondition var generate constraints
  as well as a map that will allow converting back from a Z3 unsat core *)
  let compile_summary ctr_map pre (sum_atoms, _, _, _) =
    Atom.Set.fold
      (fun a acc ->
         let c = Atom.compile pre invmap a in
         IntMap.add (Hashtbl.hash c) (c, a) acc
      )
      (Atom.Set.inter partition sum_atoms)
      ctr_map
  in
  let ctr_map = List.fold2_exn pres summaries ~init:IntMap.empty ~f:compile_summary in
  let lockinvs = List.map locks ~f:(fun l -> Lock.Map.find l invmap) in
  (* add the constraint by star introduction *)
  let star_intro_ctr = Constr.mk_eq_one (pres @ lockinvs) in
  (ctr_map, star_intro_ctr)


(* combine list of summaries of methods called in parallel,
   currently expects a pair of summaries as we only consider two threads --
   this is meant to be generalised in the future to n threads *)
let process_case = function
  | [ (_, sum1); (_, sum2)] -> [sum1; sum2]
  | _ -> assert false

(* run the analysis relative to the given heap location *)
let analyse_location locks summary_pairs partition =
  (* let accesses_partition (_,(atoms,_,_,_)) =
    not (Atom.Set.is_empty (Atom.Set.inter atoms partition)) in *)
  (* only keep method pairs that both access the given location *)
  (* let summary_pairs =
     List.filter summary_pairs ~f:(List.for_all ~f:accesses_partition) in *)
  (* build a map from locks to permission variables in each lock's resource invariant *)
  let invmap =
    List.fold
      locks
      ~init:Lock.Map.empty
      ~f:(fun acc l -> Lock.Map.add l (mk_permvar ()) acc)
  in
  (* throw away info from file_env -- we don't need it for now *)
  let cases = List.map ~f:process_case summary_pairs in
  (* for each pair of methods, generate the permissions constraints *)
  let compiled = List.map ~f:(compile_case partition locks invmap) cases in
  let merged = merge compiled in
  run_check merged

let analyse_class get_proc_desc _ methods =
  L.out "SUMMARISATION START@." ;
  (* summarise all methods -- NB for now we ignore methods that fail analysis. *)
  let method_summaries =
    List.filter ~f:should_analyze methods |>
    List.map ~f:(summarise get_proc_desc) |>
    List.filter_opt in
  (* compute all atoms and locks across all methods *)
  L.out "SUMMARISATION END@." ;
  let (locks_set, all_atoms) =
    List.fold
      method_summaries
      ~init:(Lock.Set.empty, Atom.Set.empty)
      ~f:(fun (lock_acc, atoms_acc) (_, ((atoms, _, _, _) as sum)) ->
          let lock_acc' = Summary.get_lockset sum |> Lock.Set.union lock_acc in
          let atoms_acc' = Atom.Set.union atoms atoms_acc in
          (lock_acc', atoms_acc')
        )
  in
  let locks = Lock.Set.elements locks_set in
  L.out "LOCKS %d /ATOMS %d @." (List.length locks) (Atom.Set.cardinal all_atoms);
  (* quotient set of atoms by may_alias *)
  let partitions = Atom.Set.quotient may_alias all_atoms in
  L.out "PARTITIONS@." ;
  (* create all pairs of analyseable methods *)
  let summary_pairs = all_pairs method_summaries in
  (* for each heap location, run the analysis on the method pairs *)
  List.iter ~f:(analyse_location locks summary_pairs) partitions

(* partition methods in file by class and then run analyse_class on each set *)
let file_analysis _ _ get_proc_desc file_env =
  let get_class = function
    | Typ.Procname.Java java_pname -> Typ.Procname.java_get_class_type_name java_pname
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
  ClassMap.iter (analyse_class get_proc_desc) classmap
