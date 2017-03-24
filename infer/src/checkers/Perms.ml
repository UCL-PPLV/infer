open! IStd

module T = ThreadSafetyDomain
module F = Format
module L = Logging

let mk_permvar () =
  Ident.create_fresh Ident.kprimed

module Constr = struct
  type t = Exp.t

  let rec sum = function
    | [p] -> Exp.Var p
    | p::ps -> Exp.BinOp (Binop.PlusA, Exp.Var p, sum ps)
    | _ -> assert false

  let mk_sum q ps =
    Exp.eq (Exp.Var q) (sum ps)
  let mk_lb ps =
    Exp.BinOp (Binop.Ge, sum ps, Exp.zero)
  let mk_ub ps =
    Exp.BinOp (Binop.Le, sum ps, Exp.one)
  let mk_eq_one ps =
    Exp.eq (sum ps) (Exp.one)
  let mk_gt_zero ps =
    Exp.BinOp (Binop.Gt, sum ps, Exp.zero)

  let rec to_z3 fmt e = match e with
    | Exp.Var id ->
        F.pp_print_string fmt (Ident.to_string id)
    | Exp.BinOp(Binop.Eq, t1, t2) ->
        F.fprintf fmt "(= %a %a)" to_z3 t1 to_z3 t2
    | Exp.BinOp(op, t1, t2) ->
        F.fprintf fmt "(%s %a %a)" (Binop.str Pp.text op) to_z3 t1 to_z3 t2
    | Exp.Const _ ->
        F.pp_print_string fmt (if Exp.is_zero e then "0.0" else "1.0")
    | _ ->
        assert false

  let rec vars = function
    | Exp.Var v -> Ident.IdentSet.singleton v
    | Exp.BinOp(_, t1, t2) -> Ident.IdentSet.union (vars t1) (vars t2)
    | _ -> Ident.IdentSet.empty

  (* ordered set of permission constraints *)
  module Set = struct
    include PrettyPrintable.MakePPSet(Exp)

    (* variables of a constraint set *)
    let vars c =
      fold (fun exp a -> Ident.IdentSet.union (vars exp) a) c Ident.IdentSet.empty
  end
end

(* let should_report_on_proc (_, _, proc_name, proc_desc) =
  not (Typ.Procname.java_is_autogen_method proc_name) &&
  Procdesc.get_access proc_desc <> PredSymb.Private &&
  not (Annotations.pdesc_return_annot_ends_with proc_desc Annotations.visibleForTesting) *)

(* compute all pairs (as lists) but disregarding order within the pair *)
let all_pairs =
  let rec aux = function
    | [] -> []
    | (x::xs) as all ->
      let with_x = List.map ~f:(fun y -> [x;y]) all in
      with_x @ (aux xs) in
  aux

let may_alias _ _ = true
  (* let open AccessPath in
  let unrelated_types () =
    let get_type p =
      let (_,_,_,tenv) =
        Option.value_exn
          (List.last_exn a.Atom.path |> CallSite.pname |> Summary.get_summary) in
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
   if the types are equal and the enclosing types may alias *)
   | Typ.Tint _, _ | Typ.Tfloat _, _ ->
    Typ.equal typ1 typ2 &&
    may_alias_ tenv1 (Raw.truncate p1) tenv2 (Raw.truncate p2)
  in
  L.out "MAY_ALIAS? (%a <~> %a) = %b@." Atom.pp a1 Atom.pp a2 res ;
  res *)

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
  (* F.fprintf fmt "(set-option :dump-models true)@." ; *)
  (* ask for an unsat core if unsat *)
  F.fprintf fmt "(set-option :unsat_core true)@." ;
  (* request decimals, not fractions, may append "?" if imprecise *)
  (* F.fprintf fmt "(set-option :pp.decimal true)@." ; *)
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
        let traceelems = List.map is ~f:(fun i -> snd (IntMap.find i ctr_map)) in
        (* let traceelems = T.TraceElem.Set.of_list traceelems in *)
        let () =
          List.iter ~f:(fun (_,c,_) -> L.out "Z3: unsat core: %a@." T.TraceElem.pp c) traceelems in
        (* let w = T.TraceElem.Set.choose (T.TraceElem.Set.filter T.TraceElem.is_write traceelems) in *)
        let (_,w,_) = List.hd_exn traceelems in
        (* let traceelems = T.TraceElem.Set.elements (T.TraceElem.Set.remove w traceelems) in *)
        let traceelems = List.map (List.tl_exn traceelems) ~f:(fun (_,t,_) -> t) in
        let site = T.TraceElem.call_site w in
        let pname, loc = CallSite.pname site, CallSite.loc site in
        let msg = Localise.to_issue_id Localise.thread_safety_violation in
        let description =
          match traceelems with
          | [] -> F.asprintf "The <%a> is a potential self-race." T.TraceElem.pp w
          | _ -> F.asprintf "The <%a> potentially races with:@.%a" T.TraceElem.pp w
                   (Pp.comma_seq T.TraceElem.pp) traceelems
        in
        let ltr = [Errlog.make_trace_element 0 loc "" []] in
        let exn = Exceptions.Checkers (msg, Localise.verbatim_desc description) in
        L.out "about to report %a" Typ.Procname.pp pname ;
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
      [] in
  (vars, ctr_map, bounded_ctrs @ star_intro_ctrs)

let compile_access pre inv k t =
  (* L.out "compiling %a %a@." T.AccessPrecondition.pp k T.TraceElem.pp t ; *)
  let (_, access) = T.TraceElem.kind t in
  let definitely_locked = match k with
    | T.AccessPrecondition.Protected -> true
    | _ -> false  in
  let vars = if definitely_locked then [pre;inv] else [pre] in
  match access with
  | T.Access.Read -> Constr.mk_gt_zero vars
  | T.Access.Write -> Constr.mk_eq_one vars

let compile_summary partition inv ctr_map pre (_,_,accesses,_) =
  let pd_to_triples (k, paths) =
    T.PathDomain.get_reports paths |>
    List.map ~f:(fun (_,t,ps) -> (k, t, T.PathDomain.Passthroughs.elements ps))
  in
  let elems =
    T.AccessDomain.bindings accesses |>
    List.map ~f:pd_to_triples |>
    List.concat |>
    List.filter ~f:(fun (_,t,_) -> T.PathDomain.Sinks.mem t partition) in
  List.fold elems
    ~init:ctr_map
    ~f:(fun acc ((k, t, _) as elem)->
        let c = compile_access pre inv k t in
        IntMap.add (Hashtbl.hash c) (c, elem) acc
      )

(* for a given pair of methods, generate appropriate constraints *)
let compile_case partition inv summaries =
  (* for each method create a precondition permission variable for the given location *)
  let pres = List.map summaries ~f:(fun _ -> mk_permvar ()) in
  (* for a given summary and precondition var generate constraints
  as well as a map that will allow converting back from a Z3 unsat core *)
  let ctr_map = List.fold2_exn pres summaries ~init:IntMap.empty ~f:(compile_summary partition inv) in
  (* add the constraint by star introduction *)
  let star_intro_ctr = Constr.mk_eq_one (inv :: pres) in
  (ctr_map, star_intro_ctr)

(* run the analysis relative to the given heap location *)
let analyse_location cases partition =
  (* let summary_pairs =
     List.filter summary_pairs ~f:(List.for_all ~f:accesses_partition) in *)
  let inv = mk_permvar () in
  (* L.out "compiling %d cases@." (List.length cases) ; *)
  let compiled = List.map ~f:(compile_case partition inv) cases in
  let merged = merge compiled in
  run_check merged

let quotient pred2 init =
  let rec aux acc s =
    if T.PathDomain.Sinks.is_empty s then acc else
      let a = T.PathDomain.Sinks.choose s in
      let (a_part, non_a_part) = T.PathDomain.Sinks.partition (pred2 a) s in
      aux (a_part::acc) non_a_part
  in
  aux [] init

let should_analyze (_,_,_,pdesc) =
  let pn = Procdesc.get_proc_name pdesc in
  not (Typ.Procname.is_constructor pn) &&
  not (Typ.Procname.is_class_initializer pn) &&
  not (FbThreadSafety.is_logging_method pn)

let summary_to_paths (_,_,accesses,_) =
  T.AccessDomain.fold
    (fun _ v acc -> T.PathDomain.join v acc)
    accesses
    T.PathDomain.empty

let analyse_class get_proc_desc _ methods =
  let summarise (idenv, tenv, proc_name, proc_desc) =
    let callback_arg =
      let summary = Specs.get_summary_unsafe "compute_post_for_procedure" proc_name in
      let get_procs_in_file _ = [] in
      { Callbacks.get_proc_desc; get_procs_in_file; idenv; tenv; summary; proc_desc } in
      (ThreadSafety.checker callback_arg).Specs.payload.threadsafety
  in
  let method_summaries =
    List.filter methods ~f:should_analyze |> List.map ~f:summarise |> List.filter_opt in
  (* L.out "Found %d summaries@." (List.length method_summaries) ; *)
  let all_accesses =
    List.fold
      method_summaries
      ~init:T.PathDomain.empty
      ~f:(fun acc s -> summary_to_paths s |> T.PathDomain.join acc)
  in
  let all_traceelems = T.PathDomain.sinks all_accesses in
  let partitions = quotient may_alias all_traceelems in
  let summary_pairs = all_pairs method_summaries in
  List.iter ~f:(analyse_location summary_pairs) partitions

module ClassMap = PrettyPrintable.MakePPMap(Typ.Name)

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
