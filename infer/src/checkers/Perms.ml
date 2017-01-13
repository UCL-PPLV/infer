open! IStd

(* TODO
   (increasing importance)
   - Interprocedural
   - track breaking of soundness assumptions eg reentrancy
   - static fields?
   - include only public methods in check
   - finish check of parallel compositions
*)

open! PermsDomain

let get_class = function
  | Procname.Java java_pname -> Procname.java_get_class_type_name java_pname
  | _ -> assert false

module ClassMap =
  PrettyPrintable.MakePPMap
    (struct
      include Typename
      let pp_key = pp
    end)


module Summary = struct
  include Summary.Make (struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
    end)

  let of_state { pre; inv; constraints } =
    {
      sum_pre = pre;
      sum_inv = inv;
      sum_constraints = constraints
    }

  let subst theta { sum_pre; sum_inv; sum_constraints } =
    {
      sum_pre = Field.Map.map (Ident.subst theta) sum_pre;
      sum_inv = Field.Map.map (Ident.subst theta) sum_inv;
      sum_constraints = Constr.Set.map (Constr.subst theta) sum_constraints
    }

  (* let par_compose s1 s2 =
    assert (Field.Map.cardinal s1.sum_pre = Field.Map.cardinal s2.sum_pre) ;
    assert (Field.Map.cardinal s1.sum_inv = Field.Map.cardinal s2.sum_inv) ;
    assert (Field.Map.cardinal s1.sum_pre = Field.Map.cardinal s2.sum_inv) ;
    let new_pre = Field.Map.map (fun _ -> Ident.mk ()) s1.sum_pre in
    let mk_theta m =
      Field.Map.fold (fun _ v a -> Ident.Map.add v (Ident.mk ()) a) m Ident.Map.empty in
    let extend_with_inv m1 m2 a =
      Field.Map.fold
        (fun f v (a1,a2) ->
           let newv = Ident.mk () in
           let a1' = Ident.Map.add v newv a1 in
           let a2' = Ident.Map.add (Field.Map.find f m2) newv a2 in
           (a1',a2'))
        m1
        a in
    (* add constraints of the form x = x1 + x2, where x1/x2 are permissions *)
    (* in the pre, for the premise of the frame rule *)
    let add_splittings pre1 pre2 exps =
      Field.Map.fold
        (fun f v a ->
           let v1, v2 = Field.Map.find f pre1, Field.Map.find f pre2 in
           Constr.Set.add (Constr.mk_add v v1 v2) a
        )
        new_pre
        exps in
    (* create substitutions to distinct fresh variables for pre1 and pre2 *)
    let theta1, theta2 = mk_theta s1.sum_pre, mk_theta s2.sum_pre in
    (* extend substitutions with *shared* new fresh variables for inv1 and inv2 *)
    (* this means that for the same field f, theta1[inv1[f]]==theta2[sum_inv2[f]] *)
    let theta1, theta2 = extend_with_inv s1.sum_inv s2.sum_inv (theta1, theta2) in
    (* get all variables used in constraints *)
    let c1vars, c2vars = Constr.Set.vars s1.sum_constraints, Constr.Set.vars s1.sum_constraints in
    (* compute all those that are not in theta[pre U inv] *)
    let exist1 = Ident.Set.filter (fun v -> not (Ident.Map.mem v theta1)) c1vars in
    let exist2 = Ident.Set.filter (fun v -> not (Ident.Map.mem v theta2)) c2vars in
    (* extend substitutions with distinct fresh variables for the above vars *)
    let add_fresh v a = Ident.Map.add v (Ident.mk ()) a in
    let theta1 = Ident.Set.fold add_fresh exist1 theta1 in
    let theta2 = Ident.Set.fold add_fresh exist2 theta2 in
    (* perform substitutions on constraints *)
    let c1 = Constr.Set.subst theta1 s1.sum_constraints in
    let c2 = Constr.Set.subst theta2 s2.sum_constraints in
    let pre1 = Field.Map.map (Ident.subst theta1) s1.sum_pre in
    let pre2 = Field.Map.map (Ident.subst theta2) s2.sum_pre in
    let consts = add_splittings pre1 pre2 (Constr.Set.union c1 c2) in
    let consts =
      Ident.Set.fold
        (fun v a -> Constr.Set.add (Constr.mk_lb v) (Constr.Set.add (Constr.mk_ub v) a))
        (Constr.Set.vars consts)
        consts in
    {
      sum_pre = new_pre;
      (* resulting inv is the image of either substitution *)
      sum_inv = Field.Map.map (Ident.subst theta1) s1.sum_inv;
      (* add splitting constraints to the unioned result *)
      sum_constraints = consts;
    } *)

  let pp fmt { sum_pre; sum_inv; sum_constraints } =
    F.fprintf fmt "{ sum_pre=%a; sum_inv=%a; sum_constraints=%a }"
      (Field.Map.pp ~pp_value:Ident.pp) sum_pre
      (Field.Map.pp ~pp_value:Ident.pp) sum_inv
      Constr.Set.pp sum_constraints

end


(* Make a transfer functions module given the fields of a class *)
module MakeTransferFunctions(CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = PermsDomain.Domain
  type extras = ProcData.no_extras

  let do_mem mk_constr fieldname astate =
    if not (Field.Map.mem fieldname astate.curr) then
      L.out "%a not present in %a@." Field.pp fieldname State.pp astate;
    let fld_var = Field.Map.find fieldname astate.curr in
    State.add_constr (mk_constr fld_var) astate
  let do_store fieldname astate =
    do_mem Constr.mk_eq_one fieldname astate
  let do_load fieldname astate =
    do_mem Constr.mk_gt_zero fieldname astate

  (* stolen from ThreadSafety *)
  module TSTF = ThreadSafety.TransferFunctions(CFG)

  (* add or remove permissions from invariant *)
  let hale mk_constr a =
    Field.Map.fold
      (fun f lvar acc ->
         let v = Ident.mk () in
         let cn = mk_constr v lvar (Field.Map.find f a.inv) in
         acc |> State.add_fld f v |> State.add_constr cn
      )
      a.curr
      { a with curr = Field.Map.empty }

  let do_sync pn args astate =
    let exhale = hale Constr.mk_minus in
    let inhale = hale Constr.mk_add in
    (* decide if a lock statement is about "this" *)
    let lock_effect_on_this pn args astate =
      (* L.out "args=%a this_refs=%a@." (PrettyPrintable.pp_collection ~pp_item:Exp.pp) (IList.map fst args) Ident.Set.pp astate.this_refs; *)
      let this_arg = match args with
        | (Exp.Var ident, _)::_ -> Ident.Set.mem ident astate.this_refs
        | _ -> false in
      if this_arg then TSTF.get_lock_model pn else TSTF.NoEffect in
    match lock_effect_on_this pn args astate with
    | TSTF.Lock ->     inhale astate
    | TSTF.Unlock ->   exhale astate
    | TSTF.NoEffect -> astate

  (* actual transfer function *)
  let exec_instr astate { ProcData.pdesc; ProcData.tenv } _ cmd =
    let classname = get_class (Procdesc.get_proc_name pdesc) in
    (* L.out "Analysing instruction %a@." (Sil.pp_instr Pp.text) cmd ; *)
    match cmd with
    | Sil.Store (Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _, _)
      when PatternMatch.is_subtype tenv tname classname ->
      do_store fieldname astate
    | Sil.Load (_, Exp.Lfield(_, fieldname, Typ.Tstruct tname), _, _)
      when PatternMatch.is_subtype tenv tname classname ->
      do_load fieldname astate
    | Sil.Load (v,l,_,_) when Exp.is_this l ->
      State.add_ref v astate
    | Sil.Load (v,Exp.Var v',_,_) when Ident.Set.mem v' astate.this_refs ->
      State.add_ref v astate
    | Sil.Load (v,_,_,_) ->
      State.remove_ref v astate
    | Sil.Remove_temps (idents, _) ->
      IList.fold_left (fun a v -> State.remove_ref v a) astate idents
    (* | Sil.Load (_,l,_,_) ->
      L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
      L.out "***Root is = %a***@." Exp.pp (Exp.root_of_lexp l) ;
      astate *)
    | Sil.Call (_, Const (Cfun pn), args, _, _) ->
      do_sync pn args astate
    | _ -> astate
end

module Analyzer =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (MakeTransferFunctions)

module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* compute the summary of a method *)
let compute_and_store_post callback =
  (* retrieve the fields of a given class *)
  let get_fields pdesc =
    match Tenv.lookup pdesc.ProcData.tenv (get_class callback.Callbacks.proc_name) with
    | None -> assert false
    | Some { StructTyp.fields } ->
      Field.Set.of_list (IList.map (fun (fld, _, _) -> fld) fields) in
  let compute_post pdesc =
    let fields = get_fields pdesc in
    let initial =
      let m = Field.Map.mk fields in
      { State.empty with pre = m; curr = m; inv = Field.Map.mk fields } in
    let pdata = ProcData.make_default pdesc.ProcData.pdesc pdesc.ProcData.tenv in
    match Analyzer.compute_post ~initial pdata with
    | None -> None
    | Some a -> L.out "Found spec: %a@." Analyzer.TransferFunctions.Domain.pp a ;
      Some (Summary.of_state a) in
  Interprocedural.compute_and_store_post
    ~compute_post
    ~make_extras:ProcData.make_empty_extras
    callback

(* compute all pairs (as lists) but disregarding order within the pair *)
let all_pairs =
  let rec aux = function
    | [] -> []
    | (x::xs) as all ->
      let with_x = IList.map (fun y -> [x;y]) all in
      with_x @ (aux xs) in
  aux


let read_process_lines in_channel =
  let lines = ref [] in
  begin
    try
      while true do
        lines := input_line in_channel :: !lines
      done;
    with End_of_file ->
      ()
  end;
  List.rev !lines

(* create a list of substitutions from all inv variables of a list of lists of summaries
   to the same targets *)
let mk_inv_thetas ss =
  let vs =
    Field.Map.fold
      (fun f _ a -> Field.Map.add f (Ident.mk ()) a)
      ((IList.hd (IList.hd ss)).sum_inv)
      Field.Map.empty in
  let mk s =
    Field.Map.fold
      (fun f v acc -> Ident.Map.add v (Field.Map.find f vs) acc)
      s.sum_inv
      Ident.Map.empty in
  IList.map (IList.map mk) ss

let extend_with_pres thetas ss =
  let extend_with_pre theta sum =
    Field.Map.fold
      (fun _ v acc -> Ident.Map.add v (Ident.mk ()) acc)
      sum.sum_pre
      theta in
  IList.map2 (IList.map2 extend_with_pre) thetas ss

let extend_with_exists thetas ss =
  let extend_with_exist theta sum =
    let vars = Constr.Set.vars sum.sum_constraints in
    let evars = Ident.Set.filter (fun v -> not (Ident.Map.mem v theta)) vars in
    Ident.Set.fold (fun v acc -> Ident.Map.add v (Ident.mk ()) acc) evars theta in
  IList.map2 (IList.map2 extend_with_exist) thetas ss

let apply_substs thetas ss =
  IList.map2 (IList.map2 Summary.subst) thetas ss

let add_splits_and_flatten sums =
  let aux sums =
    let s = IList.hd sums in
    let new_pre = Field.Map.map (fun _ -> Ident.mk ()) s.sum_pre in
    let constrs =
      IList.fold_left
        (fun acc s' -> Constr.Set.union s'.sum_constraints acc)
        Constr.Set.empty
        sums in
    let constrs =
      Field.Map.fold
        (fun f v acc ->
           let vs = IList.map (fun s' -> Field.Map.find f s'.sum_pre) sums in
           let c = Constr.mk_sum v vs in
           Constr.Set.add c acc
        )
        new_pre
        constrs in
    {
      sum_inv = s.sum_inv;
      sum_pre = new_pre;
      sum_constraints = constrs
    } in
  IList.map aux sums

let file_analysis _ _ get_proc_desc file_env =
  let summarise ((idenv, tenv, proc_name, proc_desc) as p) =
    let callback =
      {Callbacks.get_proc_desc; get_procs_in_file = (fun _ -> []);
       idenv; tenv; proc_name; proc_desc} in
    (p, compute_and_store_post callback) in
  let classmap =
    IList.fold_left
      (fun a ((_,_,pname,_) as p) ->
         let c = get_class pname in
         let procs = try ClassMap.find c a with Not_found -> [] in
         ClassMap.add c (p::procs) a
      )
      ClassMap.empty
      file_env in
  let process_case = function
    | [ ((_,_,p1,_), Some sum1); ((_,_,p2,_), Some sum2)] -> ([p1; p2], [sum1; sum2])
    | _ -> assert false in
  let merge cases =
    let (_, summaries) = IList.split cases in
    let thetas = mk_inv_thetas summaries in
    let thetas = extend_with_pres thetas summaries in
    let thetas = extend_with_exists thetas summaries in
    let sums = apply_substs thetas summaries in
    let sums' = add_splits_and_flatten sums in
    let constraints =
      IList.fold_left
        (fun acc s -> Constr.Set.union s.sum_constraints acc)
        Constr.Set.empty
        sums' in
    let constraints =
      Ident.Set.fold
        (fun v a -> Constr.Set.add (Constr.mk_lb v) (Constr.Set.add (Constr.mk_ub v) a))
        (Constr.Set.vars constraints)
        constraints in
    constraints in
  let run_check merged =
    let in_ch,out_ch = Unix.open_process "z3 -in" in
    let fmt = F.formatter_of_out_channel out_ch in
    L.out "Passing to Z3:@.%a@." Constr.Set.pp merged ;
    F.fprintf fmt "%a@." Constr.Set.to_z3 merged ;
    Out_channel.close out_ch ;
    IList.iter (L.out "Z3 says: %s@.") (read_process_lines in_ch) ;
    ignore (Unix.close_process (in_ch, out_ch)) in
  let analyse_class _ procs =
    let summaries = IList.map summarise procs in
    let combinations = all_pairs summaries in
    let cases = IList.map process_case combinations in
    let merged = merge cases in
    run_check merged in
  ClassMap.iter analyse_class classmap
