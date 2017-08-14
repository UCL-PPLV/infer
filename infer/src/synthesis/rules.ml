open! IStd
open! SynSpecs

type c_instr_type = Sil.instr list   
type subst_type = Ident.t * Exp.t
type ident_type = Pvar.t * Typ.t
type points_to_type = Pvar.t * Exp.t

type syn_spec =
  (* Gamma: available parameters and local variables *)
  ident_type list *
  (* Expected precondition *)
  Prop.exposed Prop.t *
  (* Expected postcondition *)
  Prop.exposed Prop.t 

type rule_result = 
  | RSuccess of
      (* Subgoal spec *)
      syn_spec *
      (* List of commands to be appended to subgoals *)
      c_instr_type
  | RFail

let find_all_pointsto sigma : points_to_type list = 
  List.filter_map ~f:(fun (exp, pv) ->
    let found_ptsto = List.find ~f:(fun hpred ->
      match hpred with 
      | Sil.Hpointsto (e, _, _) -> Exp.equal exp e
      | _ -> false
    ) sigma in 
    match found_ptsto with 
    | None -> None
    | Some Sil.Hpointsto (_, Eexp (v, _), _) -> Some (pv, v)
    | _ -> assert false (* Should be unreachable *)
  ) (create_pvar_env_list sigma) @ 
  List.filter_map ~f:(function
    | Sil.Hpointsto (Lvar pv, Eexp (Const v, _), _)  -> Some (pv, Exp.Const v)
    | _ -> None 
    ) sigma

let find_pointsto_cond (cond : points_to_type -> bool) sigma : points_to_type option =
  let all_points_to = find_all_pointsto sigma in
  let good_pts = List.filter ~f:cond all_points_to in
  match good_pts with
  | h :: _ -> Some h
  | _ -> None

let find_ghost_pts = find_pointsto_cond (fun (i, e) ->
    match e with
    | Exp.Var v when Ident.is_primed v -> true
    | _ -> false)

(* Returns:
- ident_type - a name for the new fresh local variable
- c_instr - a list of low-level instructions representing the read
- subst_type - a substitution to be applied to previous spec (pre/post)
*)
let mk_c_read (proc_name : Typ.Procname.t) (v : Ident.t) (rhs : Pvar.t) :
  ident_type * c_instr_type * subst_type =
  let local_name = Ident.create_fresh Ident.knormal in 
  let lhs = Pvar.mk (Mangled.from_string (Ident.to_string local_name)) proc_name in 
  let subst = (v, Exp.Var local_name) in

  let temp1 = Ident.create_fresh Ident.knormal in 
  let temp2 = Ident.create_fresh Ident.knormal in 
  let p_typ = Typ.mk (Typ.Tptr (Typ.mk (Typ.Tint(Typ.IInt)), Typ.Pk_pointer)) in 
  let typ = get_typ_from_ptr_exn p_typ in 
  let instrs = 
    [ Sil.Load (temp1, Exp.Lvar rhs, p_typ, Location.dummy)
    ; Sil.Load (temp2, Exp.Var temp1, typ, Location.dummy)
    ; Sil.Store (Exp.Lvar lhs, typ, Exp.Var temp2, Location.dummy)
    ; Sil.Remove_temps ([temp1; temp2], Location.dummy)
    ; Sil.Abstract (Location.dummy) ] in
  (lhs, typ), instrs, subst

(* Apply the read rule to a single ghost-pointing entry in the
   precondition via the following derivation:

 y is fresh   Γ,y ; [y/A]{ φ ; x -> A * P } ; [y/A]{ ψ ; Q } ---> S
------------------------------------------------------------------------------ [read]
            Γ ; { φ ; x -> A * P } ; { ψ ; Q } ---> let y := *x ; S

   In the case of success, the result is a new read-instruction, 
   pre/post with substituted ghost by a freshly generated local y, and
   also Г, which is extended with y.

*)
let read_rule proc_name gamma
    (given_pre: Prop.exposed Prop.t)
    (given_post: Prop.exposed Prop.t) (): rule_result = 
  let ptsto = find_ghost_pts given_pre.sigma in
  match ptsto with
  | None -> RFail
  | Some (pvar, Exp.Var v) -> 
      let lhs_typ, instrs, subst' = mk_c_read proc_name v pvar in
      let subst = Sil.subst_of_list [subst'] in
      let new_pre, new_post = (Prop.prop_sub subst given_pre,
                               Prop.prop_sub subst given_post) in
      let new_gamma = lhs_typ :: gamma in
      RSuccess ((new_gamma, new_pre, new_post), instrs)
  | _ -> RFail

(* let write_rule pvars_locals (actual_post: Prop.normal Prop.t)
  (given_post: Prop.exposed Prop.t): rule_result =
  
  let curr_ptsto = find_pointsto actual_post.sigma in
  let desired_ptsto = find_pointsto given_post.sigma in

  (* [TODO] Refactor all this into a separate function *)
  let ptsto_diff_list = List.filter_map ~f:(fun (pv_curr, exp_curr) ->
    let found_in_desired = List.find ~f:(fun (pv_des, _) ->
      Pvar.equal pv_curr pv_des
    ) desired_ptsto in
    match found_in_desired with
    | None -> None
    | Some (_, exp_des) ->
      match exp_des with
      | Exp.Const _ as const -> Some (pv_curr, const)
      | _ ->
        if Exp.equal exp_curr exp_des then None
        else
        let found_original_ptsto = List.find ~f:(fun (_, exp_orig) ->
          Exp.equal exp_des exp_orig
        ) curr_ptsto in
        match found_original_ptsto with
        | None -> None
        | Some (pv_orig, _) ->
          let pv_orig_local = List.find ~f:(fun (pv, _) ->
            Pvar.equal pv_orig pv
          ) pvars_locals in
          match pv_orig_local with
          | None -> None
          | Some (_, local) -> Some (pv_curr, Exp.Lvar local)
  ) curr_ptsto in

  match ptsto_diff_list with
  | [] -> RFail
  | diff_list -> RSuccess (
      (* Apply the rule to the list of diffs to synthesize all the writes *)
      List.map ~f:(fun (pv, exp) ->
        match exp with
        | Exp.Const const ->
          let temp = Ident.create_fresh Ident.knormal in
          let p_typ = Typ.mk (Typ.Tptr
            (Typ.mk (Typ.Tint(Typ.IInt)), Typ.Pk_pointer)) in
          let typ = get_typ_from_ptr_exn p_typ in
          [ Sil.Load (temp, Exp.Lvar pv, p_typ, Location.dummy)
          ; Sil.Store (Exp.Var temp, typ, Exp.Const const, Location.dummy)
          ; Sil.Remove_temps ([temp], Location.dummy)
          ; Sil.Abstract (Location.dummy) ]
        | Exp.Lvar local ->
          let temp1 = Ident.create_fresh Ident.knormal in
          let temp2 = Ident.create_fresh Ident.knormal in
          let p_typ = Typ.mk (Typ.Tptr
            (Typ.mk (Typ.Tint(Typ.IInt)), Typ.Pk_pointer)) in
          let typ = get_typ_from_ptr_exn p_typ in
          [ Sil.Load (temp1, Exp.Lvar pv, p_typ, Location.dummy)
          ; Sil.Load (temp2, Exp.Lvar local, typ, Location.dummy)
          ; Sil.Store (Exp.Var temp1, typ, Exp.Var temp2, Location.dummy)
          ; Sil.Remove_temps ([temp1; temp2], Location.dummy)
          ; Sil.Abstract (Location.dummy) ]
        | _ -> assert false
      ) diff_list
    ) *)
