open! IStd
open! SynSpecs

type rule_result = RSuccess of Sil.instr list list | RFail

let write_rule pvars_locals (actual_post: Prop.normal Prop.t)
  (given_post: Prop.exposed Prop.t): rule_result =
  let find_pointsto sigma =
    (* [Q] What this first component is for? *)
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
  in
  
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
    )
