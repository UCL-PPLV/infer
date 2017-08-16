open! IStd
open! SynSpecs

module F = Format

type c_instr_type = Sil.instr list   
type subst_type = Ident.t * Exp.t
type ident_type = Pvar.t * Typ.t
type points_to_type = Pvar.t * Exp.t

type c_instr_node = { instrs: c_instr_type
                    ; mutable fst_succ: c_instr_node option
                    ; mutable snd_succ: c_instr_node option}

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
      c_instr_node
  | RFail

let mk_c_instr_node ?(fst_succ=None) ?(snd_succ=None) instrs =  
  {instrs; fst_succ; snd_succ}

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

let find_ghost_pts = find_pointsto_cond (fun (_, e) ->
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
    ; Sil.Abstract (Location.dummy) ]
  in
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
  | Some (pvar, Exp.Var v) -> 
      let lhs_typ, instrs, subst' = mk_c_read proc_name v pvar in
      let subst = Sil.subst_of_list [subst'] in
      let new_pre, new_post = (Prop.prop_sub subst given_pre,
                               Prop.prop_sub subst given_post) in
      let new_gamma = lhs_typ :: gamma in
      RSuccess ((new_gamma, new_pre, new_post), mk_c_instr_node instrs)
  | _ -> RFail

let find_diff_pts ptsto_list1 ptsto_list2 = 
  List.filter_map ~f:(fun (pv1, exp1) ->
    List.hd (List.filter_map ~f:(fun (pv2, exp2) ->
      if ((Pvar.equal pv1 pv2) && not (Exp.equal exp1 exp2)) then
        Some (pv1, exp2)
      else None
    ) ptsto_list2)
  ) ptsto_list1

let mk_c_write (lhs : Pvar.t) (new_v : Exp.t) 
  (given_pre : Prop.exposed Prop.t) : c_instr_type * Prop.exposed Prop.t = 
  let new_pre = 
    let new_sigma = 
      let pvar_ptsto = fst (List.hd_exn (List.filter ~f:(fun (_, pv) -> 
        Pvar.equal lhs pv
      ) (create_pvar_env_list given_pre.sigma))) in 
      List.map ~f:(fun hpred -> 
        match new_v with 
        | Exp.Var _ -> 
          begin
          if not (Exp.equal pvar_ptsto (Sil.hpred_get_lhs hpred)) then hpred 
          else 
            match hpred with 
            | Sil.Hpointsto (lh_alias, Eexp (_, inst), typ) -> 
              Sil.Hpointsto (lh_alias, Eexp (new_v, inst), typ)
            | _ -> hpred 
          end
        | Exp.Const _ -> 
          begin
          if not (Exp.equal (Exp.Lvar lhs) (Sil.hpred_get_lhs hpred)) then hpred 
          else
            match hpred with 
            | Sil.Hpointsto (lh, Eexp (_, inst), typ) -> 
              Sil.Hpointsto (lh, Eexp (new_v, inst), typ)
            | _ -> hpred
          end
        | _ -> hpred
      ) given_pre.sigma
    in 
    Prop.set ~sigma:new_sigma given_pre 
  in 
  let instrs = match new_v with 
  | Exp.Var local -> 
    let temp1 = Ident.create_fresh Ident.knormal in
    let temp2 = Ident.create_fresh Ident.knormal in
    let p_typ = Typ.mk (Typ.Tptr
      (Typ.mk (Typ.Tint(Typ.IInt)), Typ.Pk_pointer)) in
    let typ = get_typ_from_ptr_exn p_typ in 
    [ Sil.Load (temp1, Exp.Lvar lhs, p_typ, Location.dummy)
    ; Sil.Load (temp2, Exp.Var local, typ, Location.dummy)
    ; Sil.Store (Exp.Var temp1, typ, Exp.Var temp2, Location.dummy)
    ; Sil.Remove_temps ([temp1; temp2], Location.dummy)
    ; Sil.Abstract (Location.dummy) ]
  | Exp.Const const ->
    let temp = Ident.create_fresh Ident.knormal in
    let p_typ = Typ.mk (Typ.Tptr
      (Typ.mk (Typ.Tint(Typ.IInt)), Typ.Pk_pointer)) in
    let typ = get_typ_from_ptr_exn p_typ in
    [ Sil.Load (temp, Exp.Lvar lhs, p_typ, Location.dummy)
    ; Sil.Store (Exp.Var temp, typ, Exp.Const const, Location.dummy)
    ; Sil.Remove_temps ([temp], Location.dummy)
    ; Sil.Abstract (Location.dummy) ]
  | _ -> assert false
  in 
  (instrs, new_pre)

let write_rule gamma (given_pre: Prop.exposed Prop.t)
  (given_post: Prop.exposed Prop.t) (): rule_result =

  let curr_ptsto = find_all_pointsto given_pre.sigma in
  let desired_ptsto = find_all_pointsto given_post.sigma in

  let diff_ptsto = (find_diff_pts curr_ptsto desired_ptsto) in 

  match (List.hd diff_ptsto) with
  | None -> RFail 
  | Some (pv, exp2) -> 
    let instrs, new_pre = mk_c_write pv exp2 given_pre in
    RSuccess ((gamma, new_pre, given_post), mk_c_instr_node instrs)

(* Make a conditional expression
   Returns - node before the branch
   Args - cond_exp: the conditional expression 
        - instrs_true: the first node of the true-branch instructions
        - instrs_false: the first node of the false-branch instructions
*)
let mk_conditional (cond_exp: Exp.t) (* Likely BinOp *) 
  (instrs_true: c_instr_node option) (instrs_false: c_instr_node option)
  : c_instr_node = 
  let prune_true_instr = Sil.Prune (cond_exp, Location.dummy, true, Sil.Ik_if) in 
  let prune_true_node = Some (mk_c_instr_node [prune_true_instr] ~fst_succ:instrs_true) in 

  let prune_false_instr = Sil.Prune (cond_exp, Location.dummy, true, Sil.Ik_if) in 
  let prune_false_node = Some (mk_c_instr_node [prune_false_instr] ~fst_succ:instrs_false) in 

  let branch_node = mk_c_instr_node [] ~fst_succ:prune_true_node ~snd_succ:prune_false_node in 
  branch_node

(* All combinations of taking n elements from ls - returns a list of lists *)
let rec extract n ls =
  if n <= 0 then [[]]
  else match ls with
  | [] -> []
  | h :: tl ->
    let with_h = List.map ~f:(fun l -> h :: l) (extract (n-1) tl) in
    let without_h = extract n tl in
    with_h @ without_h

(* All permutations of a list - returns a list of lists *)
let rec permutations = 
  let ins_all_positions x l =
    let rec perm_aux prev acc = function
      | [] -> (prev @ [x]) :: acc |> List.rev
      | hd::tl as l -> perm_aux (prev @ [hd]) ((prev @ [x] @ l) :: acc) tl
    in
    perm_aux [] [] l
  in
  function
  | [] -> []
  | x::[] -> [[x]] 
  | x::xs -> 
      List.fold_left ~init:[] ~f:(fun acc p -> acc @ ins_all_positions x p) (permutations xs)


let mk_fun_call_node (ret_opt: (Ident.t * Typ.t) option) (fun_name : string)
  (params : (Exp.t * Typ.t) list) = 
  let proc_name = Exp.Const (Const.Cfun (Typ.Procname.from_string_c_fun fun_name)) in 
  let func_call_instr = Sil.Call (ret_opt, proc_name, params, Location.dummy, CallFlags.default) in

  mk_c_instr_node [func_call_instr]

let func_change_pre sub (given_pre: Prop.exposed Prop.t) (fun_pre: Prop.exposed Prop.t)
  (fun_post: Prop.exposed Prop.t) = 
  (* Use sub2 to substitute primed variables in fun_pre and fun_post *)
  let fun_pre = Prop.prop_sub (Sil.subst_of_list (Sil.sub_to_list sub)) fun_pre in
  let fun_post = Prop.prop_sub (Sil.subst_of_list (Sil.sub_to_list sub)) fun_post in 

  (* Find program variables referenced by fun_post in given_pre and alter 
  the value they point to to match fun_post *)
  let new_pre_sigma = List.map ~f:(fun hpred -> 
    let found_in_fun_pre = List.find ~f:(fun hpred_fpost ->
      Exp.equal (Sil.hpred_get_lhs hpred) (Sil.hpred_get_lhs hpred_fpost)
    ) fun_post.sigma in 
    match found_in_fun_pre with 
    | None -> hpred
    | Some hpred_fpost -> 
    hpred_fpost 
  ) given_pre.sigma in 

  (* Remove atoms from pre that are in fun_pre and add parts from fun_post *)
  let new_pre_pi = 
    List.filter_map ~f:(fun atom ->
      if List.mem fun_pre.pi atom ~equal:Sil.equal_atom then None 
      else Some atom
    ) given_pre.pi @ 
    fun_post.pi in

  Prop.set ~sigma:new_pre_sigma ~pi:new_pre_pi given_pre 
 
(* Incomplete: need to choose params properly *)
let func_call_rule tenv proc_desc gamma (given_pre : Prop.exposed Prop.t) 
  (given_post : Prop.exposed Prop.t) procspec (): rule_result = 
  let proc_name = Procdesc.get_proc_name proc_desc in 

  let fun_pre, fun_post = make_spec procspec tenv proc_name in
  let fun_params = procspec.Parsetree.proc.params in 
  let ret_val = if String.equal procspec.Parsetree.proc.ret_typ "void" then None 
                else Some (Ident.create_fresh Ident.knormal, Typ.mk (Typ.Tint(Typ.IInt))) in
  let fun_name = procspec.Parsetree.proc.id in 

  let n_params = List.length fun_params in 
  let possible_params = List.concat (List.map ~f:permutations (extract n_params gamma)) in

  (* TODO: Instantiate Pvars in function preposts with each of? the possible_params
     At the moment it just takes the first possible param combination *)
  let params' = List.hd_exn possible_params in 
  let params = List.map ~f:(fun (pvar, typ) -> (Exp.Lvar pvar, typ)) params' in 

  match Prover.check_implication_for_footprint proc_name tenv 
    (Prop.normalize tenv given_pre) fun_pre with
  | ImplFail _ -> RFail (* Current pre |/- function pre *)
  | ImplOK (_, _, sub2, _, _, _, _, _, _, _) -> 

    let new_pre = func_change_pre sub2 given_pre fun_pre fun_post in 

    (* placeholder *)
    RSuccess ((gamma, new_pre, given_post), 
              mk_fun_call_node ret_val fun_name params)

 
