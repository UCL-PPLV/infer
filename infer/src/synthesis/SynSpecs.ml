open! IStd

let get_typ_from_ptr_exn (ptr_typ: Typ.t) = match ptr_typ.desc with
  | Tptr (t, _) -> t 
  | _ -> failwith "Not a pointer type"

(* Create a alias list of Exp (temp var) * Pvar (real var) from a sigma *)
let create_pvar_env_list (sigma: Prop.sigma) : (Exp.t * Pvar.t) list =
  let env = ref [] in
  let filter = function
    | Sil.Hpointsto (Lvar pvar, Eexp (Var v, _), _) ->
        if not (Pvar.is_global pvar) then env := (Exp.Var v, pvar) :: !env
    | _ -> ()
  in
  List.iter ~f:filter sigma;
  !env

let make_spec (procspec: Parsetree.procspec) tenv proc_name  = 
  let raw_pre = procspec.pre in 
  let raw_post = procspec.post in
  let known_vals = ref [] in

  let make_sigma ?(primed=false) raw_sigma = List.concat (List.filter_map ~f:(fun pt_hpred ->
    match pt_hpred with 
    | Parsetree.Hpred_empty -> None
    | Parsetree.Hpred_hpointsto (pv_name, value) -> 
      let pvar = Pvar.mk (Mangled.from_string pv_name) proc_name in 
      let pvar_ptsto = 
        let found_pvar_loc = List.find ~f:(fun (n, _) -> 
          String.equal pv_name n) !known_vals in
        match found_pvar_loc with
        | None -> 
          let new_loc_var = Ident.create_fresh Ident.kprimed (* Ident.knormal *) in
          known_vals := (pv_name, new_loc_var) :: !known_vals;
          new_loc_var
        | Some p -> snd p
      in 
      match value with 
      | Parsetree.Int i -> 
        let int_const_exp = Exp.Const (Const.Cint(IntLit.of_int i)) in
        Some [(Prop.mk_ptsto tenv 
          (Exp.Lvar pvar) 
          (Sil.Eexp (int_const_exp, Sil.inst_none)) 
          (Exp.Sizeof {typ=(Typ.mk (Typ.Tint (Typ.IInt))); nbytes=None;
              dynamic_length=None; subtype=Subtype.exact}))]
      | Parsetree.Location name ->
        let found_known = List.find ~f:(fun (l, _) -> 
          String.equal l name) !known_vals in 
        match found_known with 
        | None ->
          let new_loc_var_ptsto = 
            if primed then Ident.create_fresh Ident.kprimed 
            else Ident.create_fresh Ident.kprimed (* Ident.knormal *) in 
          known_vals := (name, new_loc_var_ptsto) :: !known_vals;
          Some [
            (Prop.mk_ptsto tenv 
              (Exp.Lvar pvar) 
              (Sil.Eexp (Exp.Var pvar_ptsto, Sil.inst_none)) 
              (Exp.Sizeof {typ=(Typ.mk (Typ.Tptr (Typ.mk (Typ.Tint(Typ.IInt)), 
                Typ.Pk_pointer))); 
                  nbytes=None; dynamic_length=None; subtype=Subtype.exact}));
            (Prop.mk_ptsto tenv
              (Exp.Var pvar_ptsto) 
              (Sil.Eexp (Exp.Var new_loc_var_ptsto, Sil.inst_none)) 
              (Exp.Sizeof {typ=(Typ.mk (Typ.Tint(Typ.IInt))); 
                  nbytes=None; dynamic_length=None; subtype=Subtype.exact}))
            ]
        | Some (_, loc_var_ptsto) -> 
          Some [
           (Prop.mk_ptsto tenv 
              (Exp.Lvar pvar) 
              (Sil.Eexp (Exp.Var pvar_ptsto, Sil.inst_none)) 
              (Exp.Sizeof {typ=(Typ.mk (Typ.Tptr (Typ.mk (Typ.Tint(Typ.IInt)), 
                Typ.Pk_pointer))); 
                  nbytes=None; dynamic_length=None; subtype=Subtype.exact}));
            (Prop.mk_ptsto tenv
              (Exp.Var pvar_ptsto) 
              (Sil.Eexp (Exp.Var loc_var_ptsto, Sil.inst_none)) 
              (Exp.Sizeof {typ=(Typ.mk (Typ.Tint(Typ.IInt))); 
                  nbytes=None; dynamic_length=None; subtype=Subtype.exact}))
          ]
  ) raw_sigma) in 

  let make_pi raw_pi = List.filter_map ~f:(fun pt_atom -> 
    let rec make_atom raw_atom = 
      match raw_atom with 
      | Parsetree.Atom_empty -> None
      | Parsetree.Atom_not a -> 
        let atom = make_atom a in 
        begin
        match atom with 
        | None -> None
        | Some atom -> Some (Exp.UnOp (Unop.LNot, atom, None))
        end
      | Parsetree.Atom_eq (name, value) 
      | Parsetree.Atom_neq (name, value) 
      | Parsetree.Atom_lt (name, value) 
      | Parsetree.Atom_gt (name, value) -> 
        let name_var =  
          let found_known_name = List.find ~f:(fun (l, _) -> 
            String.equal l name) !known_vals in 
          match found_known_name with 
          | None ->
            let new_loc_var_ptsto = Ident.create_fresh Ident.knormal in 
            known_vals := (name, new_loc_var_ptsto) :: !known_vals;
            new_loc_var_ptsto
          | Some (_, loc_var_ptsto) -> loc_var_ptsto
        in 
        match value with 
        | Parsetree.Int i ->
          let int_const_exp = Exp.Const (Const.Cint(IntLit.of_int i)) in 
          begin
          match raw_atom with 
          | Parsetree.Atom_eq _ -> Some (Exp.BinOp (Binop.Eq, Exp.Var name_var, int_const_exp))
          | Parsetree.Atom_neq _ -> Some (Exp.BinOp (Binop.Ne, Exp.Var name_var, int_const_exp))
          | Parsetree.Atom_lt _ -> Some (Exp.BinOp (Binop.Lt, Exp.Var name_var, int_const_exp))
          | Parsetree.Atom_gt _ -> Some (Exp.BinOp (Binop.Gt, Exp.Var name_var, int_const_exp))
          | _ -> failwith "Should be unreachable"
          end
          
        | Parsetree.Location loc -> 
          let loc_var = 
            let found_known_loc = List.find ~f:(fun (l, _) -> 
              String.equal l loc) !known_vals in 
            match found_known_loc with 
            | None ->
              let new_loc_var_ptsto = Ident.create_fresh Ident.knormal in 
              known_vals := (name, new_loc_var_ptsto) :: !known_vals;
              new_loc_var_ptsto
            | Some (_, lv) -> lv
          in 
          begin
            match raw_atom with 
            | Parsetree.Atom_eq _ -> 
              Some (Exp.BinOp (Binop.Eq, Exp.Var name_var, Exp.Var loc_var))
            | Parsetree.Atom_neq _ ->
              Some (Exp.BinOp (Binop.Ne, Exp.Var name_var, Exp.Var loc_var))
            | Parsetree.Atom_lt _ ->
              Some (Exp.BinOp (Binop.Lt, Exp.Var name_var, Exp.Var loc_var))
            | Parsetree.Atom_gt _ ->
              Some (Exp.BinOp (Binop.Gt, Exp.Var name_var, Exp.Var loc_var))
            | _ -> failwith "Should be unreachable"
          end
    in 
    match make_atom pt_atom with
    | None -> None
    | Some exp -> Some (Sil.Aeq (exp, Exp.Const (Const.Cint (IntLit.one))))
  ) raw_pi
  in 

  (* Pre: construct spatial part *)
  let made_pre_sigma = make_sigma raw_pre.sigma in 

  (* Pre: construct pure part TODO *)
  let made_pre_pi = make_pi raw_pre.pi in 

  let made_pre = Prop.set ~sigma:made_pre_sigma ~pi:made_pre_pi Prop.prop_emp in

  (* Post: construct spatial part *)
  let made_post_sigma = make_sigma ~primed:true raw_post.sigma in 
  
  (* Post: construct pure part *)
  let made_post_pi = make_pi raw_post.pi in 

  let made_post = Prop.set ~sigma:made_post_sigma ~pi:made_post_pi Prop.prop_emp in
  made_pre, made_post  

