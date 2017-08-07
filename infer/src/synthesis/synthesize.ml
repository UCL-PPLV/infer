open! IStd

module F = Format

let path_to_source = "/tmp/swap-proto.c" (* Should be put in /tmp/ *)

let print_sigma sigma = 
  List.iter ~f:(fun s -> 
    Sil.pp_hpred Pp.text F.std_formatter s;
    F.print_string " "
  ) sigma

let print_pi pi = 
  List.iter ~f:(fun p -> 
    Sil.pp_atom Pp.text F.std_formatter p;
    F.print_string " " 
  ) pi

let print_specs specs = 
  List.iter ~f:(fun (s: Prop.normal Specs.spec) -> 
    let joined_pre = s.pre in
    let pre = Specs.Jprop.to_prop joined_pre in
    let sigma = pre.sigma
    and pi = pre.pi
    and sigma_fp = pre.sigma_fp
    and pi_fp = pre.pi_fp in
    F.print_string "pre: \n";
    F.print_string "sigma: \n";
    print_sigma sigma;
    F.print_string "\npi: \n";
    print_pi pi;
    F.print_string "\nsigma_fp: \n";
    print_sigma sigma_fp;
    F.print_string "\npi_fp: \n";
    print_pi pi_fp;
    F.print_string "\n";

    let posts = s.posts in 
    List.iter ~f:(fun (p: Prop.normal Prop.t * Paths.Path.t) -> 
      let post = fst p in 
      let sigma = post.sigma
      and pi = post.pi
      and sigma_fp = post.sigma_fp
      and pi_fp = post.pi_fp in
      F.print_string "post: \n";
      F.print_string "sigma: \n";
      print_sigma sigma;
      F.print_string "\npi: \n";
      print_pi pi;
      F.print_string "\nsigma_fp: \n";
      print_sigma sigma_fp;
      F.print_string "\npi_fp: \n";
      print_pi pi_fp;
      F.print_string "\n";
    ) posts;
  ) specs

let print_node_instrs proc_desc = 
  let rec print_nodes node = 
    Procdesc.Node.pp_instrs Pp.text ~sub_instrs:true None F.std_formatter node;
    F.print_string "preds: ";
    List.iter ~f:(fun p -> 
      Procdesc.Node.pp F.std_formatter p; F.print_string " ") (Procdesc.Node.get_preds node);
    F.print_string "; node: ";
    Procdesc.Node.pp F.std_formatter node;
    F.print_string "; succs: ";
    List.iter ~f:(fun s -> 
      Procdesc.Node.pp F.std_formatter s; F.print_string " ") (Procdesc.Node.get_succs node);
    F.print_string "\n\n";
    match Procdesc.Node.get_kind node with
    | Procdesc.Node.Exit_node _ -> () 
    | _ -> print_nodes (List.hd_exn (Procdesc.Node.get_succs node))
  in
  let start_node = Procdesc.get_start_node proc_desc in 
  print_nodes start_node;
  F.print_string "\n"

let c_prog_of_sig ?(body="  /* ?? */") {Parsetree.ret_typ; id; params} = 
  let params_str = String.concat ~sep:", " 
    (List.map ~f:(fun {Parsetree.typ; id} -> typ ^ " " ^ id) params) in
  "#include <stdio.h>\n" ^ 
  ret_typ ^ " " ^ id ^ "(" ^ params_str ^ ") { \n  " ^ body ^ "\n}\n" ^  
  "int main() { return 0; }\n"

let pprint_output proc_desc (procspec: Parsetree.procspec) = 
  let rec print_nodes node stmts = 
    let stmt = match Procdesc.Node.get_instrs node with 
    (* read *)
    | [ Sil.Load (_, Exp.Lvar pvar, _, _)
      ; Sil.Load (_, _, _, _)
      ; Sil.Store (Exp.Lvar local, typ, _, _) 
      ; Sil.Remove_temps _
      ; Sil.Abstract _ ] ->
      let local_name = Pvar.get_simplified_name local in 
      let pvar_name = Pvar.get_simplified_name pvar in 
      let typ_name = Typ.to_string typ in 
      let stmt = F.sprintf "%s %s = *%s;" typ_name local_name pvar_name in 
      stmt
    (* write ptr *)
    | [ Sil.Load (_, Exp.Lvar pvar, _, _)
      ; Sil.Load (_, Exp.Lvar local, _, _)
      ; Sil.Store _ 
      ; Sil.Remove_temps _
      ; Sil.Abstract _ ] -> 
      let pvar_name = Pvar.get_simplified_name pvar in 
      let local_name = Pvar.get_simplified_name local in 
      let stmt = F.sprintf "*%s = %s;" pvar_name local_name in 
      stmt
    (* write const *)
    | [ Sil.Load (_, Exp.Lvar pvar, _, _)
      ; Sil.Store (_, _, Exp.Const const, _)
      ; Sil.Remove_temps _
      ; Sil.Abstract _ ] ->
      let pvar_name = Pvar.get_simplified_name pvar in
      let const = Const.to_string const in
      let stmt = F.sprintf "*%s = %s;" pvar_name const in
      stmt
    | _ -> ""
    in 
    match Procdesc.Node.get_kind node with
    | Procdesc.Node.Exit_node _ -> stmts
    | Procdesc.Node.Start_node _ -> print_nodes (List.hd_exn (Procdesc.Node.get_succs node)) (stmts)
    | _ -> print_nodes (List.hd_exn (Procdesc.Node.get_succs node)) (stmt::stmts)
  in
  let start_node = Procdesc.get_start_node proc_desc in 
  let statements = List.rev (print_nodes start_node []) in
  F.print_string "\n";
  let statements_str = String.concat ~sep:"\n  " statements in
  let c_prog_str = c_prog_of_sig procspec.proc ~body:statements_str in
  c_prog_str

(* Create a alias list of Exp (temp var) * Pvar (real var) from a sigma (of a pre) *)
let create_pvar_env_list (sigma: Prop.sigma) : (Exp.t * Pvar.t) list =
  let env = ref [] in
  let filter = function
    | Sil.Hpointsto (Lvar pvar, Eexp (Var v, _), _) ->
        if not (Pvar.is_global pvar) then env := (Exp.Var v, pvar) :: !env
    | _ -> ()
  in
  List.iter ~f:filter sigma;
  !env

(* Find the Exp that a named variable was aliased to *)
let find_exp_replacement (name: string) (exp_replace_list: (Exp.t * Pvar.t) list) = 
  match List.find ~f:(fun p -> String.equal (Pvar.get_simplified_name (snd p)) name) 
      exp_replace_list with
  | Some pair -> pair
  | None -> failwith "find_exp_replacement: No var of that name found"

(* Find the Exp that an Exp points to in a sigma *)
let find_pointsto (e: Exp.t) sigma = 
  match List.find ~f:(fun h -> Exp.equal (Sil.hpred_get_lhs h) (e)) sigma with 
  | Some Sil.Hpointsto (_, Eexp (Var v, _), _) -> Exp.Var v
  | _ -> failwith "find_pointsto: No value found"

let insert_penultimate_node node proc_desc = 
  Procdesc.node_set_succs_exn proc_desc 
    (List.hd_exn (Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc))) [node] [];
  Procdesc.node_set_succs_exn proc_desc node [(Procdesc.get_exit_node proc_desc)] []

let remove_nullifys proc_desc = 
  Procdesc.iter_nodes (fun n ->
    let instrs = Procdesc.Node.get_instrs n in 
    let new_instrs = List.filter ~f:(function
      | Sil.Nullify _ -> false
      | _ -> true) instrs in
    Procdesc.Node.replace_instrs n new_instrs;
  ) proc_desc

let get_typ_from_ptr_exn (ptr_typ: Typ.t) = match ptr_typ.desc with
  | Tptr (t, _) -> t 
  | _ -> failwith "Not a pointer type"

let make_spec (procspec: Parsetree.procspec) tenv proc_name  = 
  let raw_pre = procspec.pre in 
  let raw_post = procspec.post in
  let known_vals = ref [] in

  let make_sigma raw_sigma = List.concat (List.filter_map ~f:(fun pt_hpred ->
    match pt_hpred with 
    | Parsetree.Hpred_empty -> None
    | Parsetree.Hpred_hpointsto (pv_name, value) -> 
      let pvar = Pvar.mk (Mangled.from_string pv_name) proc_name in 
      let pvar_ptsto = 
        let found_pvar_loc = List.find ~f:(fun (n, _) -> 
          String.equal pv_name n) !known_vals in
        match found_pvar_loc with
        | None -> 
          let new_loc_var = Ident.create_fresh Ident.knormal in
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
          let new_loc_var_ptsto = Ident.create_fresh Ident.knormal in 
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
  let made_post_sigma = make_sigma raw_post.sigma in 
  
  let made_post_sigma_flt = List.filter_map ~f:(fun hpred_post ->
    match Sil.hpred_get_lhs hpred_post with 
    | Exp.Lvar _ -> 
      let found_in_pre = List.find ~f:(fun hpred_pre ->
        if Sil.equal_hpred hpred_pre hpred_post then true else false
      ) made_pre_sigma in
      begin
      match found_in_pre with 
      | Some _ -> None
      | None -> Some hpred_post
      end
    | _ -> Some hpred_post
  ) made_post_sigma in 

  (* Post: construct pure part *)
  let made_post_pi = make_pi raw_post.pi in 

  let made_post = Prop.set ~sigma:made_post_sigma ~pi:made_post_pi Prop.prop_emp in
  made_pre, made_post

let synthesize proc_name (procspec: Parsetree.procspec) = 
  let proc_name_readable = Typ.Procname.to_string proc_name in
  F.print_string ("Begin proc: " ^ proc_name_readable ^ "\n");
  let tenv = Tenv.create () in 
  let cfg = Cfg.create_cfg () in
  let proc_desc = Cfg.create_proc_desc cfg (ProcAttributes.default proc_name Config.Clang) in
  
  let pvars = List.map ~f:(fun (param: Parsetree.param) -> 
    (Pvar.mk (Mangled.from_string param.id) proc_name, 
      Typ.mk (Typ.Tptr (Typ.mk (Typ.Tint(Typ.IInt)), 
                Typ.Pk_pointer)))
  ) (procspec.proc.params) in 

  F.print_string "pvars: "; 
  List.iter ~f:(fun (pv, _) -> Pvar.pp Pp.text F.std_formatter pv) pvars;
  F.print_string "\n";

  let local_vars = List.mapi ~f:(fun i _ -> 
    Pvar.mk (Mangled.from_string ("l" ^ (string_of_int i))) proc_name) pvars in
  let read_instrs = List.map2_exn ~f:(fun (pvar, p_typ) local -> 
    let temp1 = Ident.create_fresh Ident.knormal in 
    let temp2 = Ident.create_fresh Ident.knormal in 
    let typ = get_typ_from_ptr_exn p_typ in 
    [ Sil.Load (temp1, Exp.Lvar pvar, p_typ, Location.dummy)
    ; Sil.Load (temp2, Exp.Var temp1, typ, Location.dummy)
    ; Sil.Store (Exp.Lvar local, typ, Exp.Var temp2, Location.dummy)
    ; Sil.Remove_temps ([temp1; temp2], Location.dummy)
    ; Sil.Abstract (Location.dummy) ]
  ) pvars local_vars in 

  let read_nodes = List.rev_map ~f:(fun instrs -> 
    Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") instrs)
    read_instrs in
  List.iter ~f:(fun n -> insert_penultimate_node n proc_desc) read_nodes;
  Procdesc.compute_distance_to_exit_node proc_desc;

  let sigma_constants = List.filter_map ~f:(function
    | Parsetree.Hpred_hpointsto (_, Parsetree.Int(value)) -> 
      Some (Const.Cint(IntLit.of_int value))
    | _ -> None
  ) procspec.post.sigma in

  let pi_constants = List.filter_map ~f:(function
    | Parsetree.Atom_eq (_, Parsetree.Int(value)) ->
      Some (Const.Cint(IntLit.of_int value))
    | _ -> None
  ) procspec.post.pi in 

  let constant_writes = List.concat (List.map ~f:(fun (pv, p_typ) -> 
    List.map ~f:(fun const -> 
      let temp = Ident.create_fresh Ident.knormal in 
      let typ = get_typ_from_ptr_exn p_typ in 
      [ Sil.Load (temp, Exp.Lvar pv, p_typ, Location.dummy)
      ; Sil.Store (Exp.Var temp, typ, Exp.Const const, Location.dummy)
      ; Sil.Remove_temps ([temp], Location.dummy)
      ; Sil.Abstract (Location.dummy) ]
    ) (sigma_constants @ pi_constants)) pvars) in

  let pointer_writes = List.concat (List.map ~f:(fun (pv, p_typ) -> 
    List.map ~f:(fun local -> 
      let temp1 = Ident.create_fresh Ident.knormal in 
      let temp2 = Ident.create_fresh Ident.knormal in 
      let typ = get_typ_from_ptr_exn p_typ in 
      [ Sil.Load (temp1, Exp.Lvar pv, p_typ, Location.dummy)
      ; Sil.Load (temp2, Exp.Lvar local, typ, Location.dummy)
      ; Sil.Store (Exp.Var temp1, typ, Exp.Var temp2, Location.dummy)
      ; Sil.Remove_temps ([temp1; temp2], Location.dummy)
      ; Sil.Abstract (Location.dummy) ]
    ) (local_vars @ (fst (List.unzip pvars)))) pvars) in

  let possible_writes = pointer_writes @ constant_writes in 

  let write_node = Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") 
    [] in
  insert_penultimate_node write_node proc_desc;
  Procdesc.compute_distance_to_exit_node proc_desc;

  remove_nullifys proc_desc;

  (* This section is duplicated from synthesize_writes in order to get the initial number of matches *)
  let my_new_pre, my_new_post = make_spec procspec tenv proc_name in 
  F.printf "My new pre: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_pre);
  F.printf "\n";
  F.printf "My new post: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_post);
  F.printf "\n";
  
  let nodes = Procdesc.get_nodes proc_desc in 
  let all_instrs = List.concat (List.map ~f:(Procdesc.Node.get_instrs) nodes) in 
  let post = fst (List.hd_exn (SymExec.instrs tenv proc_desc all_instrs [((Prop.normalize tenv my_new_pre), 
    Paths.Path.start (List.hd_exn nodes))])) in 

  F.printf "Actual post: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter post;
  F.printf "\n";

  match Prover.check_implication_for_footprint proc_name tenv 
    post my_new_post with 
  
  | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
      frame_fld, missing_fld, frame_typ, missing_typ) -> 
    F.printf "Post: sub1: \n";
    List.iter ~f:(fun (i, e) -> 
      Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
      Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub1);
    F.printf "\nPost: sub2: \n";
    List.iter ~f:(fun (i, e) -> 
      Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
      Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub2);
    F.printf "\nPost: Frame: \n";
    Prop.pp_sigma Pp.text F.std_formatter frame;
    F.printf "\nPost: missing pi: \n";
    Prop.pp_pi Pp.text F.std_formatter missing_pi;
    F.printf "\nPost: missing sigma: \n";
    Prop.pp_sigma Pp.text F.std_formatter missing_sigma; F.printf "\n";

    let post = Prop.prop_sub (Sil.sub_to_list sub1 |> Sil.subst_of_list) post in
    let my_new_post = Prop.prop_sub (Sil.sub_to_list sub2 |> Sil.subst_of_list) my_new_post in
    F.printf "Actual post after sub: \n";
    Prop.pp_prop Pp.text F.std_formatter post;
    F.printf "\nMy new post after sub: \n"; 
    Prop.pp_prop Pp.text F.std_formatter my_new_post; F.printf "\n";
    begin
    match Prover.check_implication_for_footprint proc_name tenv 
    (Prop.normalize tenv post) my_new_post with
    | ImplOK (checks, sub1, sub2, frame, [], [],
        frame_fld, missing_fld, frame_typ, missing_typ) 
          when phys_equal (Sil.sub_to_list sub2) [] -> 
      F.print_string "post = given post: Yes\n";
      F.print_string "Given post: \n";
      Prop.pp_prop Pp.text F.std_formatter my_new_post;
      F.printf "\nPost: sub1: \n";
      List.iter ~f:(fun (i, e) -> 
        Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
        Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub1);
      F.printf "\nPost: sub2: \n";
      List.iter ~f:(fun (i, e) -> 
        Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
        Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub2);
      F.printf "\nPost: Frame: \n";
      Prop.pp_sigma Pp.text F.std_formatter frame;
      F.printf "\n";
      failwith "Nothing to synthesize"
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
        frame_fld, missing_fld, frame_typ, missing_typ) -> 
      F.printf "Post: sub1: \n";
      List.iter ~f:(fun (i, e) -> 
        Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
        Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub1);
      F.printf "\nPost: sub2: \n";
      List.iter ~f:(fun (i, e) -> 
        Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
        Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list sub2);
      F.printf "\nPost: Frame: \n";
      Prop.pp_sigma Pp.text F.std_formatter frame;
      F.printf "\nPost: missing pi: \n";
      Prop.pp_pi Pp.text F.std_formatter missing_pi;
      F.printf "\nPost: missing sigma: \n";
      Prop.pp_sigma Pp.text F.std_formatter missing_sigma;
      F.printf "\n";
      
      failwith "Now we should synthesize writes/find path condition"
    | ImplFail _ -> 
      failwith "Could not unify given post and actual post - we should synthesize writes"
    end
  | ImplFail _ -> 
    failwith "Could not unify given post and actual post - we should synthesize writes"

let run ~arg = 
  let pspec = ParseMain.run arg in 
  match pspec with
  | None -> failwith "Input file is empty"
  | Some procspec -> 
  let proc_name = Typ.Procname.from_string_c_fun procspec.proc.id in 
  let c_prog_str = synthesize proc_name procspec in 
  let out_path = (Str.string_before arg 
    (Str.search_backward (Str.regexp_string "/") arg (String.length arg)))
      ^ "/result.c" in 
  F.printf "Synthesis result is stored in %s \n" out_path;
  Out_channel.write_all ~data:c_prog_str out_path
  

  