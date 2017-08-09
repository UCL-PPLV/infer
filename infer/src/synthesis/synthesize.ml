open! IStd

module F = Format
    
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

let insert_penultimate_node node proc_desc = 
  let pred_nodes = Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc) in 
  begin
  match List.hd pred_nodes with 
  | Some pred -> 
    Procdesc.node_set_succs_exn proc_desc pred [node] []
  | None -> assert false
  end;
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

(* Legacy: to be removed *)
let synthesize_writes tenv proc_desc (queue: Sil.instr list list)
  (pre: Prop.exposed Prop.t) (actual_post: Prop.normal Prop.t) (given_post: Prop.exposed Prop.t) = 
  F.printf "Begin synthesize writes\n";
  let proc_name = Procdesc.get_proc_name proc_desc in 
  let sigma_matches sigma1 sigma2 = 
    List.filter ~f:(fun hpred1 -> 
      match List.find ~f:(fun hpred2 ->
        if Sil.equal_hpred hpred1 hpred2 then true else false
      ) sigma2
      with
      | Some _ -> true
      | None -> false 
    ) sigma1 
  in 
  
  let rec synth_writes matches queue (post: Prop.normal Prop.t) = 
    match Prover.check_implication_for_footprint proc_name tenv post given_post with
    | ImplOK (checks, sub1, sub2, frame, missing_sigma, missing_pi,
      frame_fld, missing_fld, frame_typ, missing_typ) 
      when (Sil.equal_exp_subst sub2 Sil.exp_sub_empty) -> 
      F.printf "\nWrites finished\n" 
    | ImplOK _
    | ImplFail _ ->
      let next_instrs = List.hd queue in 
      match next_instrs with 
      | None -> failwith "Nothing left in synthesis queue"
      | Some new_instrs -> 
        (* Get number of matches *)       
        let new_matches = sigma_matches post.sigma given_post.sigma in 
        let best_matches = 
          if List.length(new_matches) > List.length(matches) then 
            let write_node = Procdesc.create_node proc_desc Location.dummy 
              (Procdesc.Node.Stmt_node "") new_instrs in 
            insert_penultimate_node write_node proc_desc;
            new_matches
          else 
            let penultimate_node = 
              List.hd_exn (Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc)) in 
            Procdesc.Node.replace_instrs penultimate_node new_instrs;
            matches
        in 
        Procdesc.compute_distance_to_exit_node proc_desc;
        
        F.printf "\nInstrs:\n";
        print_node_instrs proc_desc;

        Procdesc.signal_did_preanalysis proc_desc;
        let summary = Specs.reset_summary proc_desc in 
        let new_summary = Interproc.analyze_procedure_s summary proc_desc tenv in 
        let post = fst (List.hd_exn ((List.hd_exn (Specs.get_specs_from_payload new_summary)).Specs.posts)) in 

        F.printf "\nPost: \n";
        Prop.pp_prop Pp.text F.std_formatter post;
        F.print_newline ();        

        (* Alias finding trickery *)
        let matched_pvars = List.filter_map ~f:(fun v -> 
          match List.find ~f:(fun (e, _) -> 
            Exp.equal e v) (create_pvar_env_list pre.sigma) with
          | None -> None 
          | Some (_, p) -> Some p
        ) (List.map ~f:(Sil.hpred_get_lhs) best_matches) in
        F.printf "\nMatched pvars: \n";
        List.iter ~f:(Pvar.pp Pp.text F.std_formatter) matched_pvars;
        F.printf "\n";
        (* Filter out writes that change parts of sigma that already match *)
        let rec get_new_queue queue = 
          match List.hd queue with 
          | None -> failwith "Nothing left in queue"
          | Some instrs -> 
            match instrs with 
            | Sil.Load (_, Exp.Lvar pv, _, _) :: _ -> 
              if List.mem matched_pvars pv ~equal:Pvar.equal then get_new_queue (List.tl_exn queue)
              else queue 
            | _ -> queue  
          in
        let new_queue = get_new_queue (List.tl_exn queue) in 
        synth_writes best_matches new_queue post
  in 
  F.printf "\nPre: \n";
  Prop.pp_prop Pp.text F.std_formatter pre;
  F.printf "\nGiven Post: \n";
  Prop.pp_prop Pp.text F.std_formatter given_post;
  F.print_newline ();
  F.printf "\nActual Post: \n";
  Prop.pp_prop Pp.text F.std_formatter actual_post;
  synth_writes (sigma_matches actual_post.sigma given_post.sigma) queue actual_post
(* End legacy section *)

type rule_result = RSuccess of Sil.instr list list | RFail

let write_rule pvars_locals (actual_post: Prop.normal Prop.t) 
  (given_post: Prop.exposed Prop.t): rule_result = 
  let find_pointsto sigma = 
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


let synthesize proc_name (procspec: Parsetree.procspec) = 
  let proc_name_readable = Typ.Procname.to_string proc_name in
  F.print_string ("Begin proc: " ^ proc_name_readable ^ "\n");
  let tenv = Tenv.create () in 
  let cfg = Cfg.create_cfg () in
  let proc_attributes = ProcAttributes.default proc_name Config.Clang in 
  AttributesTable.store_attributes proc_attributes; 
  let proc_desc = Cfg.create_proc_desc cfg proc_attributes in
  Procdesc.compute_distance_to_exit_node proc_desc;

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

  let read_nodes = List.map ~f:(fun instrs -> 
    Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") instrs
  ) read_instrs in
  List.iter ~f:(fun n -> insert_penultimate_node n proc_desc) read_nodes;
  Procdesc.compute_distance_to_exit_node proc_desc;

  let my_new_pre, my_new_post = make_spec procspec tenv proc_name in 
  F.printf "Given pre: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_pre);
  F.printf "\n";
  F.printf "Given post: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_post);
  F.printf "\n";

  Procdesc.signal_did_preanalysis proc_desc;
  let summary = Specs.reset_summary proc_desc in 
  let new_summary = Interproc.analyze_procedure_s summary proc_desc tenv in 
  let pre = Specs.Jprop.to_prop 
    (List.hd_exn (Specs.get_specs_from_payload new_summary)).Specs.pre in 
  let post = fst (List.hd_exn 
    ((List.hd_exn (Specs.get_specs_from_payload new_summary)).Specs.posts)) in 


  match Prover.check_implication_for_footprint proc_name tenv pre my_new_pre with
  | ImplFail _ -> failwith "Could not unify actual pre and given pre"
  | ImplOK (checks, pre_sub1, pre_sub2, frame, missing_pi, missing_sigma,
      frame_fld, missing_fld, frame_typ, missing_typ) -> 
  F.printf "Pre: sub1: \n";
  List.iter ~f:(fun (i, e) -> 
    Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
    Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list pre_sub1);
  F.printf "\nPre: sub2: \n";
  List.iter ~f:(fun (i, e) -> 
    Ident.pp Pp.text F.std_formatter i; F.printf " * "; 
    Exp.pp F.std_formatter e; F.printf "; ") (Sil.sub_to_list pre_sub2);
  F.printf "\nPre: Frame: \n";
  Prop.pp_sigma Pp.text F.std_formatter frame;
  F.printf "\nPre: missing pi: \n";
  Prop.pp_pi Pp.text F.std_formatter missing_pi;
  F.printf "\nPre: missing sigma: \n";
  Prop.pp_sigma Pp.text F.std_formatter missing_sigma;
  F.printf "\n";

  let pre = Prop.set ~pi:(pre.pi @ missing_pi) pre in 

  F.printf "Actual post: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter post;
  F.printf "\n";

  match Prover.check_implication_for_footprint proc_name tenv post my_new_post with
  | ImplOK (checks, post_sub1, post_sub2, frame, missing_pi, missing_sigma,
    frame_fld, missing_fld, frame_typ, missing_typ) 
    when (Sil.equal_exp_subst post_sub2 Sil.exp_sub_empty) ->
    F.printf "\nPost: Frame: \n";
    Prop.pp_sigma Pp.text F.std_formatter frame;
    F.printf "\nPost: missing pi: \n";
    Prop.pp_pi Pp.text F.std_formatter missing_pi;
    F.printf "\nPost: missing sigma: \n";
    Prop.pp_sigma Pp.text F.std_formatter missing_sigma;
    F.printf "\n";
    failwith "Nothing to synthesize"
  | ImplFail _ 
  | ImplOK _ -> 
    let pre_sub2 = Sil.subst_of_list (Sil.sub_to_list pre_sub2) in 
    let pre = Prop.prop_sub pre_sub2 pre in 
    let post = Prop.normalize tenv (Prop.prop_sub pre_sub2 post) in 
    let my_new_post = Prop.prop_sub pre_sub2 my_new_post in 
    
    F.printf "Given sigma (after sub): \n";
    Prop.pp_sigma Pp.text F.std_formatter my_new_post.sigma;
    F.printf "\nActual post sigma (after sub): \n"; 
    Prop.pp_sigma Pp.text F.std_formatter post.sigma;
    
    (* Unify here: This section would be put in a loop, with post |- my_new_post as 
       the loop condition. *) 
    let pvars_locals = List.zip_exn (List.map ~f:(fst) pvars) local_vars in 
    let rules = [write_rule] in (* Rules are functions from prop to rule_result *)
    let slns = List.map ~f:(fun rule -> rule pvars_locals post my_new_post) rules in 
    
    let new_nodes = List.map ~f:(function 
      | RFail -> []
      | RSuccess instr_lists -> (List.map ~f:(
        Procdesc.create_node proc_desc Location.dummy 
          (Procdesc.Node.Stmt_node "")) instr_lists)
    ) slns in 
    
    List.iter ~f:(fun n -> insert_penultimate_node n proc_desc) 
      (List.hd_exn new_nodes); 
    (* For now, only one rule so only one set of new nodes. *)

    pprint_output proc_desc procspec

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
  