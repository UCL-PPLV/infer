open! IStd
open! SynSpecs
open! SynOut
open! Rules

module F = Format
   
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
  
