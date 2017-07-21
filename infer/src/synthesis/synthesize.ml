open! IStd

module F = Format

let path_to_source = "/home/ben/Desktop/swap/swap-proto.c" (* Should be put in /tmp/ *)

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

let make_post (procspec: Parsetree.procspec) (actual_pre: Prop.normal Prop.t) tenv proc_desc = 
  let raw_pre = procspec.pre in 
  let raw_post = procspec.post in
  let filter_emp_hpreds = List.filter ~f:(function
    | Parsetree.Hpred_empty -> false
    | _ -> true) in
  let non_empty_post_sigma = filter_emp_hpreds raw_post.sigma in 
  match non_empty_post_sigma with 
  | [] -> F.printf "Making empty post\n"; Prop.expose Prop.prop_emp
  | _ -> 
  let non_empty_pre_sigma = filter_emp_hpreds raw_pre.sigma in
  let quantified_vars = List.map ~f:(function
    | Parsetree.Hpred_hpointsto (s, _) -> s
    | _ -> failwith "Case not handled - not pointsto"
  ) non_empty_pre_sigma in

  (* Get alias, pointsto, and typ of each quantified variable *)
  let exp_replace_list = create_pvar_env_list actual_pre.sigma in
  let pvars = List.map ~f:(fun (mang, typ) -> 
    let pvar = (snd (List.find_exn ~f:(fun p -> 
      Mangled.equal (Pvar.get_name (snd p)) mang) exp_replace_list)) in
    (pvar, typ)
  ) (Procdesc.get_formals proc_desc) in 
  let param_pointsto_list = List.filter_map ~f:(ident) (List.map ~f:(fun quant -> 
    let found_alias = List.find ~f:(fun (_, p) -> 
      String.equal (Pvar.get_simplified_name p) quant) exp_replace_list in
    match found_alias with 
    | None -> None (* Prop in spec is not in proc params - ignore *)
    | Some (param, pvar) -> 
      let pointsto = find_pointsto param actual_pre.sigma in 
      let typ = snd (List.find_exn ~f:(fun p -> Pvar.equal (fst p) pvar) pvars) in 
      Some (quant, param, pointsto, typ)
  ) quantified_vars) in 

  let hpred_list = List.filter_map ~f:(ident) (List.map ~f:(function 
    | Parsetree.Hpred_hpointsto (p, q) -> begin
      let found_in_pre = List.find ~f:(function 
        | Parsetree.Hpred_hpointsto (_, n) -> String.equal n q
        | _ -> failwith "Case not handled - not pointsto"
      ) non_empty_pre_sigma in
      match found_in_pre with 
      | Some Parsetree.Hpred_hpointsto (m, n) -> begin
        let found_param = List.find ~f:(fun (name, _, _, _) ->
          String.equal p name) param_pointsto_list in
        match found_param with 
        | None -> 
          begin
          let find_matching_pre = List.find ~f:(function
            | Parsetree.Hpred_hpointsto (m, _) -> String.equal m p
            | _ -> failwith "Case not handled - not pointsto"
          ) non_empty_pre_sigma in 
          match find_matching_pre with
          | Some Parsetree.Hpred_hpointsto (_, n) -> 
            if not (String.equal n q) then 
              failwithf "Var %s modified in post but not passed in function params" p
            else 
              None
          | None -> failwithf "Var %s exists in post but is not in pre" p
           (* TODO: Have synthesis procedure for making new variable pointing to *)
          | _ -> failwith "Case not handled - not pointsto"
          end
        | Some (_, param, _, _) ->
          begin 
          let found_pointsto = List.find ~f:(fun (name, _, _, _) -> 
            String.equal m name) param_pointsto_list in
          match found_pointsto with 
          | None -> 
            if not (String.equal p m) then 
              failwithf "Var %s pointing to %s is in post but %s does not exist in pre" p q q
              (* TODO: Have sythesis procedure for pointing to fresh variables *)
            else None
          | Some (_, _, pointsto, typ) -> 
            Some (Prop.mk_ptsto tenv param (Sil.Eexp (pointsto, Sil.inst_none))
            (Exp.Sizeof {typ=(get_typ_from_ptr_exn typ); nbytes=None; 
              dynamic_length=None; subtype=Subtype.exact}))
          end
        end

      | None -> begin
        let found_in_params = List.find ~f:(fun (quant2, _, _, _) 
          -> String.equal q quant2) param_pointsto_list in 
        match found_in_params with
        | None -> failwithf "Var %s pointing to %s given in post but %s is not in pre" p q q
        | Some (_, param2, _, typ) ->
          let _, param1, _, _ = List.find_exn ~f:(fun (quant1, _, _, _) -> 
            String.equal quant1 p) param_pointsto_list in
          Some (Prop.mk_ptsto tenv param1 (Sil.Eexp (param2, Sil.inst_none))
            (Exp.Sizeof {typ=typ; nbytes=None; 
              dynamic_length=None; subtype=Subtype.exact}))
        end
        
      | _ -> failwith "Case not handled - not pointsto"
      end

    | _ -> failwith "Case not handled - not pointsto"
  ) non_empty_post_sigma) in 

  Prop.from_sigma hpred_list

let rec synthesize_writes callbacks procspec (queue: Sil.instr list list) matches =
  let proc_desc = callbacks.Callbacks.proc_desc in 
  let proc_name = Procdesc.get_proc_name proc_desc in 
  let summary = Interproc.analyze_procedure callbacks in
  (* Specs.pp_summary_text F.std_formatter summary; *)
  let specs = Specs.get_specs_from_payload summary in 
  print_specs specs;
  let post = fst (List.hd_exn (List.hd_exn specs).Specs.posts) in
  let pre = Specs.Jprop.to_prop (List.hd_exn specs).Specs.pre in 

  (* This section is duplicated in the initial synthesize to count initial matches *)
  let my_new_post = make_post procspec pre callbacks.Callbacks.tenv proc_desc in 
  match Prover.check_implication_for_footprint proc_name callbacks.Callbacks.tenv post my_new_post with 
  | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
    frame_fld, missing_fld, frame_typ, missing_typ) -> 
    F.print_string "post = given post: Yes\n";
    F.print_string "Given post: \n";
    Prop.pp_prop Pp.text F.std_formatter my_new_post;
    F.print_string "\n"
  | ImplFail _ -> 
  F.print_string "post = given post: No\n";

  let new_matches = ref 0 in
  
  List.iter ~f:(fun hpred1 -> 
    List.iter ~f:(fun hpred2 ->
      if Sil.equal_hpred hpred1 hpred2 then 
        begin
        new_matches := !new_matches + 1;
        F.print_string "Match found! - ";
        F.print_string "hpred1: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred1;
        F.print_string " && hpred2: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred2;
        F.print_string "\n"
        end;
    ) my_new_post.sigma;
  ) post.sigma;
  F.print_string "\n";

  let abstract_inst = Sil.Abstract (Location.dummy) in 
  let next_instrs = List.hd queue in
  match next_instrs with 
  | None -> failwith "Nothing left in synthesis queue"
  | Some ni ->
  let new_instrs = ni @ [abstract_inst] in 

  begin
  if !new_matches > matches then 
    let write_node = Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") 
      new_instrs in 
    insert_penultimate_node write_node proc_desc;
    Procdesc.compute_distance_to_exit_node proc_desc;
  else
    let penultimate_node = 
      List.hd_exn (Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc)) in 
    Procdesc.Node.replace_instrs penultimate_node new_instrs;
  end;

  F.print_string "Node instrs after\n";
  print_node_instrs proc_desc;

  (* Recursive call to run - after the instructions have been changed *)
  let new_queue = List.tl_exn queue in 
  synthesize_writes callbacks procspec new_queue (max !new_matches matches)

let synthesize proc_name exe_env procspec = 
  let proc_name_readable = Typ.Procname.to_string proc_name in
  F.print_string ("Begin proc: " ^ proc_name_readable ^ "\n");
  let get_proc_desc proc_name = Exe_env.get_proc_desc exe_env proc_name in
  let get_procs_in_file proc_name =
    match Exe_env.get_cfg exe_env proc_name with
    | Some cfg
      -> List.map ~f:Procdesc.get_proc_name (Cfg.get_defined_procs cfg)
    | None -> [] in
  let tenv = Exe_env.get_tenv exe_env proc_name in 
  let pd = get_proc_desc proc_name in
  match pd with 
  | None -> failwithf "Could not find proc desc for %a" Typ.Procname.pp proc_name
  | Some proc_desc -> 
  let idenv = Idenv.create proc_desc in
  let summary = Specs.reset_summary proc_desc in 
  let new_summary = Interproc.analyze_procedure { get_proc_desc; 
    get_procs_in_file; idenv; tenv; summary; proc_desc; } in
  let specs = Specs.get_specs_from_payload new_summary in
  print_specs specs;

  let num_specs = List.length specs in
  if num_specs > 1 then failwith "Too many specs!";
  let one_spec = List.hd specs in 
  match one_spec with
  | None -> failwith "No specs"
  | Some spec ->
  let pre = Specs.Jprop.to_prop spec.pre in

  F.print_string "formals: ";
  List.iter ~f:(fun f -> Mangled.pp F.std_formatter (fst f); F.print_string " ") (Procdesc.get_formals proc_desc);
  F.print_string "\n";
  
  let exp_replace_list = create_pvar_env_list pre.sigma in
  let pvars = List.map ~f:(fun (mang, typ) -> 
    let pvar = snd (List.find_exn ~f:(fun p -> Mangled.equal (Pvar.get_name (snd p)) mang) exp_replace_list) in
    (pvar, typ)
  ) (Procdesc.get_formals proc_desc) in 

  let local_vars = List.mapi ~f:(fun i _ -> Pvar.mk (Mangled.from_string ("l" ^ (string_of_int i))) proc_name) pvars in
  let read_instrs = List.map2_exn ~f:(fun (pvar, p_typ) local -> 
    let temp1 = Ident.create_fresh Ident.knormal in 
    let temp2 = Ident.create_fresh Ident.knormal in 
    let typ = get_typ_from_ptr_exn p_typ in 
    [ Sil.Load (temp1, Exp.Lvar pvar, p_typ, Location.dummy);
    Sil.Load (temp2, Exp.Var temp1, typ, Location.dummy);
    Sil.Store (Exp.Lvar local, typ, Exp.Var temp2, Location.dummy);
    Sil.Remove_temps ([temp1; temp2], Location.dummy) ]
  ) pvars local_vars in 
  let abstract_instr = Sil.Abstract (Location.dummy) in 

  let read_node = Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") 
    ((List.concat read_instrs) @ [abstract_instr]) in
  insert_penultimate_node read_node proc_desc;
  Procdesc.compute_distance_to_exit_node proc_desc;

  let possible_writes = List.concat (List.map ~f:(fun (pv, typ) -> 
    List.map ~f:(fun local -> 
      let temp1 = Ident.create_fresh Ident.knormal in 
      let temp2 = Ident.create_fresh Ident.knormal in 
      [ Sil.Load (temp1, Exp.Lvar pv, get_typ_from_ptr_exn typ, Location.dummy);
      Sil.Load (temp2, Exp.Lvar local, get_typ_from_ptr_exn typ, Location.dummy);
      Sil.Store (Exp.Var temp1, get_typ_from_ptr_exn typ, Exp.Var temp2, Location.dummy);
      Sil.Remove_temps ([temp1; temp2], Location.dummy) ]
    ) local_vars) pvars) in

  let write_node = Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") 
    [] in
  insert_penultimate_node write_node proc_desc;
  Procdesc.compute_distance_to_exit_node proc_desc;

  remove_nullifys proc_desc;
  Specs.clear_spec_tbl ();
  let callbacks = { Callbacks.get_proc_desc; 
    get_procs_in_file; idenv; tenv; summary; proc_desc; } in

  (* Re-analyze after putting in the initial reads *)
  let specs = Specs.get_specs_from_payload (Interproc.analyze_procedure callbacks) in
  let pre = Specs.Jprop.to_prop (List.hd_exn specs).Specs.pre in 
  let post = fst (List.hd_exn (List.hd_exn specs).Specs.posts) in 

  (* This section is duplicated from synthesize_writes in order to get the initial number of matches *)
  let my_new_post = make_post procspec pre callbacks.Callbacks.tenv callbacks.Callbacks.proc_desc in 
  match Prover.check_implication_for_footprint proc_name callbacks.Callbacks.tenv post my_new_post with 
  | ImplOK _ -> 
    F.print_string "post = given post: Yes\n";
    F.print_string "Given post: \n";
    Prop.pp_prop Pp.text F.std_formatter my_new_post;
    F.print_string "\n"
  | ImplFail _ -> 
  F.print_string "post = given post: No\n";

  let new_matches = ref 0 in
  List.iter ~f:(fun hpred1 -> 
    List.iter ~f:(fun hpred2 ->
      if Sil.equal_hpred hpred1 hpred2 then 
        begin
        new_matches := !new_matches + 1;
        end;
    ) my_new_post.sigma;
  ) post.sigma;
  F.print_string "\n";

  F.printf "INITIAL MATCHES: %d\n" !new_matches;
  
  synthesize_writes callbacks procspec possible_writes !new_matches

let run ~arg = 
  let pspec = ParseMain.run arg in 
  match pspec with
  | None -> failwith "Input file is empty"
  | Some procspec -> 
  let proc_sig = procspec.proc in
  let c_prog_of_sig {Parsetree.ret_typ; id; params} = 
  let params_str = String.concat ~sep:", " 
    (List.map ~f:(fun {Parsetree.typ; id} -> typ ^ " " ^ id) params) in
  "#include <stdio.h>\n" ^ 
  ret_typ ^ " " ^ id ^ "(" ^ params_str ^ ") { }\n" ^ 
  "int main() { return 0; }" in 
  let c_prog = c_prog_of_sig proc_sig in 
  Out_channel.write_all path_to_source ~data:c_prog;

  ClangWrapper.exe ~prog:"clang" ~args:[path_to_source];

  let all_clusters = DB.find_source_dirs () in 
  let one_cluster = List.hd all_clusters in
  match one_cluster with
  | None -> failwith "No clusters in source dir"
  | Some cluster -> 
  let exe_env = Exe_env.from_cluster cluster in 
  let call_graph = Exe_env.get_cg exe_env in
  let procs_to_analyze = Cg.get_defined_nodes call_graph in
  match List.find ~f:(fun pn -> 
    String.equal (Typ.Procname.to_string pn) proc_sig.id) procs_to_analyze with
  | None -> failwith ("No proc found with name " ^ proc_sig.id)
  | Some proc_name ->
  synthesize proc_name exe_env procspec
  

  