open! IStd

module F = Format

let path_to_source = "/home/ben/Desktop/swap/swap-proto.c"
let synth_pname = "swap"

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
  | Some pair -> fst pair
  | None -> failwith "find_exp_replacement: No var of that name found"

(* Find the Exp that an Exp points to in a sigma *)
let find_pointsto (e: Exp.t) sigma = 
  match List.find ~f:(fun h -> Exp.equal (Sil.hpred_get_lhs h) (e)) sigma with 
  | Some Sil.Hpointsto (_, Eexp (Var v, _), _) -> Exp.Var v
  | _ -> failwith "find_pointsto: No value found"

let create_new_post tenv (pre: Prop.normal Prop.t) = 
  let exp_replace_list = create_pvar_env_list pre.sigma in
  let x_val = find_exp_replacement "x" exp_replace_list in
  let y_val = find_exp_replacement "y" exp_replace_list in
  let x_pointsto = find_pointsto x_val pre.sigma in
  let y_pointsto = find_pointsto y_val pre.sigma in 
  let my_new_hpred1 = Prop.mk_ptsto tenv x_val (Sil.Eexp (y_pointsto, Sil.inst_none)) 
    (Exp.Sizeof 
      {typ=(Typ.mk (Tint IInt)); nbytes=None; dynamic_length=None; subtype=Subtype.exact}) in
  let my_new_hpred2 = Prop.mk_ptsto tenv y_val (Sil.Eexp (x_pointsto, Sil.inst_none)) 
    (Exp.Sizeof
      {typ=(Typ.mk (Tint IInt)); nbytes=None; dynamic_length=None; subtype=Subtype.exact}) in
  let my_new_sigma = my_new_hpred1 :: my_new_hpred2 :: [] in
  Prop.from_sigma my_new_sigma

let insert_penultimate_node node proc_desc = 
  Procdesc.node_set_succs_exn proc_desc 
    (List.hd_exn (Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc))) [node] [];
  Procdesc.node_set_succs_exn proc_desc node [(Procdesc.get_exit_node proc_desc)] []

let remove_nullifys proc_desc = 
  Procdesc.iter_instrs (fun n i -> match i with 
    | Sil.Nullify _ -> 
      let instrs = Procdesc.Node.get_instrs n in 
      let new_instrs = List.filter ~f:(function
        | Sil.Nullify _ -> false
        | _ -> true) instrs in
      Procdesc.Node.replace_instrs n new_instrs;

    | _ -> ()
  ) proc_desc

let print_node_instrs proc_desc = 
  List.iter ~f:(fun n ->
    Procdesc.Node.pp_instrs Pp.text ~sub_instrs:true None F.std_formatter n;
    F.print_string "preds: ";
    List.iter ~f:(fun p -> 
      Procdesc.Node.pp F.std_formatter p; F.print_string " ") (Procdesc.Node.get_preds n);
    F.print_string "; node: ";
    Procdesc.Node.pp F.std_formatter n;
    F.print_string "; succs: ";
    List.iter ~f:(fun s -> 
      Procdesc.Node.pp F.std_formatter s; F.print_string " ") (Procdesc.Node.get_succs n);
    F.print_string "\n"
  ) (Procdesc.get_nodes proc_desc);
  F.print_string "\n"

let get_typ_from_ptr_exn (ptr_typ: Typ.t) = match ptr_typ.desc with
  | Tptr (t, _) -> t 
  | _ -> failwith "Not a pointer type"

let rec synthesize_writes callbacks node (queue: Sil.instr list list) =
  let proc_desc = callbacks.Callbacks.proc_desc in 
  let proc_name = Procdesc.get_proc_name proc_desc in 
  let summary = Interproc.analyze_procedure callbacks in
  (* Specs.pp_summary_text F.std_formatter summary; *)
  let specs = Specs.get_specs_from_payload summary in 
  print_specs specs;
  let post = fst (List.hd_exn (List.hd_exn specs).Specs.posts) in
  let pre = Specs.Jprop.to_prop (List.hd_exn specs).Specs.pre in 
  let my_new_post = create_new_post callbacks.Callbacks.tenv pre in 

  match Prover.check_implication_for_footprint proc_name callbacks.Callbacks.tenv post my_new_post with 
  | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
    frame_fld, missing_fld, frame_typ, missing_typ) -> 
    F.print_string "post = given post: Yes\n";
  | ImplFail _ -> 
  F.print_string "post = given post: No\n";

  let new_instrs = ref [] in
  
  List.iter ~f:(fun hpred1 -> 
    List.iter ~f:(fun hpred2 ->
      if Sil.equal_hpred hpred1 hpred2 then 
        begin
        new_instrs := Procdesc.Node.get_instrs node;
        F.print_string "Match found! - ";
        end;
      F.print_string "hpred1 is: ";
      Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred1;
      F.print_string " and hpred2 is: ";
      Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred2;
      F.print_string "\n"
    ) my_new_post.sigma;
  ) post.sigma;
  F.print_string "\n";

  let abstract_inst = Sil.Abstract (Location.dummy) in 
  let next_instrs = List.hd_exn queue in
  new_instrs := !new_instrs @ next_instrs @ [abstract_inst];
  Procdesc.Node.replace_instrs node !new_instrs;

  F.print_string "Node instrs after\n";
  print_node_instrs proc_desc;

  
  (* Recursive call to run - after the instructions have been changed *)
  let new_queue = List.tl queue in 
  match new_queue with
  | None -> failwith "Nothing left in synthesis queue"
  | Some nq -> synthesize_writes callbacks node nq

let synthesize proc_name exe_env = 
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
  let posts = List.map ~f:fst spec.posts in
  let post = List.hd posts in 
  match post with
  | None -> ()
  | Some _ ->

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
    Sil.Store (Exp.Lvar local, typ, Exp.Var temp2, Location.dummy) ]
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
      [Sil.Load (temp1, Exp.Lvar pv, get_typ_from_ptr_exn typ, Location.dummy);
      Sil.Load (temp2, Exp.Lvar local, get_typ_from_ptr_exn typ, Location.dummy);
      Sil.Store (Exp.Var temp1, get_typ_from_ptr_exn typ, Exp.Var temp2, Location.dummy)]
    ) local_vars) pvars) in

  let write_node = Procdesc.create_node proc_desc Location.dummy (Procdesc.Node.Stmt_node "") 
    [] in
  insert_penultimate_node write_node proc_desc;
  Procdesc.compute_distance_to_exit_node proc_desc;

  remove_nullifys proc_desc;
  Specs.clear_spec_tbl ();
  let callbacks = { Callbacks.get_proc_desc; 
    get_procs_in_file; idenv; tenv; summary; proc_desc; } in
  
  synthesize_writes callbacks write_node possible_writes

let run () = 
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
    String.equal (Typ.Procname.to_string pn) synth_pname) procs_to_analyze with
  | None -> failwith ("No proc found with name " ^ synth_pname)
  | Some proc_name ->
  synthesize proc_name exe_env
  

  