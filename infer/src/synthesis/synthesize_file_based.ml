open! IStd

module F = Format

let path_to_source = "/home/ben/Desktop/swap/swap-proto.c"
let synth_proc_name = "swap"

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
      F.print_string "path: \n";
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

let rec synthesize queue = 
  ClangWrapper.exe ~prog:"clang" ~args:[path_to_source];

  let all_clusters = DB.find_source_dirs () in 
  let one_cluster = List.hd all_clusters in
  match one_cluster with
  | None -> failwith "No clusters in source dir"
  | Some cluster -> 
  let exe_env = Exe_env.from_cluster cluster in 
  let call_graph = Exe_env.get_cg exe_env in
  let procs_to_analyze = Cg.get_defined_nodes call_graph in
  List.iter ~f:(fun proc_name -> 
    let get_proc_desc proc_name = Exe_env.get_proc_desc exe_env proc_name in
    let get_procs_in_file proc_name =
      match Exe_env.get_cfg exe_env proc_name with
      | Some cfg
        -> List.map ~f:Procdesc.get_proc_name (Cfg.get_defined_procs cfg)
      | None -> [] in
    let proc_name_readable = Typ.Procname.to_string proc_name in
    if String.equal proc_name_readable "main" then () else begin
    F.print_string ("Begin proc: " ^ proc_name_readable ^ "\n");
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
    | Some post ->
    let my_new_post = create_new_post tenv pre in
    match Prover.check_implication_for_footprint proc_name tenv post my_new_post with 
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
      frame_fld, missing_fld, frame_typ, missing_typ) -> 
      print_endline "post = given post: Yes";
      
      let file = In_channel.read_all path_to_source in
      let regexp = Str.regexp "/* ?? */.*\n" in
      let new_file = Str.replace_first regexp "" file in
      Out_channel.write_all ~data:new_file path_to_source;

    | ImplFail _ -> print_endline "post = given post: No";

    List.iter ~f:(fun hpred1 -> 
      List.iter ~f:(fun hpred2 ->
        if Sil.equal_hpred hpred1 hpred2 then begin
        print_string "Match found - ";
        let file = In_channel.read_all path_to_source in
        let regexp = Str.regexp_string "/* ?? */" in
        let new_prog_line = (List.hd_exn queue) ^ ";\n  /* ?? */" in
        let new_file = Str.replace_first regexp new_prog_line file in
        Out_channel.write_all ~data:new_file path_to_source;
        end;
        print_string "hpred1 is: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred1;
        print_string " and hpred2 is: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred2;
        print_endline ""
      ) my_new_post.sigma;
    ) post.sigma;

    let file = In_channel.read_all path_to_source in
    let regexp = Str.regexp_string "/* ?? */" in
    let split_file = Str.split regexp file in
    let head = List.hd_exn split_file in
    let tail = List.nth_exn split_file 1 in
    let trimmed_tail = Str.string_after tail ((String.index_exn tail '}') + 1) in
    let new_prog_line = "/* ?? */\n  " ^ (List.nth_exn queue 1) ^ ";\n}" in
    let new_file = head ^ new_prog_line ^ trimmed_tail in
    Out_channel.write_all path_to_source ~data:new_file;

    print_string (In_channel.read_all path_to_source);
    F.print_string ("End proc: " ^ proc_name_readable ^ "\n\n");

    (* Recursive call to run - after the source file has been changed *)
    let new_queue = List.tl queue in 
    match new_queue with
    | None -> failwith "Nothing left in synthesis queue"
    | Some nq -> synthesize nq
    end
  ) procs_to_analyze

let possible_reads (prog_vars: string list) = 
  let local_vars = 
    let varnames = 
      let make_varname (n: int) = Some ("t" ^ (string_of_int n)) in
      Stream.from make_varname in
    let len = List.length prog_vars in
    Stream.npeek len varnames
  in
  let read_stem = format_of_string "%s = *%s" in
  let reads = List.map2_exn ~f:(fun tv pv -> 
    Printf.sprintf read_stem tv pv
  ) local_vars prog_vars in
  (reads, local_vars)
  

let possible_writes temp_vars prog_vars = 
  let write_stem = format_of_string "*%s = %s" in
  List.concat (List.map ~f:(fun pv -> 
    List.map ~f:(fun tv -> 
      Printf.sprintf write_stem pv tv
    ) temp_vars
  ) prog_vars)

let run () = 
  let prog_var_names = ["x"; "y"] in
  let reads, temp_vars = possible_reads prog_var_names in
  let writes = possible_writes temp_vars prog_var_names in
  
  let local_decls = String.concat (List.map ~f:(fun t -> "int " ^ t ^ "; ") temp_vars) in
  let chained_reads = ((String.concat ~sep:"; " reads) ^ ";\n  /* ?? */") in
  let decls_and_reads = local_decls ^ "\n  " ^ chained_reads in
  let file = In_channel.read_all path_to_source in
  let regexp = Str.regexp_string "/* ?? */" in
  let new_file = Str.replace_first regexp decls_and_reads file in
  Out_channel.write_all path_to_source ~data:new_file;
  synthesize writes;  
  