open! IStd
open! SynSpecs
open! SynOut
open! Rules

module F = Format

let syn_max_depth = 1
   
let insert_penultimate_node node proc_desc = 
  let pred_nodes = Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc) in 
  begin
  match List.hd pred_nodes with 
  | Some pred -> 
    Procdesc.node_set_succs_exn proc_desc pred [node] []
  | None -> assert false
  end;
  Procdesc.node_set_succs_exn proc_desc node [(Procdesc.get_exit_node proc_desc)] []

let synthesize proc_name (procspecs: Parsetree.procspec list) = 
  let procspec = List.hd_exn procspecs in 
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

  let my_new_pre, my_new_post = Synlog.make_spec procspec tenv proc_name in 
  F.printf "Given pre: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_pre);
  F.printf "\n";
  F.printf "Given post: \n";
  Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_post);
  F.printf "\n";

  Procdesc.signal_did_preanalysis proc_desc; 

  match Prover.check_implication_for_footprint proc_name tenv 
    (Prop.normalize tenv my_new_pre) my_new_post with
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

    (* Currently no backtracking - takes the first branch in rule order every time only *)
    (* Rules are functions from prop to rule_result - make sure to remember the "thunk" *)
    let rec unify depth pre post = 
      begin
      if depth > syn_max_depth then failwith "Depth exceeded"
      end;
      match Prover.check_implication_for_footprint proc_name tenv (Prop.normalize tenv pre) post with 
      | ImplOK (checks, sub1, sub2, frame, missing_sigma, missing_pi,
        frame_fld, missing_fld, frame_typ, missing_typ) 
        when (Sil.equal_exp_subst sub2 Sil.exp_sub_empty) -> 
        pprint_output proc_desc procspec

      | ImplOK _
      | ImplFail _ ->
        let slns = 
          [ read_rule proc_name pvars pre post ] in 
      
        let new_nodes, new_pre, new_post = (* Get the result nodes of the first rule that succeeded *) 
          let rec try_rules slns pre post = 
            match slns with 
            | [] -> 
              print_node_instrs proc_desc; 
              failwith "No unify rules succeeded"
            | sln :: _ -> begin
              match sln () with 
              | RFail -> try_rules (List.tl_exn slns) pre post
              | RSuccess (instr_lists, r_pre, r_post) -> 
                let nodes = List.map ~f:(fun instrs -> 
                  Procdesc.create_node proc_desc Location.dummy 
                    (Procdesc.Node.Stmt_node "") instrs
                ) instr_lists in 
                (nodes, r_pre, r_post)
              end
          in 
          try_rules slns pre post 
        in 
        List.iter ~f:(fun n -> insert_penultimate_node n proc_desc) new_nodes; 

        unify (depth + 1) new_pre new_post in
    unify 0 my_new_pre my_new_post

let run ~arg = 
  let pspec = ParseMain.run arg in 
  match pspec with
  | [] -> failwith "Input file is empty"
  | procspec :: _ as procspecs -> 
  let proc_name = Typ.Procname.from_string_c_fun procspec.proc.id in 
  let c_prog_str = synthesize proc_name procspecs in 
  let out_path = (Str.string_before arg 
    (Str.search_backward (Str.regexp_string "/") arg (String.length arg)))
      ^ "/result.c" in 
  F.printf "Synthesis result is stored in %s \n" out_path;
  Out_channel.write_all ~data:c_prog_str out_path
  
