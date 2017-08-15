open! IStd
open! SynSpecs
open! SynOut
open! Rules

module F = Format

let syn_max_depth = 20
   
let insert_penultimate_node node proc_desc = 
  let pred_nodes = Procdesc.Node.get_preds (Procdesc.get_exit_node proc_desc) in 
  begin
  match List.hd pred_nodes with 
  | Some pred -> 
    Procdesc.node_set_succs_exn proc_desc pred [node] []
  | None -> assert false
  end;
  Procdesc.node_set_succs_exn proc_desc node [(Procdesc.get_exit_node proc_desc)] []

(* Debug printing *)
let print_init_spec pvars procspec tenv proc_name
    my_new_pre my_new_post =
  begin
    F.print_string "pvars: "; 
    List.iter ~f:(fun (pv, _) -> Pvar.pp Pp.text F.std_formatter pv) pvars;
    F.print_string "\n";  
    F.printf "Given pre: \n";
    Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_pre);
    F.printf "\n";
    F.printf "Given post: \n";
    Prop.pp_prop_with_typ Pp.text F.std_formatter (Prop.normalize tenv my_new_post);
    F.printf "\n";
  end

(* Sanity checker *)
let analyse_and_proceed proc_name tenv my_new_pre my_new_post : bool =
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
      false
  | ImplFail _ | ImplOK _ -> true
      

let proceed_with_prefix instr_list
    (kont : unit -> c_instr_type option) : c_instr_type option =
  match kont () with
  | Some res -> Some (instr_list @ res)
  | None -> None

(**************************************************************)
(* Currently no backtracking - takes the first branch in rule order
   every time only. Rules are functions from prop to rule_result -
   make sure to remember the "thunk" *)
(**************************************************************)   

let rec synthesize_with_rules depth gamma tenv proc_desc
    (pre : Prop.exposed Prop.t) (post : Prop.exposed Prop.t) :
    c_instr_type option =
  begin
    if depth > syn_max_depth then failwith "Depth exceeded"
  end;
  let proc_name = Procdesc.get_proc_name proc_desc in
  match Prover.check_implication_for_footprint proc_name tenv (Prop.normalize tenv pre) post with
  (* This means we are done: let's spit out the output as a string *)
  | ImplOK (_, _, sub2, _, _, _, _, _, _, _)
    when (Sil.equal_exp_subst sub2 Sil.exp_sub_empty) ->
      (* TODO: please, explain this check -- why we need empty substitutions? *)
      (* End of synthesis, return empty instruction list *)
      F.printf "Synthesis success";
      Some []
  | ImplOK _ 
  | ImplFail _ ->
      (* Apply all kinds of rules *)
      (* TODO: add write rule as well *)
      let rules = [ read_rule proc_name gamma pre post
                  ; write_rule gamma pre post ] in
      let rec try_rules rules : c_instr_type option =
        match rules with
        | [] ->
            None
        | rule :: tl -> match rule () with
          | RFail -> try_rules tl
          | RSuccess ((r_gamma, r_pre, r_post), instr_list) ->
              (* Run top-level synthesis recursively *)
              F.printf "\npreposts: \n";
              Prop.pp_sigma Pp.text F.std_formatter r_pre.sigma;
              F.printf "\n";
              Prop.pp_sigma Pp.text F.std_formatter r_post.sigma;
              F.printf "\n"; 
              proceed_with_prefix instr_list (fun _ ->
                  synthesize_with_rules (depth + 1) r_gamma tenv
                    proc_desc r_pre r_post)
      in try_rules rules


(******************************************)
(* Main non-recursive synthesis procedure *)
(******************************************)
let synthesize proc_name (procspecs: Parsetree.procspec list) : string = 
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
  let my_new_pre, my_new_post = make_spec procspec tenv proc_name in 

  (* Debug print *)
  print_init_spec pvars procspec tenv proc_name my_new_pre my_new_post;

  (* TODO: Mystery statement ahead, please, investigate. *)
  Procdesc.signal_did_preanalysis proc_desc;

  if not (analyse_and_proceed proc_name tenv my_new_pre my_new_post)
  then failwith "Nothing to synthesize"
  else
    let result = synthesize_with_rules 0 pvars tenv proc_desc my_new_pre my_new_post
    in match result with
    | Some r -> 
      pprint_output r procspec
    | None -> failwith "Synthesis failed"

(**************************************)
(* Main runner function for synthesis *)
(**************************************)
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
  
