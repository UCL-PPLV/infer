(*
 * Copyright (c) 2016 - present Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *)

open! IStd

module F = Format
module L = Logging

(** backward analysis for computing set of maybe-live variables at each program point *)

module Domain = AbstractDomain.FiniteSet(Var)

(* compilers 101-style backward transfer functions for liveness analysis. gen a variable when it is
   read, kill the variable when it is assigned *)
module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain
  type extras = ProcData.no_extras

  let exec_instr astate proc_data node instr = 
    match astate with
    | _ -> astate
end

module Analyzer =
  AbstractInterpreter.Make (ProcCfg.Normal) (TransferFunctions)

let print_specs specs = 
  List.iter ~f:(fun (s: Prop.normal Specs.spec) -> 
    let joined_pre = s.pre in
    let pre = Specs.Jprop.to_prop joined_pre in
    let sigma = pre.sigma
    and pi = pre.pi
    and sigma_fp = pre.sigma_fp
    and pi_fp = pre.pi_fp in
    print_endline "pre: ";
    print_endline "sigma: ";
    List.iter ~f:(fun s -> 
      Sil.pp_hpred Pp.text F.std_formatter s;
      print_string " "
    ) sigma;
    print_endline "\npi: ";
    List.iter ~f:(fun p -> 
      Sil.pp_atom Pp.text F.std_formatter p;
      print_string " "
    ) pi;
    print_endline "\nsigma_fp: ";
    List.iter ~f:(fun s -> 
      Sil.pp_hpred Pp.text F.std_formatter s;
      print_string " "
    ) sigma_fp;
    print_endline "\npi_fp: ";
    List.iter ~f:(fun p -> 
      Sil.pp_atom Pp.text F.std_formatter p;
      print_string " "
    ) pi_fp;
    print_endline "";

    let posts = s.posts in 
    List.iter ~f:(fun (p: Prop.normal Prop.t * Paths.Path.t) -> 
      let post = fst p in 
      let sigma = post.sigma
      and pi = post.pi
      and sigma_fp = post.sigma_fp
      and pi_fp = post.pi_fp in
      print_endline "post: ";
      print_endline "sigma: ";
      List.iter ~f:(fun s -> 
        Sil.pp_hpred Pp.text F.std_formatter s;
        print_string " "
      ) sigma;
      print_endline "\npi: ";
      List.iter ~f:(fun p -> 
        Sil.pp_atom Pp.text F.std_formatter p;
        print_string " "
      ) pi;
      print_endline "\nsigma_fp: ";
      List.iter ~f:(fun s -> 
        Sil.pp_hpred Pp.text F.std_formatter s;
        print_string " "
      ) sigma_fp;
      print_endline "\npi_fp: ";
      List.iter ~f:(fun p ->
        Sil.pp_atom Pp.text F.std_formatter p;
        print_string " "
      ) pi_fp;
      print_endline "";
    ) posts;
  ) specs

(** create a replacement list from for pointsto for program variables *)
let create_pvar_env_list (sigma: Prop.sigma) : (Exp.t * Exp.t) list =
  let env = ref [] in
  let filter = function
    | Sil.Hpointsto (Lvar pvar, Eexp (Var v, _), _) ->
        if not (Pvar.is_global pvar) then env := (Exp.Var v, Exp.Lvar pvar) :: !env
    | _ -> () in
  List.iter ~f:filter sigma;
  !env

let swap_post = ref Prop.prop_emp

let swap_incmpl_post = ref Prop.prop_emp

let checker { Callbacks.get_proc_desc; get_procs_in_file; 
  idenv; tenv; summary; proc_desc; } : Specs.summary =
  let pname = Procdesc.get_proc_name proc_desc in 
  let proc_name_readable = Typ.Procname.to_string pname in
  if String.equal proc_name_readable "main" then 
    summary
  else
  begin
  print_endline ("Begin proc: " ^ proc_name_readable);
  let new_summary = Interproc.analyze_procedure { Callbacks.get_proc_desc; 
  get_procs_in_file; idenv; tenv; summary; proc_desc; } in
  let specs = Specs.get_specs_from_payload new_summary in
  Specs.pp_specs Pp.text F.std_formatter specs;
  print_string "\n";
  print_specs specs;
  let spec = List.hd specs in
  let pre = match spec with
  | Some s -> Specs.Jprop.to_prop s.pre
  | None -> Prop.prop_emp in
  let posts = match spec with 
  | Some s -> List.map ~f:fst s.posts
  | None -> [] 
  in 
  let post = List.hd posts in 
  begin
  match post with
  | None -> ();
  | Some post -> 
    (* let exp_replace_list = create_pvar_env_list pre.sigma in *)
    (* let replaced_post_sigma = List.map ~f:(Sil.hpred_replace_exp exp_replace_list) post.sigma in *)
    (* match Prover.check_implication_base pname tenv true true post (Prop.expose pre) with *)
    match Prover.check_implication_for_footprint pname tenv pre (Prop.expose post) with 
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
       frame_fld, missing_fld, frame_typ, missing_typ) -> print_endline "Yes";
    | ImplFail _ -> print_endline "No";

    if String.equal proc_name_readable "swap" then swap_post := post;
    if String.equal proc_name_readable "swap_incmpl" then swap_incmpl_post := post;

    if not (Prop.equal_prop !swap_post Prop.prop_emp) && 
      not (Prop.equal_prop !swap_incmpl_post Prop.prop_emp)
    then match Prover.check_implication_for_footprint pname tenv pre (Prop.expose post) with 
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
       frame_fld, missing_fld, frame_typ, missing_typ) -> print_endline "\nYes*Yes";
    | ImplFail _ -> print_endline "\nNo*No";
    else ()
  end;
  summary
  end