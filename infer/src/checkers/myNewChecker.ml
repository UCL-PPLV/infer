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

let print_sigma sigma = 
  List.iter ~f:(fun s -> 
    Sil.pp_hpred Pp.text F.std_formatter s;
    print_string " "
  ) sigma

let print_pi pi = 
  List.iter ~f:(fun p -> 
    Sil.pp_atom Pp.text F.std_formatter p;
    print_string " " 
  ) pi

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
    print_sigma sigma;
    print_endline "\npi: ";
    print_pi pi;
    print_endline "\nsigma_fp: ";
    print_sigma sigma_fp;
    print_endline "\npi_fp: ";
    print_pi pi_fp;
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
      print_sigma sigma;
      print_endline "\npi: ";
      print_pi pi;
      print_endline "\nsigma_fp: ";
      print_sigma sigma_fp;
      print_endline "\npi_fp: ";
      print_pi pi_fp;
      print_endline "";
    ) posts;
  ) specs

(** create a replacement list from for pointsto for program variables *)
let create_pvar_env_list (sigma: Prop.sigma) : (Exp.t * Pvar.t) list =
  let env = ref [] in
  let filter = function
    | Sil.Hpointsto (Lvar pvar, Eexp (Var v, _), _) ->
        if not (Pvar.is_global pvar) then env := (Exp.Var v, pvar) :: !env
    | _ -> ()
  in
  List.iter ~f:filter sigma;
  !env

let swap_post = ref Prop.prop_emp

let swap_incmpl_post = ref Prop.prop_emp

let find_exp_replacement (name: string) (exp_replace_list: (Exp.t * Pvar.t) list) = 
  match List.find ~f:(fun p -> String.equal (Pvar.get_simplified_name (snd p)) name) 
      exp_replace_list with
  | Some pair -> fst pair
  | None -> failwith "find_exp_replacement: No var of that name found"

let find_original (e: Exp.t) sigma = 
  match List.find ~f:(fun h -> Exp.equal (Sil.hpred_get_lhs h) (e)) sigma with 
  | Some Sil.Hpointsto (_, Eexp (Var v, _), _) -> Exp.Var v
  | _ -> failwith "find_original: No original value found"

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
  print_string "\n";
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

    begin
    match Prover.check_implication_for_footprint pname tenv pre (Prop.expose post) with 
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
       frame_fld, missing_fld, frame_typ, missing_typ) -> print_endline "pre = post: Yes"
    | ImplFail _ -> print_endline "pre = post: No"
    end;

    let exp_replace_list = create_pvar_env_list pre.sigma in
    let x_val = find_exp_replacement "x" exp_replace_list in
    let y_val = find_exp_replacement "y" exp_replace_list in
    let x_pointsto = find_original x_val pre.sigma in
    let y_pointsto = find_original y_val pre.sigma in 
    let my_new_hpred1 = Prop.mk_ptsto tenv x_val (Sil.Eexp (y_pointsto, Sil.inst_none)) 
      (Exp.Sizeof 
        {typ=(Typ.mk (Tint IInt)); nbytes=None; dynamic_length=None; subtype=Subtype.exact}) in
    let my_new_hpred2 = Prop.mk_ptsto tenv y_val (Sil.Eexp (x_pointsto, Sil.inst_none)) 
      (Exp.Sizeof
        {typ=(Typ.mk (Tint IInt)); nbytes=None; dynamic_length=None; subtype=Subtype.exact}) in
    let my_new_sigma = my_new_hpred1 :: my_new_hpred2 :: [] in
    let my_new_post = Prop.from_sigma my_new_sigma in

    begin match Prover.check_implication_for_footprint pname tenv post my_new_post with 
    | ImplOK (checks, sub1, sub2, frame, missing_pi, missing_sigma,
       frame_fld, missing_fld, frame_typ, missing_typ) -> print_endline "post = given post: Yes"
    | ImplFail _ -> print_endline "post = given post: No"
    end;

    List.iter ~f:(fun hpred1 -> 
      List.iter ~f:(fun hpred2 ->
        if Sil.equal_hpred hpred1 hpred2 then print_string "Match found - ";
        print_string "hpred1 is: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred1;
        print_string " and hpred2 is: ";
        Sil.pp_hpred {Pp.text with opt = SIM_WITH_TYP} F.std_formatter hpred2;
        print_endline ""
      ) my_new_post.sigma;
    ) post.sigma;



  print_endline "";
  end;
  summary
  end
