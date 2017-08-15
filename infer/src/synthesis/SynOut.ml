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

let pprint_output (all_instrs: Rules.c_instr_type) (procspec: Parsetree.procspec) = 
  let rec print_instrs instrs = 
    match instrs with 
      (* read *)
      | Sil.Load (_, Exp.Lvar pvar, _, _) ::
        Sil.Load (_, _, _, _) ::
        Sil.Store (Exp.Lvar local, typ, _, _) ::
        Sil.Remove_temps _ ::
        Sil.Abstract _ :: tl ->
          let local_name = Pvar.get_simplified_name local in 
          let pvar_name = Pvar.get_simplified_name pvar in 
          let typ_name = Typ.to_string typ in 
          let stmt = F.sprintf "%s %s = *%s;" typ_name local_name pvar_name in
          stmt :: (print_instrs tl)
      (* write ptr *)
      | Sil.Load (_, Exp.Lvar pvar, _, _) ::
        Sil.Load (_, Exp.Var local, _, _) ::
        Sil.Store _ :: 
        Sil.Remove_temps _ ::
        Sil.Abstract _ :: tl -> 
          let pvar_name = Pvar.get_simplified_name pvar in 
          let local_name = Ident.to_string local in 
          let stmt = F.sprintf "*%s = %s;" pvar_name local_name in 
          stmt :: (print_instrs tl)
      (* write const *)
      | Sil.Load (_, Exp.Lvar pvar, _, _) ::
        Sil.Store (_, _, Exp.Const const, _) ::
        Sil.Remove_temps _ ::
        Sil.Abstract _ :: tl ->
          let pvar_name = Pvar.get_simplified_name pvar in
          let const = Const.to_string const in
          let stmt = F.sprintf "*%s = %s;" pvar_name const in 
          stmt :: (print_instrs tl)
      | _ -> []
  in
  let statements_str = String.concat ~sep:"\n  " (print_instrs all_instrs)  in
  let c_prog_str = c_prog_of_sig procspec.proc ~body:statements_str in
  c_prog_str