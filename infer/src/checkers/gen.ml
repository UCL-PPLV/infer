(* hacky program which enumerates all the possible permutations of C statements
that can be generated given the names of pointers and schemes for reading and
assigning to pointers *)

let ptr_assign_stmt pname value = String.concat "" ["*"; pname; " = "; value];;

let ptr_read_stmt pname vname = String.concat "" [vname; " = "; "*"; pname];;

let pnames = ["x"; "y"];;

let varnames = 
  let make_varname (n: int) = Some ("t" ^ (string_of_int n)) in
  Stream.from make_varname;;

let local_vars = 
  let len = List.length pnames in
  Stream.npeek len varnames;;

let possible_reads = 
  List.map2 ptr_read_stmt pnames local_vars;;

let possible_writes =
  let rec mapf (flst: ('a -> 'b) list) (x: 'a) : 'b list =
    match flst with 
    | [] -> []
    | f :: fs -> (f x) :: (mapf fs x)
  in 
  List.flatten (List.map (mapf (List.map ptr_assign_stmt pnames)) local_vars);;
    
let rec print_list lst = 
  match lst with
  | [] -> print_string "Nil \n"
  | x :: xs -> print_string x; print_string " :: "; print_list xs;;

let ins_at_all_pos (x: 'a) (lst: 'a list) : 'a list list = 
  let rec ins_all_pos y lst1 lst2 =
    match lst2 with 
    | [] -> []
    | [z] -> (lst1 @ [y; z]) :: (lst1 @ [z; y]) :: []
    | z :: zs -> (lst1 @ (y :: z :: zs)) :: ins_all_pos y (lst1 @ [z]) zs
  in 
  ins_all_pos x [] lst;;

let rec permutations (lst: 'a list) : 'a list list = 
  match lst with 
  | [] -> [[]]
  | [x] -> [[x]]
  | x :: xs -> List.flatten (List.map (ins_at_all_pos x) (permutations xs));;

let declarations = 
  String.concat "; " (List.map (Printf.sprintf "int %s") local_vars);;

let possible_progs = 
  let possible_rw = possible_reads :: [] @ permutations possible_writes in
  List.map (fun l -> declarations :: l) possible_rw;;

let c_prog = format_of_string " 
#include <stdlib.h>

void swap(int* x, int* y) {
%s
}
  
int main() {
  return 0;
}
";;

let file_write_loop = 
  for i = 1 to List.length possible_progs do
    let filename = "./generated/p" ^ string_of_int i ^ ".c" in
    let oc = open_out filename in 
    Printf.fprintf oc c_prog ((String.concat ";\n" (List.nth possible_progs (i - 1))) ^ ";");
    close_out oc;
  done;;

let () = 
  List.iter print_list possible_progs;
  print_string "Number of possible programs: ";
  print_int (List.length possible_progs);
  print_string "\n";
  file_write_loop;;

