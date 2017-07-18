open! Core
open Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.start Lexer.token lexbuf with
  | Lexer.SyntaxError s -> print_string ("error" ^ s); exit(-1)
  | Parser.Error -> fprintf stderr "%a: parser error\n" print_position lexbuf;
    exit (-1)

let run filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_with_error lexbuf;
  In_channel.close inx

let () =
  Command.basic ~summary:""
    Command.Spec.(empty +> anon ("filename" %: file))
    run 
  |> Command.run