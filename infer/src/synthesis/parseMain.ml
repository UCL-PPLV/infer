open! Core
open Synlexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Synparser.start Synlexer.token lexbuf with
  | Synlexer.LexerError s -> fprintf stderr "Synlexer error: %s\n" s; exit(-1)
  | Synparser.Error -> fprintf stderr "%a: Synparser error\n" print_position lexbuf;
    exit (-1)

let run (filename: string) : Parsetree.procspec option =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let procspec = parse_with_error lexbuf in 
  In_channel.close inx;
  procspec

