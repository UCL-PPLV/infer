{
  open Lexing
  open Synparser

  exception LexerError of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      }
}

let newline = ('\010' | '\013' | "\013\010" | "\n" | "\r\n")
let blank = [' ' '\009' '\012']
let letter = ['A'-'Z' '_' 'a'-'z']
let digit = ['0'-'9']
let alphanum = digit | letter
let ident = letter alphanum*
let num = digit+
let ret_type = "void"
let type = "int*"

rule token = parse
  | newline   { next_line lexbuf; token lexbuf }
  | blank+    { token lexbuf }
  | "|->"     { POINTSTO }
  | ","       { COMMA }
  | "["       { LBRACKET }
  | "("       { LPAREN }
  | "]"       { RBRACKET }
  | ")"       { RPAREN }
  | ";"       { SEMICOLON }
  | ";;"      { DOUBLESEMI }
  | "*"       { STAR }
  | "&&"      { AND }
  | "="       { EQ }
  | "!="      { NEQ }
  | "!"       { NOT }
  | ">"       { GT }
  | "<"       { LT }
  | "emp"     { EMP }
  | ret_type  { RET_TYPE (Lexing.lexeme lexbuf) }
  | type      { TYPE (Lexing.lexeme lexbuf) }
  | num       { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | ident     { ID (Lexing.lexeme lexbuf) }
  | eof       { EOF }
  | _         { raise (LexerError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }