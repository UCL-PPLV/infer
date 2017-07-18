%token <int> INT
%token <string> ID
%token <string> TYPE
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token POINTSTO
%token STAR
%token AND
%token EOF
%token SEMICOLON
%token COLON
%token COMMA
%token EMP

%start <Parsetree.procspec> start

%%

start: 
| EOF                                             { None }
| pre = prop; func = proc; post = prop EOF        { Procspec (pre, func, post) }
;

proc:
| id = ID; LPAREN; pl = param_list; RPAREN        { Proc (id, pl) }
;

param_list:
| /* empty */                                     { [] }
| p = param                                       { [p] }
| p = param; COMMA; pl = param_list               { p :: pl }
;

param:
| t = TYPE; id = ID                               { Param (t, id) }
;

prop: 
| LBRACKET p = pi; SEMICOLON; s = sigma; RBRACKET { Aprop (p, s) }
;

sigma:
| h = hpred                                       { [h] }
| h = hpred; STAR; s = sigma                      { h :: s }
;

hpred:
| EMP                                             { Hpred_empty }
| id1 = ID; POINTSTO; id2 = ID; COLON; t = TYPE   { Hpred_hpointsto (id1, id2, t) }
;

/* Hpointsto Exp.t (strexp0 'inst) Exp.t */

pi: 
| a = atom                                        { [a] }
| a = atom; AND; p = pi                           { a :: p }
;

atom: 
| /* empty */                                     { Atom_empty }
;


