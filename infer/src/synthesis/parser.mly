%token <int> INT
%token <string> ID
%token <string> TYPE
%token LPAREN
%token RPAREN
%token LSQBRAC
%token RSQBRAC
%token POINTSTO
%token ADDRESSOF
%token STAR
%token AND
%token EOF
%token SEMICOLON
%token COMMA
%token EMP

%start <Procspec.t> start

%%

start: 
| pre = prop; func = proc; post = prop            { Procspec (pre, func, post)}
;

proc:
| id = ID; LPAREN; pl = param_list; RPAREN        { Proc (ID, param_list) }

param_list:
| /* empty */                                     { [] }
| p = param                                       { [p] }
| p = param; COMMA; pl = param_list               { p :: pl }
;

param:
| t = TYPE; id = ID                               { Param (t, id) }
;

prop: 
| LSQBRAC p = pi; SEMICOLON; s = sigma; RSQBRAC   { Prop (p, s) }
;

sigma:
| h = hpred                                       { [Hpred (h)] }
| h = hpred; STAR; s = sigma                      { Hpred (h) :: s }
;

hpred:
| EMP                                             { Hpred_empty }
| id1 = ID; POINTSTO; id2 = ID; COLON; t = TYPE   { Hpred_hpointsto (id1, id2, t) }
;

/* Hpointsto Exp.t (strexp0 'inst) Exp.t */

pi: 
| a = atom                                        { [Atom (a)] }
| a = atom; AND; p = pi                           { Atom (a) :: p }
;

atom: 
| /* empty */                                     { Atom_empty }
;


