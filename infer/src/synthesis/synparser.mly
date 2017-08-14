%token <int> INT
%token <string> ID
%token <string> RET_TYPE
%token <string> TYPE
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token POINTSTO
%token STAR
%token AND
%token EQ
%token NEQ
%token NOT
%token GT
%token LT
%token EOF
%token SEMICOLON
%token DOUBLESEMI
%token COMMA
%token EMP

%start <Parsetree.procspec list> start

%%

start: 
| EOF                                                        { [] }
| ps = procspec                                              { [ps] }
| ps = procspec; st = start                                  { ps :: st }
;

procspec:
| pre = prop; proc = proc; post = prop                       { {Parsetree.pre; proc; post} }
;

proc:
| ret_typ = RET_TYPE; id = ID; LPAREN; params = param_list; RPAREN    { {Parsetree.ret_typ; id; params} }
;

param_list:
| /* empty */                                                { [] }
| p = param                                                  { [p] }
| p = param; COMMA; pl = param_list                          { p :: pl }
;

param:
| typ = TYPE; id = ID                                        { {Parsetree.typ; id} }
;

prop: 
| LBRACKET pi = pi; SEMICOLON; sigma = sigma; RBRACKET       { {Parsetree.pi; sigma} }
;

sigma:
| h = hpred                                                  { [h] }
| h = hpred; STAR; s = sigma                                 { h :: s }
;

hpred:
| EMP                                                        { Parsetree.Hpred_empty }
| id1 = ID; POINTSTO; id2 = ID                               { Parsetree.Hpred_hpointsto (id1, Parsetree.Location (id2)) }
| id = ID; POINTSTO; int = INT                               { Parsetree.Hpred_hpointsto (id, Parsetree.Int (int)) }
;

/* Hpointsto Exp.t (strexp0 'inst) Exp.t */

pi: 
| a = atom                                                   { [a] }
| a = atom; AND; p = pi                                      { a :: p }
;

atom: 
| /* empty */                                                { Parsetree.Atom_empty }
| NOT LPAREN; a = atom; RPAREN                               { Parsetree.Atom_not (a) }
| id1 = ID; EQ; id2 = ID                                     { Parsetree.Atom_eq (id1, Parsetree.Location (id2)) }
| id1 = ID; NEQ; id2 = ID                                    { Parsetree.Atom_neq (id1, Parsetree.Location (id2)) }
| id1 = ID; LT; id2 = ID                                     { Parsetree.Atom_lt (id1, Parsetree.Location (id2)) }
| id1 = ID; GT; id2 = ID                                     { Parsetree.Atom_gt (id1, Parsetree.Location (id2)) }
| id = ID; EQ; int = INT                                     { Parsetree.Atom_eq (id, Parsetree.Int (int)) }
| id = ID; NEQ; int = INT                                    { Parsetree.Atom_neq (id, Parsetree.Int (int)) }
| id = ID; LT; int = INT                                     { Parsetree.Atom_lt (id, Parsetree.Int (int)) }
| id = ID; GT; int = INT                                     { Parsetree.Atom_gt (id, Parsetree.Int (int)) }
;


