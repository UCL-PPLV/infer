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
%token EOF
%token SEMICOLON
%token COLON
%token COMMA
%token EMP

%start <Parsetree.procspec option> start

%%

start: 
| EOF                                                        { None }
| pre = prop; proc = proc; post = prop EOF                   { Some {Parsetree.pre; proc; post} }
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
| typ = TYPE; id = ID                                          { {Parsetree.typ; id} }
;

prop: 
| LBRACKET pi = pi; SEMICOLON; sigma = sigma; RBRACKET            { {Parsetree.pi; sigma} }
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
| /* empty */                                                { Atom_empty }
;


