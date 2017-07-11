%token <int> INT
%token <string> ID
%token <string> TYPE
%token POINTSTO
%token ADDRESSOF
%token STAR
%token AND
%token EOF
%token SEMICOLON
%token EMP


%start <my_prop.t option> start

%%

start: 
| EOF                            { None }
| p = prop                       { Some p }
;

prop: 
| pi SEMICOLON sigma             { }
;

sigma:
| hpred                          { }
| sigma STAR sigma               { }
;

hpred:
| EMP                            { }
| ID POINTSTO ID COLON TYPE      { }

/* Hpointsto Exp.t (strexp0 'inst) Exp.t */

pi: 
| atom                           { }
| pi AND pi                      { }

atom: 
| /* empty */                    { }


