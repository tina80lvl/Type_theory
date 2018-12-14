%{
  open Tree;;
%}
%token <string> VAR
%token OPEN CLOSE
%token DOT
%token EOF
%token LMBD
%start main
%type <Tree.tree> main
%%
main:
    expr EOF { $1 }
expr:
    appl LMBD VAR DOT expr { Appl ($1, Abstr($3, $5)) }
    | LMBD VAR DOT expr    { Abstr ($2, $4) }
    | appl                 { $1 }
appl:
    appl atom  { Appl ($1, $2) }
    | atom     { $1 }
atom:
    OPEN expr CLOSE  { $2 }
    | VAR            { Var ($1) }
