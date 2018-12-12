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
    appl LMBD VAR DOT main EOF  { Appl ($1, Abstr(Var($3), $5)) }
    | LMBD VAR DOT main EOF     { Abstr ($2, $4) }
    | appl EOF                  { $1 }
appl:
    appl atom  { Appl ($1, $2) }
    | atom     { $2 }
atom:
    OPEN main CLOSE  { $2 }
    | VAR            { Var ($1) }
