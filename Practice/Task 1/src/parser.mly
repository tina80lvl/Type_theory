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
    appl LMBD VAR DOT expr EOF  {  }
    | appl                      {  }
appl:
    appl atom  {  }
    | atom     {  }
atom:
    OPEN expr CLOSE  { $2 }
    | VAR            { Var ($1) }
expr:
    VAR                 { Var ($1) }
    | OPEN expr CLOSE   { $2 }
    | expr IMPL expr    { Binop (Impl, $1, $3) }
    | expr AND expr     { Binop (Conj, $1, $3) }
    | expr OR expr      { Binop (Disj, $1, $3) }
