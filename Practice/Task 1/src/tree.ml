type op = Conj | Disj | Impl;;

type tree = Binop of op * tree * tree | Var of string;;
