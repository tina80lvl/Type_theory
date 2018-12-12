type var = Var of string;;

type tree = Abstr var * tree | Appl tree * tree | Var of string;;
