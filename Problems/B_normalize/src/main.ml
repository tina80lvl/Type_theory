open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;

let need_to_change var = VarSet.exists var;;

let change_var var =
  let new_var = var + "\'" in
    if need_to_change new_var then change_var new_var else new_var
    ;;

(* TODO: check if it's nessecary to substitute again *)
let substitute expr_of_abstraction var expr_to_subs =
  let rec subs e = match e with
  | Var v -> if v == var then (* TODO: change variable in abstraction to e *)
  | Appl (l,r) -> subs l; subs r
  | Abstr (v,r) -> subs r;
  in subs expr_of_abstraction
  ;;

let try_to_apply l r = match l with
  | Abstr (v,rr) -> substitute rr v r; (* rr - expression without variable of abstraction *)
  | _ -> 
  ;;

let string_of_tree tree =
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf (try_to_apply l v);
    | Abstr (v,r) -> VarSet.add v; s_t r;
  in s_t tree;
  contents buf;;

let lines =
let init = create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

lines >>  Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> printf "%s\n";;
