open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

let string_of_tree tree =
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

(*let (ic,oc) = (open_in "input.txt", open_out "output.txt");;*)

input_line stdin >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> printf "%s\n";;

(*
close_out oc;;
close_in ic;;
*)
