open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;

let var_set = VarSet.empty;;

let need_to_change var = VarSet.mem var var_set;;

let string_of_tree tree =
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let rec change_var var =
  (*printf "var = %s\n" var;*)
  let new_var = var ^ "\'" in
    if need_to_change new_var then change_var new_var else new_var
    ;;

let rec check_redex tree =
 (* printf "checking redex = %s\n" (string_of_tree tree); *)
  match tree with
  | Var v -> (*printf "flag 4\n";*) false
  | Appl (l, r) -> (*printf "flag 5\n";*)(match l with
                    | Abstr (v1, r1) -> true
                    | _ -> (check_redex l || check_redex r))
  | Abstr (v, r) -> (*printf "flag 6\n";*) check_redex r
  ;;

let rec var_exists var whr = match whr with
  | Var v -> var = v
  | Appl (l,r) -> var_exists var l || var_exists var r
  | Abstr (v,r) -> (var = v) || var_exists var r

let rec reduction expr = match expr with
  | Var ov -> expr
  | Appl (l, r) -> (
    match l with
      | Abstr (v,rr) -> (* rr - expression without variable of abstraction *)
        let substitute expr_of_abstraction var expr_to_subs =
          (* printf "var_s = %s\n" var; printf "expr_to_subs = %s\n" (string_of_tree r);*)
            let rec subs e = match e with
              | Var vs -> (*printf "flag 1 %s %s\n" vs var;*) if vs = var then expr_to_subs else Var(if var_exists vs expr_to_subs then change_var vs else vs)
              | Appl (ls,rs) -> (*printf "flag 2\n";*) Appl ((subs ls), (subs rs))
              | Abstr (vs,rs) -> (*printf "flag 3\n";*)  if vs == var then Abstr((if var_exists vs expr_to_subs then change_var vs else vs), rs) else Abstr((if var_exists vs expr_to_subs then change_var vs else vs), subs rs) (* TODO: check closest lambda *)
            in subs expr_of_abstraction;
        in substitute rr v r;
      | _ -> Appl(reduction l, reduction r)
    )
  | Abstr (ov, oe) -> VarSet.add ov var_set; Abstr(ov, reduction oe)
  ;;

let rec try_to_reduce tree = if check_redex tree then ((*printf "true\n";*) try_to_reduce (reduction tree)) else ((*printf "false\n";*) tree);;

let lines =
let init = create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

(* file input *)
(* let (ic) = (open_in "input.txt");;
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> string_of_tree >> printf "%s\n";; *)
(* let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> string_of_tree >> fprintf oc "%s\n";; *)

(* terminal input *)
lines >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> string_of_tree >> printf "%s\n";;
