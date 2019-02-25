open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;

let var_set = VarSet.empty;;

let need_to_change var = VarSet.mem var var_set;;

let rec change_var var =
  (*printf "var = %s\n" var;*)
  let new_var = var ^ "\'" in
    if need_to_change new_var then change_var new_var else new_var
    ;;

let rec check_redex tree =
  (* printf "%s\n" (string_of_tree tree); *)
  match tree with
  | Var v -> false
  | Appl (l, r) -> (match l with
                    | Abstr (v1, r1) -> true
                    | _ -> (check_redex l || check_redex r))
  | Abstr (v, r) -> check_redex r
  ;;

let string_of_tree tree =
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let rec var_exists var whr = match whr with
  | Var v -> var = v
  | Appl (l,r) -> var_exists var l || var_exists var r
  | Abstr (v,r) -> (var = v) || var_exists var r

let rec try_to_apply l r = match l with
  | Abstr (v,rr) -> (* substitute rr v r;  rr - expression without variable of abstraction *)
    let substitute expr_of_abstraction var expr_to_subs =
      let n_var = var_exists var expr_to_subs in
    (*printf "var_s = %s\n" var; printf "expr_to_subs = %s\n" (string_of_tree r);*)
        let rec subs e = match e with
          | Var vs -> (*printf "flag 1 %s %s\n" vs var; *)if vs = var then expr_to_subs else Var(if n_var then change_var vs else vs)
          | Appl (ls,rs) ->(* printf "flag 2\n";*) Appl ((subs ls), (subs rs))
          | Abstr (vs,rs) -> (*printf "flag 3\n"; *) if vs == var then Abstr((if n_var then change_var vs else vs), rs) else Abstr((if n_var then change_var vs else vs), subs rs) (* TODO: check closest lambda *)
        in subs expr_of_abstraction;
    in substitute rr v r;
  | _ -> Appl(l, r)
  ;;

let rec reduce tree =
  if (check_redex tree)
  then
    let rec s_tr t = match t with
      | Var v -> t
      | Appl (l,r) -> try_to_apply l r
      | Abstr (v,r) -> VarSet.add v var_set; s_tr r
    in s_tr tree;
  else tree
  ;;

let lines =
let init = create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

lines >> Lexing.from_string >> Parser.main Lexer.main >> reduce >> string_of_tree >> printf "%s\n";;
