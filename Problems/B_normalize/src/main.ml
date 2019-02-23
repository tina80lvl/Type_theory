open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;

let var_set = VarSet.empty;;

let need_to_change var = VarSet.mem var var_set;;

let rec change_var var =
  let new_var = var ^ "\'" in
    if need_to_change new_var then change_var new_var else new_var
    ;;

let rec try_to_apply l r = match l with
  | Abstr (v,rr) -> (* substitute rr v r;  rr - expression without variable of abstraction *)
    let substitute expr_of_abstraction var expr_to_subs =
      let rec subs e = match e with
      | Var vs -> if vs == var then e else Var(vs);
      | Appl (ls,rs) -> try_to_apply (subs ls) (subs rs);
      | Abstr (vs,rs) -> if vs == var then Abstr(vs, rs) else Abstr(vs, subs rs); (* TODO: check closest lambda *)
      in subs expr_of_abstraction;
    in substitute rr v r;
  | _ -> Appl(l, r);
  ;;

let string_of_tree tree =
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v;
    | Appl (l,r) -> add_string buf "("; let loc_appl = try_to_apply l r in
                                        if loc_appl == Appl(l, r)
                                        then (s_t l; add_string buf " "; s_t r;)
                                        else s_t loc_appl; add_string buf ")";
    | Abstr (v,r) -> VarSet.add v var_set; add_string buf "(\\"; add_string buf v; add_string buf ".("; s_t r; add_string buf ")";
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
