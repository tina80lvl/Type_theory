open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

(* let (ic,oc) = (open_in "input.txt", open_out "output.txt");; *)
type deBruijn = DB_free of string | DB_bound of int | DB_appl of deBruijn * deBruijn | DB_abstr of deBruijn;;

let rec to_deBruijn bounded expr = match expr with
  | Var v -> (
    let rec is_bounded it arr = match arr with
      | x::tl -> if (v = x) then Some(it) else is_bounded (it + 1) tl
      | [] -> None
    in (match (is_bounded 0 bounded) with
      | Some(x) -> DB_bound(x)
      | None -> DB_free(v) )
    )
  | Appl(l, r) -> DB_appl((to_deBruijn bounded l), (to_deBruijn bounded r))
  | Abstr(v, r) -> DB_abstr(to_deBruijn (v::bounded) r)
  ;;

let rec inc_vars expr loc_lvl exp_lvl = match expr with
  | DB_free ov -> expr
  | DB_bound ov ->
    if (ov >= exp_lvl)
    then DB_bound(ov + loc_lvl)
    else DB_bound(ov)
  | DB_appl (l, r) -> DB_appl(inc_vars l loc_lvl exp_lvl, inc_vars r loc_lvl exp_lvl)
  | DB_abstr (r) -> DB_abstr(inc_vars r loc_lvl (exp_lvl + 1))
  ;;

let string_of_db tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
  | DB_free v -> add_string buf v
  | DB_bound v -> add_string buf (string_of_int v)
  | DB_appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
  | DB_abstr (r) -> add_string buf "(\\"; (*add_string buf v;*) add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let rec reduction expr lvl = (
  (* fprintf oc "🌍🌍🌍 reduction of: %s\n" (string_of_db expr); *)
  match expr with
  | DB_free ov -> expr
  | DB_bound ov -> expr
  | DB_appl (l, r) -> (
    match l with
      | DB_abstr (rr) -> (* rr - expression without variable of abstraction *)
        let substitute expr_of_abstraction expr_to_subs =
          (* fprintf oc "expr_of_abstr = %s\n" (string_of_db expr_of_abstraction);
          fprintf oc "expr_to_subs = %s\n" (string_of_db expr_to_subs); *)
            let rec subs e loc_lvl =
              (* fprintf oc "e = %s\n" (string_of_db e); *)
              (match e with
              | DB_free dv -> e
              | DB_bound dv ->
                if dv = loc_lvl
                then inc_vars expr_to_subs (loc_lvl) 0
                else
                  if dv >= loc_lvl
                  then DB_bound(dv - 1) (* from wiki *)
                  else e
              | DB_appl (ls,rs) -> DB_appl (subs ls loc_lvl, subs rs loc_lvl)
              | DB_abstr (rs) -> DB_abstr(subs rs (loc_lvl + 1)) )
            in subs expr_of_abstraction 0;
        in substitute rr r;
      | _ -> DB_appl(reduction l lvl, reduction r lvl)
    )
  | DB_abstr (oe) -> DB_abstr(reduction oe (lvl + 1))
  )
  ;;

let rec check_redex tree =
 (* printf "checking redex = %s\n" (string_of_tree tree); *)
  match tree with
  | DB_free v -> false
  | DB_bound v -> false
  | DB_appl (l, r) -> (match l with
                    | DB_abstr (r1) -> true
                    | _ -> (check_redex l || check_redex r))
  | DB_abstr (r) -> check_redex r
  ;;

let rec try_to_reduce tree = (*change_vars_back *)
(* fprintf oc "🎀 reduction of: %s\n" (string_of_tree tree); *)
  (if check_redex tree
   then ((*printf "true\n";*) try_to_reduce (reduction tree 0))
   else ((*printf "false\n";*) tree));;

let unique_name = Stream.from (fun i -> Some ("x" ^ string_of_int i));;
let rec give_names tree hmap lvl = match tree with
  | DB_free v -> Var(v)
  | DB_bound v -> Var(Hashtbl.find hmap (lvl - v - 1))
  | DB_appl (l, r) -> Appl(give_names l hmap lvl, give_names r hmap lvl)
  | DB_abstr (r) -> (
    let n_v = (Stream.next unique_name)
    in let tmp = Abstr(n_v, give_names r (Hashtbl.add hmap lvl n_v; hmap) (lvl + 1)) in
    Hashtbl.remove hmap lvl;
    tmp)
  ;;

let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t (give_names tree (Hashtbl.create 1000) 0);
  contents buf;;

let lines =
let init = Buffer.create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

(* file input *)
(* ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce (*>> change_vars_back *)>> string_of_tree >> printf "%s\n";; *)

(* terminal input *)
lines >> Lexing.from_string >> Parser.main Lexer.main >> to_deBruijn [] >> try_to_reduce >> string_of_tree >> printf "%s\n";;
