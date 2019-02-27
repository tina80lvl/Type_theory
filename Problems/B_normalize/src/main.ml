open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;
(* module HashTb = Hashtbl.Make(String);; *)

let var_set = VarSet.empty;;
let global_vars = Hashtbl.create 1000;;
let rec print_list lst = match lst with
  | [] -> printf "\n"; []
  | x::l -> printf "%s " x; print_list l
  ;;
(* Вернуть список имён свободных переменных *)
(* val free_vars : Tree.tree -> VarSet.elt list *)
let free_vars lmbd =
  let rec free_vars_rec lmbd blocked = match lmbd with
    | Var v -> if VarSet.mem v blocked
               then VarSet.empty
               else VarSet.singleton v
    | Abstr (v, r) -> free_vars_rec r (VarSet.add v blocked)
    | Appl (l, r) -> VarSet.union (free_vars_rec l blocked) (free_vars_rec r blocked)
  in VarSet.elements (free_vars_rec lmbd VarSet.empty)
  ;;

(* Проверить свободу для подстановки. Параметры:
 что подставляем, где подставляем, вместо чего подставляем *)
(* val free_to_sub : Tree.tree -> Tree.tree -> string -> bool *)
let free_to_sub theta lmbd x =
  print_list (free_vars theta);
  let free_set = VarSet.of_list (free_vars theta) in
    let rec is_free lmbd x blocked = match lmbd with
        | Var a -> if a = x
                   then ((VarSet.inter free_set blocked) = VarSet.empty)
                   else true
        | Abstr (a, lm) -> if a = x
                           then true
                           else is_free lm x (VarSet.add a blocked)
        | Appl (left, right) -> (is_free left x blocked) && (is_free right x blocked)
      in is_free lmbd x VarSet.empty
      ;;

(* val add_el_to_hmap : (string, string) Hashtbl.t -> string -> string -> (string, string) Hashtbl.t *)
let add_el_to_hmap map k v = printf "%s %s\n" k, v; Hashtbl.add map k v; Hashtbl.add global_vars k v; map;;
(* val merge_maps : (string, string) Hashtbl.t -> unit *)
let merge_maps map = Hashtbl.iter (fun x y -> Hashtbl.add map x y) global_vars;;
(* val unique_name : string Stream.t *)
let unique_name = Stream.from (fun i -> Some ("$" ^ string_of_int i));;
(* val change_vars : Tree.tree -> (string, string) Hashtbl.t -> Tree.tree *)
let rec change_vars lmbd map =
  merge_maps map;
  (match lmbd with
    | Var a -> if Hashtbl.mem map a
               then Var(Hashtbl.find map a)
               else lmbd
    | Appl(left, right) -> Appl(change_vars left map, change_vars right map)
    | Abstr(a, lm) -> let new_var = (Stream.next unique_name)
                      in Abstr(new_var, change_vars lm (add_el_to_hmap map a new_var))
  )
  ;;

(* val check_redex : Tree.tree -> bool *)
let rec check_redex tree =
 (* printf "checking redex = %s\n" (string_of_tree tree); *)
  match tree with
  | Var v -> (*printf "flag 4\n";*) false
  | Appl (l, r) -> (*printf "flag 5\n";*)(match l with
                    | Abstr (v1, r1) -> true
                    | _ -> (check_redex l || check_redex r))
  | Abstr (v, r) -> (*printf "flag 6\n";*) check_redex r
  ;;

(* val var_exists : string -> Tree.tree -> bool *)
let rec var_exists var whr = match whr with
  | Var v -> var = v
  | Appl (l,r) -> var_exists var l || var_exists var r
  | Abstr (v,r) -> (var = v) || var_exists var r

(* val reduction : Tree.tree -> Tree.tree *)
let rec reduction expr = match expr with
  | Var ov -> expr
  | Appl (l, r) -> (
    match l with
      | Abstr (v,rr) -> (* rr - expression without variable of abstraction *)
        let substitute expr_of_abstraction var expr_to_subs =
          (* printf "var_s = %s\n" var; printf "expr_to_subs = %s\n" (string_of_tree r);*)
            let rec subs e = match e with
              | Var vs -> (*printf "flag 1 %s %s\n" vs var;*)
                if vs = var
                then expr_to_subs
                else Var((*if free_to_sub expr_to_subs expr_of_abstraction vs
                         then change_var expr_to_subs expr_of_abstraction vs
                         else *)vs)
              | Appl (ls,rs) -> (*printf "flag 2\n";*) Appl ((subs ls), (subs rs))
              | Abstr (vs,rs) -> (*printf "flag 3\n";*)
                if vs == var then Abstr(((*if free_to_sub expr_to_subs expr_of_abstraction vs
                                         then change_var expr_to_subs expr_of_abstraction vs
                                         else *)vs), rs)
                             else Abstr(((*if free_to_sub expr_to_subs expr_of_abstraction vs
                                         then change_var expr_to_subs expr_of_abstraction vs
                                         else *)vs), subs rs) (* TODO: check closest lambda *)
            in subs expr_of_abstraction;
        in substitute rr v r;
      | _ -> Appl(reduction l, reduction r)
    )
  | Abstr (ov, oe) -> VarSet.add ov var_set; Abstr(ov, reduction oe)
  ;;

(*  *)
let rec get_original_var var =
  let loc_var = Hashtbl.find global_vars var
  in
    if (String.get loc_var 0 = '$')
    then get_original_var loc_var
    else var
  ;;

(*  *)
let rec change_vars_back expr = match expr with
  | Var v -> Var(get_original_var v)
  | Appl (l,r) -> Appl((change_vars_back l), (change_vars_back r))
  | Abstr (v,r) -> Abstr((get_original_var v), (change_vars_back r))
  ;;

(* val try_to_reduce : Tree.tree -> Tree.tree *)
let rec try_to_reduce tree = (*change_vars_back *)
  (if check_redex tree
   then ((*printf "true\n";*) try_to_reduce (reduction (change_vars tree (Hashtbl.create 1000))))
   else ((*printf "false\n";*) tree));;

(* val string_of_tree : Tree.tree -> string *)
let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

(* val lines : string *)
let lines =
let init = Buffer.create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

(* file input *)
let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> change_vars_back >> string_of_tree >> printf "%s\n";;

(* terminal input *)
(* lines >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> string_of_tree >> printf "%s\n";; *)
