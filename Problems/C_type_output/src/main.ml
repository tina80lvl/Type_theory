open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

type type_of_type = SimpleT of int | ComplexT of type_of_type * type_of_type;;
type type_eq = EqT of type_of_type * type_of_type;;

(* module Hashtbl = Map.Make(Tree);; *)
(*module TabsMap = Map.Make(type_of_type);;
let equations = [];;
let types = [];;
let tabs = [];;*)
(* let types_map = Hashtbl.empty;; *)
(* let types_map = Hashtbl.create 1000;; *)

let unique_type = Stream.from (fun i -> Some (i));;
let next_type() = (Stream.next unique_type);;

let rec put_tab tb str = if tb == 0 then str else put_tab (tb - 1) (str ^ "*   ");;

(* let rec print_list lst = match lst with
  | [] -> ()
  | x::tl -> printf "%s " x; print_list lst
  ;; *)
let rec checkPT pt =
  match pt with
  | SimpleT t -> (string_of_int t);
  | ComplexT (f, t) -> "(" ^ (checkPT f) ^ "->" ^ (checkPT t) ^ ")";
;;
let checkEq (EqT(l, r)) = printf "%s=%s\n" (checkPT l) (checkPT r);;
let checkSys sys = List.iter checkEq sys;; (* REMOVE *)

(* TODO: remove hmaps as params *)
let rec build_system expr tb hmap_free hmap_bond = match expr with
  | Var v ->
    let n_t = (
    (* printf "flag 1\n"; *)
      if Hashtbl.mem hmap_bond v
      then Hashtbl.find hmap_bond v
      else
        if Hashtbl.mem hmap_free v
        then Hashtbl.find hmap_free v
        else (let nn_t = next_type() in Hashtbl.add hmap_free v nn_t; nn_t)
      )
             in ([], SimpleT(n_t), (tb + 1))
  | Appl (l, r) -> (
    (* printf "flag 2\n"; *)
    let (s1, t1, tb1) = build_system l (tb + 1) hmap_free hmap_bond in
      let (s2, t2, tb2) = build_system r (tb + 1) hmap_free hmap_bond in
        (* (((EqT(t1, ComplexT(t2, SimpleT(tb2 + 1))))::(s1 @ s2)), SimpleT(tb2 + 1), (tb2 + 1)); *)
        let n_t1 = next_type() in
          (((EqT(t1, ComplexT(t2, SimpleT(n_t1))))::(s1 @ s2)), SimpleT(n_t1), (tb2 + 1));
    )
  | Abstr (v, r) -> (
    (* printf "flag 3\n"; *)
    let n_t = next_type() in
    Hashtbl.add hmap_bond v n_t;
    let (s1, t1, tb1) = build_system r (tb + 1) hmap_free hmap_bond in
      Hashtbl.remove hmap_bond v;
      (s1, ComplexT(SimpleT(n_t), t1), tb1)
    )
  ;;


let eq_types_map = Hashtbl.create 1000;;

let rec remove_el n = function
  | [] -> []
  | x::lst -> if n = 0 then lst else x::remove_el (n - 1) lst
  ;;

let rec reverse_eq eq = match eq with | EqT(t1, t2) -> EqT(t2, t1);;
let rec rewrite_el eq = function
  | [] -> []
  | x::lst -> if x == eq then (reverse_eq eq)::lst else x::(rewrite_el eq lst)
  ;;

let rec reduce_all eq = function
  | [] -> []
  | x::lst -> if x == eq
              then
                (match x with
                  | EqT(t1, t2) -> (
                    let rec red e1 e2 = match e1 with
                      | SimpleT st -> EqT(e1,e2)::lst
                      | ComplexT (ct1, ct2) -> red ct1 ct2
                    in red t1 t2
                    )
                )
              else x::(reduce_all eq lst)
  ;;

let step1 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | ComplexT (lft, rght) -> match r with
          | SimpleT typ1 -> (next_eq tl (EqT(r, l)::n_system))
          | _ -> next_eq tl (x::n_system)
        | _ -> next_eq tl (x::n_system)
      )
    | [] -> n_system (* not sure *)
    in next_eq system []
    ;;

let step2 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l,r with
        | SimpleT t1, SimpleT t2 -> if t1 = t2 then next_eq tl n_system else next_eq tl (x::n_system)
        | _ -> next_eq tl (x::n_system)
      )
    | [] -> n_system (* not sure *)
    in next_eq system []
    ;;

let step3 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | SimpleT t -> next_eq tl (x::n_system)
        | ComplexT (t1, t2) -> (match r with
          | SimpleT st -> next_eq tl (x::n_system)
          | ComplexT (ct1, ct2) -> next_eq tl (EqT(t1,ct1)::EqT(t2,ct2)::n_system)
          )
      )
    | [] -> n_system (* not sure *)
    in next_eq system []
    ;;

let vars_to_change = Hashtbl.create 1000;;
let substitute system =
  let rec subs n_system = function
    | [] -> n_system
    | x::lst -> match x with
      | EqT (l, r) ->
        let rec search_var eq = match eq with
          | SimpleT st -> if Hashtbl.mem vars_to_change eq then Hashtbl.find vars_to_change eq else eq
          | ComplexT (ct1, ct2) -> ComplexT(search_var ct1, search_var ct2)
        in (EqT((search_var l), (search_var r))) :: (subs var expr lst) :: n_system
  in subs [] system
  ;;

let step4 system =
  let rec next_eq lst = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | SimpleT t -> match r with
          | ComplexT (lft, rght) -> Hashtbl.add vars_to_change l r
          | _ -> next_eq tl
        | _ -> next_eq tl
      )
    | [] -> ()
  in substitute (next_eq system)
  ;;

(* let rec solve_system system =
(*  TODO: check system *)
  let rec next_eq = match system with
    | x::lst -> match x with
      | EqT (l, r) -> match l with
        | Complex (lft, rght) -> match r with
          | SimpleT typ1 -> next_eq (n + 1) rewrite_el x system
          | Complex (t1, t2) -> lst.append EqT(lft, t1); lst.append EqT(rght, t2)
        | SimpleT typ -> match r with
          | SimpleT typ2 -> if typ == typ2 then solve_system remove_el
          | ComplexT (t1, t2) -> change_all
      solve_system lst
    | _ ->
    in solve_system equations;; *)

let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l, r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v, r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let lines =
let init = Buffer.create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init);;

let inp = lines >>  Lexing.from_string >> Parser.main Lexer.main;;

let (a, b, c) = build_system inp 0 (Hashtbl.create 100) (Hashtbl.create 100);;
checkSys a;
