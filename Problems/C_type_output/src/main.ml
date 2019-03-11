open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

type type_of_type = SimpleT of int | ComplexT of type_of_type * type_of_type;;
type type_eq = EqT of type_of_type * type_of_type;;

(* module TypesMap = Map.Make(type_of_type);;
module TabsMap = Map.Make(type_of_type);;
let equations = [];;
let types = [];;
let tabs = [];;
let types_map = TypesMap.empty;; *)

let unique_type = Stream.from (fun i -> Some ("t" ^ string_of_int i));;
let next_type = (Stream.next unique_type);;

let rec put_tab tb str = if tb == 0 then str in put_tab (tb - 1) (str + "*   ");;

(* TODO: not sure about adding equations *)
let rec build_system expr tb = match expr with
  | Var v -> let n_t = (if TypeMap.mem v types_map then TypeMap.key v types_map else next_type)
             in TypesMap.add Var(v) n_t types_map;
             n_t;
  | Appl (l, r) -> let t_l = build_system l (tb + 1) and t_r = build_system r (tb + 1)
                   in let n_t = next_type in
                   (*equations.append SimpleT(t_l); equations.append SimpleT(t_r);*)
                   equations.append EqT(t_l, ComplexT(t_r, n_t)); TypesMap.add Appl(l, r) n_t types_map;
                   n_t;
  | Abstr (v, r) -> let t_v = (if TypeMap.mem v types_map then TypeMap.key v types_map else next_type) and t_r = build_system r (tb + 1)
                    in (*equations.append SimpleT(t_r);*)
                    TypesMap.add Abstr(v,r) ComplexT(TypesMap.key v types_map, t_r) types_map;
                    ComplexT(TypesMap.key v types_map, t_r);;

let new_equations = [];;
let eq_types_map = TypesMap.empty;;

let rec remove_el n = function
  | [] -> []
  | x::lst -> if n = 0 then lst else x::remove_el (n - 1) lst
  ;;

let reverse_eq eq = match eq with | EqT(t1, t2) -> EqT(t2, t1);;
let rec rewrite_el eq = function
  | [] -> []
  | x::lst -> if x == eq then (reverse_eq eq)::lst else x::rewrite eq lst
  ;;

let rec reduce_all eq = function
  | [] -> []
  | x::lst -> if x == eq
              then
                (match x with
                  | EqT(t1, t2) -> let rec red e1 e2 = match e1 with
                    | SimpleT st -> EqT(e1,e2)::lst
                    | ComplexT (ct1, ct2) -> red ct1 ct2)
              else x::(reduce_all eq lst)
  ;;

let step1 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | ComplexT (lft, rght) -> match r with
          | SimpleT typ1 -> (next_eq tl EqT(typ1, l)::n_system)
          | _ -> (next_eq tl x::n_system)
        | _ -> (next_eq tl x::n_system)
      )
    | [] -> n_system (* not sure *)
    in next_eq system []
    ;;

let step2 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l,r with
        | SimpleT t1, Simple t2 -> if t1 = t2 then (next_eq tl n_system)
        | _ -> (next_eq tl x::n_system)
      | _ -> (next_eq tl x::n_system) (* not sure *)
      )
    | [] -> n_system (* not sure *)
    in next_eq system []
    ;;

let step3 =

let vars_to_change = Hashtbl.create 1000;;
let substitute system =
  let rec subs = function
    | [] -> []
    | x::lst -> match x with
      | EqT (l, r) ->
        let rec search_var eq = match eq with
          | SimptleT st -> if Hashtbl.mem vars_to_change st then Hashtbl.find vars_to_change st else eq
          | ComplexT (ct1, ct2) -> ComplexT(search_var ct1, search_var ct2)
        in EqT((search_var l), (search_var r))::(subs var expr lst)
  in subs system
  ;;

let step4 system =
  let rec next_eq lst n_system i = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | SimpleT t -> match r with
          | ComplexT (lft, rght) -> Hashtbl.add vars_to_change l r
          | _ -> (next_eq tl x::n_system)
        | _ -> (next_eq tl x::n_system)
      )
    | [] -> n_system (* not sure *)
    in substitute (next_eq system [] 0)
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
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l, r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v, r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
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
