open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;
let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

type type_of_type = SimpleT of int | ComplexT of type_of_type * type_of_type;;
type type_eq = EqT of type_of_type * type_of_type;;

let unique_type = Stream.from (fun i -> Some (i));;
let next_type() = (Stream.next unique_type);;

let rec checkPT pt =
  match pt with
  | SimpleT t -> (string_of_int t);
  | ComplexT (f, t) -> "(" ^ (checkPT f) ^ "->" ^ (checkPT t) ^ ")";
;;
let checkEq (EqT(l, r)) = fprintf oc "%s = %s\n" (checkPT l) (checkPT r);;
let checkSys sys = List.iter checkEq sys;; (* REMOVE *)

(* TODO: remove hmaps as params *)
let hmap_free = Hashtbl.create 1703;;
let hmap_bond = Hashtbl.create 1703;;
let rec build_system expr = match expr with
  | Var v ->
    let n_t = (
    (* fprintf oc "flag 1\n"; *)
      if Hashtbl.mem hmap_bond v
      then Hashtbl.find hmap_bond v
      else
        if Hashtbl.mem hmap_free v
        then Hashtbl.find hmap_free v
        else (let nn_t = next_type() in Hashtbl.add hmap_free v nn_t; nn_t)
      )
             in ([], SimpleT(n_t))
  | Appl (l, r) -> (
    (* fprintf oc "flag 2\n"; *)
    let (s1, t1) = build_system l in
      let (s2, t2) = build_system r in
        let n_t1 = next_type() in
          (((EqT(t1, ComplexT(t2, SimpleT(n_t1))))::(s1 @ s2)), SimpleT(n_t1));
    )
  | Abstr (v, r) -> (
    (* fprintf oc "flag 3\n"; *)
    let n_t = next_type() in
    Hashtbl.add hmap_bond v n_t;
    let (s1, t1) = build_system r in
      Hashtbl.remove hmap_bond v;
      (s1, ComplexT(SimpleT(n_t), t1))
    )
  ;;

let step1 system =
  (* fprintf oc "⚡️⚡️⚡️Step 1:\n"; *)
  let rec next_eq lst n_system = match lst with
    | [] -> n_system (* not sure *)
    | x::tl -> (match x with
      | EqT (l, r) -> (
        (* checkEq x; *)
        match l with
        | ComplexT (lft, rght) -> (match r with
          | SimpleT typ1 -> (next_eq tl (EqT(r, l)::n_system))
          | _ -> next_eq tl (x::n_system))
        | _ -> next_eq tl (x::n_system)
        )
      )
    in next_eq system []
    ;;

let step2 system =
  (* fprintf oc "⚡️⚡️⚡️Step 2:\n"; *)
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
  (* fprintf oc "⚡️⚡️⚡️Step 3:\n"; *)
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

let substitute (sl, sr) system inner_iter =
  (* fprintf oc "---- Substitution: "; checkEq (EqT(sl,sr)); fprintf oc "---- into: \n"; checkSys system; *)
  let rec subs n_system = function
    | [] -> n_system
    | x::lst -> match x with
      | EqT (l, r) -> (
        (* fprintf oc "------ Equation: "; checkEq (x); *)
        if List.length n_system = (inner_iter)
        then (
          (* fprintf oc "true\n"; *)
          (subs (List.rev (x::(List.rev n_system))) lst)
          (* (subs (x::n_system) lst) *)
          )
        else (
          (* fprintf oc "false\n"; *)
          let rec search_var eq =
            (* fprintf oc "Searching var: "; *)
            (match eq with
            | SimpleT st -> (
              (* fprintf oc "simple (%d)\n" st; *)
              if eq = sl
              then (
                (* fprintf oc "               changed 👆\n"; *)
                sr)
              else eq)
            | ComplexT (ct1, ct2) -> (
              (* fprintf oc "complex\n"; *)
              ComplexT(search_var ct1, search_var ct2))
              )
          in let loc_eq = EqT((search_var l), (search_var r))
             in subs (List.rev (loc_eq::(List.rev n_system))) lst
             (* in subs (loc_eq::n_system) lst *)
          )
        )
  in subs [] system
  ;;

let step4 system =
  (* fprintf oc "⚡️⚡️⚡️Step 4:\n"; *)
  (* fprintf oc "♎️ System in st4:\n"; checkSys system; *)
  let rec next_eq lst it =
    if it = List.length lst
    then lst
    else
      let x = (List.nth lst it)
      in
        (* fprintf oc "-- Next eq: "; checkEq x; *)
        match x with
        | EqT (l, r) -> (match l with
          | SimpleT t ->
            let n_sys = substitute (l, r) lst it
            in next_eq n_sys (it + 1)
          | _ -> next_eq lst (it + 1))
  in next_eq system 0
  ;;

exception SystemHasNoType;;
let rec find_var var whr = match whr with
  | SimpleT t -> if t = var then true else false
  | ComplexT (l, r) -> (find_var var l) || (find_var var r)
  ;;
let rec find_in_system var system = match system with
  | [] -> false
  | x::tl -> match x with
    | EqT (l, r) ->
      (find_var var l) || (find_var var r) || (find_in_system var tl)

let rec no_type system = match system with
  | [] -> false
  | x::tl -> (
    match x with
    | EqT(l, r) -> (match l with
      | SimpleT t -> (match r with
        | SimpleT t1 -> no_type tl
        | _ -> (find_var t r) || no_type tl)
      | _ -> no_type tl)
    )
  ;;

let rec is_final system = match system with
 | [] -> true
 | x::tl -> (match x with
   | EqT (l, r) -> match l with
     | SimpleT t -> not (find_in_system t tl)
     | _ -> false) && is_final tl
  ;;

exception Interrupt;;
let tio = ref 0;;
let rec solve_system system =
  (* checkSys system; *)
  fprintf oc "\n🌍🌍🌍Solving...\n";
  tio := !tio + 1;
  if (!tio > 200) then raise Interrupt else
  if no_type system
  then raise SystemHasNoType
  else
    if is_final system
    then system
    else
    (
      let s1 = step1 system in
      fprintf oc "🍒s1: \n"; checkSys s1;
      let s2 = step2 s1 in
      fprintf oc "🍒s2: \n"; checkSys s2;
      let s3 = step3 s2 in
      fprintf oc "🍒s3: \n"; checkSys s3;
      let s4 = step4 s3 in
      fprintf oc "🍒s4: \n"; checkSys s4; fprintf oc "----------------\n";
      solve_system s4
      )
  ;;

let derived_types = Hashtbl.create 1703
let rec create_types_map system = match system with
  | [] -> ()
  | x::tl -> match x with
    | EqT (l, r) -> (
      Hashtbl.add derived_types l r; create_types_map tl;
      fprintf oc "added: "; checkEq x)
  ;;

let put_tab tab =
  let rec p_t tb str =
    if tb == 0 then str else p_t (tb - 1) (str ^ "*   ")
  in p_t tab ""
  ;;

let r_unique_type = Stream.from (fun i -> Some (i));;
let r_next_type() = (Stream.next r_unique_type);;

let correct_type tp =
  if Hashtbl.mem derived_types tp
  then Hashtbl.find derived_types tp
  else tp
  ;;

let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let string_of_type tp =
  fprintf oc "👀\n";
  let rec s_t t =
    let l_t = correct_type t in
      match l_t with
      | SimpleT st -> (
        fprintf oc "simple (%d)\n" st;
        string_of_int st)
      | ComplexT (l, r) -> (
        fprintf oc "complex\n" ;
        "(" ^ s_t l ^ "->" ^ s_t r ^ ")")
  in s_t tp
  ;;

let make_proof input =
  let buf = Buffer.create 100500 in
  let rec m_p expr tb =
    match expr with
    | Var v ->
      let n_t = (
        if Hashtbl.mem hmap_bond v
        then Hashtbl.find hmap_bond v
        else
          if Hashtbl.mem hmap_free v
          then Hashtbl.find hmap_free v
          else (let nn_t = r_next_type() in Hashtbl.add hmap_free v nn_t; nn_t)
        )
       in
         (* tab context : type |- expression : type *)
         add_string buf (put_tab tb); add_string buf v;
         add_string buf " : "; add_string buf (string_of_type (SimpleT(n_t)));
         add_string buf " |- "; add_string buf v; add_string buf " : ";
         add_string buf (string_of_type (SimpleT(n_t))); add_string buf " [rule #1]\n";
        (SimpleT(n_t))
    | Appl (l, r) -> (
      let (t1) = m_p l (tb + 1) in (* may be should change order *)
        let (t2) = m_p r (tb + 1) in
          let n_t1 = r_next_type() in
            (* tab |- expression : type *)
            add_string buf (put_tab tb);
            add_string buf "|- "; add_string buf (string_of_tree expr);
            add_string buf " : "; add_string buf (string_of_type (SimpleT(n_t1)));
            add_string buf " [rule #2]\n";
            (SimpleT(n_t1));
      )
    | Abstr (v, r) -> (
      let n_t = r_next_type() in
      Hashtbl.add hmap_bond v n_t;
      let (t1) = m_p r (tb + 1) in
        Hashtbl.remove hmap_bond v;
        (* tab |- expression : type *)
        add_string buf (put_tab tb);
        add_string buf "|- "; add_string buf (string_of_tree expr);
        add_string buf " : "; add_string buf (string_of_type (ComplexT(SimpleT(n_t), t1)));
        add_string buf " [rule #3]\n";
        (ComplexT(SimpleT(n_t), t1))
      )
    in m_p input 0;
    contents buf
    ;;

let inp = ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main;;

let (a, b) = build_system inp;;

let solver =
  try
    (let final_system = solve_system a in
      checkSys final_system;
      create_types_map final_system;
      let (_) = printf "%s\n" (make_proof inp) in ())
  with SystemHasNoType -> fprintf oc "❌❌❌Expression has no type❌❌❌\n";;
