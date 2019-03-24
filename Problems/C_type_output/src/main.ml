open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

type type_of_type = SimpleT of int | ComplexT of type_of_type * type_of_type;;
type type_eq = EqT of type_of_type * type_of_type;;

let unique_type = Stream.from (fun i -> Some (i));;
let next_type() = (Stream.next unique_type);;

let hmap_free = Hashtbl.create 1703;;
let hmap_bond = Hashtbl.create 1703;;
let rec build_system expr = match expr with
  | Var v ->
    let n_t = (
      if Hashtbl.mem hmap_bond v
      then Hashtbl.find hmap_bond v
      else
        if Hashtbl.mem hmap_free v
        then Hashtbl.find hmap_free v
        else (let nn_t = next_type() in Hashtbl.add hmap_free v nn_t; nn_t)
      )
             in ([], SimpleT(n_t))
  | Appl (l, r) -> (
    let (s2, t2) = build_system r in
      let (s1, t1) = build_system l in
        let n_t1 = next_type() in
          (((EqT(t1, ComplexT(t2, SimpleT(n_t1))))::(s1 @ s2)), SimpleT(n_t1));
    )
  | Abstr (v, r) -> (
    let n_t = next_type() in
    Hashtbl.add hmap_bond v n_t;
    let (s1, t1) = build_system r in
      Hashtbl.remove hmap_bond v;
      (s1, ComplexT(SimpleT(n_t), t1))
    )
  ;;

let flag = ref false;;
let step1 system =
  let rec next_eq lst n_system = match lst with
    | [] -> n_system (* not sure *)
    | x::tl -> (match x with
      | EqT (l, r) -> (
        match l with
        | ComplexT (lft, rght) -> (match r with
          | SimpleT typ1 -> flag := true; (next_eq tl (EqT(r, l)::n_system))
          | _ -> next_eq tl (x::n_system))
        | _ -> next_eq tl (x::n_system)
        )
      )
    in next_eq system []
    ;;

let step2 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l,r with
        | SimpleT t1, SimpleT t2 -> if t1 = t2 then (flag := true; next_eq tl n_system) else next_eq tl (x::n_system)
        | _ -> next_eq tl (x::n_system)
      )
    | [] -> n_system
    in next_eq system []
    ;;

let step3 system =
  let rec next_eq lst n_system = match lst with
    | x::tl -> (match x with
      | EqT (l, r) -> match l with
        | SimpleT t -> next_eq tl (x::n_system)
        | ComplexT (t1, t2) -> (match r with
          | SimpleT st -> next_eq tl (x::n_system)
          | ComplexT (ct1, ct2) -> (flag := true; next_eq tl (EqT(t1,ct1)::EqT(t2,ct2)::n_system))
          )
      )
    | [] -> n_system
    in next_eq system []
    ;;

let substitute (sl, sr) system inner_iter =
  flag := true;
  let rec subs n_system = function
    | [] -> n_system
    | x::lst -> match x with
      | EqT (l, r) -> (
        if List.length n_system = (inner_iter)
        then (subs (List.rev (x::(List.rev n_system))) lst)
        else (
          let rec search_var eq =
            (match eq with
            | SimpleT st -> (
              if eq = sl
              then sr
              else eq)
            | ComplexT (ct1, ct2) -> (
              ComplexT(search_var ct1, search_var ct2))
              )
          in let loc_eq = EqT((search_var l), (search_var r))
             in subs (List.rev (loc_eq::(List.rev n_system))) lst
          )
        )
  in subs [] system
  ;;

let step4 system =
  let rec next_eq lst it =
    if it = List.length lst
    then lst
    else
      let x = (List.nth lst it)
      in
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

let mk_step n system =
  flag := false;
  match n with
  | 1 -> step1 system
  | 2 -> step2 system
  | 3 -> step3 system
  | 4 -> step4 system
  ;;

let rec solve_system system =
  if no_type system
  then raise SystemHasNoType
  else
    if is_final system
    then system
    else
    (
      let s1 = mk_step 1 system
      in if !flag then solve_system s1 else
        let s2 = mk_step 2 system
        in if !flag then solve_system s2 else
          let s3 = mk_step 3 system
          in if !flag then solve_system s3 else
            let s4 = mk_step 4 system
            in if !flag then solve_system s4 else
              solve_system s4;
      )
  ;;

let derived_types = Hashtbl.create 1703;;
let rec create_types_map system = match system with
  | [] -> ()
  | x::tl -> match x with
    | EqT (l, r) -> (
      Hashtbl.add derived_types l r; create_types_map tl;
      )
  ;;

let put_tab tab =
  let rec p_t tb str =
    if tb == 0 then str else p_t (tb - 1) (str ^ "*   ")
  in p_t tab ""
  ;;

let r_unique_type = Stream.from (fun i -> Some (i));;
let r_next_type() = (Stream.next r_unique_type);;

let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let correct_type tp =
  if Hashtbl.mem derived_types tp
  then Hashtbl.find derived_types tp
  else tp
  ;;
  
let string_of_type tp =
  let rec s_t t =
    let l_t = correct_type t in
      match l_t with
      | SimpleT st -> (
        "t" ^ (string_of_int (st + 1)))
      | ComplexT (l, r) -> (
        "(" ^ s_t l ^ " -> " ^ s_t r ^ ")")
  in s_t tp
  ;;

let answer = ref [];;
let to_answer str = answer := str::(!answer);;
let rec print_answer lst = match lst with
  | [] -> ()
  | x::tl -> (printf "%s" x; print_answer tl)
  ;;

let context = ref "";;
let g_context = ref "";;
let added_to_context = Hashtbl.create 1703;;

let put_context = context := "";
  Hashtbl.iter (
    fun k v -> (
    (* fprintf oc "LOCAL: iter step: %s %d\n" k v; *)
    if !context = ""
    then (
      if (not (Hashtbl.mem added_to_context k))
      then (
        Hashtbl.add added_to_context k v;
        context := !context ^ k ^ " : " ^ string_of_type (correct_type (SimpleT(v)));
        Hashtbl.remove added_to_context k;
        )
      )
    else (
      if (not (Hashtbl.mem added_to_context k))
      then  (
        Hashtbl.add added_to_context k v;
        context := !context ^ ", " ^ k ^ " : " ^ string_of_type (correct_type (SimpleT(v)));
        Hashtbl.remove added_to_context k;
        )
      )
    )
  )
  ;;
let put_gcontext =
  Hashtbl.iter (
    fun k v -> (
    if !context = ""
    then (
      if (not (Hashtbl.mem added_to_context k))
      then (
        Hashtbl.add added_to_context k v;
        context := !context ^ k ^ " : " ^ string_of_type (correct_type (SimpleT(v)));
        )
      )
    else (
      if (not (Hashtbl.mem added_to_context k))
      then  (
        Hashtbl.add added_to_context k v;
        context := !context ^ ", " ^ k ^ " : " ^ string_of_type (correct_type (SimpleT(v)));
        )
      )
    )
  )
  ;;

let make_proof input =
  let rec m_p expr tb cntx =
    match expr with
    | Var v ->
      let n_t = (
        if Hashtbl.mem hmap_bond v
        then Hashtbl.find hmap_bond v
        else
          if Hashtbl.mem hmap_free v
          then Hashtbl.find hmap_free v
          else (
            let nn_t = r_next_type() in Hashtbl.add hmap_free v nn_t; nn_t)
        )
       in
         (* tab context : type |- expression : type *)
         let loc_s =
          if cntx = ""
          then (put_tab tb) ^ cntx ^ "|- " ^ v ^ " : " ^ (string_of_type (SimpleT(n_t))) ^ " [rule #1]\n"
          else (put_tab tb) ^ cntx ^ " |- " ^ v ^ " : " ^ (string_of_type (SimpleT(n_t))) ^ " [rule #1]\n"
         in to_answer loc_s;
         (SimpleT(n_t))
    | Appl (l, r) -> (
      let (_) = m_p r (tb + 1) cntx in
        let (_) = m_p l (tb + 1) cntx in
          let n_t1 = r_next_type() in
            (* tab |- expression : type *)
            let loc_s =
              if cntx = ""
              then (put_tab tb) ^ cntx ^ "|- " ^ (string_of_tree expr) ^ " : " ^ (string_of_type (SimpleT(n_t1))) ^ " [rule #2]\n"
              else (put_tab tb) ^ cntx ^ " |- " ^ (string_of_tree expr) ^ " : " ^ (string_of_type (SimpleT(n_t1))) ^ " [rule #2]\n"
            in to_answer loc_s;
            (SimpleT(n_t1));
      )
    | Abstr (v, r) -> (
      let n_t = r_next_type() in
      Hashtbl.add hmap_bond v n_t;
      let (t1) = m_p r (tb + 1) ((
          fun loc_c -> if loc_c = ""
          then (v ^ " : " ^ (string_of_type (SimpleT(n_t))))
          else (cntx ^ ", " ^ v ^ " : " ^ (string_of_type (SimpleT(n_t))) )) cntx) in
        Hashtbl.remove hmap_bond v;
        (* tab |- expression : type *)
        let loc_s =
          if cntx = ""
          then (put_tab tb) ^ cntx ^ "|- " ^ (string_of_tree expr) ^ " : " ^ (string_of_type (ComplexT(SimpleT(n_t), t1))) ^ " [rule #3]\n"
          else (put_tab tb) ^ cntx ^ " |- " ^ (string_of_tree expr) ^ " : " ^ (string_of_type (ComplexT(SimpleT(n_t), t1))) ^ " [rule #3]\n"
        in to_answer loc_s;
        (ComplexT(SimpleT(n_t), t1))
      )
    in m_p input 0 !context
    ;;

let inp = input_line stdin >> Lexing.from_string >> Parser.main Lexer.main;;

let (a, b) = build_system inp;;

let solver =
  try
    (let final_system = solve_system a in
      create_types_map final_system;
      put_gcontext hmap_free;
      Hashtbl.reset hmap_free; Hashtbl.reset hmap_bond;
      let (_) = make_proof inp in print_answer !answer
      )
  with SystemHasNoType -> printf "Expression has no type\n";;
