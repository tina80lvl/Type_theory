open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

(* let (ic,oc) = (open_in "input.txt", open_out "output.txt");; *)
let (>>) x f = f x;;

module VarSet = Set.Make(String);;
module VarMap = Map.Make(String);;

let var_set = VarSet.empty;;
let global_vars = Hashtbl.create 1000;;
let rec print_list lst = match lst with
  | [] -> printf "\n"; []
  | x::l -> printf "%s " x; print_list l
  ;;

(* val free_vars : Tree.tree -> VarSet.elt list *)
let free_vars expr =
  let rec f_v expr blocked = match expr with
    | Var v -> if VarSet.mem v blocked
               then VarSet.empty
               else VarSet.singleton v
    | Abstr (v, r) -> f_v r (VarSet.add v blocked)
    | Appl (l, r) -> VarSet.union (f_v l blocked) (f_v r blocked)
  in VarSet.elements (f_v expr VarSet.empty)
  ;;

(* val free_to_sub : Tree.tree -> Tree.tree -> string -> bool *)
let free_to_sub theta expr x =
  let free_set = VarSet.of_list (free_vars theta) in
    let rec is_free expr x blocked = match expr with
        | Var v -> if v = x
                   then ((VarSet.inter free_set blocked) = VarSet.empty)
                   else true
        | Appl (l, r) -> (is_free l x blocked) && (is_free r x blocked)
        | Abstr (v, r) -> if v = x
                           then true
                           else is_free r x (VarSet.add v blocked)
      in is_free expr x VarSet.empty
      ;;

(* let print_hmap hm = Hashtbl.iter (fun x y -> fprintf oc "k v = %s %s\n" x y) hm;; *)
(* val add_el_to_hmap : (string, string) Hashtbl.t -> string -> string -> (string, string) Hashtbl.t *)
let add_el_to_hmap map k v = (*printf "%s %s\n" k, v;*) Hashtbl.add map k v; Hashtbl.add global_vars v k; map;;
let rem_el_from_hmap map k = (*printf "%s %s\n" k, v;*) Hashtbl.remove map k; map;;

(* val merge_maps : (string, string) Hashtbl.t -> unit *)
let merge_maps map = Hashtbl.iter (fun x y -> Hashtbl.add map x y) global_vars;;
(* val unique_name : string Stream.t *)
let unique_name = Stream.from (fun i -> Some ("x" ^ string_of_int i));;
(* val string_of_tree : Tree.tree -> string *)
let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;
(* let already_changed = Hashtbl.create 1000;; *)

let ret_var v map changed =
  if (Hashtbl.mem map v)
  then (
     if (Hashtbl.mem changed v)
     then (List.hd (List.rev (Hashtbl.find_all map v)))
     else (Hashtbl.find map v))
  else v
  ;;
(* val change_vars : Tree.tree -> (string, string) Hashtbl.t -> Tree.tree *)
let rec change_vars expr map changed =
  (* fprintf oc "⚡️⚡️⚡️ expr: ";
  fprintf oc "%s\n" (string_of_tree expr);
  fprintf oc "🧨 changed:\n";
  print_hmap changed;
  fprintf oc "🥺 map:\n";
  print_hmap map; *)
  (match expr with
    | Var v -> ((*fprintf oc "⌛️ var: %s\n" v;*) Var(ret_var v map changed))
    | Appl(l, r) -> ((*fprintf oc "⌛️ appl\n";*) Appl(change_vars l map changed, change_vars r map changed))
    | Abstr(v, r) -> ((*fprintf oc "⌛️ abstr\n";*)
                     let new_var = (Stream.next unique_name)
                     in
                      if Hashtbl.mem map v
                      then (Abstr(ret_var v map changed, change_vars r (add_el_to_hmap map v new_var) (add_el_to_hmap changed v v)))
                      else  Abstr(new_var, (change_vars r (add_el_to_hmap map v new_var) changed))
                     )
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
let rec reduction expr = (
  (* fprintf oc "🌍🌍🌍 reduction of: %s" (string_of_tree expr); *)
  match expr with
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
                else Var(vs)
              | Appl (ls,rs) -> (*printf "flag 2\n";*) Appl ((subs ls), (subs rs))
              | Abstr (vs,rs) -> (*printf "flag 3\n";*)
                if vs == var then Abstr(vs, rs)
                             else Abstr(vs, subs rs)
            in subs expr_of_abstraction;
        in substitute rr v r;
      | _ -> Appl(reduction l, reduction r)
    )
  | Abstr (ov, oe) -> VarSet.add ov var_set; Abstr(ov, reduction oe)
  ;
  (* fprintf oc "☁️☁️☁️ reduced: %s" (string_of_tree expr) *)
  )
  ;;

(* val get_original_var : string -> string *)
let rec get_original_var var =
  (* printf "flag original %s\n" var; *)
  (* print_hmap global_vars; *)
  if (String.get var 0 = '$')
  then (let loc_var = Hashtbl.find global_vars var in get_original_var loc_var)
  else var
  ;;

let new_var v = v ^ "\'";;
let check_to_replace var expr =
  let rec c_r e = match expr with
    | Var v -> if (get_original_var v = get_original_var v)
               then if v = var
                    then false
                    else true
               else false
    | Appl (l,r) -> c_r l; c_r r
    | Abstr (v,r) -> c_r r
  in c_r expr
  ;;

(* val change_vars_back : Tree.tree -> Tree.tree *)
let rec change_vars_back expr = match expr with
  | Var v -> Var(get_original_var v)
  | Appl (l,r) -> Appl((change_vars_back l), (change_vars_back r))
  | Abstr (v,r) -> Abstr(get_original_var v, (change_vars_back r))
  ;;

(* val try_to_reduce : Tree.tree -> Tree.tree *)
let rec try_to_reduce tree = (*change_vars_back *)
  (if check_redex tree
   then ((*printf "true\n";*) try_to_reduce (reduction (change_vars tree (Hashtbl.create 1000) (Hashtbl.create 1000))))
   else ((*printf "false\n";*) tree));;



(* val lines : string *)
let lines =
let init = Buffer.create 100000 in
  let rec f () =
  try
    let s = input_line stdin in
      (add_string init s; add_string init " "; f (); ())
  with e -> () in
    (f (); contents init)
  ;;

(* file input *)
<<<<<<< HEAD
(* ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce (*>> change_vars_back *)>> string_of_tree >> printf "%s\n";; *)

(* terminal input *)
lines >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce (*>> change_vars_back*) >> string_of_tree >> printf "%s\n";;
=======
(* let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> change_vars_back >> string_of_tree >> printf "%s\n";; *)

(* terminal input *)
lines >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce >> string_of_tree >> printf "%s\n";;
>>>>>>> 6707f0d19499ee525f46019f2ca74b28139239ff
