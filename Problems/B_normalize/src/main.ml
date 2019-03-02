open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;

(* let (ic,oc) = (open_in "input.txt", open_out "output.txt");; *)
(* let print_pair_hmap hm = Hashtbl.iter (fun (a,b) y -> fprintf oc "(%s, %d) %s\n" a b y) hm;; *)

let unique_name = Stream.from (fun i -> Some (string_of_int i));;
let string_of_tree tree =
  let buf = Buffer.create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Appl (l,r) -> add_string buf "("; s_t l; add_string buf " "; s_t r; add_string buf ")"
    | Abstr (v,r) -> add_string buf "(\\"; add_string buf v; add_string buf "."; s_t r; add_string buf ")"
  in s_t tree;
  contents buf;;

let changed_vars = Hashtbl.create 100000;;

let add_pair_to_hmap l r v =
  (*fprintf oc "add: (%s %d), %s\n" l r v; *)
  Hashtbl.add changed_vars (l,r) v;;

let ret_var v cnt =
  if Hashtbl.mem changed_vars (v,cnt)
  then Hashtbl.find changed_vars (v,cnt)
  else
    let n_v = (String.make 1 (String.get v 0)) ^ (Stream.next unique_name)
    in
      (* fprintf oc "⚽️\n"; *)
      add_pair_to_hmap v cnt n_v;
      n_v
  ;;

let last_cnt v cnt =
  let rec l_c c = (
    (* fprintf oc "looking for: %s %d\nin \n" v c; print_pair_hmap changed_vars; *)
    if (Hashtbl.mem changed_vars (v,c))
    then c
    else (if (c > 0) then l_c (c - 1) else -1))
  in l_c cnt
  ;;

let rec change_vars expr cnt =
  (* fprintf oc "🍇lvl: %d\n⚡️⚡️⚡️ expr: %s\n🧨 changed:\n" cnt (string_of_tree expr); print_pair_hmap changed_vars; (* DEBUG *) *)
  (match expr with
    | Var v -> (
      (* fprintf oc "⌛️ var: %s\n" v; (* DEBUG *) *)
      let n_c = last_cnt v cnt
      in (
        (* fprintf oc "🚌 %d\n" n_c; *)
        if (n_c > -1)
        then Var(ret_var v n_c)
        else (add_pair_to_hmap v cnt v; Var(v))
         )
      )
    | Appl(l, r) -> (
      (* fprintf oc "⌛️ appl\n";  *)
      (* let lft = change_vars l cnt
      in
        let rht = change_vars r cnt
        in Appl(lft, rht) *)
        Appl(change_vars l cnt, change_vars r cnt)
      )
    | Abstr(v, r) -> (
      (* fprintf oc "⌛️ abstr\n"; (* DEBUG *) *)
      let vr = ret_var v (cnt + 1)
        in let tmp = (Abstr(vr, change_vars r (cnt + 1)))
            in Hashtbl.remove changed_vars (v, cnt + 1); tmp;
      )
  )
  ;;

let rec check_redex tree =
 (* printf "checking redex = %s\n" (string_of_tree tree); *)
  match tree with
  | Var v -> false
  | Appl (l, r) -> (match l with
                    | Abstr (v1, r1) -> true
                    | _ -> (check_redex l || check_redex r))
  | Abstr (v, r) -> check_redex r
  ;;

let rec reduction expr = (
  (* print_pair_hmap changed_vars; *)
  (* fprintf oc "🌍🌍🌍 reduction of: %s\n" (string_of_tree expr); *)
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
                | Appl (ls,rs) -> (*printf "flag 2\n";*)
                  let l_a = (subs ls)
                  in let r_a = (subs rs)
                      in Appl (l_a, r_a)
                | Abstr (vs,rs) -> (*printf "flag 3\n";*)
                  if vs == var then Abstr(vs, rs)
                               else Abstr(vs, subs rs)
            in subs expr_of_abstraction;
        in substitute rr v r;
      | _ -> let l_a = (reduction l)
               in let r_a = (reduction r)
                    in Appl (l_a, r_a)
    )
  | Abstr (ov, oe) -> Abstr(ov, reduction oe)
  ;
  )
  ;;

let rec try_to_reduce tree = (*change_vars_back *)
(* fprintf oc "🎀 reduction of: %s\n" (string_of_tree tree); *)
  (if check_redex tree
   then ((*printf "true\n";*) try_to_reduce (reduction (change_vars tree 0)))
   else ((*printf "false\n";*) tree));;

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
lines >> Lexing.from_string >> Parser.main Lexer.main >> try_to_reduce (*>> change_vars_back*) >> string_of_tree >> printf "%s\n";;
