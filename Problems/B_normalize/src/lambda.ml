(* infix for ocaml :( :) *)

type Lambda =
  | FreeVar of String
  | LocVar of Int
  | Lambda  Lambda
  | Int  Lambda
  ;;

(* let toLambda :: tree -> Lambda *)
(* let toLambda tree = (* TODO *) toLambda' in
  let toLambda' lmbd = Map.Make(Int) (* TODO not clear *) in *)


(* let inToString :: Int -> String *)
let rec intToString i = match i with
  | i' when i' < 26 -> [char_of_int i]
  | _ -> char_of_int (i mod 26) : intToString (i / 26)
  in char_of_int i = char_of_int (i + int_of_char 'a') (* different *)
  ;;


let get_fv expr = match expr with
  | (lmbd1  lmbd2) -> ((++) `on` get_fv) lmbd1 lmbd2
  | (i  lmbd)      -> get_fv lmbd
  | (FreeVar name) -> [name]
  | (LocalVar i)   -> []
  ;;

let reduce lmbd = if b then reduce lmbd' else lmbd'
  in (lmbd', b) = reduce' lmbd

let rec getAcc expr = match expr with
  | (λ1 :$ λ2)     -> (max `on` getAcc) λ1 λ2
  | (i :-> λ)      -> i `max` getAcc λ
  | (LocalVar i)   -> i
  | (FreeVar name) -> 0
  ;;

(* reduce' ∷ Lambda → (Lambda, Bool) *)
let reduce' expr = match expr with
  | λ@((i :-> λ1) :$ λ2) -> res
    in
     λ1' = rename (1 + (getAcc λ1 `max` getAcc λ2)) λ1
     res = (insert λ1' (i, λ2), True)
  | λ@(λ1 :$ λ2) -> res
    in
      (λ1', b1) = reduce' λ1
      (λ2', b2) = reduce' λ2
      res = (λ1' :$ λ2', b1 || b2)
  | λ@(i :-> λ1) -> res
    in
       (λ1', b) = reduce' λ1
       res = (i :-> λ1', b)
  | λ@(LocalVar _) -> (λ, False)
  | λ@(FreeVar _)  -> (λ, False)


  (*
let getFV (λ1 :$ λ2)     = ((++) `on` getFV) λ1 λ2;;
let getFV (i :-> λ)      = getFV lmbd;;
let getFV (FreeVar name) = [name];;
let getFV (LocalVar i)   = [];; *)

(* let f x y z =
  let g x = 5 in
  let q x y z = g x in
  q x y z;

let g x = 5 *)

(* let my_show lmbd names =
  let k = foldr (max . length . takeWhile (=='z')) 0 names in
  let prefix = replicate (k+1) 'z' in
  let my_show' lmbd = match lmbd with
  | (FreeVar name) -> name
  | (LocalVar i)   -> prefix ++ intToString i
  | (λ1 :$ λ2)     -> "(" ++ my_show' λ1 ++ " " ++ my_show' λ2 ++ ")"
  | (i :-> λ)      -> "(\\" ++ prefix ++ intToString i ++ "." ++ my_show' λ ++ ")"
  in *)
