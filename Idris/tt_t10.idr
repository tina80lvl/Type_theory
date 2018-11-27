------ HW 10 ------

----1
--(a) x = y -> y = x
symmetry : {x : Nat} -> {y : Nat} -> x = y -> y = x
symmetry Refl = Refl

--(b) x = y -> y = z -> x = z
transition : x = y -> y = z -> x = z
transition Refl Refl = Refl

--(c) (P: A->B) -> x = y -> P x = P y
congruence : (P : a->b) -> x = y -> P x = P y
congruence f Refl = Refl

----2
--(a) x = x + 0
addingz : (x : Nat) -> x = x + 0
-- 0 = 0 + 0
addingz Z = Refl
-- (S k) = (S k) + 0 = S (k + 0)
-- rec : k = k + 0
-- cong S rec : S k = S (k + 0)
addingz (S k) = let rec = addingz k in
                 congruence S rec

-- --(b) S x = 1 + x
-- hetchl : (x : Nat) -> S x = 1 + x
-- hetchl Z = Refl
-- hetchl (S k) =
--
-- --(c) S x = x + 1
-- hetchr : (x : Nat) -> S x = x + 1
-- hetchr Z = Refl
-- hetchr (S k) =
--
-- --(d) S x + S x = S (S (x + x))
-- succsame : (x : Nat) ->
-- succsame Z = Refl
-- succsame (S k) =
--
-- --(e) S x + S y = S (S (x + y))
-- succdiff : (x : Nat) ->
-- succdiff Z = Refl
-- succdiff (S k) =
--
-- --(f) S (x + y) = x + (S y)
-- hetch : (x : Nat) ->
-- hetch Z = Refl
-- hetch (S k) =
--
-- --(g) x + y = y + x
-- hetch : (x : Nat) ->
-- hetch Z = Refl
-- hetch (S k) =
--
-- --(h) x + (y + z) = (x + y) + z
-- hetch : (x : Nat) ->
-- hetch Z = Refl
-- hetch (S k) =
