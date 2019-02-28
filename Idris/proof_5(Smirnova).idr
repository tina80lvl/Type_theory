infix 0 .:
data (.:) : Nat -> Nat -> Type where
  Divides : (n : Nat) -> (m : Nat) -> (q : Nat) -> n = q * m -> n .: m

p : (n : Nat) -> (m : Nat) -> n .: m -> n .: m
p n m (Divides n m q prf) = Divides n m q prf

t : (a = b) -> a -> b
t Refl a = a

d : {n, m, l, nm, ml : Nat} ->
  n = nm * m -> m = ml * l ->
    n = nm * (ml * l)
d {n} {nm} prfnm prfml = let k = cong {f = \x => n = nm * x} prfml
  in t k prfnm

h : {a, b, c, e : Nat} -> a = b * (c * e) -> b * (c * e) = (b * c) * e -> a = (b * c) * e
h p ass = let k = cong ass
  in t k p

f : {n, nm, m, ml, l : Nat} -> n = nm * m -> m = ml * l -> n = (nm * ml) * l
f {nm} {ml} {l} prfnm prfml = h (d prfnm prfml) (multAssociative nm ml l)

j : n .: m -> m .: l -> n .: l
j (Divides n m nm prfnm) (Divides m l ml prfml) = Divides n l (nm * ml) (f prfnm prfml)
