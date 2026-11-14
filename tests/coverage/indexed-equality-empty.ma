data Nat : Set { zero : Nat; succ : Nat -> Nat }
data Empty : Set {}
data Eq (A : Set) (x : A) : A -> Set { refl : Eq A x x }
-- The sole constructor cannot inhabit these different constructor indices.
fun noConfusion : Eq Nat zero (succ zero) -> Empty {}
