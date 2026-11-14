data Nat : Set { zero : Nat; succ : Nat -> Nat }
data Vec (A : Set) : Nat -> Set
{ nil : Vec A zero
; cons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
}
-- The cons result index cannot unify with zero; its absence is not a hole.
fun emptyLength : Vec Nat zero -> Nat
{ emptyLength (nil .Nat) = zero }
