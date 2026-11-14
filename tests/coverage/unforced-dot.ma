data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- A dot cannot be used to claim an arbitrary input is definitionally zero.
fun invalid : Nat -> Nat { invalid .zero = zero }
