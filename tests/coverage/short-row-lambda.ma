data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- Clause arity may be shorter than the Pi telescope: a checked RHS handles
-- remaining arguments. Coverage may pad this row with wildcards.
fun constant : Nat -> Nat -> Nat { constant x = \y -> x }
let use : Nat = constant zero (succ zero)
