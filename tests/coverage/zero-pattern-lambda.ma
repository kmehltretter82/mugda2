data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun identity : Nat -> Nat { identity = \x -> x }
let use : Nat = identity zero
