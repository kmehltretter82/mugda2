data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun value : Nat { value = zero }
let witness : Nat = value
