data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun predecessor : Nat -> Nat
{ predecessor zero = zero
; predecessor (succ n) = n
}
