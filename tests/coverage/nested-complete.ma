data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun classify : Nat -> Nat
{ classify zero = zero
; classify (succ zero) = zero
; classify (succ (succ n)) = n
}
