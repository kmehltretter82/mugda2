-- UTF-8 span check: λ 🌱
data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

fun copy : Nat -> Nat
{ copy zero = zero
; copy (succ n) = succ (copy n)
}
