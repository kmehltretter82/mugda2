data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- Both top-level constructors occur; succ (succ zero) is still missing.
fun missing : Nat -> Nat
{ missing zero = zero
; missing (succ zero) = zero
}
