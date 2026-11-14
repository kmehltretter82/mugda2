data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun missing : Nat -> Nat { missing zero = zero }
