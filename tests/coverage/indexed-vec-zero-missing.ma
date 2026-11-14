data Nat : Set { zero : Nat; succ : Nat -> Nat }
data Vec (A : Set) : Nat -> Set
{ nil : Vec A zero
; cons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
}
-- nil Nat is a genuine missing input, not an impossible indexed branch.
fun missing : Vec Nat zero -> Nat {}
