data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- Existing size-pattern admissibility applies before ordinary coverage.
fun missing : Size -> Nat { missing ($ i) = zero }
