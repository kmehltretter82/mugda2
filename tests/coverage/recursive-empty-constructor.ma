data Void : Set { roll : Void -> Void }
data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- This pattern is structurally exhaustive without proving Void inhabited.
fun eliminate : Void -> Nat { eliminate (roll x) = zero }
