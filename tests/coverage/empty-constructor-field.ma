data Empty : Set {}
data Box : Set { box : Empty -> Box }
data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- Declaring a constructor does not establish that its arguments are inhabited.
fun eliminate : Box -> Nat {}
