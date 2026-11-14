data Empty : Set {}
data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun eliminate : Empty -> Nat {}
