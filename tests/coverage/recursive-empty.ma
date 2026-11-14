data Void : Set { roll : Void -> Void }
data Nat : Set { zero : Nat; succ : Nat -> Nat }
-- Void has no finite inductive values. A finite search that cannot establish
-- this must return unknown, never manufacture roll (...) as a closed witness.
fun eliminate : Void -> Nat {}
