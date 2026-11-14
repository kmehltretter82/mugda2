data Nat : Set { zero : Nat; succ : Nat -> Nat }
sized data SNat : Size -> Set
{ szero : (i : Size) -> SNat ($ i)
; ssucc : (i : Size) -> SNat i -> SNat ($ i)
}
fun missing : (i : Size) -> SNat i -> Nat
{ missing .($ j) (szero j) = zero }
