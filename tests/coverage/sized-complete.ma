data Nat : Set { zero : Nat; succ : Nat -> Nat }
sized data SNat : Size -> Set
{ szero : (i : Size) -> SNat ($ i)
; ssucc : (i : Size) -> SNat i -> SNat ($ i)
}
-- Dot size patterns are forced by constructor indices and do not make a
-- separate run-time case. Size arguments must not be ordinary data constructors.
fun classify : (i : Size) -> SNat i -> Nat
{ classify .($ j) (szero j) = zero
; classify .($ j) (ssucc j x) = zero
}
