data Nat : Set { zero : Nat; succ : Nat -> Nat }
sized data SNat : Size -> Set
{ szero : (i : Size) -> SNat ($ i)
; ssucc : (i : Size) -> SNat i -> SNat ($ i)
}
codata Unit : Set { unit : Unit }
cofun classify : SNat # -> Unit
{ classify (szero ($ .#)) = unit
; classify (ssucc ($ .#) x) = unit
}
