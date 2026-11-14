-- Positive sized counterpart to the unsupported descent in legacy badterm2.ma.
-- This is the finite source fixture already retained in Legacy/Fixtures.lean.
sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ sub .($ i) (zero i) j y = zero i
; sub i x .($ j) (zero j) = x
; sub .($ i) (succ i x) .($ j) (succ j y) = sub ($ i) x j y
}

fun div : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ div .($ i) (zero i) j y = zero i
; div .($ i) (succ i x) j y = succ i (div i (sub i x j y) j y)
}
