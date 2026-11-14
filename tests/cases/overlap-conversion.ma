-- Neutral arguments must block an earlier constructor clause rather than
-- falling through to the catch-all branch during dependent conversion.
data Bool : Set
{ tt : Bool; ff : Bool }
data Unit : Set
{ unit : Unit }
data Empty : Set {}

fun F : Bool -> Set
{ F tt = Empty
; F b = Unit
}

fun bad : (b : Bool) -> F b
{ bad b = unit }

let contradiction : Empty = bad tt
