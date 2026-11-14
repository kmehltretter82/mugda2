data Bool : Set { tt : Bool; ff : Bool }
data Eq (A : Set) (x : A) : A -> Set { refl : Eq A x x }
-- Overlap is permitted; source order determines evaluation.
fun choose : Bool -> Bool
{ choose b = tt
; choose ff = ff
}
let first : Eq Bool (choose ff) tt = refl Bool tt
