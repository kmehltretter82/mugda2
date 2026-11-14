data Bool : Set { tt : Bool; ff : Bool }
data Unit : Set { unit : Unit }
data Empty : Set {}
fun F : Bool -> Set { F tt = Empty; F b = Unit }
-- Coverage must not justify falling through a stuck earlier constructor row.
fun bad : (b : Bool) -> F b { bad b = unit }
let contradiction : Empty = bad tt
