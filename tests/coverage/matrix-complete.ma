data Bool : Set { tt : Bool; ff : Bool }
fun conjunction : Bool -> Bool -> Bool
{ conjunction tt b = b
; conjunction ff tt = ff
; conjunction ff ff = ff
}
