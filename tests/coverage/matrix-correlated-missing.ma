data Bool : Set { tt : Bool; ff : Bool }
-- Every column mentions every constructor; (tt, ff) and (ff, tt) are absent.
fun diagonal : Bool -> Bool -> Bool
{ diagonal tt tt = tt
; diagonal ff ff = ff
}
