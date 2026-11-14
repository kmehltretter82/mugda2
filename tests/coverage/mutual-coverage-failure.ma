data Bool : Set { tt : Bool; ff : Bool }
let previous : Bool = tt
mutual
{
  fun good : Bool -> Bool { good b = b }
  fun missing : Bool -> Bool { missing tt = good tt }
}
