data Nat : Set
{ zero : Nat }

mutual
{
  fun good : Nat -> Nat
  { good x = x }

  fun bad : Nat -> Nat
  { bad x = Size }
}
