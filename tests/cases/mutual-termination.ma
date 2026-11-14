data Nat : Set
{ zero : Nat }

mutual
{
  fun good : Nat -> Nat
  { good x = x }

  fun loop : Nat -> Nat
  { loop x = loop x }
}

-- Whole-document rejection prevents using good after the failed mutual block.
let useGood : Nat = good zero
