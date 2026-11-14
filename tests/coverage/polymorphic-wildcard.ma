-- Opaque type columns covered by variables require no constructor enumeration.
fun identity : (A : Set) -> A -> A { identity A x = x }
