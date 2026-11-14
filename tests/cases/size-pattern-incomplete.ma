-- A bare successor size pattern is incomplete at the infinity size.
fun foo : Size -> Set
{ foo ($ i) = foo i }
