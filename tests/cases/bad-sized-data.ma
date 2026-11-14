-- A sized inductive constructor must target a successor bound.
sized data BadList : Size -> Set
{ nil : (i : Size) -> BadList i }
