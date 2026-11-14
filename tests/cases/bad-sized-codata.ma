-- A sized coinductive constructor must target its bound, not fixed infinity.
sized codata BadCo : Size -> Set
{ nil : BadCo # }
