-- Negative occurrence of Bad in the constructor's argument type.
data Bad : Set
{ wrap : (Bad -> Bad) -> Bad }
