import Mugda2.Legacy.Core

/-!
A finite JSON encoder for result records. Object fields are lists: this avoids
the classical dependencies in the pinned Lean JSON type's ordered-map metadata.
Strings retain Unicode and escape every JSON control character.
-/
namespace Mugda2

inductive Json where
  | null
  | bool (value : Bool)
  | num (value : Nat)
  | str (value : String)
  | arr (values : List Json)
  | obj (fields : List (String × Json))

class ToJson (α : Type) where
  encode : α → Json

def encodeJson [ToJson α] (value : α) : Json := ToJson.encode value

instance : ToJson Nat := ⟨Json.num⟩
instance : ToJson String := ⟨Json.str⟩
instance : ToJson Bool := ⟨Json.bool⟩
instance [ToJson α] : ToJson (List α) := ⟨fun values => .arr (values.map encodeJson)⟩
instance [ToJson α] : ToJson (Option α) :=
  ⟨fun value => match value with | none => .null | some value => encodeJson value⟩

namespace Json

def mkObj : List (String × Json) → Json := .obj

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 97 + (n - 10))

private def escapeChar (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

private def escapeChars : List Char → List Char
  | [] => []
  | c :: rest => escapeChar c ++ escapeChars rest

def quote (value : String) : String :=
  "\"" ++ String.ofList (escapeChars (MugdaCore.sourceChars value)) ++ "\""

mutual
  def compress : Json → String
    | .null => "null"
    | .bool true => "true"
    | .bool false => "false"
    | .num value => toString value
    | .str value => quote value
    | .arr values => "[" ++ compressValues values ++ "]"
    | .obj fields => "{" ++ compressFields fields ++ "}"

  private def compressValues : List Json → String
    | [] => ""
    | [value] => compress value
    | value :: rest => compress value ++ "," ++ compressValues rest

  private def compressFields : List (String × Json) → String
    | [] => ""
    | [(key, value)] => quote key ++ ":" ++ compress value
    | (key, value) :: rest => quote key ++ ":" ++ compress value ++ "," ++ compressFields rest
end

end Json
end Mugda2
