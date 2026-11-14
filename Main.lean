import Mugda2
import Mugda2.Checker

open Mugda2.Giralf

/-- Executable demonstration of the constructive Lean 4 cost prototype
    and the EXP-A two-list vs. single-list queue benchmark. -/
def runDemo : IO UInt32 := do
  IO.println "=== Mugda2: Constructive Lean 4 Cost Prototype / EXP-A Preparation ==="
  let input := [10, 20, 30, 40, 50]
  let rBatched := fifoRoundtrip (BatchedQ.module Nat) input
  let rSingle  := fifoRoundtrip (SingleListQ.module Nat) input
  IO.println s!"Input list (n = {input.length}):                 {repr input}"
  IO.println s!"BatchedQueue roundtrip output:          {repr rBatched.val} (actual cost = {rBatched.cost} steps, linear bound 3n = {3 * input.length})"
  IO.println s!"SingleListQueue roundtrip output:       {repr rSingle.val} (actual cost = {rSingle.cost} steps, budget B(n) = {expABudget input.length})"
  pure 0

private def usage : String :=
  "Usage: mugda2 [demo]\n" ++
  "       mugda2 check [--fuel N] [--comparison-fuel N] [--closure-fuel N] " ++
  "[--lex-fuel N] [--parse-fuel N] file.ma\n" ++
  "Check prints one JSON result; exit codes: 0 accepted, 1 rejected, 2 unknown, 64 usage, 74 I/O."

private def naturalArgument (value : String) : Option Nat :=
  let bytes := value.toByteArray.toList
  if bytes.isEmpty then none
  else bytes.foldlM (fun n byte =>
    if 48 ≤ byte.toNat && byte.toNat ≤ 57 then some (10 * n + byte.toNat - 48)
    else none) 0

private def isOption (value : String) : Bool :=
  match value.toByteArray.toList with
  | first :: second :: _ => Nat.beq first.toNat 45 && Nat.beq second.toNat 45
  | _ => false

private def parseCheckArgs : List String → Mugda2.Budget → Except String (Mugda2.Budget × String)
  | [path], budget =>
      if isOption path then .error "Missing source file" else .ok (budget, path)
  | flag :: value :: rest, budget => do
      let fuel ← match naturalArgument value with
        | some fuel => .ok fuel
        | none => .error ("Expected a nonnegative integer after " ++ flag)
      let budget ← match flag with
        | "--fuel" => .ok { budget with checkerFuel := fuel }
        | "--comparison-fuel" => .ok { budget with comparisonFuel := fuel }
        | "--closure-fuel" => .ok { budget with closureFuel := fuel }
        | "--lex-fuel" => .ok { budget with lexerFuel := some fuel }
        | "--parse-fuel" => .ok { budget with parserFuel := some fuel }
        | _ => .error ("Unknown option: " ++ flag)
      parseCheckArgs rest budget
  | _, _ => .error "Expected options followed by one source file"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["demo"] => runDemo
  | "check" :: rest =>
      match parseCheckArgs rest {} with
      | .error error =>
          IO.eprintln (error ++ "\n" ++ usage)
          pure 64
      | .ok (budget, path) =>
          try
            let bytes ← IO.FS.readBinFile path
            match MugdaCore.decodeSourceBytes bytes.toList [] with
            | none =>
                IO.eprintln ("Invalid UTF-8 source: " ++ path)
                pure 74
            | some chars =>
                let result := Mugda2.checkSource (String.ofList chars) budget
                IO.println ((Mugda2.resultJson path budget result).compress)
                pure result.exitCode
          catch _ =>
            IO.eprintln ("Cannot read file: " ++ path)
            pure 74
  | ["--help"] | ["-h"] =>
      IO.println usage
      pure 0
  | _ =>
      IO.eprintln usage
      pure 64
