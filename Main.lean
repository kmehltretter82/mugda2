import Mugda2

open Mugda2.Giralf

/-- Executable demonstration of the Constructive Lean 4 Giralf / Calf formalization
    and the EXP-A two-list vs. single-list queue benchmark. -/
def main : IO UInt32 := do
  IO.println "=== Mugda2: Constructive Lean 4 Formalization of Giralf (Potential Functions as Types) ==="
  let input := [10, 20, 30, 40, 50]
  let rBatched := fifoRoundtrip (BatchedQ.module Nat) input
  let rSingle  := fifoRoundtrip (SingleListQ.module Nat) input
  IO.println s!"Input list (n = {input.length}):                 {repr input}"
  IO.println s!"BatchedQueue roundtrip output:          {repr rBatched.val} (actual cost = {rBatched.cost} steps, linear bound 3n = {3 * input.length})"
  IO.println s!"SingleListQueue roundtrip output:       {repr rSingle.val} (actual cost = {rSingle.cost} steps, budget B(n) = {expABudget input.length})"
  pure 0
