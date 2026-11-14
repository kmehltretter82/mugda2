import Mugda2.Experiments.QueueImplementations
import Mugda2.Experiments.SizedCertificates
import Mugda2.Json

/-!
Finite host-control observations for EXP-A/EXP-B. Declared abstract costs and
certificate metrics are not native timings or a winning-foundation decision.
Large repeat counters are inspected symbolically, without expanding denotation.
-/
namespace Mugda2.Experiments.Runtime

open Mugda2.Giralf
open Mugda2.Experiments.SizedCertificates

private def sameNats : List Nat → List Nat → Bool
  | [], [] => true
  | a :: restA, b :: restB => Nat.beq a b && sameNats restA restB
  | _, _ => false

private def queueObservation (n : Nat) : Json × Bool :=
  let input := List.range n
  let batched := fifoRoundtrip (batchedQueue Nat).toQueueModule input
  let single := fifoRoundtrip (singleListQueue Nat).toQueueModule input
  let budget := expABudget n
  let batchedCorrect := sameNats batched.val input
  let singleCorrect := sameNats single.val input
  let batchedWithinBudget := decide (batched.cost ≤ budget)
  let singleWithinBudget := decide (single.cost ≤ budget)
  (Json.mkObj [
    ("schemaVersion", .str "mugda2.experiments.v1"),
    ("experiment", .str "EXP-A-host-control"),
    ("evidence", .str "measured"),
    ("endpoint", .str "host-Lean-declared-abstract-steps"),
    ("inputSize", .num n),
    ("budget", .num budget),
    ("batchedCost", .num batched.cost),
    ("singleListCost", .num single.cost),
    ("batchedCorrect", .bool batchedCorrect),
    ("singleListCorrect", .bool singleCorrect),
    ("batchedWithinBudget", .bool batchedWithinBudget),
    ("singleListWithinBudget", .bool singleWithinBudget)],
    batchedCorrect && singleCorrect && batchedWithinBudget && singleWithinBudget)

private def certificateObservation (depth counter : Nat) (name : String)
    (helper : Preprocessor) : Json × Bool :=
  let source := fixture depth counter
  let result := normalize helper source
  let sourceHeight := height source
  let sourceEvents := expandedEventCount source
  let resultHeight := height result
  let resultEvents := expandedEventCount result
  let heightPreserved := decide (resultHeight ≤ sourceHeight)
  let eventsPreserved := Nat.beq resultEvents sourceEvents
  (Json.mkObj [
    ("schemaVersion", .str "mugda2.experiments.v1"),
    ("experiment", .str "EXP-B-host-control"),
    ("evidence", .str "measured"),
    ("endpoint", .str "raw-certificate-AST"),
    ("depth", .num depth),
    ("counter", .num counter),
    ("helper", .str name),
    ("sourceHeight", .num sourceHeight),
    ("sourceSyntaxNodes", .num (syntaxNodes source)),
    ("sourceCounterBits", .num (counterBitTotal source)),
    ("expandedEvents", .num sourceEvents),
    ("resultHeight", .num resultHeight),
    ("resultSyntaxNodes", .num (syntaxNodes result)),
    ("resultExpandedEvents", .num resultEvents),
    ("heightPreserved", .bool heightPreserved),
    ("eventsPreserved", .bool eventsPreserved)],
    heightPreserved && eventsPreserved)

private def queueSizes : List Nat := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256]
private def certificateDepths : List Nat := [0, 1, 2, 4, 8]
private def certificateCounters : List Nat := [0, 1, 2, 16, 256, 2^40]

def run : IO UInt32 := do
  let mut correct := true
  for n in queueSizes do
    let (row, passed) := queueObservation n
    IO.println row.compress
    correct := correct && passed
  for depth in certificateDepths do
    for counter in certificateCounters do
      for (name, helper) in [("identity", identityPreprocessor), ("neutral", neutralPreprocessor)] do
        let (row, passed) := certificateObservation depth counter name helper
        IO.println row.compress
        correct := correct && passed
  pure (if correct then 0 else 1)

end Mugda2.Experiments.Runtime

def main : IO UInt32 := Mugda2.Experiments.Runtime.run
