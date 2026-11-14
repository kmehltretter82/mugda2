import Mugda2.Experiments.QueueClient
import Mugda2.Giralf

/-! Concrete implementations discharge primitive operation contracts. Neither
the abstract client nor its proof imports this module. -/

namespace Mugda2.Experiments

open Mugda2.Giralf

def batchedQueue (E : Type u) : AmortizedQueue (BatchedQ E) E where
  toQueueModule := BatchedQ.module E
  potential := BatchedQ.phi
  potential_empty := BatchedQ.phi_empty
  enqueue_bound := by
    intro q x
    simp only [BatchedQ.module_enqueue, BatchedQ.enqueue_exact_amortized]
    omega
  dequeue_bound q := by
    dsimp only [BatchedQ.module]
    have h := BatchedQ.dequeue_bounded_amortized q
    dsimp only at h
    cases hres : (BatchedQ.dequeue q).val with
    | none => simpa only [hres] using h
    | some pair =>
      simpa only [hres] using h

def singleListQueue (E : Type u) : AmortizedQueue (List E) E where
  toQueueModule := SingleListQ.module E
  potential := fun _ => 0
  potential_empty := rfl
  enqueue_bound := by
    intro q x
    change q.length + 1 ≤ q.length + 2
    omega
  dequeue_bound := by
    intro q
    cases q
    all_goals exact Nat.le_refl 1

theorem queue_swap (xs : List E) :
    (fifoRoundtrip (batchedQueue E).toQueueModule xs).val =
      (fifoRoundtrip (singleListQueue E).toQueueModule xs).val ∧
    (fifoRoundtrip (batchedQueue E).toQueueModule xs).cost ≤ expABudget xs.length ∧
    (fifoRoundtrip (singleListQueue E).toQueueModule xs).cost ≤ expABudget xs.length :=
  let left := roundtrip_correct_and_bounded (batchedQueue E) xs
  let right := roundtrip_correct_and_bounded (singleListQueue E) xs
  ⟨left.1.trans right.1.symm, left.2, right.2⟩

end Mugda2.Experiments
