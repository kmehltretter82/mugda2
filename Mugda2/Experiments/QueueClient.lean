import Mugda2.Experiments.QueueContract

/-! Representation-independent client cost derivation. Its import closure has
only the cost monad, the abstract queue, and per-operation contracts. -/

namespace Mugda2.Experiments

open Mugda2.Giralf

theorem enqueueAll_amortized (M : AmortizedQueue Q E) (q : Q) (xs : List E) :
    (enqueueAll M.toQueueModule q xs).cost +
        M.potential (enqueueAll M.toQueueModule q xs).val ≤
      xs.length * ((M.contents q).length + xs.length + 1) + M.potential q := by
  induction xs generalizing q with
  | nil => simp only [enqueueAll, CostM.ret_cost, CostM.ret_val, List.length_nil,
      Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | cons x xs ih =>
    simp only [enqueueAll, bind, CostM.bind_cost, CostM.bind_val]
    have hrest := ih (M.enqueue q x).val
    have hstep := M.enqueue_bound q x
    simp only [M.contents_enqueue, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] at hrest ⊢
    rw [Nat.add_mul, Nat.one_mul]
    simp only [Nat.mul_add, Nat.mul_one] at hrest ⊢
    omega

theorem dequeueN_amortized (M : AmortizedQueue Q E) (k : Nat) (q : Q) :
    (dequeueN M.toQueueModule k q).cost +
        M.potential (dequeueN M.toQueueModule k q).val.2 ≤ k + M.potential q := by
  induction k generalizing q with
  | zero => simp only [dequeueN, CostM.ret_cost, CostM.ret_val, Nat.zero_add, Nat.le_refl]
  | succ k ih =>
    simp only [dequeueN, bind, CostM.bind_cost, CostM.bind_val]
    have hstep := M.dequeue_bound q
    cases hdeq : (M.dequeue q).val with
    | none =>
      simp only [hdeq, CostM.ret_cost, CostM.ret_val, Nat.add_zero] at hstep ⊢
      omega
    | some pair =>
      rcases pair with ⟨x, q'⟩
      simp only [hdeq, CostM.bind_cost, CostM.bind_val, CostM.ret_cost,
        CostM.ret_val, Nat.add_zero] at hstep ⊢
      have hrest := ih q'
      omega

theorem roundtrip_cost_le (M : AmortizedQueue Q E) (xs : List E) :
    (fifoRoundtrip M.toQueueModule xs).cost ≤ expABudget xs.length := by
  simp only [fifoRoundtrip, bind, CostM.bind_cost, CostM.ret_cost, Nat.add_zero]
  have henq := enqueueAll_amortized M M.empty xs
  have hdeq := dequeueN_amortized M xs.length (enqueueAll M.toQueueModule M.empty xs).val
  simp only [M.contents_empty, List.length_nil, Nat.zero_add, M.potential_empty, Nat.add_zero] at henq
  have hbudget : xs.length * (xs.length + 1) + xs.length ≤ expABudget xs.length := by
    simp only [expABudget, Nat.mul_succ]
    omega
  omega

theorem roundtrip_correct_and_bounded (M : AmortizedQueue Q E) (xs : List E) :
    (fifoRoundtrip M.toQueueModule xs).val = xs ∧
      (fifoRoundtrip M.toQueueModule xs).cost ≤ expABudget xs.length :=
  ⟨fifoRoundtrip_correct M.toQueueModule xs, roundtrip_cost_le M xs⟩

end Mugda2.Experiments
