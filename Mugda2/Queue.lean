import Mugda2.Cost

/-! Abstract FIFO operations and representation-independent clients.
This module imports no concrete queue implementation. -/

namespace Mugda2.Giralf

/-- Specification predicate for `dequeue` return value vs. `contents`. -/
def DequeueResultSpec (contents : Q → List E) (q : Q) : Option (E × Q) → Prop
  | none         => contents q = []
  | some (x, q') => contents q = x :: contents q'

/-- Abstract modular FIFO Queue interface (`QueueModule Q E`) with an abstraction map
    `contents : Q → List E` and cost-instrumented `enqueue` and `dequeue`. -/
structure QueueModule (Q : Type u) (E : Type u) where
  empty            : Q
  enqueue          : Q → E → CostM Q
  dequeue          : Q → CostM (Option (E × Q))
  contents         : Q → List E
  contents_empty   : contents empty = []
  contents_enqueue : ∀ q x, contents (enqueue q x).val = contents q ++ [x]
  contents_dequeue : ∀ q, DequeueResultSpec contents q (dequeue q).val

/-- Generic client helper: enqueue every element of `xs` into queue `q` using module `M`. -/
def enqueueAll (M : QueueModule Q E) : Q → List E → CostM Q
  | q, []      => CostM.ret q
  | q, x :: xs => do
      let q' ← M.enqueue q x
      enqueueAll M q' xs

/-- Generic client helper: dequeue `k` elements from queue `q` using module `M`. -/
def dequeueN (M : QueueModule Q E) : Nat → Q → CostM (List E × Q)
  | 0,     q => CostM.ret ([], q)
  | k + 1, q => do
      let res ← M.dequeue q
      match res with
      | none         => CostM.ret ([], q)
      | some (x, q') => do
          let (ys, qFinal) ← dequeueN M k q'
          CostM.ret (x :: ys, qFinal)

/-- **The Shared `EXP-A` Client (`fifoRoundtrip`):**
    Enqueues all elements of `xs` into `M.empty` and then dequeues `xs.length` elements. -/
def fifoRoundtrip (M : QueueModule Q E) (xs : List E) : CostM (List E) := do
  let q ← enqueueAll M M.empty xs
  let (ys, _) ← dequeueN M xs.length q
  CostM.ret ys

/-- Behavioral lemma 1: `enqueueAll` appends `xs` to `M.contents q`, for *any* `QueueModule`. -/
theorem contents_enqueueAll (M : QueueModule Q E) (q : Q) (xs : List E) :
    M.contents (enqueueAll M q xs).val = M.contents q ++ xs := by
  induction xs generalizing q with
  | nil =>
    simp [enqueueAll, CostM.ret_val]
  | cons x xs ih =>
    simp only [enqueueAll, bind, CostM.bind_val]
    rw [ih, M.contents_enqueue, List.append_assoc, List.singleton_append]

/-- Behavioral lemma 2: `dequeueN` extracts the exact prefix of length `k` when
    `M.contents q = pref ++ suff` with `pref.length = k`, for *any* `QueueModule`. -/
theorem dequeueN_prefix (M : QueueModule Q E) (pref suff : List E) (q : Q)
    (hq : M.contents q = pref ++ suff) :
    (dequeueN M pref.length q).val.1 = pref ∧
    M.contents (dequeueN M pref.length q).val.2 = suff := by
  induction pref generalizing q with
  | nil =>
    simpa [dequeueN, CostM.ret_val] using hq
  | cons x xs ih =>
    simp only [List.length_cons, dequeueN, bind, CostM.bind_val]
    have hdeq := M.contents_dequeue q
    cases hres : (M.dequeue q).val with
    | none =>
      rw [hres] at hdeq
      dsimp only [DequeueResultSpec] at hdeq
      rw [hq] at hdeq
      contradiction
    | some pair =>
      rcases pair with ⟨y, q'⟩
      rw [hres] at hdeq
      dsimp only [DequeueResultSpec] at hdeq
      rw [hq, List.cons_append] at hdeq
      injection hdeq with hxy hrest
      subst hxy
      have ⟨ih₁, ih₂⟩ := ih q' hrest.symm
      simp [CostM.ret_val, ih₁, ih₂]

/-- **Theorem 5D — Modular Behavioral Correctness (`EXP-A` Behavioral Noninterference):**
    For *every* implementation `M : QueueModule Q E`, the client `fifoRoundtrip M xs`
    returns `xs` in exact FIFO order (`(fifoRoundtrip M xs).val = xs`), without inspecting
    `M`'s private representation! -/
theorem fifoRoundtrip_correct (M : QueueModule Q E) (xs : List E) :
    (fifoRoundtrip M xs).val = xs := by
  simp only [fifoRoundtrip, bind, CostM.bind_val, CostM.ret_val]
  have henq := contents_enqueueAll M M.empty xs
  rw [M.contents_empty, List.nil_append] at henq
  have hdeq := dequeueN_prefix M xs [] (enqueueAll M M.empty xs).val (by simpa using henq)
  exact hdeq.1

/-- Common `EXP-A` quadratic budget `B n = n * (n + 3)` covering both implementations. -/
def expABudget (n : Nat) : Nat := n * (n + 3)

end Mugda2.Giralf
