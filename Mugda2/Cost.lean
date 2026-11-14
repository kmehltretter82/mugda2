/-! Cost-instrumented computations shared by the queue interface and cost prototype. -/

namespace Mugda2.Giralf

/-!
## §1. The Cost-Aware Logical Framework (`Calf` Core Monad & Phase Distinction)

In *Calf* (Niu, Sterling, Grodin & Harper, POPL 2022) and *Potential Functions as Types*
(Grodin, Chu, Li, Hoffmann & Harper, 2026), computations are equipped with a quantitative
cost effect (`step c`) alongside a phase distinction (`extEq`) that erases cost in the
behavioral/extensional phase.
-/

/-- Cost-instrumented computation monad tracking a pure result `val : A` and exact
    abstract step count `cost : Nat`. -/
structure CostM (A : Type u) where
  val  : A
  cost : Nat
  deriving Repr, DecidableEq

namespace CostM

/-- Return a value with zero cost. -/
def ret (x : A) : CostM A := ⟨x, 0⟩

/-- Record `c` units of abstract operational cost while returning `x`. -/
def step (c : Nat) (x : A) : CostM A := ⟨x, c⟩

/-- Sequential composition of cost-instrumented computations; costs add. -/
def bind (m : CostM A) (k : A → CostM B) : CostM B :=
  let r := k m.val
  ⟨r.val, m.cost + r.cost⟩

instance : Monad CostM where
  pure := ret
  bind := bind

/-- Extensional (behavioral-phase) equivalence: ignores `cost` and compares only `val`.
    Corresponds to the open/behavioral modality `◯` in Calf. -/
def extEq (m₁ m₂ : CostM A) : Prop :=
  m₁.val = m₂.val

/-- Quantitative refinement (`Decalf` / `Calf` cost ordering): same behavioral result,
    and `m₁` costs at most `m₂`. -/
def refines (m₁ m₂ : CostM A) : Prop :=
  m₁.val = m₂.val ∧ m₁.cost ≤ m₂.cost

@[simp] theorem ret_val (x : A) : (ret x).val = x := rfl
@[simp] theorem ret_cost (x : A) : (ret x).cost = 0 := rfl
@[simp] theorem step_val (c : Nat) (x : A) : (step c x).val = x := rfl
@[simp] theorem step_cost (c : Nat) (x : A) : (step c x).cost = c := rfl
@[simp] theorem bind_val (m : CostM A) (k : A → CostM B) :
    (bind m k).val = (k m.val).val := rfl
@[simp] theorem bind_cost (m : CostM A) (k : A → CostM B) :
    (bind m k).cost = m.cost + (k m.val).cost := rfl

/-- Left identity law for `CostM`. -/
theorem bind_ret_left (x : A) (k : A → CostM B) :
    bind (ret x) k = k x := by
  unfold bind ret
  cases k x
  simp [Nat.zero_add]

/-- Right identity law for `CostM`. -/
theorem bind_ret_right (m : CostM A) :
    bind m ret = m := by
  cases m
  rfl

/-- Associativity law for `CostM`. -/
theorem bind_assoc (m : CostM A) (f : A → CostM B) (g : B → CostM C) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  cases m with
  | mk v c =>
    simp [bind, Nat.add_assoc]

/-- `step` composition law: stepping by `c₁` then `c₂` equals stepping by `c₁ + c₂`. -/
theorem step_add (c₁ c₂ : Nat) (x : A) :
    bind (step c₁ x) (fun y => step c₂ y) = step (c₁ + c₂) x := rfl

/-- **Behavioral Noninterference (Phase Distinction):**
    In the behavioral phase (`extEq`), charging `c` steps is invisible. -/
theorem step_extEq_ret (c : Nat) (x : A) :
    extEq (step c x) (ret x) := rfl

/-- Quantitative refinement is reflexive. -/
theorem refines_refl (m : CostM A) : refines m m :=
  ⟨rfl, Nat.le_refl _⟩

/-- Quantitative refinement is transitive. -/
theorem refines_trans {m₁ m₂ m₃ : CostM A}
    (h₁₂ : refines m₁ m₂) (h₂₃ : refines m₂ m₃) : refines m₁ m₃ :=
  ⟨Eq.trans h₁₂.1 h₂₃.1, Nat.le_trans h₁₂.2 h₂₃.2⟩

/-- Monotonicity of `bind` with respect to quantitative refinement. -/
theorem bind_refines {m₁ m₂ : CostM A} {k₁ k₂ : A → CostM B}
    (hm : refines m₁ m₂)
    (hk : ∀ x, refines (k₁ x) (k₂ x)) :
    refines (bind m₁ k₁) (bind m₂ k₂) := by
  rcases hm with ⟨hval, hcost⟩
  have hk_m := hk m₂.val
  refine ⟨?_, ?_⟩
  · rw [bind_val, bind_val, hval, hk_m.1]
  · rw [bind_cost, bind_cost, hval]
    exact Nat.add_le_add hcost hk_m.2

end CostM

end Mugda2.Giralf
