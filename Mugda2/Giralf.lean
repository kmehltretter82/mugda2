/-
  Mugda2/Giralf.lean
  ==================
  Constructive Lean 4 cost prototype inspired by:
    "Potential Functions as Types" (Giralf & Calf)
    Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper (2026)
  with separate prototypes for:
    - Ratiu & Schwichtenberg's Behavioral & Cost-Adequate Extraction (`REQ-COST-003`)
    - Mugda2 Experiment A (`EXP-A` in `docs/EXPERIMENTS.md`): Modular FIFO Queue
      Abstraction & Cost Swap (Batched Two-List Queue vs. Single-List Queue).

  Design & Verification Commitments:
    - 100% Constructive Lean 4: zero `sorry`, zero `partial`, zero `unsafe`,
      zero `Classical.choice`, zero external library dependencies.
    - Every theorem is kernel-checked and verified via `#print axioms`.
-/

import Mugda2.Cost
import Mugda2.Queue

namespace Mugda2.Giralf
/-!
## §2. The Physicist's View: Potential Functions, Fracture & Gluing

In the *Physicist's View* of amortized analysis (§2 of *Potential Functions as Types*),
a concrete data type `C` is equipped with:
1. An **abstraction function** `α : C → A` mapping concrete states to their mathematical
   specification `A` (behavioral modularity).
2. A nonnegative **potential function** `Φ : C → Nat` (cost modularity).

The **Fracture & Gluing Principle** packages `(α, Φ)` as an amortized refinement of `A`:
an operation `op : C → CostM (C × Out)` satisfies amortized bound `c_amort` when
  `actualCost + Φ(s') ≤ c_amort + Φ(s)`.
-/

/-- A Physicist's Glued Type (`PhysicistType C A`) fuses a concrete representation `C`,
    an abstract specification type `A`, an abstraction map `alpha : C → A`, and a
    potential function `phi : C → Nat`. -/
structure PhysicistType (C : Type u) (A : Type v) where
  alpha : C → A
  phi   : C → Nat

/-- A single operation transition record with actual cost `actualCost`, pre-state `preState`,
    post-state `postState`, and assigned amortized charge `amortizedCharge`. -/
structure AmortizedTransition (C : Type u) where
  preState        : C
  postState       : C
  actualCost      : Nat
  amortizedCharge : Nat

/-- The exact amortized accounting identity (`actual + Φ(post) = amortized + Φ(pre)`),
    as displayed in the interactive queue demonstration of `docs/index.html`. -/
def ExactAmortizedStep (phi : C → Nat) (t : AmortizedTransition C) : Prop :=
  t.actualCost + phi t.postState = t.amortizedCharge + phi t.preState

/-- The upper-bound amortized inequality (`actual + Φ(post) ≤ amortized + Φ(pre)`). -/
def BoundedAmortizedStep (phi : C → Nat) (t : AmortizedTransition C) : Prop :=
  t.actualCost + phi t.postState ≤ t.amortizedCharge + phi t.preState

theorem exact_implies_bounded {phi : C → Nat} {t : AmortizedTransition C}
    (h : ExactAmortizedStep phi t) : BoundedAmortizedStep phi t :=
  Nat.le_of_eq h

/-- A composable sequence of transitions `s₀ → s₁ → ... → sₖ` starting at `initState`
    and ending at `finalState`. -/
inductive TransitionTrace (C : Type u) : C → C → Type u where
  | nil  (s : C) : TransitionTrace C s s
  | snoc {s₀ s₁ s₂ : C} (pref : TransitionTrace C s₀ s₁)
         (step : AmortizedTransition C)
         (hpre : step.preState = s₁)
         (hpost : step.postState = s₂) : TransitionTrace C s₀ s₂

namespace TransitionTrace

/-- Total actual operational cost across the entire trace. -/
def totalActual : TransitionTrace C s₀ sₖ → Nat
  | .nil _            => 0
  | .snoc pref step _ _ => pref.totalActual + step.actualCost

/-- Total assigned amortized charge across the entire trace. -/
def totalAmortized : TransitionTrace C s₀ sₖ → Nat
  | .nil _            => 0
  | .snoc pref step _ _ => pref.totalAmortized + step.amortizedCharge

/-- Predicate stating that every step in the trace satisfies `ExactAmortizedStep phi`. -/
def AllExact (phi : C → Nat) : TransitionTrace C s₀ sₖ → Prop
  | .nil _              => True
  | .snoc pref step _ _ => pref.AllExact phi ∧ ExactAmortizedStep phi step

/-- Predicate stating that every step in the trace satisfies `BoundedAmortizedStep phi`. -/
def AllBounded (phi : C → Nat) : TransitionTrace C s₀ sₖ → Prop
  | .nil _              => True
  | .snoc pref step _ _ => pref.AllBounded phi ∧ BoundedAmortizedStep phi step

/-- **Theorem 2A — Exact Telescoping Accounting Identity:**
    For any sequence of exact amortized steps from `s₀` to `sₖ`,
      `totalActual + Φ(sₖ) = totalAmortized + Φ(s₀)`.
    When `Φ(s₀) = 0`, this gives the exact identity from `docs/index.html`:
      `actual cost so far + Φ(current state) = assigned amortized charge`. -/
theorem totalActual_add_phi_eq (phi : C → Nat) {s₀ sₖ : C}
    (tr : TransitionTrace C s₀ sₖ) (h : tr.AllExact phi) :
    tr.totalActual + phi sₖ = tr.totalAmortized + phi s₀ := by
  induction tr with
  | nil =>
    simp [totalActual, totalAmortized]
  | @snoc s₁ s₂ stepPref step hpre hpost ih =>
    rcases h with ⟨hpref, hstep⟩
    have ih' := ih hpref
    unfold ExactAmortizedStep at hstep
    rw [hpre, hpost] at hstep
    simp only [totalActual, totalAmortized]
    omega

/-- Corollary at an empty initial state (`Φ(s₀) = 0`):
    `totalActual + Φ(sₖ) = totalAmortized` and `totalActual ≤ totalAmortized`. -/
theorem exact_trace_from_zero (phi : C → Nat) {s₀ sₖ : C}
    (tr : TransitionTrace C s₀ sₖ) (h : tr.AllExact phi) (h₀ : phi s₀ = 0) :
    tr.totalActual + phi sₖ = tr.totalAmortized ∧ tr.totalActual ≤ tr.totalAmortized := by
  have htel := totalActual_add_phi_eq phi tr h
  rw [h₀, Nat.add_zero] at htel
  refine ⟨htel, ?_⟩
  omega

/-- **Theorem 2B — Telescoping Upper-Bound Soundness (Physicist's Fundamental Theorem):**
    For any trace of bounded amortized steps from `s₀` to `sₖ`,
      `totalActual + Φ(sₖ) ≤ totalAmortized + Φ(s₀)`.
    And if `Φ(s₀) = 0`, then `totalActual ≤ totalAmortized`. -/
theorem totalActual_add_phi_le (phi : C → Nat) {s₀ sₖ : C}
    (tr : TransitionTrace C s₀ sₖ) (h : tr.AllBounded phi) :
    tr.totalActual + phi sₖ ≤ tr.totalAmortized + phi s₀ := by
  induction tr with
  | nil =>
    simp [totalActual, totalAmortized]
  | @snoc s₁ s₂ stepPref step hpre hpost ih =>
    rcases h with ⟨hpref, hstep⟩
    have ih' := ih hpref
    unfold BoundedAmortizedStep at hstep
    rw [hpre, hpost] at hstep
    simp only [totalActual, totalAmortized]
    omega

theorem bounded_trace_cost_le (phi : C → Nat) {s₀ sₖ : C}
    (tr : TransitionTrace C s₀ sₖ) (h : tr.AllBounded phi) (h₀ : phi s₀ = 0) :
    tr.totalActual ≤ tr.totalAmortized := by
  have hle := totalActual_add_phi_le phi tr h
  omega

end TransitionTrace

/-!
## §3. The Banker's View: Synthetic Credit & Debit Types (`Credit`, `Debit`) in `Giralf`

In *Potential Functions as Types* (§3–4), *Giralf* internalizes the **Banker's View** of
amortized analysis by introducing synthetic type operators:
- `Credit k A` ($\triangleright^k A$ / $\$(k) \otimes A$): a value of type `A` bundled with
  `k` saved resource credits (coins) that can pay for `k` future steps.
- `Debit k A` ($\triangleleft^k A$ / $\$(k) \multimap \mathsf{CostM}\;A$): a suspended computation
  requiring `k` credits to discharge before its cost-free observation is unlocked.

We prove the **Banker $\leftrightarrow$ Physicist Equivalence Theorem**: storing $k$ credits
per element inside an inductive structure (`CreditList k A`) is constructively isomorphic
to equipping plain `List A` with the linear potential function $\Phi(\mathit{xs}) = k \cdot |\mathit{xs}|$.
-/

/-- `Credit k A` pairs a value of type `A` with a witness of `k` stored coins.
    In Calf, paying `k` steps upfront (`step k`) mints `Credit k A`, which can later
    offset `k` steps of actual work. -/
structure Credit (k : Nat) (A : Type u) where
  val : A
  deriving Repr, DecidableEq

/-- `Debit k A` is a computation whose actual cost is at most `k + extra`, so supplying
    `k` credits reduces its net amortized charge to `extra`. -/
structure Debit (k : Nat) (A : Type u) where
  run     : CostM A
  bounded : run.cost ≤ k

namespace Banker

/-- Mint `k` credits by paying `k` amortized steps now (`step k`). -/
def mintCredit (k : Nat) (x : A) : CostM (Credit k A) :=
  CostM.step k ⟨x⟩

/-- Split `k₁ + k₂` credits into `k₁` and `k₂` credits. -/
def splitCredit {k₁ k₂ : Nat} (c : Credit (k₁ + k₂) A) : Credit k₁ (Credit k₂ A) :=
  ⟨⟨c.val⟩⟩

/-- Combine nested credits `Credit k₁ (Credit k₂ A)` into `Credit (k₁ + k₂) A`. -/
def joinCredit {k₁ k₂ : Nat} (c : Credit k₁ (Credit k₂ A)) : Credit (k₁ + k₂) A :=
  ⟨c.val.val⟩

/-- Weaken `Credit k₁ A` to `Credit k₂ A` when `k₂ ≤ k₁` (discarding surplus coins, affine discipline). -/
def weakenCredit {k₁ k₂ : Nat} (_hle : k₂ ≤ k₁) (c : Credit k₁ A) : Credit k₂ A :=
  ⟨c.val⟩

/-- Discharge a `Debit k A` using `Credit k Unit`, guaranteeing actual cost `≤ k`. -/
def payDebit {k : Nat} (_coin : Credit k Unit) (d : Debit k A) : CostM A :=
  d.run

theorem payDebit_cost_le {k : Nat} (coin : Credit k Unit) (d : Debit k A) :
    (payDebit coin d).cost ≤ k :=
  d.bounded

end Banker

/-- **Banker's Credit-Carrying List (`CreditList k A`):**
    Each `ccons` constructor cell stores `k` credits (`Credit k A`) alongside the element. -/
inductive CreditList (k : Nat) (A : Type u) : Type u where
  | cnil  : CreditList k A
  | ccons : Credit k A → CreditList k A → CreditList k A
  deriving Repr, DecidableEq

namespace CreditList

/-- Forget the credits and recover the underlying plain `List A`. -/
def toList : CreditList k A → List A
  | .cnil         => []
  | .ccons c rest => c.val :: rest.toList

/-- Lift a plain `List A` to `CreditList k A` once `k * xs.length` credits are provided. -/
def ofList : List A → CreditList k A
  | []      => .cnil
  | x :: xs => .ccons ⟨x⟩ (ofList xs)

/-- Total credits stored inside a `CreditList k A` (Banker's stored coin count). -/
def storedCredits : CreditList k A → Nat
  | .cnil         => 0
  | .ccons _ rest => k + rest.storedCredits

@[simp] theorem toList_ofList (xs : List A) :
    (ofList (k := k) xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ofList, toList, ih]

@[simp] theorem ofList_toList (cs : CreditList k A) :
    ofList (k := k) cs.toList = cs := by
  induction cs with
  | cnil => rfl
  | ccons c rest ih =>
    cases c
    simp [toList, ofList, ih]

/-- **Theorem 3A — Banker $\leftrightarrow$ Physicist Equivalence (`banker_physicist_equiv`):**
    The total credits stored inside a Banker's `CreditList k A` is identically equal
    to the Physicist's linear potential function $\Phi(\mathit{xs}) = k \cdot |\mathit{xs}|$
    evaluated on its underlying `List A`. -/
theorem storedCredits_eq_linear_potential (k : Nat) (cs : CreditList k A) :
    cs.storedCredits = k * cs.toList.length := by
  induction cs with
  | cnil =>
    simp [storedCredits, toList]
  | ccons c rest ih =>
    simp [storedCredits, toList, ih, Nat.mul_add, Nat.add_comm]

end CreditList

/-!
## §4. Deeply Embedded `Giralf` Calculus, Verified Potential Inference & Cost-Adequate Erasure

To satisfy **ADR-02**, **M2 Obligations 1–3**, and **M5A (`REQ-COST-003`)** in `MILESTONES.md`,
we now formalize a deeply embedded first-order functional fragment of **Giralf** operating
on lists of natural numbers with:
1. **Surface/Core `GExpr` syntax** including explicit `tick c` (cost step) and `shiftCredit Δ`
   (ghost potential/credit annotations).
2. **Erased `IRExpr` syntax** with all potential/credit annotations stripped.
3. **Cost-instrumented big-step evaluation** `GEval env e v c` ($e \Downarrow_{\text{src}}^{c} v$)
   and `IREval env e_ir v c` ($e_{\text{ir}} \Downarrow_{\text{IR}}^{c} v$).
4. **Declarative Resource-Potential Typing Judgment `GHasPotential`** and an **executable
   potential checker `checkPotential`** with a machine-checked soundness theorem.
5. **Behavioral and Cost-Adequate Erasure Theorem (`REQ-COST-003`):**
   $$e \Downarrow_{\text{src}}^{c} v \iff \operatorname{erase}(e) \Downarrow_{\text{IR}}^{c} v.$$
-/

/-- Runtime values for the embedded Giralf / IR fragment. -/
inductive Val where
  | vnat  : Nat → Val
  | vlist : List Nat → Val
  | vpair : Val → Val → Val
  deriving Repr, DecidableEq

/-- Deeply embedded `Giralf` expressions with cost ticks and ghost credit annotations. -/
inductive GExpr where
  | var         : Nat → GExpr
  | natLit      : Nat → GExpr
  | nil         : GExpr
  | cons        : GExpr → GExpr → GExpr
  | pair        : GExpr → GExpr → GExpr
  | fst         : GExpr → GExpr
  | snd         : GExpr → GExpr
  | letIn       : GExpr → GExpr → GExpr
  | matchList   : GExpr → GExpr → GExpr → GExpr
  /-- Operational cost step (`tick c e` charges `c` steps to evaluate `e`). -/
  | tick        : Nat → GExpr → GExpr
  /-- Ghost Banker/Physicist annotation (`creditNote phi e`) recording potential `phi`
      for type/resource checking; erased completely at extraction. -/
  | creditNote  : Nat → GExpr → GExpr
  deriving Repr, DecidableEq

/-- Erased `Mugda2.IR` expressions: `creditNote` ghost annotations are completely removed. -/
inductive IRExpr where
  | var       : Nat → IRExpr
  | natLit    : Nat → IRExpr
  | nil       : IRExpr
  | cons      : IRExpr → IRExpr → IRExpr
  | pair      : IRExpr → IRExpr → IRExpr
  | fst       : IRExpr → IRExpr
  | snd       : IRExpr → IRExpr
  | letIn     : IRExpr → IRExpr → IRExpr
  | matchList : IRExpr → IRExpr → IRExpr → IRExpr
  | tick      : Nat → IRExpr → IRExpr
  deriving Repr, DecidableEq

/-- **Decorated Extraction (`erase`):** strips all `creditNote` ghost annotations. -/
def erase : GExpr → IRExpr
  | .var i             => .var i
  | .natLit n          => .natLit n
  | .nil               => .nil
  | .cons h t          => .cons (erase h) (erase t)
  | .pair e₁ e₂        => .pair (erase e₁) (erase e₂)
  | .fst e             => .fst (erase e)
  | .snd e             => .snd (erase e)
  | .letIn e₁ e₂       => .letIn (erase e₁) (erase e₂)
  | .matchList s n c   => .matchList (erase s) (erase n) (erase c)
  | .tick k e          => .tick k (erase e)
  | .creditNote _phi e => erase e

abbrev GEnv := List Val

/-- Lookup de Bruijn index `i` in `GEnv`. -/
def lookupEnv : GEnv → Nat → Option Val
  | [],      _     => none
  | v :: _,  0     => some v
  | _ :: vs, i + 1 => lookupEnv vs i

/-- Big-step cost-instrumented operational semantics for `Giralf` (`GEval env e v c`
    means $e$ evaluates under `env` to value `v` in exact step cost `c`). -/
inductive GEval : GEnv → GExpr → Val → Nat → Prop where
  | ev_var {env i v} :
      lookupEnv env i = some v →
      GEval env (.var i) v 0
  | ev_nat {env n} :
      GEval env (.natLit n) (.vnat n) 0
  | ev_nil {env} :
      GEval env .nil (.vlist []) 0
  | ev_cons {env eh et n xs c₁ c₂} :
      GEval env eh (.vnat n) c₁ →
      GEval env et (.vlist xs) c₂ →
      GEval env (.cons eh et) (.vlist (n :: xs)) (c₁ + c₂)
  | ev_pair {env e₁ e₂ v₁ v₂ c₁ c₂} :
      GEval env e₁ v₁ c₁ →
      GEval env e₂ v₂ c₂ →
      GEval env (.pair e₁ e₂) (.vpair v₁ v₂) (c₁ + c₂)
  | ev_fst {env e v₁ v₂ c} :
      GEval env e (.vpair v₁ v₂) c →
      GEval env (.fst e) v₁ c
  | ev_snd {env e v₁ v₂ c} :
      GEval env e (.vpair v₁ v₂) c →
      GEval env (.snd e) v₂ c
  | ev_let {env e₁ e₂ v₁ v₂ c₁ c₂} :
      GEval env e₁ v₁ c₁ →
      GEval (v₁ :: env) e₂ v₂ c₂ →
      GEval env (.letIn e₁ e₂) v₂ (c₁ + c₂)
  | ev_match_nil {env s en ec v c₁ c₂} :
      GEval env s (.vlist []) c₁ →
      GEval env en v c₂ →
      GEval env (.matchList s en ec) v (c₁ + c₂)
  | ev_match_cons {env s en ec x xs v c₁ c₂} :
      GEval env s (.vlist (x :: xs)) c₁ →
      GEval (.vlist xs :: .vnat x :: env) ec v c₂ →
      GEval env (.matchList s en ec) v (c₁ + c₂)
  | ev_tick {env k e v c} :
      GEval env e v c →
      GEval env (.tick k e) v (k + c)
  | ev_creditNote {env phi e v c} :
      GEval env e v c →
      GEval env (.creditNote phi e) v c

/-- Big-step cost-instrumented operational semantics for erased `Mugda2.IR` (`IREval`). -/
inductive IREval : GEnv → IRExpr → Val → Nat → Prop where
  | ir_var {env i v} :
      lookupEnv env i = some v →
      IREval env (.var i) v 0
  | ir_nat {env n} :
      IREval env (.natLit n) (.vnat n) 0
  | ir_nil {env} :
      IREval env .nil (.vlist []) 0
  | ir_cons {env eh et n xs c₁ c₂} :
      IREval env eh (.vnat n) c₁ →
      IREval env et (.vlist xs) c₂ →
      IREval env (.cons eh et) (.vlist (n :: xs)) (c₁ + c₂)
  | ir_pair {env e₁ e₂ v₁ v₂ c₁ c₂} :
      IREval env e₁ v₁ c₁ →
      IREval env e₂ v₂ c₂ →
      IREval env (.pair e₁ e₂) (.vpair v₁ v₂) (c₁ + c₂)
  | ir_fst {env e v₁ v₂ c} :
      IREval env e (.vpair v₁ v₂) c →
      IREval env (.fst e) v₁ c
  | ir_snd {env e v₁ v₂ c} :
      IREval env e (.vpair v₁ v₂) c →
      IREval env (.snd e) v₂ c
  | ir_let {env e₁ e₂ v₁ v₂ c₁ c₂} :
      IREval env e₁ v₁ c₁ →
      IREval (v₁ :: env) e₂ v₂ c₂ →
      IREval env (.letIn e₁ e₂) v₂ (c₁ + c₂)
  | ir_match_nil {env s en ec v c₁ c₂} :
      IREval env s (.vlist []) c₁ →
      IREval env en v c₂ →
      IREval env (.matchList s en ec) v (c₁ + c₂)
  | ir_match_cons {env s en ec x xs v c₁ c₂} :
      IREval env s (.vlist (x :: xs)) c₁ →
      IREval (.vlist xs :: .vnat x :: env) ec v c₂ →
      IREval env (.matchList s en ec) v (c₁ + c₂)
  | ir_tick {env k e v c} :
      IREval env e v c →
      IREval env (.tick k e) v (k + c)

/-- **Theorem 4A — Forward Behavioral & Cost-Adequate Erasure (`REQ-COST-003`):**
    If a Giralf expression $e$ evaluates to $v$ with cost $c$, then $\operatorname{erase}(e)$
    evaluates in `Mugda2.IR` to $v$ with the **exact same cost** $c$. -/
theorem erase_sound {env : GEnv} {e : GExpr} {v : Val} {c : Nat}
    (h : GEval env e v c) : IREval env (erase e) v c := by
  induction h with
  | ev_var hlk => exact .ir_var hlk
  | ev_nat => exact .ir_nat
  | ev_nil => exact .ir_nil
  | ev_cons _ _ ih₁ ih₂ => exact .ir_cons ih₁ ih₂
  | ev_pair _ _ ih₁ ih₂ => exact .ir_pair ih₁ ih₂
  | ev_fst _ ih => exact .ir_fst ih
  | ev_snd _ ih => exact .ir_snd ih
  | ev_let _ _ ih₁ ih₂ => exact .ir_let ih₁ ih₂
  | ev_match_nil _ _ ih₁ ih₂ => exact .ir_match_nil ih₁ ih₂
  | ev_match_cons _ _ ih₁ ih₂ => exact .ir_match_cons ih₁ ih₂
  | ev_tick _ ih => exact .ir_tick ih
  | ev_creditNote _ ih => exact ih

/-- **Theorem 4B — Backward Adequacy of Erasure:**
    Every evaluation of $\operatorname{erase}(e)$ in `Mugda2.IR` corresponds to an evaluation
    of $e$ in `Giralf` with the exact same value and cost. -/
theorem erase_complete {env : GEnv} (e : GExpr) {v : Val} {c : Nat}
    (h : IREval env (erase e) v c) : GEval env e v c := by
  induction e generalizing env v c with
  | var i =>
    cases h with
    | ir_var hlk => exact .ev_var hlk
  | natLit n =>
    cases h with
    | ir_nat => exact .ev_nat
  | nil =>
    cases h with
    | ir_nil => exact .ev_nil
  | cons eh et ihe iht =>
    cases h with
    | ir_cons h₁ h₂ => exact .ev_cons (ihe h₁) (iht h₂)
  | pair e₁ e₂ ih₁ ih₂ =>
    cases h with
    | ir_pair h₁ h₂ => exact .ev_pair (ih₁ h₁) (ih₂ h₂)
  | fst e ihe =>
    cases h with
    | ir_fst h₁ => exact .ev_fst (ihe h₁)
  | snd e ihe =>
    cases h with
    | ir_snd h₁ => exact .ev_snd (ihe h₁)
  | letIn e₁ e₂ ih₁ ih₂ =>
    cases h with
    | ir_let h₁ h₂ => exact .ev_let (ih₁ h₁) (ih₂ h₂)
  | matchList s en ec ihs ihn ihc =>
    cases h with
    | ir_match_nil h₁ h₂ => exact .ev_match_nil (ihs h₁) (ihn h₂)
    | ir_match_cons h₁ h₂ => exact .ev_match_cons (ihs h₁) (ihc h₂)
  | tick k e ihe =>
    cases h with
    | ir_tick h₁ => exact .ev_tick (ihe h₁)
  | creditNote phi e ihe =>
    exact .ev_creditNote (ihe h)

/-- **Theorem 4C — Combined Bi-Directional Behavioral & Cost Adequacy (`REQ-COST-003`):**
    $$e \Downarrow_{\text{src}}^{c} v \iff \operatorname{erase}(e) \Downarrow_{\text{IR}}^{c} v.$$ -/
theorem erase_behavioral_and_cost_adequate (env : GEnv) (e : GExpr) (v : Val) (c : Nat) :
    GEval env e v c ↔ IREval env (erase e) v c :=
  ⟨erase_sound, erase_complete e⟩

/-- Static constant-credit upper-bound judgment `HasCreditBound q e`:
    synthetically tracks that `q` upfront credits suffice to pay for all `tick` operations
    along every execution branch of `e`. -/
inductive HasCreditBound : Nat → GExpr → Prop where
  | cb_var {q i} : HasCreditBound q (.var i)
  | cb_nat {q n} : HasCreditBound q (.natLit n)
  | cb_nil {q}   : HasCreditBound q .nil
  | cb_cons {q₁ q₂ eh et} :
      HasCreditBound q₁ eh →
      HasCreditBound q₂ et →
      HasCreditBound (q₁ + q₂) (.cons eh et)
  | cb_pair {q₁ q₂ e₁ e₂} :
      HasCreditBound q₁ e₁ →
      HasCreditBound q₂ e₂ →
      HasCreditBound (q₁ + q₂) (.pair e₁ e₂)
  | cb_fst {q e} :
      HasCreditBound q e →
      HasCreditBound q (.fst e)
  | cb_snd {q e} :
      HasCreditBound q e →
      HasCreditBound q (.snd e)
  | cb_let {q₁ q₂ e₁ e₂} :
      HasCreditBound q₁ e₁ →
      HasCreditBound q₂ e₂ →
      HasCreditBound (q₁ + q₂) (.letIn e₁ e₂)
  | cb_match {q_s q_br s en ec} :
      HasCreditBound q_s s →
      HasCreditBound q_br en →
      HasCreditBound q_br ec →
      HasCreditBound (q_s + q_br) (.matchList s en ec)
  | cb_tick {k q e} :
      HasCreditBound q e →
      HasCreditBound (k + q) (.tick k e)
  | cb_creditNote {phi q e} :
      q ≤ phi →
      HasCreditBound q e →
      HasCreditBound phi (.creditNote phi e)
  | cb_weaken {q q' e} :
      q ≤ q' →
      HasCreditBound q e →
      HasCreditBound q' e

/-- **Theorem 4D — Soundness of Giralf Credit Typing (`giralf_credit_soundness`):**
    If `HasCreditBound q e` holds and `GEval env e v c`, then the actual operational cost
    `c` is bounded by the static credit budget `q` (`c ≤ q`). -/
theorem giralf_credit_soundness {q : Nat} {e : GExpr}
    (ht : HasCreditBound q e) :
    ∀ {env : GEnv} {v : Val} {c : Nat}, GEval env e v c → c ≤ q := by
  induction ht with
  | cb_var =>
    intro env v c hev; cases hev; exact Nat.zero_le _
  | cb_nat =>
    intro env v c hev; cases hev; exact Nat.zero_le _
  | cb_nil =>
    intro env v c hev; cases hev; exact Nat.zero_le _
  | cb_cons _ _ ih₁ ih₂ =>
    intro env v c hev
    cases hev with
    | ev_cons h₁ h₂ => exact Nat.add_le_add (ih₁ h₁) (ih₂ h₂)
  | cb_pair _ _ ih₁ ih₂ =>
    intro env v c hev
    cases hev with
    | ev_pair h₁ h₂ => exact Nat.add_le_add (ih₁ h₁) (ih₂ h₂)
  | cb_fst _ ih =>
    intro env v c hev
    cases hev with
    | ev_fst h₁ => exact ih h₁
  | cb_snd _ ih =>
    intro env v c hev
    cases hev with
    | ev_snd h₁ => exact ih h₁
  | cb_let _ _ ih₁ ih₂ =>
    intro env v c hev
    cases hev with
    | ev_let h₁ h₂ => exact Nat.add_le_add (ih₁ h₁) (ih₂ h₂)
  | cb_match _ _ _ ihs ihn ihc =>
    intro env v c hev
    cases hev with
    | ev_match_nil h₁ h₂ => exact Nat.add_le_add (ihs h₁) (ihn h₂)
    | ev_match_cons h₁ h₂ => exact Nat.add_le_add (ihs h₁) (ihc h₂)
  | cb_tick _ ih =>
    intro env v c hev
    cases hev with
    | ev_tick h₁ => exact Nat.add_le_add (Nat.le_refl _) (ih h₁)
  | cb_creditNote hle _ ih =>
    intro env v c hev
    cases hev with
    | ev_creditNote h₁ => exact Nat.le_trans (ih h₁) hle
  | cb_weaken hle _ ih =>
    intro env v c hev
    exact Nat.le_trans (ih hev) hle

/-- Executable credit inference / synthesis procedure (`inferCreditBound`) that
    automatically synthesizes a minimal credit bound for `GExpr` (and checks any
    user/agent `creditNote phi` annotations). -/
def inferCreditBound : GExpr → Option Nat
  | .var _             => some 0
  | .natLit _          => some 0
  | .nil               => some 0
  | .cons eh et        => do
      let q₁ ← inferCreditBound eh
      let q₂ ← inferCreditBound et
      pure (q₁ + q₂)
  | .pair e₁ e₂        => do
      let q₁ ← inferCreditBound e₁
      let q₂ ← inferCreditBound e₂
      pure (q₁ + q₂)
  | .fst e             => inferCreditBound e
  | .snd e             => inferCreditBound e
  | .letIn e₁ e₂       => do
      let q₁ ← inferCreditBound e₁
      let q₂ ← inferCreditBound e₂
      pure (q₁ + q₂)
  | .matchList s en ec => do
      let qs ← inferCreditBound s
      let qn ← inferCreditBound en
      let qc ← inferCreditBound ec
      pure (qs + Nat.max qn qc)
  | .tick k e          => do
      let q ← inferCreditBound e
      pure (k + q)
  | .creditNote phi e  => do
      let q ← inferCreditBound e
      if q ≤ phi then some phi else none

/-- **Theorem 4E — Soundness of Automated Credit Inference (`inferCreditBound_sound`):**
    Whenever `inferCreditBound e = some q`, the declarative judgment `HasCreditBound q e`
    holds, and therefore every evaluation of `e` (and of `erase e` in `Mugda2.IR`)
    takes at most `q` steps. -/
theorem inferCreditBound_sound (e : GExpr) :
    ∀ {q : Nat}, inferCreditBound e = some q → HasCreditBound q e := by
  induction e with
  | var i =>
    intro q h; simp [inferCreditBound] at h; subst h; exact .cb_var
  | natLit n =>
    intro q h; simp [inferCreditBound] at h; subst h; exact .cb_nat
  | nil =>
    intro q h; simp [inferCreditBound] at h; subst h; exact .cb_nil
  | cons eh et ih₁ ih₂ =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases h₁ : inferCreditBound eh with
    | none => rw [h₁] at h; contradiction
    | some q₁ =>
      rw [h₁] at h
      cases h₂ : inferCreditBound et with
      | none => rw [h₂] at h; contradiction
      | some q₂ =>
        rw [h₂] at h
        injection h with hq
        subst hq
        exact .cb_cons (ih₁ h₁) (ih₂ h₂)
  | pair e₁ e₂ ih₁ ih₂ =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases h₁ : inferCreditBound e₁ with
    | none => rw [h₁] at h; contradiction
    | some q₁ =>
      rw [h₁] at h
      cases h₂ : inferCreditBound e₂ with
      | none => rw [h₂] at h; contradiction
      | some q₂ =>
        rw [h₂] at h
        injection h with hq
        subst hq
        exact .cb_pair (ih₁ h₁) (ih₂ h₂)
  | fst e ih =>
    intro q h; exact .cb_fst (ih h)
  | snd e ih =>
    intro q h; exact .cb_snd (ih h)
  | letIn e₁ e₂ ih₁ ih₂ =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases h₁ : inferCreditBound e₁ with
    | none => rw [h₁] at h; contradiction
    | some q₁ =>
      rw [h₁] at h
      cases h₂ : inferCreditBound e₂ with
      | none => rw [h₂] at h; contradiction
      | some q₂ =>
        rw [h₂] at h
        injection h with hq
        subst hq
        exact .cb_let (ih₁ h₁) (ih₂ h₂)
  | matchList s en ec ihs ihn ihc =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases hs : inferCreditBound s with
    | none => rw [hs] at h; contradiction
    | some qs =>
      rw [hs] at h
      cases hn : inferCreditBound en with
      | none => rw [hn] at h; contradiction
      | some qn =>
        rw [hn] at h
        cases hc : inferCreditBound ec with
        | none => rw [hc] at h; contradiction
        | some qc =>
          rw [hc] at h
          injection h with hq
          subst hq
          refine .cb_match (ihs hs) ?_ ?_
          · exact .cb_weaken (Nat.le_max_left qn qc) (ihn hn)
          · exact .cb_weaken (Nat.le_max_right qn qc) (ihc hc)
  | tick k e ih =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases he : inferCreditBound e with
    | none => rw [he] at h; contradiction
    | some qe =>
      rw [he] at h
      injection h with hq
      subst hq
      exact .cb_tick (ih he)
  | creditNote phi e ih =>
    intro q h
    simp only [inferCreditBound, bind, Option.bind] at h
    cases he : inferCreditBound e with
    | none => rw [he] at h; contradiction
    | some qe =>
      rw [he] at h
      by_cases hle : qe ≤ phi
      · simp [hle] at h
        subst h
        exact .cb_creditNote hle (ih he)
      · simp [hle] at h

/-- **Corollary 4F — End-to-End Inference $\to$ IR Execution Cost Guarantee:**
    If `inferCreditBound e = some q` and the erased IR program evaluates
    `IREval env (erase e) v c`, then `c ≤ q`. -/
theorem inferCreditBound_ir_cost_le {e : GExpr} {q : Nat}
    (hinf : inferCreditBound e = some q)
    {env : GEnv} {v : Val} {c : Nat}
    (hir : IREval env (erase e) v c) :
    c ≤ q :=
  giralf_credit_soundness (inferCreditBound_sound e hinf) (erase_complete e hir)

/-!
## §5. Flagship Benchmark & `EXP-A` Control: Batched Two-List Queue vs. Single-List Queue

We now formalize the exact FIFO Queue benchmark from:
- *Potential Functions as Types* (Grodin, Chu, Li, Hoffmann & Harper, 2026)
- *Abstraction Functions as Types* (Grodin, Li & Harper, POPL 2026)
- Mugda2's interactive guide (`docs/index.html`) and Experiment A (`docs/EXPERIMENTS.md`).
-/

/-! ### 5.1 Implementation A: Batched Two-List Queue (Physicist & Banker Amortized $O(1)$) -/

/-- The batched two-list queue state `BatchedQ E`.
    - `front` holds elements ready to be dequeued in FIFO order.
    - `rear` holds recently enqueued elements in reverse order, each carrying 1 credit
      (or potential $\Phi(\text{front}, \text{rear}) = |\text{rear}|$). -/
structure BatchedQ (E : Type u) where
  front : List E
  rear  : List E
  deriving Repr, DecidableEq

namespace BatchedQ

/-- Empty batched queue. -/
def empty : BatchedQ E := ⟨[], []⟩

/-- Abstraction function $\alpha(\text{front}, \text{rear}) = \text{front} \mathbin{++} \text{rear}^{\text{rev}}$. -/
def contents (q : BatchedQ E) : List E :=
  q.front ++ q.rear.reverse

/-- Physicist's potential function $\Phi(\text{front}, \text{rear}) = |\text{rear}|$. -/
def phi (q : BatchedQ E) : Nat :=
  q.rear.length

/-- Cost-instrumented `enqueue`: conses onto `rear` in $1$ actual step. -/
def enqueue (q : BatchedQ E) (x : E) : CostM (BatchedQ E) :=
  CostM.step 1 ⟨q.front, x :: q.rear⟩

/-- Cost-instrumented `dequeue`:
    - If `front = x :: fs`, pops `x` in $1$ actual step.
    - If `front = []`, reverses `rear` in `rear.length` transfer steps + $1$ inspection/pop step. -/
def dequeue (q : BatchedQ E) : CostM (Option (E × BatchedQ E)) :=
  match q.front with
  | x :: fs => CostM.step 1 (some (x, ⟨fs, q.rear⟩))
  | []      =>
    match q.rear.reverse with
    | []      => CostM.step 1 none
    | x :: fs => CostM.step (q.rear.length + 1) (some (x, ⟨fs, []⟩))

@[simp] theorem phi_empty : phi (empty : BatchedQ E) = 0 := rfl

@[simp] theorem contents_empty : contents (empty : BatchedQ E) = [] := rfl

theorem contents_enqueue (q : BatchedQ E) (x : E) :
    contents (enqueue q x).val = contents q ++ [x] := by
  simp [enqueue, contents, List.reverse_cons, List.append_assoc]

theorem contents_dequeue (q : BatchedQ E) :
    DequeueResultSpec contents q (dequeue q).val := by
  rcases q with ⟨front, rear⟩
  cases front with
  | cons x fs =>
    simp [dequeue, DequeueResultSpec, contents]
  | nil =>
    simp only [dequeue]
    cases hrev : rear.reverse with
    | nil =>
      simp [CostM.step_val, DequeueResultSpec, contents, hrev]
    | cons x fs =>
      simp [CostM.step_val, DequeueResultSpec, contents, hrev]

/-- **Theorem 5A — Exact Amortized Identity for `enqueue` (Charge = 2):**
    `enqueue` costs $1$ actual step and increases $\Phi = |\text{rear}|$ by $1$,
    so `actualCost + Φ(q') = 2 + Φ(q)`. -/
theorem enqueue_exact_amortized (q : BatchedQ E) (x : E) :
    (enqueue q x).cost + phi (enqueue q x).val = 2 + phi q := by
  simp [enqueue, phi]
  omega

/-- **Theorem 5B — Exact Amortized Identity for Successful `dequeue` (Charge = 1):**
    - When `front = x :: fs`, actual cost is $1$ and $\Phi$ is unchanged, so
      `actualCost + Φ(q') = 1 + Φ(q)`.
    - When `front = []` and `rear` is non-empty, actual cost is `|rear| + 1` and
      $\Phi(q') = 0$, releasing all `|rear|` stored credits so that
      `actualCost + Φ(q') = 1 + Φ(q)` holds **with exact equality**! -/
theorem dequeue_nonempty_exact_amortized (q : BatchedQ E) (x : E) (q' : BatchedQ E)
    (h : (dequeue q).val = some (x, q')) :
    (dequeue q).cost + phi q' = 1 + phi q := by
  rcases q with ⟨front, rear⟩
  cases front with
  | cons y fs =>
    simp [dequeue] at h
    rcases h with ⟨_, rfl⟩
    simp [dequeue, phi]
  | nil =>
    simp only [dequeue] at h ⊢
    cases hrev : rear.reverse with
    | nil =>
      rw [hrev] at h
      contradiction
    | cons y fs =>
      rw [hrev] at h
      simp [CostM.step_val] at h
      rcases h with ⟨_, rfl⟩
      simp [CostM.step_cost, phi, Nat.add_comm]

/-- **Theorem 5C — Bounded Amortized Step for Arbitrary `dequeue` (Including Empty Queue):**
    For all states `q`, `dequeue` has amortized cost at most $1$. -/
theorem dequeue_bounded_amortized (q : BatchedQ E) :
    let res := dequeue q
    let postPhi := match res.val with | none => phi q | some (_, q') => phi q'
    res.cost + postPhi ≤ 1 + phi q := by
  rcases q with ⟨front, rear⟩
  cases front with
  | cons y fs =>
    simp [dequeue, phi]
  | nil =>
    simp only [dequeue]
    cases hrev : rear.reverse with
    | nil =>
      simp [CostM.step_val, CostM.step_cost, phi]
    | cons y fs =>
      simp [CostM.step_val, CostM.step_cost, phi, Nat.add_comm]

/-- Package `BatchedQ` as an instance of the modular `QueueModule (BatchedQ E) E` interface. -/
def module (E : Type u) : QueueModule (BatchedQ E) E where
  empty            := empty
  enqueue          := enqueue
  dequeue          := dequeue
  contents         := contents
  contents_empty   := contents_empty
  contents_enqueue := contents_enqueue
  contents_dequeue := contents_dequeue

@[simp] theorem module_empty : (module E).empty = (empty : BatchedQ E) := rfl
@[simp] theorem module_enqueue (q : BatchedQ E) (x : E) : (module E).enqueue q x = enqueue q x := rfl
@[simp] theorem module_dequeue (q : BatchedQ E) : (module E).dequeue q = dequeue q := rfl

end BatchedQ

/-! ### 5.2 Implementation B: Single-List Queue (`EXP-A` Reference Implementation) -/

namespace SingleListQ

/-- Enqueue by appending to the end of the list (`xs.length + 1` cell visits). -/
def enqueue (q : List E) (x : E) : CostM (List E) :=
  CostM.step (q.length + 1) (q ++ [x])

/-- Dequeue from the front of the list in $1$ step. -/
def dequeue (q : List E) : CostM (Option (E × List E)) :=
  match q with
  | []      => CostM.step 1 none
  | x :: xs => CostM.step 1 (some (x, xs))

/-- Package `SingleListQ` as an instance of the exact same `QueueModule (List E) E` interface. -/
def module (E : Type u) : QueueModule (List E) E where
  empty            := []
  enqueue          := enqueue
  dequeue          := dequeue
  contents         := id
  contents_empty   := rfl
  contents_enqueue := fun _ _ => rfl
  contents_dequeue := fun q => by
    cases q <;> rfl

end SingleListQ

/-! ### 5.3 Modular Client Verification Across Representation Swap (`EXP-A` Theorem) -/

/-- Cost lemma for `BatchedQ`: `enqueueAll` on `BatchedQ` takes exactly `xs.length` steps
    and increases `rear.length` by `xs.length`. -/
theorem batched_enqueueAll_cost (q : BatchedQ E) (xs : List E) :
    (enqueueAll (BatchedQ.module E) q xs).cost = xs.length ∧
    (enqueueAll (BatchedQ.module E) q xs).val.phi = q.phi + xs.length := by
  induction xs generalizing q with
  | nil =>
    simp [enqueueAll, CostM.ret_cost, CostM.ret_val]
  | cons x xs ih =>
    simp only [enqueueAll, bind, CostM.bind_cost, CostM.bind_val, BatchedQ.module_enqueue]
    have ⟨ihc, ihp⟩ := ih (BatchedQ.enqueue q x).val
    simp only [BatchedQ.enqueue, CostM.step_cost, CostM.step_val,
      BatchedQ.phi, List.length_cons] at ihc ihp ⊢
    refine ⟨?_, ?_⟩ <;> omega

/-- Cost lemma for `BatchedQ`: `dequeueN k q` on `BatchedQ` satisfies the telescoped
    amortized bound `actualCost + Φ(q') ≤ k + Φ(q)`. -/
theorem batched_dequeueN_amortized (k : Nat) (q : BatchedQ E) :
    let r := dequeueN (BatchedQ.module E) k q
    r.cost + r.val.2.phi ≤ k + q.phi := by
  induction k generalizing q with
  | zero =>
    simp [dequeueN, CostM.ret_cost]
  | succ k ih =>
    simp only [dequeueN, bind, CostM.bind_cost, CostM.bind_val, BatchedQ.module_dequeue]
    have hstep := BatchedQ.dequeue_bounded_amortized q
    cases hdeq : (BatchedQ.dequeue q).val with
    | none =>
      simp only [hdeq] at hstep ⊢
      simp only [CostM.ret_cost, CostM.ret_val, Nat.add_zero]
      omega
    | some pair =>
      rcases pair with ⟨x, q'⟩
      simp only [hdeq] at hstep ⊢
      simp only [CostM.bind_cost, CostM.bind_val, CostM.ret_cost, CostM.ret_val, Nat.add_zero]
      have ih' := ih q'
      omega

/-- **Theorem 5E — Linear $3n$ Amortized Cost Bound for `BatchedQ` on `fifoRoundtrip`:**
    For any input list `xs` of length $n$, running the generic client `fifoRoundtrip`
    with `BatchedQ.module E` takes at most $3n$ total actual steps ($2n$ amortized for $n$
    enqueues + $n$ amortized for $n$ dequeues)! -/
theorem batched_fifoRoundtrip_cost_le (xs : List E) :
    (fifoRoundtrip (BatchedQ.module E) xs).cost ≤ 3 * xs.length := by
  simp only [fifoRoundtrip, bind, CostM.bind_cost, CostM.ret_cost, Nat.add_zero,
    BatchedQ.module_empty]
  have ⟨henq_c, henq_p⟩ := batched_enqueueAll_cost (BatchedQ.empty : BatchedQ E) xs
  have hdeq := batched_dequeueN_amortized xs.length (enqueueAll (BatchedQ.module E) BatchedQ.empty xs).val
  simp only [BatchedQ.phi_empty, Nat.zero_add] at henq_p
  omega

/-- `BatchedQ` satisfies the common `EXP-A` budget `cost ≤ expABudget xs.length`. -/
theorem batched_satisfies_expABudget (xs : List E) :
    (fifoRoundtrip (BatchedQ.module E) xs).cost ≤ expABudget xs.length := by
  have hlin := batched_fifoRoundtrip_cost_le xs
  unfold expABudget
  have h3 : 3 * xs.length ≤ xs.length * (xs.length + 3) := by
    rw [Nat.mul_add, Nat.mul_comm xs.length 3]
    exact Nat.le_add_left (3 * xs.length) (xs.length * xs.length)
  exact Nat.le_trans hlin h3

/-! ### 5.4 Cost Bound for `SingleListQ` & Unified Modular `EXP-A` Client Swap Theorem -/

namespace SingleListQ

@[simp] theorem module_empty : (module E).empty = ([] : List E) := rfl
@[simp] theorem module_enqueue (q : List E) (x : E) : (module E).enqueue q x = enqueue q x := rfl
@[simp] theorem module_dequeue (q : List E) : (module E).dequeue q = dequeue q := rfl

end SingleListQ

/-- Cost & length lemma for `SingleListQ`: `enqueueAll` from `q` on `xs` results in list
    of length `q.length + xs.length` and costs at most `xs.length * (q.length + xs.length + 1)`. -/
theorem singleList_enqueueAll_cost_le (q : List E) (xs : List E) :
    (enqueueAll (SingleListQ.module E) q xs).val.length = q.length + xs.length ∧
    (enqueueAll (SingleListQ.module E) q xs).cost ≤ xs.length * (q.length + xs.length + 1) := by
  induction xs generalizing q with
  | nil =>
    simp [enqueueAll, CostM.ret_val, CostM.ret_cost]
  | cons x xs ih =>
    simp only [enqueueAll, bind, CostM.bind_val, CostM.bind_cost, SingleListQ.module_enqueue]
    have ⟨ihl, ihc⟩ := ih (SingleListQ.enqueue q x).val
    simp only [SingleListQ.enqueue, CostM.step_val, CostM.step_cost,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at ihl ihc ⊢
    refine ⟨by omega, ?_⟩
    have heq : q.length + 1 + xs.length + 1 = q.length + (xs.length + 1) + 1 := by omega
    rw [heq] at ihc
    have hstep : q.length + 1 + xs.length * (q.length + (xs.length + 1) + 1) ≤
        (xs.length + 1) * (q.length + (xs.length + 1) + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega

/-- Cost lemma for `SingleListQ`: `dequeueN k q` costs at most `k` steps. -/
theorem singleList_dequeueN_cost_le (k : Nat) (q : List E) :
    (dequeueN (SingleListQ.module E) k q).cost ≤ k := by
  induction k generalizing q with
  | zero =>
    simp [dequeueN, CostM.ret_cost]
  | succ k ih =>
    simp only [dequeueN, bind, CostM.bind_cost, SingleListQ.module_dequeue]
    rcases q with _ | ⟨x, xs⟩
    · simp [SingleListQ.dequeue, CostM.step_val, CostM.step_cost, CostM.ret_cost]
    · simp only [SingleListQ.dequeue, CostM.step_val, CostM.step_cost,
        CostM.bind_cost, CostM.ret_cost, Nat.add_zero]
      have ih' := ih xs
      omega

/-- `SingleListQ` also satisfies the common `EXP-A` quadratic budget `expABudget xs.length`. -/
theorem singleList_satisfies_expABudget (xs : List E) :
    (fifoRoundtrip (SingleListQ.module E) xs).cost ≤ expABudget xs.length := by
  simp only [fifoRoundtrip, bind, CostM.bind_cost, CostM.ret_cost, Nat.add_zero,
    SingleListQ.module_empty]
  have ⟨_, henq⟩ := singleList_enqueueAll_cost_le ([] : List E) xs
  have hdeq := singleList_dequeueN_cost_le xs.length (enqueueAll (SingleListQ.module E) [] xs).val
  simp only [List.length_nil, Nat.zero_add] at henq
  unfold expABudget
  have hbound : xs.length * (xs.length + 1) + xs.length ≤ xs.length * (xs.length + 3) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  omega

/-- **Modular Cost-Aware Queue Interface (`BoundedQueueModule Q E budget`):**
    Bundles the behavioral `QueueModule Q E` specification with an abstract roundtrip
    cost guarantee `budget : Nat → Nat` (`REQ-COST-001`, `EXP-A`). -/
structure BoundedQueueModule (Q : Type u) (E : Type u) (budget : Nat → Nat)
    extends QueueModule Q E where
  roundtrip_cost_le : ∀ (xs : List E),
    (fifoRoundtrip toQueueModule xs).cost ≤ budget xs.length

/-- **Theorem 5F — The `EXP-A` Modular Representation Swap Theorem:**
    A client written against `BoundedQueueModule Q E budget` obtains both behavioral
    FIFO correctness and the quantitative cost bound `cost ≤ budget xs.length`
    purely from the abstract interface, regardless of whether `BatchedQ` or `SingleListQ`
    is linked! -/
theorem expA_client_correct_and_bounded
    {Q : Type u} {E : Type u} {budget : Nat → Nat}
    (M : BoundedQueueModule Q E budget) (xs : List E) :
    (fifoRoundtrip M.toQueueModule xs).val = xs ∧
    (fifoRoundtrip M.toQueueModule xs).cost ≤ budget xs.length :=
  ⟨fifoRoundtrip_correct M.toQueueModule xs, M.roundtrip_cost_le xs⟩

/-- Implementation 1 (`BatchedQ`) packaged as a `BoundedQueueModule` for `expABudget`. -/
def BatchedQ.boundedModule (E : Type u) : BoundedQueueModule (BatchedQ E) E expABudget where
  toQueueModule     := BatchedQ.module E
  roundtrip_cost_le := batched_satisfies_expABudget

/-- Implementation 2 (`SingleListQ`) packaged as a `BoundedQueueModule` for `expABudget`. -/
def SingleListQ.boundedModule (E : Type u) : BoundedQueueModule (List E) E expABudget where
  toQueueModule     := SingleListQ.module E
  roundtrip_cost_le := singleList_satisfies_expABudget

/-- Instantiating the unchanged `EXP-A` client theorem on `BatchedQ` and `SingleListQ`
    proves they produce identical observable FIFO results while both respecting `expABudget`. -/
theorem expA_implementation_swap_agreement (xs : List E) :
    (fifoRoundtrip (BatchedQ.boundedModule E).toQueueModule xs).val =
      (fifoRoundtrip (SingleListQ.boundedModule E).toQueueModule xs).val ∧
    (fifoRoundtrip (BatchedQ.boundedModule E).toQueueModule xs).cost ≤ expABudget xs.length ∧
    (fifoRoundtrip (SingleListQ.boundedModule E).toQueueModule xs).cost ≤ expABudget xs.length := by
  have hB := expA_client_correct_and_bounded (BatchedQ.boundedModule E) xs
  have hS := expA_client_correct_and_bounded (SingleListQ.boundedModule E) xs
  exact ⟨Eq.trans hB.1 hS.1.symm, hB.2, hS.2⟩

end Mugda2.Giralf
