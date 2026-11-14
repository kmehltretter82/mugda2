/-!
Finite host-Lean translation control for EXP-B. The indexed view below is a
height-bounded wrapper, not a native Mugda2 parametric size quantifier. All
recursive calls use the preprocessor's contracts rather than its implementation.
-/
namespace Mugda2.Experiments.SizedCertificates

inductive Event where
  | inspect
  | pivot
  deriving DecidableEq, Repr

inductive Certificate where
  | event (label : Event)
  | sequence (children : List Certificate)
  | repeat (count : Nat) (body : Certificate)

mutual
  def height : Certificate → Nat
    | .event _ => 0
    | .sequence children => childrenHeight children + 1
    | .repeat _ body => height body + 1

  def childrenHeight : List Certificate → Nat
    | [] => 0
    | child :: rest => max (height child) (childrenHeight rest)
end

/-- Pointwise contract diagnostics used by the control fixtures. They do not
    certify a helper for all inputs or implement Mugda2 source typing. -/
inductive ContractFailure where
  | boundIncreased
  | nonDecreasing
  deriving DecidableEq, Repr

def checkBound (input output : Certificate) : Except ContractFailure Unit :=
  if height output ≤ height input then .ok () else .error .boundIncreased

def checkDescent (caller callee : Certificate) : Except ContractFailure Unit :=
  if height callee < height caller then .ok () else .error .nonDecreasing

theorem growing_helper_impossible (c : Certificate) :
    ¬height (.repeat 1 c) ≤ height c := Nat.not_succ_le_self (height c)

theorem growing_helper_rejected (c : Certificate) :
    checkBound c (.repeat 1 c) = .error .boundIncreased :=
  ite_eq_right (growing_helper_impossible c)

theorem same_bound_rejected (c : Certificate) :
    checkDescent c c = .error .nonDecreasing :=
  ite_eq_right (Nat.lt_irrefl (height c))

def repeatEvents : Nat → List Event → List Event
  | 0, _ => []
  | count + 1, events => events ++ repeatEvents count events

mutual
  def denote : Certificate → List Event
    | .event label => [label]
    | .sequence children => denoteChildren children
    | .repeat count body => repeatEvents count (denote body)

  def denoteChildren : List Certificate → List Event
    | [] => []
    | child :: rest => denote child ++ denoteChildren rest
end

/-- Contracts available to the traversal; the body of `run` is abstract. -/
structure Preprocessor where
  run : Certificate → Certificate
  height_le : ∀ c, height (run c) ≤ height c
  denote_eq : ∀ c, denote (run c) = denote c

theorem childrenHeight_le : ∀ (children : List Certificate) (bound : Nat),
    (∀ c ∈ children, height c ≤ bound) → childrenHeight children ≤ bound
  | [], bound, _ => Nat.zero_le bound
  | child :: rest, bound, h =>
      Nat.max_le.mpr ⟨h child (List.mem_cons_self),
        childrenHeight_le rest bound (fun c hc => h c (List.mem_cons_of_mem child hc))⟩

theorem height_le_childrenHeight : ∀ (children : List Certificate) (child : Certificate),
    child ∈ children → height child ≤ childrenHeight children
  | [], _, h => False.elim (List.not_mem_nil h)
  | first :: rest, child, h =>
      (List.mem_cons.mp h).elim
        (fun heq => heq ▸ Nat.le_max_left (height first) (childrenHeight rest))
        (fun hrest => Nat.le_trans (height_le_childrenHeight rest child hrest)
          (Nat.le_max_right (height first) (childrenHeight rest)))

theorem denoteChildren_eq_flatten_map : ∀ children : List Certificate,
    denoteChildren children = (children.map denote).flatten
  | [] => rfl
  | child :: rest => congrArg (denote child ++ ·) (denoteChildren_eq_flatten_map rest)

theorem sequence_contract (children : List Certificate)
    (f : { c // c ∈ children } → Certificate)
    (hf : ∀ c, height (f c) ≤ height c.val ∧ denote (f c) = denote c.val) :
    height (.sequence (children.attach.map f)) ≤ height (.sequence children) ∧
      denote (.sequence (children.attach.map f)) = denote (.sequence children) := by
  exact ⟨Nat.add_le_add_right
      (childrenHeight_le _ _ (fun c hc =>
        let ⟨child, _, heq⟩ := List.mem_map.mp hc
        heq ▸ Nat.le_trans (hf child).1
          (height_le_childrenHeight children child.val child.property))) 1,
    (denoteChildren_eq_flatten_map _).trans
      ((congrArg List.flatten
        (List.map_map.trans
          ((List.map_congr_left (fun child _ => (hf child).2)).trans List.attach_map_val))).trans
        (denoteChildren_eq_flatten_map children).symm)⟩

theorem child_height_lt (children : List Certificate) (child : Certificate)
    (hmem : child ∈ children) : height child < height (.sequence children) := by
  exact Nat.lt_succ_of_le (height_le_childrenHeight children child hmem)

/-- This recursion is justified after applying an abstract helper; the result
    need not be a syntactic subterm of its parent. -/
def normalize (helper : Preprocessor) (c : Certificate) : Certificate :=
  match c with
  | .event label => .event label
  | .sequence children =>
      .sequence (children.attach.map fun child => normalize helper (helper.run child.val))
  | .repeat count body => .repeat count (normalize helper (helper.run body))
termination_by height c
decreasing_by
  · exact Nat.lt_of_le_of_lt (helper.height_le child.val)
      (child_height_lt children child.val child.property)
  · exact Nat.lt_succ_of_le (helper.height_le body)

theorem normalize_correct (helper : Preprocessor) (c : Certificate) :
    height (normalize helper c) ≤ height c ∧ denote (normalize helper c) = denote c := by
  fun_induction normalize helper c
  case case2 children ih =>
    exact sequence_contract children (fun child => normalize helper (helper.run child.val))
      (fun child => ⟨Nat.le_trans (ih child).1 (helper.height_le child.val),
        (ih child).2.trans (helper.denote_eq child.val)⟩)
  case case3 count body ih =>
    exact ⟨Nat.add_le_add_right (Nat.le_trans ih.1 (helper.height_le body)) 1,
      congrArg (repeatEvents count) (ih.2.trans (helper.denote_eq body))⟩
  case case1 label => exact ⟨Nat.le_refl _, rfl⟩

/-- The identity control contains no size inspection. -/
def identityPreprocessor : Preprocessor where
  run := id
  height_le := fun c => Nat.le_refl (height c)
  denote_eq := fun _ => rfl

/-- Remove one neutral root wrapper. It is separately checked before use by the
    traversal, whose definition and proofs remain abstract in the helper. -/
def removeNeutralRoot : Certificate → Certificate
  | .sequence [child] => child
  | .repeat 0 _ => .sequence []
  | .repeat 1 body => body
  | c => c

theorem removeNeutralRoot_contract (c : Certificate) :
    height (removeNeutralRoot c) ≤ height c ∧ denote (removeNeutralRoot c) = denote c := by
  fun_cases removeNeutralRoot c
  all_goals simp [height, childrenHeight, denote, denoteChildren, repeatEvents]

def neutralPreprocessor : Preprocessor where
  run := removeNeutralRoot
  height_le := fun c => (removeNeutralRoot_contract c).1
  denote_eq := fun c => (removeNeutralRoot_contract c).2

/-- A finite height-bounded view. The number is ordinary host data, and only
    helpers lifted from a single raw `Preprocessor` are claimed uniform below. -/
def SizedCertificate (bound : Nat) := { c : Certificate // height c ≤ bound }

def eraseSized {bound : Nat} (c : SizedCertificate bound) : Certificate := c.val

def liftPreprocessor (helper : Preprocessor) {bound : Nat}
    (c : SizedCertificate bound) : SizedCertificate bound :=
  ⟨helper.run c.val, Nat.le_trans (helper.height_le c.val) c.property⟩

def normalizeSized (helper : Preprocessor) {bound : Nat}
    (c : SizedCertificate bound) : SizedCertificate bound :=
  ⟨normalize helper c.val, Nat.le_trans (normalize_correct helper c.val).1 c.property⟩

theorem liftPreprocessor_erase (helper : Preprocessor) {bound : Nat}
    (c : SizedCertificate bound) :
    eraseSized (liftPreprocessor helper c) = helper.run (eraseSized c) := rfl

theorem normalizeSized_erase (helper : Preprocessor) {bound : Nat}
    (c : SizedCertificate bound) :
    eraseSized (normalizeSized helper c) = normalize helper (eraseSized c) := rfl

/-- Admissible annotation changes do not affect the helper's erased behavior.
    This theorem concerns the explicitly lifted interface, not arbitrary Π Nat. -/
theorem liftPreprocessor_uniform (helper : Preprocessor) {i j : Nat}
    (c : SizedCertificate i) (d : SizedCertificate j) (h : eraseSized c = eraseSized d) :
    eraseSized (liftPreprocessor helper c) = eraseSized (liftPreprocessor helper d) :=
  congrArg helper.run h

theorem normalizeSized_uniform (helper : Preprocessor) {i j : Nat}
    (c : SizedCertificate i) (d : SizedCertificate j) (h : eraseSized c = eraseSized d) :
    eraseSized (normalizeSized helper c) = eraseSized (normalizeSized helper d) :=
  congrArg (normalize helper) h

/-- Source evidence erases to the raw certificate AST, whose endpoint is its
    finite event denotation. This is not a native machine-cost theorem. -/
theorem normalizeSized_denote (helper : Preprocessor) {bound : Nat}
    (c : SizedCertificate bound) :
    denote (eraseSized (normalizeSized helper c)) = denote (eraseSized c) :=
  (normalize_correct helper c.val).2

/-- Ordinary dependent quantification can inspect the bound and change the
    erased syntax, even while preserving the bound and event denotation. -/
def sizeInspectingHelper {bound : Nat} (c : SizedCertificate bound) : SizedCertificate bound :=
  if h : height c.val + 1 ≤ bound then ⟨.repeat 1 c.val, h⟩ else c

theorem sizeInspectingHelper_denote {bound : Nat} (c : SizedCertificate bound) :
    denote (eraseSized (sizeInspectingHelper c)) = denote (eraseSized c) := by
  by_cases h : height c.val + 1 ≤ bound
  all_goals simp [sizeInspectingHelper, h, eraseSized, denote, repeatEvents]

def zeroAnnotatedEvent : SizedCertificate 0 := ⟨.event .inspect, Nat.zero_le _⟩
def oneAnnotatedEvent : SizedCertificate 1 := ⟨.event .inspect, Nat.zero_le _⟩

theorem annotations_erase_eq : eraseSized zeroAnnotatedEvent = eraseSized oneAnnotatedEvent := rfl

theorem ordinary_size_family_not_uniform :
    eraseSized (sizeInspectingHelper zeroAnnotatedEvent) ≠
      eraseSized (sizeInspectingHelper oneAnnotatedEvent) :=
  fun h => Certificate.noConfusion h

/-- Constructor equations are recorded propositionally for this well-founded
    translation, including open variables and an opaque helper parameter. -/
theorem normalize_sequence (helper : Preprocessor) (children : List Certificate) :
    normalize helper (.sequence children) =
      .sequence (children.attach.map fun child => normalize helper (helper.run child.val)) := by
  exact normalize.eq_2 helper children

theorem normalize_repeat (helper : Preprocessor) (count : Nat) (body : Certificate) :
    normalize helper (.repeat count body) = .repeat count (normalize helper (helper.run body)) := by
  exact normalize.eq_3 helper count body

mutual
  def syntaxNodes : Certificate → Nat
    | .event _ => 1
    | .sequence children => childrenNodes children + 1
    | .repeat _ body => syntaxNodes body + 1

  def childrenNodes : List Certificate → Nat
    | [] => 0
    | child :: rest => syntaxNodes child + childrenNodes rest
end

/-- Canonical binary digits, with zero encoded by one bit. This is a counter
    metric, not a machine allocation or complete serialization-size claim. -/
def counterBits (count : Nat) : Nat := if count = 0 then 1 else Nat.log2 count + 1

mutual
  def counterBitTotal : Certificate → Nat
    | .event _ => 0
    | .sequence children => childrenCounterBits children
    | .repeat count body => counterBits count + counterBitTotal body

  def childrenCounterBits : List Certificate → Nat
    | [] => 0
    | child :: rest => counterBitTotal child + childrenCounterBits rest
end

mutual
  def expandedEventCount : Certificate → Nat
    | .event _ => 1
    | .sequence children => childrenEventCount children
    | .repeat count body => count * expandedEventCount body

  def childrenEventCount : List Certificate → Nat
    | [] => 0
    | child :: rest => expandedEventCount child + childrenEventCount rest
end

theorem repeatEvents_length : ∀ (count : Nat) (events : List Event),
    (repeatEvents count events).length = count * events.length
  | 0, events => (Nat.zero_mul events.length).symm
  | count + 1, events =>
      (List.length_append ..).trans
        ((congrArg (events.length + ·) (repeatEvents_length count events)).trans
          ((Nat.add_comm _ _).trans (Nat.succ_mul count events.length).symm))

mutual
  theorem denote_length : ∀ c : Certificate, (denote c).length = expandedEventCount c
    | .event _ => rfl
    | .sequence children => denoteChildren_length children
    | .repeat count body => (repeatEvents_length count (denote body)).trans
        (congrArg (count * ·) (denote_length body))

  theorem denoteChildren_length : ∀ children : List Certificate,
      (denoteChildren children).length = childrenEventCount children
    | [] => rfl
    | child :: rest => (List.length_append ..).trans
        ((congrArg (· + (denoteChildren rest).length) (denote_length child)).trans
          (congrArg (expandedEventCount child + ·) (denoteChildren_length rest)))
end

theorem normalize_expandedEventCount (helper : Preprocessor) (c : Certificate) :
    expandedEventCount (normalize helper c) = expandedEventCount c :=
  (denote_length (normalize helper c)).symm.trans
    ((congrArg List.length (normalize_correct helper c).2).trans (denote_length c))

/-- A finite input family; metrics can inspect huge repeat counters without
    materializing the denoted event list. -/
def fixture : Nat → Nat → Certificate
  | 0, _ => .event .pivot
  | depth + 1, count => .sequence [
      .repeat 1 (.event .inspect),
      .repeat count (fixture depth count),
      .sequence []]

end Mugda2.Experiments.SizedCertificates
