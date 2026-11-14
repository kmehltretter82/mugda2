import Init

/-!
A finite first-order constructor-pattern coverage kernel.  This module does not
model dependent refinements, size patterns, dot patterns, or legacy environments.
Its positive certificates are justified against finite, signature-typed trees.
-/
namespace Mugda2.Coverage

abbrev SortId := Nat
abbrev Tag := Nat

structure Constructor where
  tag : Tag
  result : SortId
  args : List SortId

abbrev Signature := List Constructor

inductive Value where
  | con : Tag → List Value → Value

inductive Pattern where
  | wild : Pattern
  | con : Tag → List Pattern → Pattern

abbrev Row := List Pattern
abbrev Matrix := List Row

mutual
  inductive HasType (sig : Signature) : Value → SortId → Prop where
    | con (c : Constructor) (hc : c ∈ sig) (hs : ArgsTyped sig vs c.args) :
        HasType sig (.con c.tag vs) c.result
  inductive ArgsTyped (sig : Signature) : List Value → List SortId → Prop where
    | nil : ArgsTyped sig [] []
    | cons : HasType sig v s → ArgsTyped sig vs ss → ArgsTyped sig (v :: vs) (s :: ss)
end

mutual
  inductive Matches : Pattern → Value → Prop where
    | wild : Matches .wild v
    | con : MatchesRow ps vs → Matches (.con tag ps) (.con tag vs)
  inductive MatchesRow : Row → List Value → Prop where
    | nil : MatchesRow [] []
    | cons : Matches p v → MatchesRow ps vs → MatchesRow (p :: ps) (v :: vs)
end

mutual
  def matchesDecidable (p : Pattern) (v : Value) : Decidable (Matches p v) := by
    cases p with
    | wild => exact isTrue .wild
    | con tag ps =>
      cases v with
      | con tag' vs =>
        if htag : tag = tag' then
          subst tag'
          exact match matchesRowDecidable ps vs with
            | isTrue h => isTrue (.con h)
            | isFalse h => isFalse (fun | .con hm => h hm)
        else
          apply isFalse
          intro hm
          cases hm
          exact htag rfl
  termination_by sizeOf p

  def matchesRowDecidable (ps : Row) (vs : List Value) : Decidable (MatchesRow ps vs) := by
    cases ps with
    | nil =>
      cases vs with
      | nil => exact isTrue .nil
      | cons v vs => exact isFalse (fun h => nomatch h)
    | cons p ps =>
      cases vs with
      | nil => exact isFalse (fun h => nomatch h)
      | cons v vs =>
        exact match matchesDecidable p v, matchesRowDecidable ps vs with
          | isTrue h, isTrue hs => isTrue (.cons h hs)
          | isFalse h, _ => isFalse (fun | .cons hm _ => h hm)
          | _, isFalse hs => isFalse (fun | .cons _ hm => hs hm)
  termination_by sizeOf ps
end

instance (p : Pattern) (v : Value) : Decidable (Matches p v) :=
  matchesDecidable p v

instance (ps : Row) (vs : List Value) : Decidable (MatchesRow ps vs) :=
  matchesRowDecidable ps vs


def Hits (matrix : Matrix) (vs : List Value) : Prop :=
  ∃ row, row ∈ matrix ∧ MatchesRow row vs

private def hitsDecidable (matrix : Matrix) (vs : List Value) : Decidable (Hits matrix vs) :=
  match matrix with
  | [] => isFalse (fun ⟨_, h, _⟩ => nomatch h)
  | row :: rows =>
      match matchesRowDecidable row vs, hitsDecidable rows vs with
      | isTrue h, _ => isTrue ⟨row, .head _, h⟩
      | _, isTrue ht => isTrue (match ht with
          | ⟨r, hr, hm⟩ => ⟨r, .tail _ hr, hm⟩)
      | isFalse h, isFalse hs => isFalse (fun ⟨_, hr, hm⟩ => match hr with
          | .head _ => h hm
          | .tail _ ht => hs ⟨_, ht, hm⟩)

instance (matrix : Matrix) (vs : List Value) : Decidable (Hits matrix vs) :=
  hitsDecidable matrix vs

private def nilRowDecidable (matrix : Matrix) : Decidable ([] ∈ matrix) :=
  match matrix with
  | [] => isFalse (fun h => nomatch h)
  | [] :: _ => isTrue (.head _)
  | (_ :: _) :: rows => match nilRowDecidable rows with
      | isTrue h => isTrue (.tail _ h)
      | isFalse h => isFalse (fun hm => match hm with
          | .tail _ ht => h ht)

def Covers (sig : Signature) (sorts : List SortId) (matrix : Matrix) : Prop :=
  ∀ vs, ArgsTyped sig vs sorts → Hits matrix vs

def specializeRow (c : Constructor) : Row → Option Row
  | [] => none
  | .wild :: ps => some (List.replicate c.args.length .wild ++ ps)
  | .con tag qs :: ps =>
      if tag = c.tag ∧ qs.length = c.args.length then some (qs ++ ps) else none

def specialize (c : Constructor) (matrix : Matrix) : Matrix :=
  matrix.filterMap (specializeRow c)

def defaultRow : Row → Option Row
  | .wild :: ps => some ps
  | _ => none

def defaults (matrix : Matrix) : Matrix := matrix.filterMap defaultRow

private theorem args_length (h : ArgsTyped sig vs ss) : vs.length = ss.length :=
  match h with
  | .nil => rfl
  | .cons _ ht => congrArg Nat.succ (args_length ht)

private theorem matches_split (h : MatchesRow (ps ++ qs) (vs ++ ws))
    (hlen : ps.length = vs.length) : MatchesRow ps vs ∧ MatchesRow qs ws :=
  match ps, vs, hlen, h with
  | [], [], _, h => ⟨.nil, h⟩
  | [], _ :: _, hlen, _ => nomatch hlen
  | _ :: _, [], hlen, _ => nomatch hlen
  | _ :: _, _ :: _, hlen, .cons hp ht =>
      let split := matches_split ht (Nat.succ.inj hlen)
      ⟨.cons hp split.1, split.2⟩

private theorem specializeRow_sound (h : specializeRow c row = some row')
    (hm : MatchesRow row' (args ++ tail)) (hlen : args.length = c.args.length) :
    MatchesRow row (.con c.tag args :: tail) := by
  cases row with
  | nil => exact nomatch h
  | cons p ps =>
      cases p with
      | wild =>
          exact .cons .wild (matches_split ((Option.some.inj h).symm ▸ hm)
            (List.length_replicate.trans hlen.symm)).2
      | con tag qs =>
          simp only [specializeRow] at h
          split at h
          next hc =>
            exact (congrArg (fun t => MatchesRow (.con t qs :: ps)
              (.con c.tag args :: tail)) hc.1).mpr
              (let split := matches_split ((Option.some.inj h).symm ▸ hm)
                (hc.2.trans hlen.symm)
               .cons (.con split.1) split.2)
          next _ => exact nomatch h

private theorem specialize_sound (h : Hits (specialize c matrix) (args ++ tail))
    (hlen : args.length = c.args.length) : Hits matrix (.con c.tag args :: tail) :=
  match h with
  | ⟨_, hrow', hm⟩ =>
      match List.mem_filterMap.mp hrow' with
      | ⟨row, hrow, hs⟩ => ⟨row, hrow, specializeRow_sound hs hm hlen⟩

private theorem defaults_sound (h : Hits (defaults matrix) tail) :
    Hits matrix (v :: tail) :=
  match h with
  | ⟨_, hrow', hm⟩ =>
      match List.mem_filterMap.mp hrow' with
      | ⟨[], _, hs⟩ => nomatch hs
      | ⟨.wild :: ps, hrow, hs⟩ =>
          ⟨.wild :: ps, hrow, .cons .wild ((Option.some.inj hs).symm ▸ hm)⟩
      | ⟨.con _ _ :: _, _, hs⟩ => nomatch hs

private theorem args_append (h₁ : ArgsTyped sig vs ss) (h₂ : ArgsTyped sig ws ts) :
    ArgsTyped sig (vs ++ ws) (ss ++ ts) :=
  match h₁ with
  | .nil => h₂
  | .cons hv ht => .cons hv (args_append ht h₂)

private theorem args_split (ss : List SortId) (h : ArgsTyped sig vs (ss ++ ts)) :
    ArgsTyped sig (vs.take ss.length) ss ∧ ArgsTyped sig (vs.drop ss.length) ts :=
  match ss, vs, h with
  | [], _, h => ⟨.nil, h⟩
  | _ :: _, _ :: _, .cons hv ht =>
      let split := args_split _ ht
      ⟨.cons hv split.1, split.2⟩

private theorem matches_nil (h : MatchesRow row []) : row = [] :=
  match h with
  | .nil => rfl

/-- A checked set closed under construction contains the sort of every finite value. -/
def SortClosed (sig : Signature) (live : List SortId) : Prop :=
  ∀ c, c ∈ sig → (∀ s, s ∈ c.args → s ∈ live) → c.result ∈ live

def EmptySort (sig : Signature) (sort : SortId) : Prop :=
  ∀ v, ¬ HasType sig v sort

mutual
  private theorem typed_in_closed (closed : SortClosed sig live) (h : HasType sig v s) :
      s ∈ live :=
    match h with
    | .con c hc ha => closed c hc (args_in_closed closed ha)
  private theorem args_in_closed (closed : SortClosed sig live) (h : ArgsTyped sig vs ss) :
      ∀ s, s ∈ ss → s ∈ live :=
    match h with
    | .nil => fun _ hs => nomatch hs
    | .cons hv ht => fun _ hs => match hs with
        | .head _ => typed_in_closed closed hv
        | .tail _ hs' => args_in_closed closed ht _ hs'
end

/-- Certificates are independent of the implementation's fuel and search order. -/
inductive Certificate (sig : Signature) : List SortId → Matrix → Prop where
  | nil (h : [] ∈ matrix) : Certificate sig [] matrix
  | default (h : Certificate sig ss (defaults matrix)) : Certificate sig (s :: ss) matrix
  | split (branches : ∀ c, c ∈ sig → c.result = s →
      Certificate sig (c.args ++ ss) (specialize c matrix)) :
      Certificate sig (s :: ss) matrix
  | empty (h : EmptySort sig s) : Certificate sig (s :: ss) matrix

theorem Certificate.sound (certificate : Certificate sig sorts matrix) :
    Covers sig sorts matrix := by
  induction certificate with
  | nil h => exact fun _ typed => match typed with
      | .nil => ⟨[], h, .nil⟩
  | default h ih => exact fun _ typed => match typed with
      | .cons _ htail => defaults_sound (ih _ htail)
  | split branches ih =>
      intro vs typed
      cases typed with
      | cons hv htail =>
          cases hv with
          | con c hc hargs =>
              exact specialize_sound (ih c hc rfl _ (args_append hargs htail)) (args_length hargs)
  | empty h => exact fun _ typed => match typed with
      | .cons hv _ => (h _ hv).elim

/-- Unknown is distinct from a demonstrated missing constructor tuple. -/
inductive UnknownReason where
  | fuelExhausted
  | inhabitationUndecided

/-- Both definitive outcomes carry evidence checked by the kernel. -/
inductive Result (sig : Signature) (sorts : List SortId) (matrix : Matrix) where
  | covered (certificate : Certificate sig sorts matrix)
  | missing (values : List Value) (typed : ArgsTyped sig values sorts)
      (unmatched : ¬ Hits matrix values)
  | unknown (reason : UnknownReason)

private instance (sig : Signature) (live : List SortId) : Decidable (SortClosed sig live) :=
  show Decidable (∀ c, c ∈ sig → (∀ s, s ∈ c.args → s ∈ live) → c.result ∈ live) from
    inferInstance

private def liveStep (sig : Signature) (live : List SortId) : List SortId :=
  sig.foldr (fun c acc => if (∀ s, s ∈ c.args → s ∈ live) then c.result :: acc else acc) live

private def liveApprox (sig : Signature) : Nat → List SortId
  | 0 => []
  | n + 1 => liveStep sig (liveApprox sig n)

private def emptyAt (sig : Signature) (live : List SortId)
    (closed : Option (PLift (SortClosed sig live))) (s : SortId) :
    Option (PLift (EmptySort sig s)) :=
  match closed with
  | none => none
  | some hc =>
      if hn : s ∉ live then
        some ⟨fun _ hv => hn (typed_in_closed hc.down hv)⟩
      else none

private def inhabitArgs (sig : Signature)
    (get : ∀ s, Option {v : Value // HasType sig v s}) :
    (ss : List SortId) → Option {vs : List Value // ArgsTyped sig vs ss}
  | [] => some ⟨[], .nil⟩
  | s :: ss => match get s, inhabitArgs sig get ss with
      | some v, some vs => some ⟨v.val :: vs.val, .cons v.property vs.property⟩
      | _, _ => none

private def inhabit (fuel : Nat) (sig : Signature) (s : SortId) :
    Option {v : Value // HasType sig v s} :=
  match fuel with
  | 0 => none
  | n + 1 => sig.attach.findSome? (fun c =>
      if h : c.val.result = s then
        match inhabitArgs sig (inhabit n sig) c.val.args with
        | some vs => some ⟨.con c.val.tag vs.val, h ▸ HasType.con c.val c.property vs.property⟩
        | none => none
      else none)

private inductive BranchResult (sig : Signature) (s : SortId) (ss : List SortId)
    (matrix : Matrix) (cs : List Constructor) where
  | covered (certificates : ∀ c, c ∈ cs → c.result = s →
      Certificate sig (c.args ++ ss) (specialize c matrix))
  | missing (values : List Value) (typed : ArgsTyped sig values (s :: ss))
      (unmatched : ¬ Hits matrix values)
  | unknown (reason : UnknownReason)

private def checkBranches (sig : Signature)
    (search : ∀ sorts matrix, Result sig sorts matrix)
    (s : SortId) (ss : List SortId) (matrix : Matrix) :
    (cs : List Constructor) → (∀ c, c ∈ cs → c ∈ sig) → BranchResult sig s ss matrix cs
  | [], _ => .covered (fun _ h => nomatch h)
  | c :: cs, subset =>
      if heq : c.result = s then
        match search (c.args ++ ss) (specialize c matrix) with
        | .covered hc =>
            match checkBranches sig search s ss matrix cs
                (fun c' hm => subset c' (.tail _ hm)) with
            | .covered ht => .covered (fun c' hm hs => match hm with
                | .head _ => hc
                | .tail _ htail => ht c' htail hs)
            | .missing values typed unmatched => .missing values typed unmatched
            | .unknown reason => .unknown reason
        | .missing values typed _ =>
            let split := args_split c.args typed
            let full := Value.con c.tag (values.take c.args.length) ::
              values.drop c.args.length
            if hm : Hits matrix full then .unknown .inhabitationUndecided
            else .missing full
              (.cons (heq ▸ HasType.con c (subset c (.head _)) split.1) split.2) hm
        | .unknown reason => .unknown reason
      else
        match checkBranches sig search s ss matrix cs
            (fun c' hm => subset c' (.tail _ hm)) with
        | .covered ht => .covered (fun c' hm hs => match hm with
            | .head _ => (heq hs).elim
            | .tail _ htail => ht c' htail hs)
        | .missing values typed unmatched => .missing values typed unmatched
        | .unknown reason => .unknown reason

private def checkWith (fuel : Nat) (sig : Signature) (live : List SortId)
    (closed : Option (PLift (SortClosed sig live))) (sorts : List SortId)
    (matrix : Matrix) : Result sig sorts matrix :=
  match fuel with
  | 0 => .unknown .fuelExhausted
  | n + 1 =>
      match sorts with
      | [] =>
          let _ : Decidable ([] ∈ matrix) := nilRowDecidable matrix
          if h : [] ∈ matrix then .covered (.nil h)
          else .missing [] .nil (fun ⟨_, hr, hm⟩ => h (matches_nil hm ▸ hr))
      | s :: ss =>
          match emptyAt sig live closed s with
          | some empty => .covered (.empty empty.down)
          | none =>
              match checkWith n sig live closed ss (defaults matrix) with
              | .covered hc => .covered (.default hc)
              | _ =>
                  match matrix with
                  | [] =>
                      match inhabitArgs sig (inhabit (min (n + 1) (sig.length + 1)) sig)
                          (s :: ss) with
                      | some vs => .missing vs.val vs.property (fun ⟨_, h, _⟩ => nomatch h)
                      | none => .unknown .inhabitationUndecided
                  | row :: rows =>
                      match checkBranches sig (checkWith n sig live closed) s ss (row :: rows) sig
                          (fun _ h => h) with
                      | .covered branches => .covered (.split branches)
                      | .missing values typed unmatched => .missing values typed unmatched
                      | .unknown reason => .unknown reason

/--
Bounded first-order coverage. Positive answers contain a certificate; negative
answers contain a finite signature-typed unmatched tuple. Failed inhabitation
search never establishes that a constructor has an inhabitant. A checked closed
set can certify even recursively empty inductive sorts. Exhaustion stays unknown.
-/
def check (fuel : Nat) (sig : Signature) (sorts : List SortId) (matrix : Matrix) :
    Result sig sorts matrix :=
  let live := liveApprox sig (sig.length + 1)
  let closed := if h : SortClosed sig live then some (PLift.up h) else none
  checkWith fuel sig live closed sorts matrix

/-- The public acceptance bit can only be true for a checked certificate. -/
def Result.isCovered : Result sig sorts matrix → Bool
  | .covered _ => true
  | _ => false

theorem Result.sound (result : Result sig sorts matrix) (h : result.isCovered = true) :
    Covers sig sorts matrix :=
  match result, h with
  | .covered certificate, _ => certificate.sound
  | .missing _ _ _, h => nomatch h
  | .unknown _, h => nomatch h

/-- Every accepted check covers all finite signature-typed value vectors. -/
theorem check_sound (h : (check fuel sig sorts matrix).isCovered = true) :
    Covers sig sorts matrix :=
  Result.sound (check fuel sig sorts matrix) h

end Mugda2.Coverage
