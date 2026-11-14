/-
  Mugda/Metatheory.lean
  =====================
  Structural component metatheorems imported from Mugda b0c5b53, with typed
  error statements adapted to the M1 checker. Matching/erasure refinements are
  ported from Mugda 919465fdb995245f395f18423eaf31729fa8cea6. Closed native-backed verification
  facts are runtime tests in Mugda2.Regression, not theorem declarations here.
  These component results do not establish end-to-end checker soundness.
-/

import Mugda2.Legacy.Core
import Mugda2.Legacy.Soundness

namespace MugdaCore

/-! ## 0. Monad Unfolding Lemmas for `runTypeCheck` -/

@[simp] theorem runTypeCheck_pure (st : TCState) (a : α) :
    runTypeCheck st (pure a) = .ok (a, st) := rfl

@[simp] theorem runTypeCheck_bind (st : TCState) (m : TypeCheck α) (f : α → TypeCheck β) :
    runTypeCheck st (m >>= f) =
      match runTypeCheck st m with
      | .error err => .error err
      | .ok (a, st') => runTypeCheck st' (f a) := by
  unfold runTypeCheck StateT.run
  change Except.bind (m st) (fun x => f x.1 x.2) = _
  cases m st <;> rfl

/-! ## 1. Size Subtyping, Tower Laws & Erasure Metatheorems (Pillars II & III) -/

/-- **Theorem 1 (Runtime Size Idempotence at `#`)**:
    In `MugdaCore.sinfty` (`Value.hs` line 130), `$ # = #`. -/
theorem sinfty_infty : sinfty .VInfty = .VInfty := rfl

/-- **Theorem 2 (`completePatterns` Rejects `SuccP`)**:
    The ported `cp` checker rejects any `SuccP` pattern immediately (`Completness.hs` line 15). -/
theorem cp_succP_false (p : Pattern) : cp (.SuccP p) = false := rfl

/-- **Theorem 3 (`leqSize` Reflexivity & Top Element `#`)**:
    For every generic size variable `VGen k` and `#` (`VInfty`), `leqSize` succeeds. -/
theorem leqSize_infty (v : Val) (st : TCState) :
    runTypeCheck st (leqSize v .VInfty) = .ok ((), st) := rfl

theorem leqSize_gen_refl (k : Nat) (st : TCState) :
    runTypeCheck st (leqSize (.VGen k) (.VGen k)) = .ok ((), st) :=
  congrArg (runTypeCheck st)
    (ite_eq_left (show decide (k = k) = true from decide_eq_true rfl))

/-- **Theorem 4 (`leqSize` Unfolding Laws under `$` and Arbitrary `$^n` Towers)** -/
theorem leqSize_succ_gen (k : Nat) (v2 : Val) :
    leqSize (.VGen k) (.VSucc v2) = leqSize (.VGen k) v2 := rfl

theorem leqSize_succ_both (v1 v2 : Val) :
    leqSize (.VSucc v1) (.VSucc v2) = leqSize v1 v2 := rfl

/-- Iterated successor value `$^n v`. -/
def iterVSucc : Nat → Val → Val
  | 0,     v => v
  | n + 1, v => .VSucc (iterVSucc n v)

theorem leqSize_iterVSucc_gen (n k : Nat) (v : Val) :
    leqSize (.VGen k) (iterVSucc n v) = leqSize (.VGen k) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iterVSucc
    rw [leqSize_succ_gen, ih]

theorem leqSize_iterVSucc_both (n : Nat) (v1 v2 : Val) :
    leqSize (iterVSucc n v1) (iterVSucc n v2) = leqSize v1 v2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iterVSucc
    rw [leqSize_succ_both, ih]

theorem inst_succ_infty (fuel m : Nat) (flex : List Nat) (v : Val) :
    inst (fuel + 1) m flex (.VSucc v) .VInfty = inst fuel m flex v .VInfty := rfl

/-- **Theorem 5 (Universal `$^n` Tower Stripping in `inst` against `#`)**:
    Unifying `$^n v` with `#` (`.VInfty`) strips any finite number `n` of
    `.VSucc` constructors and reduces to unifying `v` with `.VInfty`. -/
theorem inst_iterVSucc_infty (n fuel m : Nat) (flex : List Nat) (v : Val) :
    inst (fuel + n) m flex (iterVSucc n v) .VInfty = inst fuel m flex v .VInfty := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h_add : fuel + (n + 1) = (fuel + n) + 1 := Nat.add_assoc fuel n 1
    rw [h_add, iterVSucc, inst_succ_infty, ih]

/-- **Theorem 6 (Size Erasure Invariance of `DotP` Matching)**:
    For any `.DotP e` pattern, `matchPat` never inspects whether the runtime value
    is a finite successor `.VSucc v` or erased `.VInfty` (`#`). -/
theorem matchPat_dotP_erased (fuel : Nat) (env : Env) (e : Expr) (v1 v2 : Val) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v1) =
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v2) := rfl

/-- **Theorem 7 (Tightness of Bug 5 Fix — `SuccP` Breaks Runtime Size Erasure)**:
    If a clause were allowed to match on a successor size pattern `.SuccP (.VarP "i")`
    (which was permitted when `completeFun _ = True` in Mugda 2008), then matching against
    the un-erased size `.VSucc (.VGen 0)` binds `"i" ↦ .VGen 0`, whereas matching against
    its `#`-erasure `.VInfty` binds `"i" ↦ .VInfty`!
    This proves why `completePatterns` (`cp (.SuccP _) = false`) is necessary for size erasure. -/
theorem succP_breaks_size_erasure (st : TCState) :
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) (.VSucc (.VGen 0))) =
      .ok (.matched [("i", .VGen 0)], st) ∧
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) .VInfty) =
      .ok (.matched [("i", .VInfty)], st) ∧
    (MatchResult.matched [("i", Val.VGen 0)] ≠ MatchResult.matched [("i", Val.VInfty)]) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  injection h with hlist
  injection hlist with hhead _
  injection hhead with _ hv
  contradiction

/-! ## 2. Universal Size-Erasure Commutation for Complete Inductive Patterns (Pillar III) -/

/- Inductive patterns accepted by `cp` (no `.SuccP`, and all constructors `.ConP .Ind`). -/
mutual
  def isIndCompletePat : Pattern → Bool
    | .VarP _         => true
    | .DotP _         => true
    | .ConP .Ind _ pl => isIndCompletePatList pl
    | _               => false

  def isIndCompletePatList : List Pattern → Bool
    | []      => true
    | p :: pl => isIndCompletePat p && isIndCompletePatList pl
end

mutual
  theorem isIndCompletePat_imp_cp (p : Pattern) (h : isIndCompletePat p = true) :
      cp p = true := by
    cases p with
    | VarP _ => rfl
    | DotP _ => rfl
    | SuccP _ => contradiction
    | ConP co n pl =>
      cases co with
      | CoInd => contradiction
      | Ind =>
        unfold isIndCompletePat at h
        unfold cp
        exact isIndCompletePatList_imp_cpList pl h

  theorem isIndCompletePatList_imp_cpList (pl : List Pattern) (h : isIndCompletePatList pl = true) :
      cpList pl = true := by
    cases pl with
    | nil => rfl
    | cons p ps =>
      unfold isIndCompletePatList at h
      unfold cpList
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨isIndCompletePat_imp_cp p h.1, isIndCompletePatList_imp_cpList ps h.2⟩
end

/- Runtime size erasure on `Val`: replaces every `.VSucc v` size with `.VInfty` (`#`)
   and recursively erases sizes inside constructor applications. -/
mutual
  def eraseSizesVal : Val → Val
    | .VSucc _              => .VInfty
    | .VApp (.VCon co y) vl => .VApp (.VCon co y) (eraseSizesValList vl)
    | v                     => v

  def eraseSizesValList : List Val → List Val
    | []      => []
    | v :: vl => eraseSizesVal v :: eraseSizesValList vl
end

def eraseSizesEnv : Env → Env
  | []            => []
  | (x, v) :: env => (x, eraseSizesVal v) :: eraseSizesEnv env

theorem eraseSizesEnv_updateEnv (env : Env) (x : Name) (v : Val) :
    eraseSizesEnv (updateEnv env x v) = updateEnv (eraseSizesEnv env) x (eraseSizesVal v) := by
  unfold updateEnv
  split <;> rfl

theorem matchPat_ind_nil_vcon (fuel : Nat) (env : Env) (x : Name) (co' : Co) (y : Name) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x []) (.VCon co' y)) =
      if x == y then .ok (.matched env, st) else .ok (.mismatch, st) := by
  change runTypeCheck st (if x == y then pure (MatchResult.matched env) else pure MatchResult.mismatch) = _
  cases (x == y) <;> rfl

theorem matchPat_ind_cons_vcon (fuel : Nat) (env : Env) (x : Name) (q : Pattern) (ql : List Pattern) (co' : Co) (y : Name) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x (q :: ql)) (.VCon co' y)) =
      if x == y then .ok (.stuck, st) else .ok (.mismatch, st) := by
  change runTypeCheck st (if x == y then pure MatchResult.stuck else pure MatchResult.mismatch) = _
  cases (x == y) <;> rfl

theorem matchPat_ind_vapp_vcon (fuel : Nat) (env : Env) (x : Name) (pl : List Pattern) (co' : Co) (y : Name) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x pl) (.VApp (.VCon co' y) vl)) =
      if x == y then runTypeCheck st (matchList fuel env pl vl) else .ok (.mismatch, st) := by
  cases pl with
  | nil =>
    change runTypeCheck st (if x == y then matchList fuel env [] vl else pure MatchResult.mismatch) = _
    cases (x == y) <;> rfl
  | cons q ql =>
    change runTypeCheck st (if x == y then matchList fuel env (q :: ql) vl else pure MatchResult.mismatch) = _
    cases (x == y) <;> rfl

theorem matchList_cons (fuel : Nat) (env : Env) (p : Pattern) (pl : List Pattern) (v : Val) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchList (fuel + 1) env (p :: pl) (v :: vl)) =
      match runTypeCheck st (matchPat fuel env p v) with
      | .error err => .error err
      | .ok (m, st1) =>
        match m with
        | .matched env' => runTypeCheck st1 (matchList fuel env' pl vl)
        | .mismatch     => .ok (.mismatch, st1)
        | .stuck        => .ok (.stuck, st1) := by
  conv => lhs; unfold matchList
  rw [runTypeCheck_bind]
  cases runTypeCheck st (matchPat fuel env p v) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨m, st1⟩
    cases m <;> rfl

/- **Theorem 8 (Universal Size-Erasure Commutation for `matchPat` and `matchList`)**:
   For every pattern `p` (and pattern spine `ps`) satisfying `isIndCompletePat`,
   matching `p` against the size-erased value `eraseSizesVal v0` in `eraseSizesEnv env`
   produces the exact size-erasure of matching `p` against `v0` in `env`. -/
mutual
  theorem matchPat_eraseSizes_comm
      (fuel : Nat) (env : Env) (p : Pattern) (v0 : Val) (st : TCState)
      (hp : isIndCompletePat p = true) :
      runTypeCheck st (matchPat fuel (eraseSizesEnv env) p (eraseSizesVal v0)) =
        (runTypeCheck st (matchPat fuel env p v0)).map
          (fun (res, st') => (res.map eraseSizesEnv, st')) := by
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      cases p with
      | DotP e => rfl
      | VarP x =>
        change Except.ok (MatchResult.matched (updateEnv (eraseSizesEnv env) x (eraseSizesVal v0)), st) =
               Except.ok (MatchResult.matched (eraseSizesEnv (updateEnv env x v0)), st)
        rw [eraseSizesEnv_updateEnv]
      | SuccP p' => contradiction
      | ConP co x pl =>
        cases co with
        | CoInd => contradiction
        | Ind =>
          unfold isIndCompletePat at hp
          cases pl with
          | nil =>
            cases v0 with
            | VCon co' y =>
              unfold eraseSizesVal
              rw [matchPat_ind_nil_vcon, matchPat_ind_nil_vcon]
              cases (x == y) <;> rfl
            | VApp u vl =>
              cases u with
              | VCon co' y =>
                unfold eraseSizesVal
                rw [matchPat_ind_vapp_vcon, matchPat_ind_vapp_vcon]
                cases (x == y) with
                | false => rfl
                | true => exact matchList_eraseSizes_comm fuel' env [] vl st rfl
              | _ => rfl
            | _ => rfl
          | cons q ql =>
            cases v0 with
            | VCon co' y =>
              unfold eraseSizesVal
              rw [matchPat_ind_cons_vcon, matchPat_ind_cons_vcon]
              cases (x == y) <;> rfl
            | VApp u vl =>
              cases u with
              | VCon co' y =>
                unfold eraseSizesVal
                rw [matchPat_ind_vapp_vcon, matchPat_ind_vapp_vcon]
                cases (x == y) with
                | false => rfl
                | true => exact matchList_eraseSizes_comm fuel' env (q :: ql) vl st hp
              | _ => rfl
            | _ => rfl

  theorem matchList_eraseSizes_comm
      (fuel : Nat) (env : Env) (ps : List Pattern) (vs : List Val) (st : TCState)
      (hps : isIndCompletePatList ps = true) :
      runTypeCheck st (matchList fuel (eraseSizesEnv env) ps (eraseSizesValList vs)) =
        (runTypeCheck st (matchList fuel env ps vs)).map
          (fun (res, st') => (res.map eraseSizesEnv, st')) := by
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      cases ps with
      | nil =>
        cases vs <;> rfl
      | cons p pl =>
        cases vs with
        | nil => rfl
        | cons v vl =>
          unfold isIndCompletePatList at hps
          rw [Bool.and_eq_true] at hps
          have ih1 := matchPat_eraseSizes_comm fuel' env p v st hps.1
          unfold eraseSizesValList
          rw [matchList_cons, matchList_cons, ih1]
          cases h1 : runTypeCheck st (matchPat fuel' env p v) with
          | error err => rfl
          | ok resSt =>
            rcases resSt with ⟨m, st1⟩
            cases m with
            | mismatch => rfl
            | stuck    => rfl
            | matched env' =>
              exact matchList_eraseSizes_comm fuel' env' pl vl st1 hps.2
end

/-! ### 2B. Universal 3-Valued Multi-Clause Matching & Neutral Stuckness (`matchClause` / `matchClauses`) -/

/-- **Theorem 8a (Constructor Pattern Stuck on Neutral `.VGen`)**:
    Matching any inductive constructor pattern `.ConP .Ind x pl` against a neutral
    variable `.VGen k` returns `.stuck` (never `.mismatch`). -/
theorem matchPat_conP_vgen_stuck (fuel : Nat) (env : Env) (x : Name) (pl : List Pattern) (k : Nat) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x pl) (.VGen k)) = .ok (.stuck, st) := by
  cases pl <;> rfl

/-- **Theorem 8b (Size Successor Pattern Stuck on Neutral `.VGen`)**:
    Matching any size successor pattern `.SuccP p'` against a neutral size variable
    `.VGen k` returns `.stuck`. -/
theorem matchPat_succP_vgen_stuck (fuel : Nat) (env : Env) (p' : Pattern) (k : Nat) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.SuccP p') (.VGen k)) = .ok (.stuck, st) := rfl

theorem matchClause_cons (fuel : Nat) (env : Env) (p : Pattern) (pl : List Pattern) (rhs : Expr) (v : Val) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchClause (fuel + 1) env (p :: pl) rhs (v :: vl)) =
      match runTypeCheck st (matchPat fuel env p v) with
      | .error err => .error err
      | .ok (m, st1) =>
        match m with
        | .matched env' => runTypeCheck st1 (matchClause fuel env' pl rhs vl)
        | .mismatch     => .ok (.mismatch, st1)
        | .stuck        => .ok (.stuck, st1) := by
  conv => lhs; unfold matchClause
  rw [runTypeCheck_bind]
  cases runTypeCheck st (matchPat fuel env p v) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨m, st1⟩
    cases m <;> rfl

theorem matchClauses_cons (fuel : Nat) (pl : List Pattern) (rhs : Expr) (cl2 : List Clause) (cll : List Val) (st : TCState) :
    runTypeCheck st (matchClauses (fuel + 1) (.mk pl rhs :: cl2) cll) =
      match runTypeCheck st (matchClause fuel [] pl rhs cll) with
      | .error err => .error err
      | .ok (m, st1) =>
        match m with
        | .matched v => .ok (some v, st1)
        | .mismatch  => runTypeCheck st1 (matchClauses fuel cl2 cll)
        | .stuck     => .ok (none, st1) := by
  conv => lhs; unfold matchClauses
  rw [runTypeCheck_bind]
  cases runTypeCheck st (matchClause fuel [] pl rhs cll) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨m, st1⟩
    cases m <;> rfl

/-- A matched first clause determines the result regardless of the later clauses. -/
theorem matchClauses_matched_stops
    (fuel : Nat) (pl : List Pattern) (rhs : Expr) (tail : List Clause)
    (args : List Val) (value : Val) (st st1 : TCState)
    (h_match : runTypeCheck st (matchClause fuel [] pl rhs args) =
      .ok (.matched value, st1)) :
    runTypeCheck st (matchClauses (fuel + 1) (.mk pl rhs :: tail) args) =
      .ok (some value, st1) := by
  rw [matchClauses_cons, h_match]

/-- **Theorem 8c (Universal Stuckness Barrier in `matchClauses`)**:
    Whenever the head pattern `p` of a clause `.mk (p :: pl) rhs` is `.stuck` on the
    head argument `v`, `matchClauses` halts immediately and returns `none` without
    falling through to any subsequent catch-all clause in `cl2`. -/
theorem matchClauses_stuck_blocks_fallthrough
    (fuel : Nat) (p : Pattern) (pl : List Pattern) (rhs : Expr) (cl2 : List Clause)
    (v : Val) (vl : List Val) (st st1 : TCState)
    (h_stuck : runTypeCheck st (matchPat fuel [] p v) = .ok (.stuck, st1)) :
    runTypeCheck st (matchClauses (fuel + 2) (.mk (p :: pl) rhs :: cl2) (v :: vl)) =
      .ok (none, st1) := by
  rw [matchClauses_cons, matchClause_cons, h_stuck]

/-- **Theorem 8d (Universal Constructor Mismatch Fallthrough in `matchClauses`)**:
    Whenever the head pattern `p` of a clause `.mk (p :: pl) rhs` is a definite constructor
    `.mismatch` on `v`, `matchClauses` advances to the remaining clauses `cl2`. -/
theorem matchClauses_mismatch_advances
    (fuel : Nat) (p : Pattern) (pl : List Pattern) (rhs : Expr) (cl2 : List Clause)
    (v : Val) (vl : List Val) (st st1 : TCState)
    (h_mis : runTypeCheck st (matchPat fuel [] p v) = .ok (.mismatch, st1)) :
    runTypeCheck st (matchClauses (fuel + 2) (.mk (p :: pl) rhs :: cl2) (v :: vl)) =
      runTypeCheck st1 (matchClauses (fuel + 1) cl2 (v :: vl)) := by
  rw [matchClauses_cons, matchClause_cons, h_mis]

/-- **Theorem 8e (Constructor Clauses Never Fall Through on Neutral Variables)**:
    For any inductive constructor head pattern `.ConP .Ind x args`, any catch-all tail
    clauses `cl2`, and any neutral head argument `.VGen k`, `matchClauses` returns `none`. -/
theorem matchClauses_conP_vgen_never_falls_through
    (fuel : Nat) (x : Name) (args pl : List Pattern) (rhs : Expr) (cl2 : List Clause)
    (k : Nat) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchClauses (fuel + 3) (.mk (.ConP .Ind x args :: pl) rhs :: cl2) (.VGen k :: vl)) =
      .ok (none, st) := by
  exact matchClauses_stuck_blocks_fallthrough (fuel + 1) (.ConP .Ind x args) pl rhs cl2 (.VGen k) vl st st
    (matchPat_conP_vgen_stuck fuel [] x args k st)

/-! ## 3. Universal `nocc`, `substVal`, `checkNoccEnv` & `checkNoccDomains` Theorems (Pillar I & II) -/

/-- **Theorem 9 (`nocc` on Generic Variables)**:
    `nocc (fuel + 1) k (.VGen j) (.VGen i)` evaluates directly to `j != i`. -/
theorem nocc_vgen_eq (fuel k j i : Nat) (st : TCState) :
    runTypeCheck st (nocc (fuel + 1) k (.VGen j) (.VGen i)) = .ok (j != i, st) := rfl

theorem lookupSubst_single_of_ne (j i : Nat) (sv : Val) (h : (j != i) = true) :
    lookupSubst i [(j, sv)] = none := by
  unfold lookupSubst
  have hij : (i == j) = false := by
    rw [bne_iff_ne] at h
    exact beq_eq_false_iff_ne.mpr (Ne.symm h)
  rw [hij]
  rfl

def isNotVInfty : Val → Bool
  | .VInfty => false
  | _       => true

/-- Pure size or atomic values containing no unreduced `.VSucc .VInfty` redex. -/
def isNormSizeOrAtom : Val → Bool
  | .VSet     => true
  | .VSize    => true
  | .VInfty   => true
  | .VCon _ _ => true
  | .VDef _   => true
  | .VGen _   => true
  | .VSucc v  => isNotVInfty v && isNormSizeOrAtom v
  | _         => false

theorem substVal_vgen (fuel : Nat) (sub : Substitution) (i : Nat) (st : TCState) :
    runTypeCheck st (substVal (fuel + 1) sub (.VGen i)) =
      match lookupSubst i sub with
      | none    => .ok (.VGen i, st)
      | some v' => .ok (v', st) := by
  change runTypeCheck st
           (match lookupSubst i sub with
            | none    => pure (.VGen i)
            | some v' => pure v') = _
  cases lookupSubst i sub <;> rfl

theorem substVal_vsucc (fuel : Nat) (sub : Substitution) (v : Val) (st : TCState) :
    runTypeCheck st (substVal (fuel + 1) sub (.VSucc v)) =
      match runTypeCheck st (substVal fuel sub v) with
      | .error err => .error err
      | .ok (v1', st1) => .ok (sinfty v1', st1) := by
  conv => lhs; unfold substVal
  rw [runTypeCheck_bind]
  cases runTypeCheck st (substVal fuel sub v) <;> rfl

/-- **Theorem 10 (Universal `nocc` → `substVal` Identity Law on Size & Atomic Values)**:
    For every normalized size/atomic value `tv`, if `nocc fuel k (.VGen j) tv` succeeds with
    `true`, then substituting `j ↦ sv` via `substVal fuel [(j, sv)] tv` leaves `tv` unchanged. -/
theorem nocc_substVal_id_of_normSizeOrAtom
    (fuel k j : Nat) (sv tv : Val) (st st' : TCState)
    (hnorm : isNormSizeOrAtom tv = true)
    (hnocc : runTypeCheck st (nocc fuel k (.VGen j) tv) = .ok (true, st')) :
    runTypeCheck st (substVal fuel [(j, sv)] tv) = .ok (tv, st) ∧ st' = st := by
  induction fuel generalizing tv st st' with
  | zero => contradiction
  | succ fuel' ih =>
    cases tv with
    | VSet =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VSize =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VInfty =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VCon co n =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VDef n =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VGen i =>
      rw [nocc_vgen_eq] at hnocc
      injection hnocc with hpair
      injection hpair with hb hst
      rw [substVal_vgen, lookupSubst_single_of_ne j i sv hb]
      exact ⟨rfl, hst.symm⟩
    | VSucc v =>
      unfold isNormSizeOrAtom at hnorm
      rw [Bool.and_eq_true] at hnorm
      unfold nocc at hnocc
      have ⟨hsub, hst⟩ := ih v st st' hnorm.2 hnocc
      refine ⟨?_, hst⟩
      rw [substVal_vsucc, hsub]
      cases v <;> first | rfl | contradiction
    | VApp _ _ => contradiction
    | VPi _ _ _ _ => contradiction
    | VLam _ _ _ => contradiction

theorem checkNoccEnv_cons (fuel k j : Nat) (x : Name) (tv : TVal) (gamma : Env) (st : TCState) :
    runTypeCheck st (checkNoccEnv fuel k j ((x, tv) :: gamma)) =
      match runTypeCheck st (nocc fuel k (.VGen j) tv) with
      | .error err => .error err
      | .ok (b, st1) =>
        if b then runTypeCheck st1 (checkNoccEnv fuel k j gamma)
        else .error (.rejected .patternRefinement "unsound size refinement in pattern: size variable occurs in another pattern variable's type") := by
  conv => lhs; unfold checkNoccEnv
  rw [runTypeCheck_bind]
  cases runTypeCheck st (nocc fuel k (.VGen j) tv) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨b, st1⟩
    cases b <;> rfl

/-- **Theorem 11 (Universal Soundness of `checkNoccEnv`)**:
    If `checkNoccEnv fuel k j gamma` succeeds, then every variable binding `(x, tv)`
    in `gamma` satisfies `nocc fuel k (.VGen j) tv = true`. -/
theorem checkNoccEnv_head
    (fuel k j : Nat) (x : Name) (tv : TVal) (gamma : Env) (st st' : TCState)
    (h : runTypeCheck st (checkNoccEnv fuel k j ((x, tv) :: gamma)) = .ok ((), st')) :
    ∃ st1, runTypeCheck st (nocc fuel k (.VGen j) tv) = .ok (true, st1) ∧
           runTypeCheck st1 (checkNoccEnv fuel k j gamma) = .ok ((), st') := by
  rw [checkNoccEnv_cons] at h
  cases hn : runTypeCheck st (nocc fuel k (.VGen j) tv) with
  | error err =>
    rw [hn] at h
    contradiction
  | ok res =>
    rcases res with ⟨b, st1⟩
    rw [hn] at h
    cases b with
    | false => contradiction
    | true => exact ⟨st1, rfl, h⟩

theorem checkNoccEnv_forall_mem
    (fuel k j : Nat) (gamma : Env) (st st' : TCState)
    (h : runTypeCheck st (checkNoccEnv fuel k j gamma) = .ok ((), st'))
    (p : Name × Val) (hp : p ∈ gamma) :
    ∃ st1 st2, runTypeCheck st1 (nocc fuel k (.VGen j) p.2) = .ok (true, st2) := by
  induction gamma generalizing st with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hd with ⟨x, tv⟩
    have ⟨st1, hn, htl⟩ := checkNoccEnv_head fuel k j x tv tl st st' h
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨st, st1, hn⟩
    · exact ih st1 htl hmem

theorem checkNoccDomains_vpi (fuel k j : Nat) (x : Name) (av : TVal) (env : Env) (b : Expr) (st : TCState) :
    runTypeCheck st (checkNoccDomains (fuel + 1) k j (.VPi x av env b)) =
      match runTypeCheck st (nocc fuel k (.VGen j) av) with
      | .error err => .error err
      | .ok (ok, st1) =>
        if !ok then .error (.rejected .patternRefinement "unsound size refinement in pattern: size variable shared across multiple arguments or branches")
        else
          match runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
          | .error err => .error err
          | .ok (bv, st2) => runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv) := by
  conv => lhs; unfold checkNoccDomains
  rw [runTypeCheck_bind]
  cases runTypeCheck st (nocc fuel k (.VGen j) av) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨ok, st1⟩
    cases ok with
    | false => rfl
    | true =>
      dsimp
      change runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b >>= fun bv => checkNoccDomains fuel (k + 1) j bv) = _
      rw [runTypeCheck_bind]
      cases runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) <;> rfl

/-- **Theorem 12 (Universal Soundness of `checkNoccDomains` on Pi Telescopes)**:
    If `checkNoccDomains (fuel + 1) k j (.VPi x av env b)` succeeds, then `nocc` succeeds
    with `true` on the domain `av` and `checkNoccDomains` succeeds on the codomain `bv`. -/
theorem checkNoccDomains_pi
    (fuel k j : Nat) (x : Name) (av : TVal) (env : Env) (b : Expr) (st st' : TCState)
    (h : runTypeCheck st (checkNoccDomains (fuel + 1) k j (.VPi x av env b)) = .ok ((), st')) :
    ∃ st1 bv st2,
      runTypeCheck st (nocc fuel k (.VGen j) av) = .ok (true, st1) ∧
      runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) = .ok (bv, st2) ∧
      runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv) = .ok ((), st') := by
  rw [checkNoccDomains_vpi] at h
  cases hn : runTypeCheck st (nocc fuel k (.VGen j) av) with
  | error err =>
    rw [hn] at h
    contradiction
  | ok res =>
    rcases res with ⟨ok, st1⟩
    rw [hn] at h
    cases ok with
    | false => contradiction
    | true =>
      change (match runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
              | Except.error err => Except.error err
              | Except.ok (bv, st2) => runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv)) = Except.ok ((), st') at h
      cases hw : runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
      | error err =>
        rw [hw] at h
        contradiction
      | ok res2 =>
        rcases res2 with ⟨bv, st2⟩
        rw [hw] at h
        exact ⟨st1, bv, st2, rfl, hw, h⟩

/-! ## 4. Matrix Order `ORDER_+` Semiring, Diagonal Witness & Ordinal Soundness (Pillars I & V) -/

/-- Scalar orders `{.Lt, .Le, .Un}` (excluding `.Mat`). -/
def isScalarOrder : Order → Bool
  | .Mat _ => false
  | _      => true

/-- **Theorem 13 (Commutativity, Associativity & Distributivity of Scalar `Order` Semiring)** -/
theorem minScalar_comm (a b : Order) : minScalar a b = minScalar b a := by
  cases a <;> cases b <;> rfl

theorem minScalar_assoc (a b c : Order) :
    minScalar (minScalar a b) c = minScalar a (minScalar b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem maxScalar_comm (a b : Order) : maxScalar a b = maxScalar b a := by
  cases a <;> cases b <;> rfl

theorem maxScalar_assoc (a b c : Order)
    (ha : isScalarOrder a = true) (hb : isScalarOrder b = true) (hc : isScalarOrder c = true) :
    maxScalar (maxScalar a b) c = maxScalar a (maxScalar b c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

theorem compScalar_assoc (a b c : Order) :
    compScalar (compScalar a b) c = compScalar a (compScalar b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem compScalar_maxScalar_distrib_left (a b c : Order)
    (hb : isScalarOrder b = true) (hc : isScalarOrder c = true) :
    compScalar a (maxScalar b c) = maxScalar (compScalar a b) (compScalar a c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

theorem compScalar_maxScalar_distrib_right (a b c : Order)
    (ha : isScalarOrder a = true) (hb : isScalarOrder b = true) :
    compScalar (maxScalar a b) c = maxScalar (compScalar a c) (compScalar b c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

/-- **Theorem 14 (Bug 3b Fix — `maxO` on Two Matrices and `collapseOrder` Always Collapse to Scalars)**:
    Combining two `.Mat` values via `maxO` (or collapsing any `Order` via `collapseOrder`)
    can never produce a nested `.Mat m`. -/
theorem maxO_mat_never_mat (m1 m2 m : Matrix Order) :
    maxO (.Mat m1) (.Mat m2) ≠ .Mat m := by
  change maxScalar (collapseOrder (.Mat m1)) (collapseOrder (.Mat m2)) ≠ .Mat m
  unfold maxScalar
  split <;> intro h <;> injection h

theorem collapseOrder_never_mat (o : Order) (m : Matrix Order) :
    collapseOrder o ≠ .Mat m := by
  cases o with
  | Lt => intro h; injection h
  | Le => intro h; injection h
  | Un => intro h; injection h
  | Mat rows =>
    unfold collapseOrder
    cases rows with
    | nil => intro h; injection h
    | cons r rs =>
      cases rs with
      | nil =>
        unfold collapseRows
        cases r with
        | nil => intro h; injection h
        | cons o0 os =>
          unfold collapseElemAt
          exact collapseOrder_never_mat o0 m
      | cons r2 rs2 =>
        unfold collapseRows minScalar
        split <;> intro h <;> injection h

/-- **Theorem 15 (Universal Diagonal Witness Characterization of `isDecr` and `checkIdem`)**:
    A matrix `.Mat m` satisfies `isDecr (.Mat m) = true` if and only if there exists a
    diagonal index `k` and entry `o` at `(k, k)` of `m` such that `isDecr o = true`. -/
theorem isDecrElemAt_iff (i : Nat) (r : List Order) :
    isDecrElemAt i r = true ↔ ∃ o, getElemOpt r i = some o ∧ isDecr o = true := by
  induction r generalizing i with
  | nil =>
    unfold isDecrElemAt getElemOpt
    simp
  | cons o os ih =>
    cases i with
    | zero =>
      unfold isDecrElemAt getElemOpt
      simp
    | succ i' =>
      unfold isDecrElemAt getElemOpt
      exact ih i'

theorem isDecrRows_iff (i : Nat) (rows : List (List Order)) :
    isDecrRows i rows = true ↔
      ∃ k row o, getElemOpt rows k = some row ∧ getElemOpt row (i + k) = some o ∧ isDecr o = true := by
  induction rows generalizing i with
  | nil =>
    unfold isDecrRows getElemOpt
    simp
  | cons r rs ih =>
    unfold isDecrRows
    rw [Bool.or_eq_true, isDecrElemAt_iff, ih (i + 1)]
    constructor
    · rintro (⟨o, ho, hdecr⟩ | ⟨k, row, o, hrow, ho, hdecr⟩)
      · refine ⟨0, r, o, rfl, ?_, hdecr⟩
        simpa using ho
      · refine ⟨k + 1, row, o, hrow, ?_, hdecr⟩
        have h_add : i + (k + 1) = (i + 1) + k := by omega
        rw [h_add]
        exact ho
    · rintro ⟨k, row, o, hrow, ho, hdecr⟩
      cases k with
      | zero =>
        unfold getElemOpt at hrow
        injection hrow with hr
        subst hr
        left
        refine ⟨o, ?_, hdecr⟩
        simpa using ho
      | succ k' =>
        unfold getElemOpt at hrow
        right
        refine ⟨k', row, o, hrow, ?_, hdecr⟩
        have h_add : (i + 1) + k' = i + (k' + 1) := by omega
        rw [h_add]
        exact ho

theorem isDecr_mat_iff (m : Matrix Order) :
    isDecr (.Mat m) = true ↔
      ∃ k row o, getElemOpt m k = some row ∧ getElemOpt row k = some o ∧ isDecr o = true := by
  change isDecrRows 0 m = true ↔ _
  have h := isDecrRows_iff 0 m
  simpa [Nat.zero_add] using h

theorem checkIdem_sound (c : Call)
    (h_idem : (c == callComb c c) = true)
    (h_ok : checkIdem c = true) :
    ∃ k row o,
      getElemOpt (callComb c c).matrix k = some row ∧
      getElemOpt row k = some o ∧
      isDecr o = true := by
  change (!(c == callComb c c) || isDecr (.Mat (callComb c c).matrix)) = true at h_ok
  rw [h_idem] at h_ok
  exact (isDecr_mat_iff (callComb c c).matrix).mp h_ok

theorem checkAll_sound
    (calls : List Call) (c : Call)
    (hall : checkAll calls = true)
    (hc : c ∈ calls)
    (hidem : (c == callComb c c) = true) :
    ∃ k row o,
      getElemOpt (callComb c c).matrix k = some row ∧
      getElemOpt row k = some o ∧
      isDecr o = true := by
  unfold checkAll at hall
  rw [List.all_eq_true] at hall
  exact checkIdem_sound c hidem (hall c hc)

/-- **Theorem 16 (Semantic Soundness & Well-Foundedness of `Order` on Transfinite Ordinals `SizeOrd`)**:
    Interpreting `.Lt` as strict transfinite ordinal decrease `<`, `.Le` as `≤`, and `.Un`
    as `True` on `MugdaSoundness.SizeOrd`, `compScalar` is sound with respect to relational
    composition, `minScalar` is sound with respect to conjunction, and no infinite sequence
    of `.Lt` steps can exist. -/
def evalScalarOrd : Order → MugdaSoundness.SizeOrd → MugdaSoundness.SizeOrd → Prop
  | .Lt => (· < ·)
  | .Le => (· ≤ ·)
  | _   => fun _ _ => True

theorem compScalar_sound_sizeOrd
    (o1 o2 : Order) (α β γ : MugdaSoundness.SizeOrd)
    (h1 : evalScalarOrd o1 α β)
    (h2 : evalScalarOrd o2 β γ) :
    evalScalarOrd (compScalar o1 o2) α γ := by
  cases o1 <;> cases o2 <;> try trivial
  · -- Lt, Lt
    exact MugdaSoundness.SizeOrd.lt_trans h1 h2
  · -- Lt, Le
    exact MugdaSoundness.SizeOrd.lt_of_succ_le_of_le h1 h2
  · -- Le, Lt
    rcases h1 with hlt | rfl
    · exact MugdaSoundness.SizeOrd.lt_trans hlt h2
    · exact h2
  · -- Le, Le
    exact MugdaSoundness.SizeOrd.le_trans h1 h2

theorem minScalar_sound_sizeOrd
    (o1 o2 : Order) (α β : MugdaSoundness.SizeOrd)
    (h1 : evalScalarOrd o1 α β)
    (h2 : evalScalarOrd o2 α β) :
    evalScalarOrd (minScalar o1 o2) α β := by
  cases o1 <;> cases o2 <;> first | trivial | exact h1 | exact Or.inl h1

theorem no_infinite_decr_sizeOrd (f : Nat → MugdaSoundness.SizeOrd) :
    ¬ (∀ n, evalScalarOrd .Lt (f (n + 1)) (f n)) := by
  intro h
  have hacc : ∀ α, Acc MugdaSoundness.SizeOrd.lt α → ∀ m, f m = α → False := by
    intro α hacc
    induction hacc with
    | intro x _ ih =>
      intro m hm
      subst hm
      exact ih (f (m + 1)) (h m) (m + 1) rfl
  exact hacc (f 0) (MugdaSoundness.SizeOrd.wf_lt.apply (f 0)) 0 rfl

/-- **Theorem 17 (Bug 3a Fix — `isPurePat` Excludes `DotP` and `SuccP`)**:
    `isPurePat` returns `false` on `.DotP` and `.SuccP`, ensuring `compareExpr` never
    constructs a `Mat` matrix for sized constructors with dot-pattern size indices. -/
theorem isPurePat_dotP_false (e : Expr) : isPurePat (.DotP e) = false := rfl
theorem isPurePat_succP_false (p : Pattern) : isPurePat (.SuccP p) = false := rfl

/-- **Theorem 18 (Bug 4 Fix — `collectCallsExpr` Extracts Calls from `LLet` Bound Expressions)**:
    Every call extracted from `e1` is included in the calls extracted from `.LLet x t1 e1 e2`. -/
theorem collectCalls_llet_includes_bound
    (nl : List (Name × Nat)) (f : Name) (pl : List Pattern)
    (x : Name) (t1 e1 e2 : Expr) (c : Call)
    (hc : c ∈ collectCallsExpr nl f pl e1) :
    c ∈ collectCallsExpr nl f pl (.LLet x t1 e1 e2) := by
  unfold collectCallsExpr
  exact List.mem_append_left _ (List.mem_append_right _ hc)

end MugdaCore
