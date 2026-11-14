import Mugda2.Legacy.Core

/-!
Transactional properties of the M1 checking monad. These establish rollback
of checker state; they are not typing or semantic soundness of the legacy
language. Rejection and resource exhaustion use the same rollback mechanism.
-/

namespace MugdaCore

/-- An error handler runs from the state at entry, including every signature,
    provisional entry, warning, and search budget. -/
theorem runTypeCheck_catch_of_error (st : TCState) (m : TypeCheck α)
    (err : TCError) (recover : TCError → TypeCheck α)
    (h : runTypeCheck st m = .error err) :
    runTypeCheck st (tryCatch m recover) = runTypeCheck st (recover err) := by
  simp only [runTypeCheck, StateT.run, MonadExcept.tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch] at h ⊢
  simp only [h, Except.tryCatch]

/-- Catching either a rejection or an exhausted search restores the entry state. -/
theorem runTypeCheck_catch_rollback (st : TCState) (m : TypeCheck α)
    (err : TCError) (fallback : α) (h : runTypeCheck st m = .error err) :
    runTypeCheck st (tryCatch m (fun _ => pure fallback)) = .ok (fallback, st) :=
  runTypeCheck_catch_of_error st m err (fun _ => pure fallback) h

/-- In particular, exhaustion never commits state before recovery. -/
theorem runTypeCheck_unknown_rollback (st : TCState) (m : TypeCheck α)
    (context : String) (fallback : α)
    (h : runTypeCheck st m = .error (.outOfFuel context)) :
    runTypeCheck st (tryCatch m (fun _ => pure fallback)) = .ok (fallback, st) :=
  runTypeCheck_catch_rollback st m (.outOfFuel context) fallback h

/-- Diagnostic context preserves both the rejection category and exhaustion. -/
theorem throwTrace_error (st : TCState) (m : TypeCheck α) (err : TCError)
    (context : String) (h : runTypeCheck st m = .error err) :
    runTypeCheck st (throwTrace m context) = .error (err.withContext context) :=
  runTypeCheck_catch_of_error st m err (fun caught => throw (caught.withContext context)) h

theorem throwTrace_outOfFuel (st : TCState) (m : TypeCheck α)
    (site context : String) (h : runTypeCheck st m = .error (.outOfFuel site)) :
    runTypeCheck st (throwTrace m context) = .error (.outOfFuel (context ++ ": " ++ site)) :=
  throwTrace_error st m (.outOfFuel site) context h

theorem typeCheckDeclaration_failure_rollback (st : TCState) (fuel : Nat)
    (decl : Declaration) (err : TCError)
    (h : runTypeCheck st (typeCheckDeclaration fuel decl) = .error err) :
    runTypeCheck st (tryCatch (typeCheckDeclaration fuel decl) (fun _ => pure ())) =
      .ok ((), st) :=
  runTypeCheck_catch_rollback st (typeCheckDeclaration fuel decl) err () h

theorem typeCheckConstructor_failure_rollback (st : TCState) (fuel : Nat)
    (dataName : Name) (sized : Sized) (positive : List Pos) (tel : Telescope)
    (constructor : Constructor) (err : TCError)
    (h : runTypeCheck st (typeCheckConstructor fuel dataName sized positive tel constructor) =
      .error err) :
    runTypeCheck st (tryCatch
      (typeCheckConstructor fuel dataName sized positive tel constructor) (fun _ => pure ())) =
      .ok ((), st) :=
  runTypeCheck_catch_rollback st
    (typeCheckConstructor fuel dataName sized positive tel constructor) err () h

theorem typeCheckFuns_failure_rollback (st : TCState) (fuel : Nat) (co : Co)
    (funs : List (TypeSig × List Clause)) (err : TCError)
    (h : runTypeCheck st (typeCheckFuns fuel co funs) = .error err) :
    runTypeCheck st (tryCatch (typeCheckFuns fuel co funs) (fun _ => pure ())) =
      .ok ((), st) :=
  runTypeCheck_catch_rollback st (typeCheckFuns fuel co funs) err () h

/-- The local signature invariant: every stored function is marked checked.
    This predicate does not assert a typing or semantic soundness theorem. -/
def SigDef.Verified : SigDef → Prop
  | .FunSig _ _ _ checked => checked = true
  | _ => True

def VerifiedSignature (sig : Signature) : Prop :=
  ∀ entry ∈ sig, entry.2.Verified

theorem addSig_verified (sig : Signature) (n : Name) (entry : SigDef)
    (hsig : VerifiedSignature sig) (hentry : entry.Verified) :
    VerifiedSignature (addSig sig n entry) := by
  intro candidate hmem
  simp only [addSig, List.mem_cons, List.mem_filter] at hmem
  exact hmem.elim (fun h => h.symm ▸ hentry) (fun h => hsig candidate h.1)

/-- The actual promotion fold used by `typeCheckFuns` never introduces an
    unverified function, even if arbitrary entries occur in the staging list. -/
theorem commitProvisional_verified (staged : Signature) (accepted : Signature)
    (haccepted : VerifiedSignature accepted) :
    VerifiedSignature (commitProvisional accepted staged) := by
  induction staged generalizing accepted with
  | nil => exact haccepted
  | cons candidate rest ih =>
    apply ih
    rcases candidate with ⟨n, entry⟩
    exact match entry with
      | .FunSig c vt cl _ =>
          addSig_verified accepted n (.FunSig c vt cl true) haccepted rfl
      | .LetSig _ _ | .ConSig _ | .DataSig _ _ _ _ _ => haccepted

theorem commitProvisional_no_unverified (staged accepted : Signature)
    (haccepted : VerifiedSignature accepted) (n : Name) (co : Co)
    (type : TVal) (clauses : List Clause)
    (hmem : (n, .FunSig co type clauses false) ∈ commitProvisional accepted staged) :
    False :=
  Bool.noConfusion (commitProvisional_verified staged accepted haccepted _ hmem)

end MugdaCore
