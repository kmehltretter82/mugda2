import Mugda2.Json
import Mugda2.Legacy.Core

/-!
The M1 interface to the adapted, pinned legacy checker. Acceptance here is a
legacy algorithm result, not an M2 core typing or semantic soundness theorem.
The legacy parser has no token locations: diagnostics honestly cover the whole
UTF-8 document. More precise spans require a location-preserving frontend.
-/

namespace Mugda2

structure Budget where
  checkerFuel : Nat := 1000
  comparisonFuel : Nat := 100
  closureFuel : Nat := 100
  lexerFuel : Option Nat := none
  parserFuel : Option Nat := none
  deriving Repr, BEq

structure SourceSpan where
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq

structure Diagnostic where
  category : MugdaCore.DiagnosticCategory
  message : String
  span : SourceSpan
  deriving Repr

inductive UnknownReason where
  | outOfFuel
  | unsupportedCoverage
  deriving Repr, BEq

structure CheckUncertainty where
  reason : UnknownReason
  context : String
  span : SourceSpan
  deriving Repr

inductive CheckOutcome (α : Type) where
  | accepted (value : α)
  | rejected (diagnostic : Diagnostic)
  | unknown (uncertainty : CheckUncertainty)
  deriving Repr

def CheckOutcome.ofExcept (span : SourceSpan)
    (result : Except MugdaCore.TCError α) : CheckOutcome α :=
  match result with
  | .ok value => .accepted value
  | .error (.rejected category message) => .rejected ⟨category, message, span⟩
  | .error (.outOfFuel context) => .unknown ⟨.outOfFuel, context, span⟩
  | .error (.unsupportedCoverage context) => .unknown ⟨.unsupportedCoverage, context, span⟩

/-- Check a whole source document with independently controlled search budgets. -/
def checkSource (source : String) (budget : Budget := {}) : CheckOutcome MugdaCore.TCState :=
  CheckOutcome.ofExcept ⟨0, source.utf8ByteSize⟩ do
    let tokens ← match budget.lexerFuel with
      | none => MugdaCore.tokenize source
      | some fuel => MugdaCore.tokenizeWithFuel fuel source
    let concrete ← match budget.parserFuel with
      | none => MugdaCore.parseTokens tokens
      | some fuel => MugdaCore.parseTokensWithFuel fuel tokens
    let declarations ← MugdaCore.scopeCheck concrete
    let (_, state) ← MugdaCore.runTypeCheck
      { terminationBudget := ⟨budget.comparisonFuel, budget.closureFuel⟩ }
      (MugdaCore.typeCheckDecls budget.checkerFuel declarations)
    pure state

def diagnosticCategoryName : MugdaCore.DiagnosticCategory → String
  | .parse => "parse"
  | .scope => "scope"
  | .typeMismatch => "typeMismatch"
  | .admissibility => "admissibility"
  | .sizePatternCompleteness => "sizePatternCompleteness"
  | .termination => "termination"
  | .patternRefinement => "patternRefinement"
  | .positivity => "positivity"
  | .coverage => "coverage"

def unknownReasonName : UnknownReason → String
  | .outOfFuel => "outOfFuel"
  | .unsupportedCoverage => "unsupportedCoverage"

def SourceSpan.toJson (span : SourceSpan) : Json :=
  Json.mkObj [
    ("startByte", Mugda2.encodeJson span.startByte), ("endByte", Mugda2.encodeJson span.endByte),
    ("scope", Mugda2.encodeJson ("document" : String))]

def Budget.toJson (budget : Budget) : Json :=
  Json.mkObj [
    ("checkerFuel", Mugda2.encodeJson budget.checkerFuel),
    ("comparisonFuel", Mugda2.encodeJson budget.comparisonFuel),
    ("closureFuel", Mugda2.encodeJson budget.closureFuel),
    ("lexerFuel", Mugda2.encodeJson budget.lexerFuel),
    ("parserFuel", Mugda2.encodeJson budget.parserFuel)]

def resultJson (sourceName : String) (budget : Budget)
    (result : CheckOutcome MugdaCore.TCState) : Json :=
  let common := [
    ("schemaVersion", Mugda2.encodeJson ("mugda2.check.v1" : String)),
    ("checker", Mugda2.encodeJson ("legacy-m1" : String)),
    ("baseline", Mugda2.encodeJson ("b0c5b53c92673e4a7d57b218b4050690e719f0e7" : String)),
    ("source", Mugda2.encodeJson sourceName), ("budget", budget.toJson)]
  Json.mkObj (common ++ match result with
    | .accepted state => [
        ("status", Mugda2.encodeJson ("accepted" : String)),
        ("declarations", Mugda2.encodeJson (state.sig.reverse.map Prod.fst))]
    | .rejected diagnostic => [
        ("status", Mugda2.encodeJson ("rejected" : String)),
        ("diagnostic", Json.mkObj [
          ("category", Mugda2.encodeJson (diagnosticCategoryName diagnostic.category)),
          ("message", Mugda2.encodeJson diagnostic.message), ("span", diagnostic.span.toJson)])]
    | .unknown uncertainty => [
        ("status", Mugda2.encodeJson ("unknown" : String)),
        ("reason", Mugda2.encodeJson (unknownReasonName uncertainty.reason)),
        ("context", Mugda2.encodeJson uncertainty.context), ("span", uncertainty.span.toJson)])

def CheckOutcome.exitCode : CheckOutcome α → UInt32
  | .accepted _ => 0
  | .rejected _ => 1
  | .unknown _ => 2

end Mugda2
