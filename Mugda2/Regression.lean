import Mugda2.Checker
import Mugda2.Legacy.Fixtures

/-! Runtime regressions, intentionally not native-evaluation-backed theorems. -/
namespace Mugda2.Regression

open MugdaCore

private def exhausted : Except TCError α → Bool
  | .error (.outOfFuel _) => true
  | _ => false

private def rejectedAs (category : DiagnosticCategory) : Except TCError α → Bool
  | .error (.rejected actual _) => actual == category
  | _ => false

private def natDecl : Declaration :=
  .DataDecl "Nat" .NotSized .Ind [] [] .Set
    [.mk "zero" (.Def "Nat"), .mk "succ" (.Pi "" (.Def "Nat") (.Def "Nat"))]

private def idFun : TypeSig × List Clause :=
  (.mk "good" (.Pi "" (.Def "Nat") (.Def "Nat")), [.mk [.VarP "x"] (.Var "x")])

private def loopFun : TypeSig × List Clause :=
  (.mk "loop" (.Pi "" (.Def "Nat") (.Def "Nat")),
    [.mk [.VarP "x"] (.App (.Def "loop") [.Var "x"])])

private def copyFun : TypeSig × List Clause :=
  (.mk "copy" (.Pi "" (.Def "Nat") (.Def "Nat")),
    [.mk [.ConP .Ind "zero" []] (.Con .Ind "zero"),
     .mk [.ConP .Ind "succ" [.VarP "x"]]
       (.App (.Con .Ind "succ") [.App (.Def "copy") [.Var "x"]])])

private def incompleteFun : TypeSig × List Clause :=
  (.mk "incomplete" (.Pi "i" .Size .Set),
    [.mk [.SuccP (.VarP "i")] (.App (.Def "incomplete") [.Var "i"])])

private def sizedIdFun : TypeSig × List Clause :=
  (.mk "good" (.Pi "i" .Size (.Pi "" (.App (.Def "SNat") [.Var "i"])
    (.App (.Def "SNat") [.Var "i"]))), [.mk [.VarP "i", .VarP "x"] (.Var "x")])

private def sameState (before after : TCState) : Bool :=
  before.sig == after.sig && before.warnings == after.warnings &&
  before.provisional.entries == after.provisional.entries &&
  before.terminationBudget.comparisonFuel == after.terminationBudget.comparisonFuel &&
  before.terminationBudget.closureFuel == after.terminationBudget.closureFuel &&
  before.sealedData == after.sealedData

/-- Catch an actual failure and inspect the surviving state, including a later lookup. -/
private def rollsBack (initialDecls : List Declaration) (block : Declaration)
    (expected : TCError → Bool) (budget : TerminationBudget := {}) : Bool :=
  match runTypeCheck { terminationBudget := budget } (typeCheckDecls 1000 initialDecls) with
  | .error _ => false
  | .ok (_, before) =>
      match runTypeCheck before (typeCheckDeclaration 1000 block) with
      | .ok _ => false
      | .error error =>
          expected error && match runTypeCheck before
              (tryCatch (typeCheckDeclaration 1000 block *> pure false) (fun _ => pure true)) with
            | .error _ => false
            | .ok (caught, after) =>
                caught && sameState before after && after.provisional.entries.isEmpty &&
                (lookupSigOpt "good" after.sig).isNone &&
                (lookupSigOpt "loop" after.sig).isNone &&
                !(runTypeCheck after (inferExpr 1000 0 [] [] (.Def "good"))).isOk

private def hasCategory (category : DiagnosticCategory) : TCError → Bool
  | .rejected actual _ => actual == category
  | _ => false

private def unsupportedCoverage : TCError → Bool
  | .unsupportedCoverage context => !context.isEmpty
  | _ => false

private def parseSourceDecls (source : String) : Except TCError (List Declaration) := do
  let tokens ← tokenize source
  let concrete ← parseTokens tokens
  scopeCheck concrete

/-- Exercise a real failed mutual declaration, recover its entry state, then
    check a corrected mutual declaration and its client using the same names. -/
private def mutualRollbackAndRecovery (attempt recovery : String)
    (expected : TCError → Bool) : Bool :=
  match parseSourceDecls attempt, parseSourceDecls recovery with
  | .ok [datatype, previous, block], .ok [_, _, corrected, useDecl] =>
    match runTypeCheck
        { warnings := ["saved warning"],
          terminationBudget := { comparisonFuel := 73, closureFuel := 81 } }
        (typeCheckDecls 1000 [datatype, previous]) with
    | .error _ => false
    | .ok (_, before) =>
      match runTypeCheck before (typeCheckDeclaration 1000 block) with
      | .ok _ => false
      | .error error =>
        !before.sealedData.isEmpty && expected error && match runTypeCheck before
            (tryCatch (typeCheckDeclaration 1000 block *> pure false) (fun _ => pure true)) with
          | .error _ => false
          | .ok (caught, after) =>
            caught && sameState before after &&
            ["good", "missing"].all (fun name =>
              (lookupSigOpt name after.sig).isNone &&
              (lookupSigOpt name after.provisional.entries).isNone &&
              !(runTypeCheck after (inferExpr 1000 0 [] [] (.Def name))).isOk) &&
            match runTypeCheck after (typeCheckDecls 1000 [corrected, useDecl]) with
            | .error _ => false
            | .ok (_, committed) =>
              committed.provisional.entries.isEmpty &&
              committed.warnings == before.warnings &&
              committed.sealedData == before.sealedData &&
              committed.terminationBudget.comparisonFuel ==
                before.terminationBudget.comparisonFuel &&
              committed.terminationBudget.closureFuel == before.terminationBudget.closureFuel &&
              (lookupSigOpt "use" committed.sig).isSome &&
              ["good", "missing"].all (fun name =>
                match lookupSigOpt name committed.sig with
                | some (.FunSig _ _ _ true) => true
                | _ => false)
  | _, _ => false

private def coverageRollbackRecovery : Bool :=
  mutualRollbackAndRecovery "
data Bool : Set { tt : Bool; ff : Bool }
let previous : Bool = tt
mutual {
  fun good : Bool -> Bool { good b = b }
  fun missing : Bool -> Bool { missing tt = good tt }
}
" "
data Bool : Set { tt : Bool; ff : Bool }
let previous : Bool = tt
mutual {
  fun good : Bool -> Bool { good b = b }
  fun missing : Bool -> Bool { missing b = good b }
}
let use : Bool = missing previous
" (hasCategory .coverage)

private def unsupportedRollbackRecovery : Bool :=
  mutualRollbackAndRecovery "
data Nat : Set { zero : Nat; succ : Nat -> Nat }
let previous : Nat = zero
mutual {
  fun good : Nat -> Nat { good n = n }
  fun missing : (Nat -> Nat) -> Nat {}
}
" "
data Nat : Set { zero : Nat; succ : Nat -> Nat }
let previous : Nat = zero
mutual {
  fun good : Nat -> Nat { good n = n }
  fun missing : (Nat -> Nat) -> Nat { missing f = f previous }
}
let use : Nat = missing good
" unsupportedCoverage

/-- A bad later constructor must not publish a partially checked datatype or
    its first constructor, and a corrected datatype must still seal once. -/
private def constructorMetadataRollbackRecovery : Bool :=
  match parseSourceDecls "
data Nat : Set { zero : Nat; succ : Nat -> Nat }
data Bad : Set { first : Bad; wrong : Nat }
", parseSourceDecls "data Bad : Set { first : Bad }" with
  | .ok [datatype, bad], .ok [corrected] =>
    match runTypeCheck
        { warnings := ["saved warning"],
          terminationBudget := { comparisonFuel := 73, closureFuel := 81 } }
        (typeCheckDeclaration 1000 datatype) with
    | .error _ => false
    | .ok (_, before) =>
      match runTypeCheck before (typeCheckDeclaration 1000 bad) with
      | .ok _ => false
      | .error error =>
        before.sealedData.any (fun entry => entry.name == "Nat") &&
        hasCategory .typeMismatch error && match runTypeCheck before
            (tryCatch (typeCheckDeclaration 1000 bad *> pure false) (fun _ => pure true)) with
          | .error _ => false
          | .ok (caught, after) =>
            caught && sameState before after &&
            ["Bad", "first", "wrong"].all (fun name => (lookupSigOpt name after.sig).isNone) &&
            !(after.sealedData.any (fun entry => entry.name == "Bad")) &&
            match runTypeCheck after (typeCheckDeclaration 1000 corrected) with
            | .error _ => false
            | .ok (_, committed) =>
              committed.sealedData.length == before.sealedData.length + 1 &&
              (committed.sealedData.filter (fun entry => entry.name == "Bad")).length == 1 &&
              (lookupSigOpt "Bad" committed.sig).isSome &&
              (lookupSigOpt "first" committed.sig).isSome &&
              (lookupSigOpt "wrong" committed.sig).isNone
  | _, _ => false

private def constructorAtFunctionDomain : Bool :=
  match MugdaCore.checkSource "
data Nat : Set { zero : Nat; succ : Nat -> Nat }
fun partial : (Nat -> Nat) -> Nat { partial succ = zero }
" with
  | .error error => unsupportedCoverage error
  | .ok _ => false

private def codataIsNotFiniteEmpty : Bool :=
  match MugdaCore.checkSource "
data Nat : Set { zero : Nat; succ : Nat -> Nat }
codata Stream : Set { next : Stream -> Stream }
fun missing : Stream -> Nat {}
" with
  | .error error => unsupportedCoverage error
  | .ok _ => false

/-- The raw checking API cannot replace a sealed inventory or extend it after
    coverage has relied on its constructor set. Both failures preserve state. -/
private def sealedInventoryCannotChange : Bool :=
  match runTypeCheck
      { warnings := ["saved warning"],
        terminationBudget := { comparisonFuel := 73, closureFuel := 81 } }
      (typeCheckDeclaration 1000 natDecl) with
  | .error _ => false
  | .ok (_, before) =>
    let rejectedUnchanged := fun (action : TypeCheck Unit) =>
      match runTypeCheck before action with
      | .ok _ => false
      | .error error =>
        hasCategory .scope error && match runTypeCheck before
            (tryCatch (action *> pure false) (fun _ => pure true)) with
          | .error _ => false
          | .ok (caught, after) =>
            caught && sameState before after &&
            (lookupSigOpt "freshCon" after.sig).isNone &&
            (lookupSigOpt "freshCon" after.provisional.entries).isNone
    before.sealedData.any (fun entry => entry.name == "Nat" && entry.constructors.length == 2) &&
    rejectedUnchanged
      (typeCheckDeclaration 1000 (.DataDecl "Nat" .NotSized .Ind [] [] .Set [])) &&
    rejectedUnchanged
      (typeCheckConstructor 1000 "Nat" .NotSized [] [] (.mk "freshCon" (.Def "Nat")))

private def successfulMutual : Bool :=
  let aliasFun := (.mk "alias" (.Pi "" (.Def "Nat") (.Def "Nat")),
    [.mk [.VarP "x"] (.App (.Def "good") [.Var "x"])])
  match runTypeCheck {} (typeCheckDecls 1000 [natDecl, .FunDecl .Ind [idFun, aliasFun]]) with
  | .error _ => false
  | .ok (_, state) =>
      state.provisional.entries.isEmpty && ["good", "alias"].all fun name =>
        match lookupSigOpt name state.sig with
        | some (.FunSig _ _ _ true) => true
        | _ => false

private def manyPatterns : List Pattern :=
  (List.range 1001).map (fun i => .VarP ("x" ++ toString i))

private def collectManyPatterns : Bool :=
  match runScopeCheck [] [] (collectVarPNames manyPatterns) with
  | .ok (names, _) => names.length == 1001 && names.contains "x1000"
  | .error _ => false

private def unicodeRoundtrip : Bool :=
  let chars := [0, 31, 32, 127, 128, 2047, 2048, 55295, 57344, 65535, 65536, 1114111].map Char.ofNat
  sourceChars (String.ofList chars) == chars

private def overlappingClauses : List Clause :=
  [.mk [.ConP .Ind "tt" []] (.Con .Ind "left"),
   .mk [.VarP "x"] (.Con .Ind "right")]

private def matchingReturns (value : Val) (expected : Option Val) : Bool :=
  match runTypeCheck {} (matchClauses 20 overlappingClauses [value]) with
  | .ok (actual, _) => actual == expected
  | .error _ => false

private def underappliedConstructorStuck : Bool :=
  match runTypeCheck {} (matchPat 8 [] (.ConP .Ind "succ" [.VarP "n"]) (.VCon .Ind "succ")) with
  | .ok (.stuck, _) => true
  | _ => false

private def matchingExhaustion : Bool :=
  match runTypeCheck {} (matchPat 0 [] (.VarP "n") (.VGen 0)) with
  | .error (.outOfFuel context) => context == "matchPat"
  | _ => false

private def coinductiveMatchingForces : Bool :=
  let state : TCState :=
    { sig := [("co", .FunSig .CoInd .VSet [.mk [] (.Con .CoInd "cell")] true)] }
  match runTypeCheck state (matchPat 20 [] (.ConP .CoInd "cell" []) (.VDef "co")) with
  | .ok (.matched [], _) => true
  | _ => false

/-- Concrete constructor branches justify dependent conversion without reducing
    an overlapping type family on a neutral input. -/
private def overlappingPositiveSource : String := "
data Bool : Set { tt : Bool; ff : Bool }
data Nat : Set { zero : Nat }
data Unit : Set { unit : Unit }
fun F : Bool -> Set { F tt = Nat; F b = Unit }
fun good : (b : Bool) -> F b { good tt = zero; good ff = unit }
let first : Nat = good tt
let second : Unit = good ff
"

private def checks : List (String × Bool) := [
  ("baseline SNat/sub accepted", (checkProgram [snatDecl, subDecl]).isOk),
  ("baseline shared-size exploit rejected for pattern refinement",
    rejectedAs .patternRefinement (checkProgram [snatDecl, snatMatBugDecl])),
  ("baseline wrapper exploit rejected for admissibility",
    rejectedAs .admissibility (checkProgram [snatDecl, wrapDecl, badWrapFunDecl])),
  ("baseline local-let recursive call rejected for termination",
    rejectedAs .termination (checkProgram [snatDecl, lletBugDecl])),
  ("baseline sized division accepted", (MugdaCore.checkSource snatDivSource).isOk),
  ("baseline Cody exploit rejected for pattern refinement",
    rejectedAs .patternRefinement (MugdaCore.checkSource codyNoWrapsSource)),
  ("baseline Fibonacci evaluates to five",
    (evalSource fibSource).toOption ==
      some ["fib4 evaluates to (succ (succ (succ (succ (succ zero)))))"]),
  ("baseline matrix termination example accepted", (MugdaCore.checkSource natpairSource).isOk),
  ("checkSType preserves exhaustion", exhausted (runTypeCheck {} (checkSType 0 0 [] [] .Set))),
  ("szMonotone preserves exhaustion",
    exhausted (runTypeCheck {} (szMonotone 1 0 0 (.VSucc (.VGen 0))))),
  ("dependent parser probe preserves exhaustion",
    exhausted (parseExpr 1 [.PrOpen, .Id "x", .Col, .Set, .PrClose, .Arrow, .Set])),
  ("pattern variable collection preserves exhaustion",
    exhausted (runScopeCheck [] [] (collectVarPNamesAux 0 [.VarP "x"] []))),
  ("syntactic comparison preserves exhaustion",
    exhausted (compareExprWithFuel 0 (.Var "x") (.VarP "x"))),
  ("call-graph closure preserves exhaustion", exhausted (completeCallsWithFuel 0 [])),
  ("mutual termination failure rolls back all functions",
    rollsBack [natDecl] (.FunDecl .Ind [idFun, loopFun]) (hasCategory .termination)),
  ("mutual body failure rolls back all functions",
    rollsBack [natDecl] (.FunDecl .Ind [idFun,
      (.mk "bad" (.Pi "" (.Def "Nat") (.Def "Nat")), [.mk [.VarP "x"] .Size])])
      (hasCategory .typeMismatch)),
  ("mutual incomplete size pattern rolls back all functions",
    rollsBack [natDecl] (.FunDecl .Ind [idFun, incompleteFun])
      (hasCategory .sizePatternCompleteness)),
  ("mutual inadmissibility rolls back all functions",
    rollsBack [snatDecl, wrapDecl] (.FunDecl .Ind (sizedIdFun ::
      match badWrapFunDecl with | .FunDecl _ funs => funs | _ => []))
      (hasCategory .admissibility)),
  ("comparison budget exhaustion rolls back all functions",
    rollsBack [natDecl] (.FunDecl .Ind [idFun, copyFun])
      (fun error => match error with | .outOfFuel _ => true | _ => false)
      { comparisonFuel := 0 }),
  ("closure budget exhaustion rolls back all functions",
    rollsBack [natDecl] (.FunDecl .Ind [idFun, copyFun])
      (fun error => match error with | .outOfFuel _ => true | _ => false)
      { closureFuel := 0 }),
  ("successful mutual block commits all verified functions", successfulMutual),
  ("mutual coverage failure restores every state field and permits same-name recovery",
    coverageRollbackRecovery),
  ("unsupported coverage restores every state field and permits same-name recovery",
    unsupportedRollbackRecovery),
  ("failed later constructor restores sealed metadata and permits corrected datatype",
    constructorMetadataRollbackRecovery),
  ("underapplied constructor at function domain is not translated as a Nat input",
    constructorAtFunctionDomain),
  ("codata is not declared empty from its lack of finite constructor trees",
    codataIsNotFiniteEmpty),
  ("raw API rejects sealed datatype replacement and extension without state changes",
    sealedInventoryCannotChange),
  ("scope collects more than a thousand pattern variables", collectManyPatterns),
  ("scope rejects a duplicate beyond the former cutoff",
    rejectedAs .scope (runScopeCheck [] [] (collectVarPNames (manyPatterns ++ [.VarP "x0"])))),
  ("constructive source decoding preserves Unicode boundaries", unicodeRoundtrip),
  ("neutral constructor matching blocks later catch-all clauses", matchingReturns (.VGen 0) none),
  ("definite constructor mismatch advances to the catch-all",
    matchingReturns (.VCon .Ind "ff") (some (.VCon .Ind "right"))),
  ("matched first clause ignores the later catch-all",
    matchingReturns (.VCon .Ind "tt") (some (.VCon .Ind "left"))),
  ("underapplied constructor matching stays stuck", underappliedConstructorStuck),
  ("matching exhaustion remains typed and identifies its stage", matchingExhaustion),
  ("coinductive constructor matching still forces an observation", coinductiveMatchingForces),
  ("dependent constructor branches remain accepted after matching fix",
    (MugdaCore.checkSource overlappingPositiveSource).isOk)
  ]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, passed) in checks do
    IO.println ((if passed then "PASS " else "FAIL ") ++ name)
    if !passed then failures := failures + 1
  IO.println s!"{checks.length - failures}/{checks.length} runtime regressions passed"
  pure (if failures == 0 then 0 else 1)

end Mugda2.Regression

def main : IO UInt32 := Mugda2.Regression.main
