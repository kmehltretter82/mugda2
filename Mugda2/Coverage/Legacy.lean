import Mugda2.Legacy.Checking
import Mugda2.Coverage.Matrix

/-!
The legacy bridge uses the finite pattern-matrix kernel on an overapproximation
of inductive constructor inputs. Parameters specialize sorts; ordinary indices
and sizes do not remove constructors. Opaque domains have an inhabited opaque
sort and can only be covered by catchalls. Observable codata have one constructor
layer with inhabited opaque fields: this never uses recursive finite-tree
emptiness for codata. Sized codata are observed only at infinity. Admissible
cofunctions cover their erased Size arguments at infinity. A kernel hole is
reported as rejection only after its closed arguments pass the original legacy
type checker and every original clause definitely mismatches them.

`Certificate.sound` proves the finite kernel judgment. This executable bridge
does not prove legacy canonical forms, conversion soundness, or productivity.
Those remain separate obligations of a verified object-language core.
-/

namespace MugdaCore

private structure CoverageSort where
  name : Name
  parameters : List Val
  sort : Nat

private structure CoverageConstructor where
  name : Name
  owner : Name
  sort : Nat
  tag : Nat
  domains : List Val
  parameterCount : Nat
  co : Co

private structure CoverageModel where
  sorts : List CoverageSort := []
  constructors : List CoverageConstructor := []
  signature : Mugda2.Coverage.Signature := [⟨0, 0, []⟩]
  nextTag : Nat := 1
  fresh : Nat := 0

private abbrev CoverageBuild := StateT CoverageModel TypeCheck

private def coverageUnsupported (context : String) : TypeCheck α :=
  throw (.unsupportedCoverage context)

private def coverageLift (action : TypeCheck α) : CoverageBuild α := liftM action

private def coverageDataView : Val → Option (Name × List Val)
  | .VDef name => some (name, [])
  | .VApp (.VDef name) args => some (name, args)
  | _ => none

private def coverageFindData (name : Name) : TypeCheck (Option SealedData) := do
  pure ((← get).sealedData.find? fun data => data.name == name)

mutual
  /-- Sort zero is inhabited and opaque. In particular a missing registry entry
      never establishes that a type is empty. -/
  private def coverageSort (fuel : Nat) (domain : Val) : CoverageBuild Nat := do
    match fuel with
    | 0 => coverageLift (throwOutOfFuel "coverage signature translation")
    | fuel + 1 =>
      let some (name, args) := coverageDataView domain | return 0
      let some data ← coverageLift (coverageFindData name) | return 0
      if data.co == .CoInd then
        if data.constructors.isEmpty then return 0
        if data.sized == .Sized && args[data.parameters.length]? != some .VInfty then return 0
      if args.length < data.parameters.length then
        coverageLift (coverageUnsupported ("underapplied datatype " ++ name))
      else
        let parameters := args.take data.parameters.length
        let model ← get
        match model.sorts.find? (fun sort => sort.name == name && sort.parameters == parameters) with
        | some sort => return sort.sort
        | none =>
          let sort := model.sorts.length + 1
          modify fun model => { model with sorts := model.sorts ++ [⟨name, parameters, sort⟩] }
          for constructor in data.constructors do
            let .mk conName conType := constructor
            let conValue ← coverageLift (whnf fuel [] (teleToType data.parameters conType))
            let (domains, sorts) ← coverageConstructorDomains fuel parameters conValue (data.co == .CoInd)
            let model ← get
            let tag := model.nextTag
            modify fun model => { model with
              constructors := model.constructors ++
                [⟨conName, name, sort, tag, domains, data.parameters.length, data.co⟩]
              signature := model.signature ++ [⟨tag, sort, sorts⟩]
              nextTag := tag + 1 }
          return sort

  private def coverageConstructorDomains (fuel : Nat) (parameters : List Val) (type : Val)
      (opaqueArguments : Bool)
      : CoverageBuild (List Val × List Nat) := do
    match fuel with
    | 0 => coverageLift (throwOutOfFuel "coverage constructor telescope")
    | fuel + 1 =>
      match type with
      | .VPi name domain env body =>
        let sort ← if opaqueArguments then pure 0 else coverageSort fuel domain
        let model ← get
        let value := parameters.headD (.VGen model.fresh)
        modify fun model => { model with fresh := model.fresh + 1 }
        let rest ← coverageLift (whnf fuel (updateEnv env name value) body)
        let (domains, sorts) ← coverageConstructorDomains fuel (parameters.drop 1) rest opaqueArguments
        return (domain :: domains, sort :: sorts)
      | _ => return ([], [])
end

private def coverageDomains (fuel : Nat) (arity : Option Nat) (fresh : Nat) (type : Val)
    : TypeCheck (List Val × Nat) := do
  match fuel with
  | 0 => throwOutOfFuel "coverage function telescope"
  | fuel + 1 =>
    if arity == some 0 then return ([], fresh)
    match type with
    | .VPi name domain env body =>
      let rest ← whnf fuel (updateEnv env name (.VGen fresh)) body
      let (domains, next) ← coverageDomains fuel (arity.map Nat.pred) (fresh + 1) rest
      return (domain :: domains, next)
    | _ =>
      if arity.isSome then coverageUnsupported "clause arity exceeds the exposed Pi telescope"
      else return ([], fresh)

private def coverageDomainSort (model : CoverageModel) (domain : Val) : TypeCheck Nat := do
  let some (name, args) := coverageDataView domain | return 0
  let some data ← coverageFindData name | return 0
  if data.co == .CoInd then
    if data.constructors.isEmpty then return 0
    if data.sized == .Sized && args[data.parameters.length]? != some .VInfty then return 0
  let parameters := args.take data.parameters.length
  match model.sorts.find? (fun sort => sort.name == name && sort.parameters == parameters) with
  | some sort => return sort.sort
  | none => coverageUnsupported ("untranslated datatype instance " ++ name)

mutual
  private def coveragePattern (fuel : Nat) (model : CoverageModel) (sizeErasure : Bool) (domain : Val)
      (pattern : Pattern) : TypeCheck Mugda2.Coverage.Pattern := do
    match fuel with
    | 0 => throwOutOfFuel "coverage pattern translation"
    | fuel + 1 =>
      match pattern with
      | .VarP _ | .DotP _ => return .wild
      | .SuccP _ =>
        if sizeErasure && domain == .VSize then return .wild
        else coverageUnsupported "successor size patterns require a sized observation bridge"
      | .ConP co name patterns =>
          let sort ← coverageDomainSort model domain
          if sort == 0 then
            coverageUnsupported "constructor pattern at a Pi, opaque, or coinductive domain"
          else
            let some constructor := model.constructors.find?
              (fun constructor => constructor.name == name && constructor.sort == sort && constructor.co == co)
              | coverageUnsupported ("constructor is not in the sealed input family: " ++ name)
            if patterns.length != constructor.domains.length then
              coverageUnsupported ("constructor pattern is not saturated: " ++ name)
            else
              return .con constructor.tag (← coveragePatterns fuel model false constructor.domains patterns)

  private def coveragePatterns (fuel : Nat) (model : CoverageModel) (sizeErasure : Bool) (domains : List Val)
      (patterns : List Pattern) : TypeCheck (List Mugda2.Coverage.Pattern) := do
    match fuel with
    | 0 => throwOutOfFuel "coverage pattern matrix"
    | fuel + 1 =>
      match domains, patterns with
      | domains, [] => return List.replicate domains.length .wild
      | domain :: domains, pattern :: patterns =>
        return (← coveragePattern fuel model sizeErasure domain pattern) ::
          (← coveragePatterns fuel model sizeErasure domains patterns)
      | _, _ => coverageUnsupported "inconsistent pattern matrix arity"
end

mutual
  private def coverageExpr (fuel : Nat) (value : Val) : TypeCheck Expr := do
    match fuel with
    | 0 => throwOutOfFuel "coverage witness quotation"
    | fuel + 1 =>
      match value with
      | .VDef name => return .Def name
      | .VCon co name => return .Con co name
      | .VInfty => return .Infty
      | .VSucc value => return .Succ (← coverageExpr fuel value)
      | .VApp head args => return .App (← coverageExpr fuel head) (← coverageExprs fuel args)
      | _ => coverageUnsupported "an erased coverage hole has no closed parameter witness"

  private def coverageExprs (fuel : Nat) (values : List Val) : TypeCheck (List Expr) := do
    match fuel with
    | 0 => throwOutOfFuel "coverage witness parameters"
    | fuel + 1 =>
      match values with
      | [] => return []
      | value :: values => return (← coverageExpr fuel value) :: (← coverageExprs fuel values)
end

mutual
  private def coverageWitness (fuel : Nat) (model : CoverageModel) (domain : Val)
      (value : Mugda2.Coverage.Value) : TypeCheck Expr := do
    match fuel with
    | 0 => throwOutOfFuel "coverage witness realization"
    | fuel + 1 =>
      let .con tag args := value
      if tag == 0 then
        match domain with
        | .VSize => return .Infty
        | .VSet =>
          let some data := (← get).sealedData.find? (fun data =>
            data.parameters.isEmpty && data.type == .Set)
            | coverageUnsupported "the opaque sort has no closed type witness"
          return .Def data.name
        | _ => coverageUnsupported "the opaque sort has no checked closed witness"
      else
        let some constructor := model.constructors.find? (fun constructor => constructor.tag == tag)
          | coverageUnsupported "unknown constructor in coverage witness"
        if constructor.co == .CoInd then
          coverageUnsupported "a missing coinductive observation has no checked total witness"
        else pure ()
        let some (owner, parameters) := coverageDataView domain
          | coverageUnsupported "coverage witness requires an opaque input refinement"
        if owner != constructor.owner then coverageUnsupported "coverage witness owner mismatch"
        else
          let .ConSig type ← lookupSig constructor.name
            | coverageUnsupported "coverage constructor signature disappeared"
          let exprs ← coverageWitnessConstructorArgs fuel model
            (parameters.take constructor.parameterCount) type args
          return if exprs.isEmpty then .Con .Ind constructor.name
            else .App (.Con .Ind constructor.name) exprs

  private def coverageWitnessConstructorArgs (fuel : Nat) (model : CoverageModel)
      (parameters : List Val) (type : Val) (values : List Mugda2.Coverage.Value) : TypeCheck (List Expr) := do
    match fuel with
    | 0 => throwOutOfFuel "coverage witness constructor arguments"
    | fuel + 1 =>
      match values, type with
      | [], _ => return []
      | value :: values, .VPi name domain env body =>
        let expr ← match parameters with
          | parameter :: _ => coverageExpr fuel parameter
          | [] => coverageWitness fuel model domain value
        checkExpr fuel 0 [] [] expr domain
        let actual ← whnf fuel [] expr
        let rest ← whnf fuel (updateEnv env name actual) body
        return expr :: (← coverageWitnessConstructorArgs fuel model (parameters.drop 1) rest values)
      | _, _ => coverageUnsupported "coverage witness constructor arity mismatch"
end

private def coverageWitnessArguments (fuel : Nat) (model : CoverageModel) (type : Val)
    (values : List Mugda2.Coverage.Value) : TypeCheck (List Val) := do
  match fuel with
  | 0 => throwOutOfFuel "coverage witness input telescope"
  | fuel + 1 =>
    match values, type with
    | [], _ => return []
    | value :: values, .VPi name domain env body =>
      let expr ← coverageWitness fuel model domain value
      checkExpr fuel 0 [] [] expr domain
      let actual ← whnf fuel [] expr
      let rest ← whnf fuel (updateEnv env name actual) body
      return actual :: (← coverageWitnessArguments fuel model rest values)
    | _, _ => coverageUnsupported "coverage witness input arity mismatch"

private def coverageDefiniteHole (fuel : Nat) (clauses : List Clause) (values : List Val)
    : TypeCheck Unit := do
  for clause in clauses do
    let .mk patterns _ := clause
    match ← matchList fuel [] patterns (values.take patterns.length) with
    | .mismatch => pure ()
    | .matched _ => coverageUnsupported "an erased hole matches an original clause"
    | .stuck => coverageUnsupported "coverage witness matching is unresolved"

private def coverageCatchallRow (co : Co) : List Val → List Pattern → Bool
  | _, [] => true
  | domain :: domains, pattern :: patterns =>
    let catchall := match pattern with
      | .VarP _ | .DotP _ => true
      | .SuccP _ => co == .CoInd && domain == .VSize
      | _ => false
    catchall && coverageCatchallRow co domains patterns
  | _, _ => false

/-- Gate promotion using an actual finite constructor matrix. Unsupported typed
    refinements and erased holes are unknown, never empty-elimination evidence. -/
def checkLegacyCoverage (fuel : Nat) (co : Co) (type : MType) (clauses : List Clause)
    : TypeCheck Unit := do
  let typeValue ← whnf fuel [] type
  let arity := match clauses with
    | [] => none
    | _ => some (clauses.foldl (fun n (.mk patterns _) => max n patterns.length) 0)
  let (domains, fresh) ← coverageDomains fuel arity 0 typeValue
  -- A first catchall already matches before any later clause is inspected.
  -- Its proof does not depend on traversing the datatype's recursive graph.
  if let .mk patterns _ :: _ := clauses then
    if coverageCatchallRow co domains patterns then
      let signature : Mugda2.Coverage.Signature := [⟨0, 0, []⟩]
      let sorts := List.replicate domains.length 0
      let matrix := [List.replicate domains.length Mugda2.Coverage.Pattern.wild]
      match Mugda2.Coverage.check fuel signature sorts matrix with
      | .covered _ => return ()
      | .unknown .fuelExhausted => throwOutOfFuel "coverage catchall certificate"
      | _ => coverageUnsupported "catchall certificate construction failed"
  let (sorts, model) ← (domains.mapM (coverageSort fuel)).run { fresh := fresh }
  let matrix ← clauses.mapM fun (.mk patterns _) => coveragePatterns fuel model (co == .CoInd) domains patterns
  match Mugda2.Coverage.check fuel model.signature sorts matrix with
  | .covered _ => pure ()
  | .unknown .fuelExhausted => throwOutOfFuel "coverage matrix search"
  | .unknown .inhabitationUndecided => coverageUnsupported "finite input inhabitation is unresolved"
  | .missing values _ _ =>
    tryCatch (do
      let actual ← coverageWitnessArguments fuel model typeValue values
      coverageDefiniteHole fuel clauses actual
      throwDiagnostic .coverage "a checked input has no matching clause") (fun err =>
        match err with
        | .rejected .coverage _ => throw err
        | .rejected _ _ => coverageUnsupported "an erased coverage hole is not a checked typed input"
        | .unsupportedCoverage _ | .outOfFuel _ => throw err)

end MugdaCore
