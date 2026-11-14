import Mugda2.Legacy.Checking
import Mugda2.Coverage.Legacy

namespace MugdaCore

/-- Check an entire mutual block against an isolated provisional environment.
    No unverified function enters `sig`, and no state escapes a failed block. -/
def typeCheckFuns (fuel : Nat) (co : Co) (funs : List (TypeSig × List Clause)) : TypeCheck Unit := do
  let saved ← get
  if !saved.provisional.entries.isEmpty then
    throwErrorMsg "nested provisional function block"
  let _ ← funs.foldlM (fun seen (.mk n _, _) => do
    if seen.contains n || (lookupSigOpt n saved.sig).isSome then
      throwDiagnostic .scope ("Identifier " ++ n ++ " already in signature")
    pure (n :: seen)) ([] : List Name)
  let checkBlock : TypeCheck Unit := do
    funs.forM fun (.mk n t, cl) => do
      let vt ← whnf fuel [] t
      modify fun st => { st with
        provisional := ⟨addSig st.provisional.entries n (.FunSig co vt cl false)⟩ }
    funs.forM fun (.mk n t, cl) => throwTrace (do
      checkT fuel t
      let vt ← whnf fuel [] t
      let adm ← match co with
        | .Ind => szCheckIndFun fuel 0 vt
        | .CoInd => szCheckCoFun fuel 0 vt
      if !adm then throwDiagnostic .admissibility "type not admissible"
      if co == .Ind && !completePatterns cl then
        throwDiagnostic .sizePatternCompleteness "size pattern incomplete"
    ) ("type of " ++ n)
    funs.forM fun (.mk n t, cl) => throwTrace (checkFun fuel t cl) n
    let budget := saved.terminationBudget
    let termOk ← match terminationCheckWithFuel budget.comparisonFuel budget.closureFuel funs with
      | .ok ok => pure ok
      | .error err => throw err
    if !termOk then throwDiagnostic .termination "Termination check fails"
    funs.forM fun (.mk n t, cl) =>
      throwTrace (checkLegacyCoverage fuel co t cl) ("coverage of " ++ n)
    let staged := (← get).provisional.entries
    let committed := commitProvisional saved.sig staged
    modify fun st => { st with sig := committed, provisional := saved.provisional }
  match runTypeCheck saved checkBlock with
  | .ok (_, checked) => set checked
  | .error err => throw err

def typeCheckDeclaration (fuel : Nat) : Declaration → TypeCheck Unit
  | .DataDecl n sz co pos tel t cs => throwTrace (do
      if (lookupSigOpt n (← getSig)).isSome then
        throwDiagnostic .scope ("Identifier " ++ n ++ " already in signature")
      let dt := teleToType tel t
      let params := tel.length
      let p' := match sz with | .Sized => params + 1 | .NotSized => params
      checkDataType fuel 0 [] [] p' dt
      let v ← whnf fuel [] dt
      let sig ← getSig
      putSig (addSig sig n (.DataSig params pos sz co v))
      match sz with
      | .Sized    => szType fuel params v
      | .NotSized => pure ()
      cs.forM (typeCheckConstructor fuel n sz pos tel)
      modify fun st => { st with sealedData := st.sealedData ++
        [⟨n, co, sz, tel, dt, cs⟩] }
    ) n
  | .LetDecl _ (.mk n t) e => throwTrace (do
      if (lookupSigOpt n (← getSig)).isSome then
        throwDiagnostic .scope ("Identifier " ++ n ++ " already in signature")
      checkT fuel t
      let vt ← whnf fuel [] t
      checkExpr fuel 0 [] [] e vt
      let sig ← getSig
      putSig (addSig sig n (.LetSig vt e))
    ) n
  | .FunDecl co funs => typeCheckFuns fuel co funs

def typeCheckDecls (fuel : Nat) (dl : List Declaration) : TypeCheck Unit :=
  dl.forM (typeCheckDeclaration fuel)

def checkProgram (dl : List Declaration) : Except TCError TCState :=
  match runTypeCheck {} (typeCheckDecls defaultFuel dl) with
  | .ok (_, st) =>
      if st.warnings.isEmpty then .ok st
      else .error (.rejected .admissibility (String.intercalate "; " st.warnings))
  | .error msg => .error msg

/-! ## 7. Port of `Concrete.hs`, `ScopeChecker.hs`, `Lexer.hs` & `Parser.hs` -/

/-! ### 7.1 Concrete Syntax (`Concrete.hs`) -/

inductive CExpr : Type where
  | Set   : CExpr
  | Size  : CExpr
  | Succ  : CExpr → CExpr
  | Infty : CExpr
  | App   : CExpr → List CExpr → CExpr
  | Lam   : Name → CExpr → CExpr
  | LLet  : Name → CExpr → CExpr → CExpr → CExpr
  | Pi    : Name → CExpr → CExpr → CExpr
  | Ident : Name → CExpr
  deriving Repr, Inhabited, BEq

inductive CTBind : Type where
  | TB    : Name → CExpr → CTBind
  | PosTB : Name → CExpr → CTBind
  deriving Repr, Inhabited, BEq

abbrev CTelescope := List CTBind

inductive CTypeSig : Type where
  | mk : Name → CExpr → CTypeSig
  deriving Repr, Inhabited, BEq

inductive CPattern : Type where
  | ConP   : Name → List CPattern → CPattern
  | SuccP  : CPattern → CPattern
  | DotP   : CExpr → CPattern
  | IdentP : Name → CPattern
  deriving Repr, Inhabited, BEq

inductive CClause : Type where
  | mk : List CPattern → CExpr → CClause
  deriving Repr, Inhabited, BEq

inductive CDeclaration : Type where
  | DataDecl   : Name → Sized → Co → CTelescope → CExpr → List CTypeSig → CDeclaration
  | FunDecl    : Co → CTypeSig → List CClause → CDeclaration
  | LetDecl    : Bool → CTypeSig → CExpr → CDeclaration
  | MutualDecl : List CDeclaration → CDeclaration
  deriving Repr, Inhabited, BEq

def cTeleToType : CTelescope → CExpr → CExpr
  | [],                 t2 => t2
  | .TB n t :: tel,     t2 => .Pi n t (cTeleToType tel t2)
  | .PosTB n t :: tel,  t2 => .Pi n t (cTeleToType tel t2)

/-! ### 7.2 Scope Checker (`ScopeChecker.hs`) -/

inductive IKind : Type where
  | DataK : IKind
  | ConK  : Co → IKind
  | FunK  : IKind
  | LetK  : IKind
  deriving Repr, Inhabited, BEq

abbrev ScopeCtx := List Name
abbrev ScopeSig := List (Name × IKind)

def lookupScopeSig (n : Name) : ScopeSig → Option IKind
  | []            => none
  | (x, k) :: xs  => if x == n then some k else lookupScopeSig n xs

def addScopeSig (n : Name) (k : IKind) (sig : ScopeSig) : ScopeSig :=
  sig ++ [(n, k)]

abbrev ScopeCheck (α : Type) := ReaderT ScopeCtx (StateT ScopeSig (Except TCError)) α

def runScopeCheck (ctx : ScopeCtx) (sig : ScopeSig) (m : ScopeCheck α) : Except TCError (α × ScopeSig) :=
  StateT.run (ReaderT.run m ctx) sig

def posTelescope : CTelescope → List Pos
  | []                => []
  | .TB _ _ :: tel    => .NSPos :: posTelescope tel
  | .PosTB _ _ :: tel => .SPos :: posTelescope tel

def collectTelescopeNames : CTelescope → List Name
  | []                => []
  | .TB n _ :: tel    => n :: collectTelescopeNames tel
  | .PosTB n _ :: tel => n :: collectTelescopeNames tel

mutual
  def scopeCheckExpr : CExpr → ScopeCheck Expr
    | .Set      => pure .Set
    | .Size     => pure .Size
    | .Succ e1  => do
        let e1' ← scopeCheckExpr e1
        pure (.Succ e1')
    | .Infty    => pure .Infty
    | .App e1 el => do
        let e1' ← scopeCheckExpr e1
        let el' ← scopeCheckExprList el
        pure (.App e1' el')
    | .Pi "" t e1 => do
        let t' ← scopeCheckExpr t
        let e1' ← scopeCheckExpr e1
        pure (.Pi "" t' e1')
    | .Pi n t e1 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw (.rejected .scope ("Identifier " ++ n ++ " already in signature"))
        | none   =>
            if ctx.contains n then throw (.rejected .scope ("Identifier " ++ n ++ " already in context"))
            else do
              let t' ← scopeCheckExpr t
              let e1' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e1)
              pure (.Pi n t' e1')
    | .Lam n e1 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw (.rejected .scope ("Identifier " ++ n ++ " already in signature"))
        | none   =>
            if ctx.contains n then throw (.rejected .scope ("Identifier " ++ n ++ " already in context"))
            else do
              let e1' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e1)
              pure (.Lam n e1')
    | .LLet n t1 e1 e2 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw (.rejected .scope ("Identifier " ++ n ++ " already in signature"))
        | none   =>
            if ctx.contains n then throw (.rejected .scope ("Identifier " ++ n ++ " already in context"))
            else do
              let t1' ← scopeCheckExpr t1
              let e1' ← scopeCheckExpr e1
              let e2' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e2)
              pure (.LLet n t1' e1' e2')
    | .Ident n => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => pure (.Con co n)
        | some .LetK      => pure (.Let n)
        | some _          => pure (.Def n)
        | none            =>
            if ctx.contains n then pure (.Var n)
            else throw (.rejected .scope ("Identifier " ++ n ++ " undefined"))

  def scopeCheckExprList : List CExpr → ScopeCheck (List Expr)
    | []      => pure []
    | e :: es => do
        let e' ← scopeCheckExpr e
        let es' ← scopeCheckExprList es
        pure (e' :: es')
end

def scopeCheckTypeSig : CTypeSig → ScopeCheck TypeSig
  | .mk n t => do
      let sig ← get
      match lookupScopeSig n sig with
      | some _ => throw (.rejected .scope ("Identifier " ++ n ++ " already in signature"))
      | none   => do
          let t' ← scopeCheckExpr t
          pure (.mk n t')

def scopeCheckConstructor (co : Co) : CTypeSig → ScopeCheck Constructor
  | .mk n t => do
      let sig ← get
      match lookupScopeSig n sig with
      | some _ => throw (.rejected .scope ("Identifier " ++ n ++ " already in signature"))
      | none   => do
          let t' ← scopeCheckExpr t
          set (addScopeSig n (.ConK co) sig)
          pure (.mk n t')

mutual
  def scopeCheckPattern : CPattern → ScopeCheck Pattern
    | .IdentP n => do
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => pure (.ConP co n [])
        | some _          => throw (.rejected .scope ("pattern " ++ n ++ " not a constructor"))
        | none            => pure (.VarP n)
    | .SuccP p2 => do
        let p2' ← scopeCheckPattern p2
        pure (.SuccP p2')
    | .ConP n pl => do
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => do
            let pl' ← scopeCheckPatternList pl
            pure (.ConP co n pl')
        | _ => throw (.rejected .scope ("pattern " ++ n ++ " not a constructor"))
    | .DotP _ => pure (.VarP "")

  def scopeCheckPatternList : List CPattern → ScopeCheck (List Pattern)
    | []      => pure []
    | p :: ps => do
        let p' ← scopeCheckPattern p
        let ps' ← scopeCheckPatternList ps
        pure (p' :: ps')
end

mutual
  def scopeCheckDotPattern : CPattern → Pattern → ScopeCheck Pattern
    | .DotP e, _ => do
        let e' ← scopeCheckExpr e
        pure (.DotP e')
    | .SuccP p1', .SuccP p2' => do
        let p2'' ← scopeCheckDotPattern p1' p2'
        pure (.SuccP p2'')
    | .ConP _ pl, .ConP co n pl' => do
        let pl'' ← scopeCheckDotPatternList pl pl'
        pure (.ConP co n pl'')
    | _, p2 => pure p2

  def scopeCheckDotPatternList : List CPattern → List Pattern → ScopeCheck (List Pattern)
    | [],      _       => pure []
    | _,       []      => pure []
    | c :: cs, p :: ps => do
        let p' ← scopeCheckDotPattern c p
        let ps' ← scopeCheckDotPatternList cs ps
        pure (p' :: ps')
end

def collectVarPNamesAux : Nat → List Pattern → List Name → ScopeCheck (List Name)
  | 0,        _,                  _ => throw (.outOfFuel "collectVarPNames")
  | _ + 1,    [],                 acc => pure acc
  | fuel + 1, .SuccP p2 :: pl,    acc => collectVarPNamesAux fuel (p2 :: pl) acc
  | fuel + 1, .ConP _ _ pl2 :: pl, acc => collectVarPNamesAux fuel (pl2 ++ pl) acc
  | fuel + 1, .VarP "" :: pl,     acc => collectVarPNamesAux fuel pl acc
  | fuel + 1, .VarP n :: pl,      acc =>
      if acc.contains n then throw (.rejected .scope ("pattern not linear: " ++ n))
      else collectVarPNamesAux fuel pl (n :: acc)
  | fuel + 1, .DotP _ :: pl,      acc => collectVarPNamesAux fuel pl acc

mutual
  /-- Number of pattern nodes visited by variable collection; dot expressions
      are scoped separately and are not traversed by this operation. -/
  def patternNodeCount : Pattern → Nat
    | .VarP _ | .DotP _ => 1
    | .SuccP p => 1 + patternNodeCount p
    | .ConP _ _ pl => 1 + patternListNodeCount pl

  def patternListNodeCount : List Pattern → Nat
    | [] => 0
    | p :: ps => patternNodeCount p + patternListNodeCount ps
end

def collectVarPNames (pl : List Pattern) : ScopeCheck (List Name) :=
  collectVarPNamesAux (patternListNodeCount pl + 1) pl []

def scopeCheckClause : CClause → ScopeCheck Clause
  | .mk pl rhs => do
      let pl' ← scopeCheckPatternList pl
      let names ← collectVarPNames pl'
      let pl'' ← withReader (fun c => c ++ names) (scopeCheckDotPatternList pl pl')
      let rhs' ← withReader (fun c => c ++ names) (scopeCheckExpr rhs)
      pure (.mk pl'' rhs')

def checkPatternLength : List CClause → Bool
  | []             => true
  | .mk pl _ :: cl => cl.all fun (.mk pl2 _) => pl2.length == pl.length

def scopeCheckFunDecls (co : Co) (decls : List CDeclaration) : ScopeCheck Declaration := do
  -- 1. Check signatures
  let tsl' ← decls.mapM fun d =>
    match d with
    | .FunDecl co' ts _ =>
        if co == co' then scopeCheckTypeSig ts
        else throw (.rejected .scope "mutual combination not supported")
    | _ => throw (.rejected .scope "mutual combination not supported")
  let names := tsl'.map fun (.mk n _) => n
  if names.eraseDups.length != names.length then
    throw (.rejected .scope "duplicate function name in mutual block")
  -- 2. Add function names to scope signature
  decls.forM fun d =>
    match d with
    | .FunDecl _ (.mk n _) _ => modify (addScopeSig n .FunK)
    | _ => pure ()
  -- 3. Check clauses
  let cll' ← decls.mapM fun d =>
    match d with
    | .FunDecl _ (.mk _ _) cl => do
        let cl' ← cl.mapM scopeCheckClause
        if checkPatternLength cl then pure cl'
        else throw (.rejected .scope "pattern length differs")
    | _ => throw (.rejected .scope "mutual combination not supported")
  pure (.FunDecl co (tsl'.zip cll'))

def scopeCheckDeclaration : CDeclaration → ScopeCheck Declaration
  | .DataDecl n sz co tel t cs => do
      let pos := posTelescope tel
      let tt := cTeleToType tel t
      let .mk _ tt' ← scopeCheckTypeSig (.mk n tt)
      let (tel', t') := splitTeleType tel.length ([], tt')
      modify (addScopeSig n .DataK)
      let names := collectTelescopeNames tel
      let cs' ← withReader (fun c => c ++ names) (cs.mapM (scopeCheckConstructor co))
      pure (.DataDecl n sz co pos tel' t' cs')
  | d@(.FunDecl co _ _) => scopeCheckFunDecls co [d]
  | .LetDecl b ts@(.mk n _) e => do
      let e' ← scopeCheckExpr e
      let ts' ← scopeCheckTypeSig ts
      modify (addScopeSig n .LetK)
      pure (.LetDecl b ts' e')
  | .MutualDecl (.FunDecl co ts cl :: rest) =>
      scopeCheckFunDecls co (.FunDecl co ts cl :: rest)
  | .MutualDecl _ => throw (.rejected .scope "mutual combination not supported")

def scopeCheck (dl : List CDeclaration) : Except TCError (List Declaration) :=
  match runScopeCheck [] [] (dl.mapM scopeCheckDeclaration) with
  | .ok (decls, _) => .ok decls
  | .error err     => .error err

/-! ### 7.3 Lexer & Recursive-Descent Parser (`Lexer.hs` & `Parser.hs`) -/

inductive Token : Type where
  | Id      : String → Token
  | Sized   : Token
  | Data    : Token
  | CoData  : Token
  | Mutual  : Token
  | Fun     : Token
  | CoFun   : Token
  | Let     : Token
  | In      : Token
  | Set     : Token
  | Eval    : Token
  | Size    : Token
  | Infty   : Token
  | Succ    : Token
  | BrOpen  : Token
  | BrClose : Token
  | PrOpen  : Token
  | PrClose : Token
  | Sem     : Token
  | Col     : Token
  | Dot     : Token
  | Arrow   : Token
  | Eq      : Token
  | Plus    : Token
  | Lam     : Token
  deriving Repr, Inhabited, BEq

def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\''

def classifyIdent : String → Token
  | "sized"  => .Sized
  | "data"   => .Data
  | "codata" => .CoData
  | "fun"    => .Fun
  | "cofun"  => .CoFun
  | "let"    => .Let
  | "const"  => .Let
  | "in"     => .In
  | "eval"   => .Eval
  | "mutual" => .Mutual
  | "Set"    => .Set
  | "Size"   => .Size
  | s        => .Id s

def dropLineComment : List Char → List Char
  | []          => []
  | '\n' :: cs  => cs
  | _ :: cs     => dropLineComment cs

def dropBlockComment : Nat → List Char → Except TCError (List Char)
  | 0,        _                 => .error (.outOfFuel "Lexer in block comment")
  | _,        []                => .error (.rejected .parse "Unterminated block comment")
  | _ + 1,    '-' :: '}' :: cs  => .ok cs
  | fuel + 1, _ :: cs           => dropBlockComment fuel cs

def takeIdentChars : List Char → List Char × List Char
  | []      => ([], [])
  | c :: cs =>
      if isIdentChar c then
        let (idChars, rest) := takeIdentChars cs
        (c :: idChars, rest)
      else ([], c :: cs)

def scanTokensAux : Nat → List Char → Except TCError (List Token)
  | 0,        _                 => .error (.outOfFuel "Lexer")
  | _,        []                => .ok []
  | fuel + 1, '-' :: '-' :: cs  => scanTokensAux fuel (dropLineComment cs)
  | fuel + 1, '{' :: '-' :: cs  => do
      let rest ← dropBlockComment fuel cs
      scanTokensAux fuel rest
  | fuel + 1, '-' :: '>' :: cs  => do
      let toks ← scanTokensAux fuel cs
      .ok (.Arrow :: toks)
  | fuel + 1, c :: cs =>
      if c.isWhitespace then scanTokensAux fuel cs
      else match c with
      | '#'  => (.Infty :: ·)   <$> scanTokensAux fuel cs
      | '$'  => (.Succ :: ·)    <$> scanTokensAux fuel cs
      | '{'  => (.BrOpen :: ·)  <$> scanTokensAux fuel cs
      | '}'  => (.BrClose :: ·) <$> scanTokensAux fuel cs
      | '('  => (.PrOpen :: ·)  <$> scanTokensAux fuel cs
      | ')'  => (.PrClose :: ·) <$> scanTokensAux fuel cs
      | ';'  => (.Sem :: ·)     <$> scanTokensAux fuel cs
      | ':'  => (.Col :: ·)     <$> scanTokensAux fuel cs
      | '.'  => (.Dot :: ·)     <$> scanTokensAux fuel cs
      | '+'  => (.Plus :: ·)    <$> scanTokensAux fuel cs
      | '='  => (.Eq :: ·)      <$> scanTokensAux fuel cs
      | '\\' => (.Lam :: ·)     <$> scanTokensAux fuel cs
      | _    =>
          if isIdentChar c then
            let (idRest, rest) := takeIdentChars cs
            let ident := String.ofList (c :: idRest)
            (classifyIdent ident :: ·) <$> scanTokensAux fuel rest
          else .error (.rejected .parse ("Unexpected character: " ++ String.ofList [c]))

/- Lean 4.35's String.toList depends on Classical.choice through the proof
   attached to the ASCII UTF-8 assembler. Decode the validated byte sequence
   directly, using the constructive multibyte assemblers and Char.ofNat for
   ASCII. This preserves all Unicode scalar values rather than dropping bytes. -/
def decodeSourceBytes : List UInt8 → List Char → Option (List Char)
  | [], acc => some acc.reverse
  | first :: rest, acc =>
      match ByteArray.utf8DecodeChar?.parseFirstByte first with
      | .invalid => none
      | .done => decodeSourceBytes rest (Char.ofNat first.toNat :: acc)
      | .oneMore =>
          match rest with
          | second :: remaining => do
              let c ← ByteArray.utf8DecodeChar?.assemble₂ first second
              decodeSourceBytes remaining (c :: acc)
          | _ => none
      | .twoMore =>
          match rest with
          | second :: third :: remaining => do
              let c ← ByteArray.utf8DecodeChar?.assemble₃ first second third
              decodeSourceBytes remaining (c :: acc)
          | _ => none
      | .threeMore =>
          match rest with
          | second :: third :: fourth :: remaining => do
              let c ← ByteArray.utf8DecodeChar?.assemble₄ first second third fourth
              decodeSourceBytes remaining (c :: acc)
          | _ => none

/-- Constructive decoding of a String's valid UTF-8 bytes. -/
def sourceChars (s : String) : List Char :=
  (decodeSourceBytes s.toByteArray.toList []).getD []

def tokenizeWithFuel (fuel : Nat) (s : String) : Except TCError (List Token) :=
  scanTokensAux fuel (sourceChars s)

def tokenize (s : String) : Except TCError (List Token) :=
  tokenizeWithFuel ((sourceChars s).length + 10) s

def startsExpr3 : List Token → Bool
  | .Set :: _    => true
  | .Size :: _   => true
  | .Infty :: _  => true
  | .Id _ :: _   => true
  | .PrOpen :: _ => true
  | _            => false

def expectTok (expected : Token) : List Token → Except TCError (List Token)
  | t :: ts => if t == expected then .ok ts else .error (.rejected .parse ("Unexpected token, expected " ++ reprStr expected))
  | []      => .error (.rejected .parse ("Unexpected EOF, expected " ++ reprStr expected))

mutual
  def parseExpr (fuel : Nat) (ts : List Token) : Except TCError (CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Lam :: .Id x :: .Arrow :: rest => do
          let (e, ts1) ← parseExpr fuel' rest
          .ok (.Lam x e, ts1)
      | .Let :: .Id x :: .Col :: rest => do
          let (ty, ts1) ← parseExpr fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e1, ts3) ← parseExpr fuel' ts2
          let ts4 ← expectTok .In ts3
          let (e2, ts5) ← parseExpr fuel' ts4
          .ok (.LLet x ty e1 e2, ts5)
      | .PrOpen :: .Id x :: .Col :: rest =>
          match parseExpr fuel' rest with
          | .ok (ty, .PrClose :: .Arrow :: tsAfter) => do
              let (body, ts1) ← parseExpr fuel' tsAfter
              .ok (.Pi x ty body, ts1)
          | .error (.outOfFuel ctx) => .error (.outOfFuel ctx)
          | .error (.unsupportedCoverage ctx) => .error (.unsupportedCoverage ctx)
          | _ => parseExprArrow fuel' ts
      | _ => parseExprArrow fuel' ts

  def parseExprArrow (fuel : Nat) (ts : List Token) : Except TCError (CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 => do
        let (e1, ts1) ← parseExpr1 fuel' ts
        match ts1 with
        | .Arrow :: ts2 => do
            let (e2, ts3) ← parseExpr fuel' ts2
            .ok (.Pi "" e1 e2, ts3)
        | _ => .ok (e1, ts1)

  def parseExpr1 (fuel : Nat) (ts : List Token) : Except TCError (CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 => do
        let (es, ts1) ← parseExpr2 fuel' ts
        match es with
        | [e]     => .ok (e, ts1)
        | e :: el => .ok (.App e el, ts1)
        | []      => .error (.rejected .parse "Parse error: empty expression")

  def parseExpr2 (fuel : Nat) (ts : List Token) : Except TCError (List CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (se, ts1) ← parseSE fuel' rest
          let (more, ts2) ← parseExpr3Many fuel' ts1
          .ok (.Succ se :: more, ts2)
      | _ => do
          let (e, ts1) ← parseExpr3 fuel' ts
          let (more, ts2) ← parseExpr3Many fuel' ts1
          .ok (e :: more, ts2)

  def parseSE (fuel : Nat) (ts : List Token) : Except TCError (CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (se, ts1) ← parseSE fuel' rest
          .ok (.Succ se, ts1)
      | _ => parseExpr3 fuel' ts

  def parseExpr3Many (fuel : Nat) (ts : List Token) : Except TCError (List CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      if startsExpr3 ts then do
        let (e, ts1) ← parseExpr3 fuel' ts
        let (es, ts2) ← parseExpr3Many fuel' ts1
        .ok (e :: es, ts2)
      else .ok ([], ts)

  def parseExpr3 (fuel : Nat) (ts : List Token) : Except TCError (CExpr × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Set :: rest   => .ok (.Set, rest)
      | .Size :: rest  => .ok (.Size, rest)
      | .Infty :: rest => .ok (.Infty, rest)
      | .Id x :: rest  => .ok (.Ident x, rest)
      | .PrOpen :: rest => do
          let (e, ts1) ← parseExpr fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (e, ts2)
      | _ => .error (.rejected .parse "Parse error in atomic expression")
end

mutual
  def parsePattern (fuel : Nat) (ts : List Token) : Except TCError (CPattern × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .PrOpen :: .Succ :: rest => do
          let (sp, ts1) ← parseSP fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (.SuccP sp, ts2)
      | .PrOpen :: .Id c :: rest => do
          let (ps, ts1) ← parsePatternsUntilEq fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (.ConP c ps, ts2)
      | .Id x :: rest => .ok (.IdentP x, rest)
      | .Dot :: rest => do
          let (e, ts1) ← parseExpr3 fuel' rest
          .ok (.DotP e, ts1)
      | _ => .error (.rejected .parse "Parse error in pattern")

  def parseSP (fuel : Nat) (ts : List Token) : Except TCError (CPattern × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (sp, ts1) ← parseSP fuel' rest
          .ok (.SuccP sp, ts1)
      | _ => parsePattern fuel' ts

  def parsePatternsUntilEq (fuel : Nat) (ts : List Token) : Except TCError (List CPattern × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Eq :: _      => .ok ([], ts)
      | .PrClose :: _ => .ok ([], ts)
      | _ => do
          let (p, ts1) ← parsePattern fuel' ts
          let (ps, ts2) ← parsePatternsUntilEq fuel' ts1
          .ok (p :: ps, ts2)
end

def parseTypeSig (fuel : Nat) : List Token → Except TCError (CTypeSig × List Token)
  | .Id name :: .Col :: ts => do
      let (ty, ts1) ← parseExpr fuel ts
      .ok (.mk name ty, ts1)
  | _ => .error (.rejected .parse "Parse error in type signature")

def parseDataTelescope (fuel : Nat) (ts : List Token) : Except TCError (CTelescope × List Token) :=
  match fuel with
  | 0 => .error (.outOfFuel "Parser")
  | fuel' + 1 =>
    match ts with
    | .PrOpen :: .Plus :: .Id x :: .Col :: rest => do
        let (ty, ts1) ← parseExpr fuel' rest
        let ts2 ← expectTok .PrClose ts1
        let (tel, ts3) ← parseDataTelescope fuel' ts2
        .ok (.PosTB x ty :: tel, ts3)
    | .PrOpen :: .Id x :: .Col :: rest => do
        let (ty, ts1) ← parseExpr fuel' rest
        let ts2 ← expectTok .PrClose ts1
        let (tel, ts3) ← parseDataTelescope fuel' ts2
        .ok (.TB x ty :: tel, ts3)
    | _ => .ok ([], ts)

def parseConstructors (fuel : Nat) (ts : List Token) : Except TCError (List CTypeSig × List Token) :=
  match fuel with
  | 0 => .error (.outOfFuel "Parser")
  | fuel' + 1 =>
    match ts with
    | .BrClose :: _ => .ok ([], ts)
    | _ => do
        let (c, ts1) ← parseTypeSig fuel' ts
        match ts1 with
        | .Sem :: ts2 => do
            let (cs, ts3) ← parseConstructors fuel' ts2
            .ok (c :: cs, ts3)
        | _ => .ok ([c], ts1)

def parseClause (fuel : Nat) : List Token → Except TCError (CClause × List Token)
  | .Id _ :: ts => do
      let (ps, ts1) ← parsePatternsUntilEq fuel ts
      let ts2 ← expectTok .Eq ts1
      let (rhs, ts3) ← parseExpr fuel ts2
      .ok (.mk ps rhs, ts3)
  | _ => .error (.rejected .parse "Parse error in clause")

def parseClauses (fuel : Nat) (ts : List Token) : Except TCError (List CClause × List Token) :=
  match fuel with
  | 0 => .error (.outOfFuel "Parser")
  | fuel' + 1 =>
    match ts with
    | .BrClose :: _ => .ok ([], ts)
    | _ => do
        let (c, ts1) ← parseClause fuel' ts
        match ts1 with
        | .Sem :: ts2 => do
            let (cs, ts3) ← parseClauses fuel' ts2
            .ok (c :: cs, ts3)
        | _ => .ok ([c], ts1)

def parseDataRest (fuel : Nat) (name : Name) (sz : Sized) (co : Co) (ts : List Token)
    : Except TCError (CDeclaration × List Token) := do
  let (tel, ts1) ← parseDataTelescope fuel ts
  let ts2 ← expectTok .Col ts1
  let (ty, ts3) ← parseExpr fuel ts2
  let ts4 ← expectTok .BrOpen ts3
  let (cs, ts5) ← parseConstructors fuel ts4
  let ts6 ← expectTok .BrClose ts5
  .ok (.DataDecl name sz co tel ty cs, ts6)

mutual
  def parseDeclaration (fuel : Nat) (ts : List Token) : Except TCError (CDeclaration × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | .Data :: .Id name :: rest => parseDataRest fuel' name .NotSized .Ind rest
      | .Sized :: .Data :: .Id name :: rest => parseDataRest fuel' name .Sized .Ind rest
      | .CoData :: .Id name :: rest => parseDataRest fuel' name .NotSized .CoInd rest
      | .Sized :: .CoData :: .Id name :: rest => parseDataRest fuel' name .Sized .CoInd rest
      | .Fun :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .BrOpen ts1
          let (cls, ts3) ← parseClauses fuel' ts2
          let ts4 ← expectTok .BrClose ts3
          .ok (.FunDecl .Ind tsig cls, ts4)
      | .CoFun :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .BrOpen ts1
          let (cls, ts3) ← parseClauses fuel' ts2
          let ts4 ← expectTok .BrClose ts3
          .ok (.FunDecl .CoInd tsig cls, ts4)
      | .Mutual :: .BrOpen :: rest => do
          let (decls, ts1) ← parseDeclarations fuel' rest
          let ts2 ← expectTok .BrClose ts1
          .ok (.MutualDecl decls, ts2)
      | .Let :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e, ts3) ← parseExpr fuel' ts2
          .ok (.LetDecl false tsig e, ts3)
      | .Eval :: .Let :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e, ts3) ← parseExpr fuel' ts2
          .ok (.LetDecl true tsig e, ts3)
      | _ => .error (.rejected .parse "Parse error in declaration")

  def parseDeclarations (fuel : Nat) (ts : List Token) : Except TCError (List CDeclaration × List Token) :=
    match fuel with
    | 0 => .error (.outOfFuel "Parser")
    | fuel' + 1 =>
      match ts with
      | []           => .ok ([], [])
      | .BrClose :: _ => .ok ([], ts)
      | _ => do
          let (d, ts1) ← parseDeclaration fuel' ts
          let (ds, ts2) ← parseDeclarations fuel' ts1
          .ok (d :: ds, ts2)
end

def parseTokensWithFuel (fuel : Nat) (ts : List Token) : Except TCError (List CDeclaration) := do
  let (decls, rest) ← parseDeclarations fuel ts
  if rest.isEmpty then .ok decls
  else .error (.rejected .parse "Parse error: unconsumed tokens")

def parseTokens (ts : List Token) : Except TCError (List CDeclaration) :=
  parseTokensWithFuel (ts.length * 4 + 20) ts

/-- Full end-to-end Constructive Lean 4 pipeline on raw `.ma` source strings:
    `tokenize → parseTokens → scopeCheck → checkProgram`. -/
def checkSource (src : String) : Except TCError TCState := do
  let toks ← tokenize src
  let cdecls ← parseTokens toks
  let adecls ← scopeCheck cdecls
  checkProgram adecls

mutual
  def showVal : Val → String
    | .VSet        => "Set"
    | .VSize       => "Size"
    | .VInfty      => "#"
    | .VSucc v     => "($ " ++ showVal v ++ ")"
    | .VApp v vl   => "(" ++ showVal v ++ " " ++ showValList vl ++ ")"
    | .VCon _ n    => n
    | .VDef n      => n
    | .VGen k      => toString k
    | .VPi x av _ e => "(" ++ x ++ " : " ++ showVal av ++ ") -> " ++ prettyExpr e
    | .VLam x _ e   => "(\\" ++ x ++ " -> " ++ prettyExpr e ++ ")"

  def showValList : List Val → String
    | []      => ""
    | [v]     => showVal v
    | v :: vl => showVal v ++ " " ++ showValList vl
end

/-- Full end-to-end check and evaluation of `eval let` declarations (`Main.hs` lines 37–52). -/
def evalSource (src : String) : Except TCError (List String) := do
  let toks ← tokenize src
  let cdecls ← parseTokens toks
  let adecls ← scopeCheck cdecls
  let st ← checkProgram adecls
  let evalDecls := adecls.filterMap fun d =>
    match d with
    | .LetDecl true (.mk n _) e => some (n, e)
    | _                         => none
  evalDecls.mapM fun (n, e) =>
    match runTypeCheck st (whnf defaultFuel [] e) with
    | .ok (v, _) => .ok (n ++ " evaluates to " ++ showVal v)
    | .error err => .error err

end MugdaCore
