import Mettapedia.Languages.Lean.Declarations.Terms
import Mettapedia.Languages.Lean.Declarations.TargetEnvironment
import Mettapedia.Languages.Lean.Recursion.FuelDerive

/-!
Export the code-equation slice's test terms, and the equation theorems of the
functions they use, as first-order data with types kept, for the Egal
interpretation.

Run from the project root:
`lake env lean scripts/ExportLeanTerms.lean`
reads the slice's test sources from `artifacts/lean-code-equations/core/tests.tsv`
and writes `artifacts/lean-declarations/terms.metta`:

  (LeanComputation i term type)          test i, read
  (LeanComputationRefused i reason)      test i, not first order
  (LeanFunction c (thm ..))              a function and its equation theorems
  (LeanFunctionRefused c reason)         a function whose equations are not read
  (LeanProjection c S S.mk i n)          the projection of field i of structure S
                                         with n parameters
  (LeanPointwise thm k)                  an equation read pointwise, k arguments added
  (LeanCasesOn c F)                      the case analysis of the family F
  (LeanEquation thm (binders ..) type lhs rhs)
  (LeanReceipt thm digest)               the equation is a receipt of the slice
  (LeanSourceEquations c (thm ..))       original equations still required when
                                        a checked fuel bridge supplies the reading
  (LeanSourceEquationRefused c thm why)  a required source statement not yet readable
  (LeanIntrinsic c kind (binders ..) type) a kernel primitive in the stated profile
  (LeanUniverseProfile c Type (levels ..)) successor-universe specialization
  (EgalName name ident)                  for each function and theorem
  (LeanProofTerms thm (t ..))            the terms Lean records for the proofs of an
                                         equation's right side: one entry for each
                                         `(proof)` there, in order; `(proof)` where
                                         no term was read
  (LeanArgumentProofs thm (t ..))        the same for the arguments of its left side
  (LeanLemma thm (binders ..) statement) a theorem those terms cite
  (LeanFamilyUses F (c ..))              the definitions the fields of the family F are
                                         written with: F is read after those functions
  (LeanLemmaTerm thm term)               the term of an auxiliary theorem Lean abstracts
                                         from a definition (`f._proof_1`)
  (LeanTheorem thm statement)            a theorem of a carried development, its statement read

A receipt of the code-equation export (`artifacts/lean-code-equations/core/receipts.tsv`)
names the theorem a MeTTa rule was taken from and the digest of its statement.
An equation read here that is such a receipt must have the same digest, or the
export fails: the MeTTa rule and the Egal theorem then come from one statement.

The functions are the closure of the constants the readable tests apply,
following the constants of each equation. Families and constructors are not
functions here; their declarations come from `ExportLeanDeclarations.lean`.

With `LEAN_TERMS_TARGET=<target>` in the environment, the roots are the
functions listed in `artifacts/lean-declarations/<target>/roots.txt` (one
constant per line, after a header line, its first column) instead of the
slice's tests, and the export is `artifacts/lean-declarations/<target>/terms.metta`.

A matcher (the function Lean generates for a `match`) is read by its
definition, `(LeanMatcher c (binders ..) body)`: a tree of case analyses
(`X.casesOn`) over its discriminants.

With `LEAN_DECLARATIONS_CHECK=1` in the environment, the export is written
beside the committed one and compared; any difference fails.
`LEAN_TERMS_OUT` selects a separate output directory for qualification before
publishing an inventory to a running consumer.
-/

open Lean Meta Elab Term
open Mettapedia.Languages.Lean.Declarations

def elabClosed (src : String) : TermElabM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError "parse error in {src}: {e}"
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The roots of a carried development: the first column of each row of its
roots file; rows starting with `#` are comments. -/
def targetRoots (target : String) : IO (List Name) := do
  let rows ← IO.FS.lines s!"artifacts/lean-declarations/{target}/roots.txt"
  return rows.toList.filterMap fun row =>
    match (row.splitOn "\t").head? with
    | some c => if c.isEmpty || c.startsWith "#" then none else some c.toName
    | none => none

/-- The library theorems a target's proofs use (`Relation.ReflTransGen.head`,
...), listed in the Egal target's `.lemmas` file: their statements are read
like the development's own, to be proved in Egal. -/
def targetLemmas (target : String) : IO (List Name) := do
  let path : System.FilePath := s!"Mettapedia/Languages/Lean/Egal/targets/{target}.lemmas"
  unless ← path.pathExists do return []
  let rows ← IO.FS.lines path
  return rows.toList.filterMap fun row =>
    let row := row.trimAscii.toString
    if row.isEmpty || row.startsWith "#" then none else some row.toName

/-- A declaration Lean generates beside a source declaration (recursors,
size functions, no-confusion, matchers, equation lemmas, structural-recursion
helpers): its evidence is its parent's, so it is not a root of the term export.
Matchers are reached from the equations that apply them. -/
def generatedHelper (c : Name) : MetaM Bool := do
  let env ← getEnv
  if isAuxRecursor env c || isNoConfusion env c || isCasesOnRecursor env c then return true
  if (← getMatcherInfo? c).isSome then return true
  -- A helper of a generated helper (`T.brecOn.go`), or a nested-block recursor (`T.rec_1`).
  if c.components.dropLast.any (fun p => p.toString.startsWith "brecOn" || p.toString.startsWith "below") then
    return true
  match c with
  | .str _ s =>
      if s.startsWith "rec_" then return true
      let helpers := ["rec", "ctorElim", "ctorIdx", "toCtorIdx", "noConfusionType", "below", "brecOn",
        "binductionOn", "ibelow", "eq_def", "_sunfold", "_unsafe_rec", "sizeOf_spec", "injEq", "inj",
        "ext_iff", "_f", "ctorElimType"]
      return s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s.startsWith "_sizeOf" || helpers.contains s || c.isInternal
  | _ => return c.isInternal

/-- The tests of a code-equation export (the slice's `core`, or a carried
development's): index and Lean source. -/
def testSources (dir : String := "core") : IO (List (Nat × String)) := do
  let path : System.FilePath := s!"artifacts/lean-code-equations/{dir}/tests.tsv"
  unless ← path.pathExists do return []
  let rows ← IO.FS.lines path
  return rows.toList.drop 1 |>.filterMap fun row =>
    match row.splitOn "\t" with
    | i :: src :: _ => i.toNat?.map (·, src)
    | _ => none

def reasonText (reason : String) : String := (Json.str reason).compress

def universeProfileAtom (name : Name) (levels : List Level) : MetaM String := do
  let atoms ← levels.mapM fun level => do
    let some value := FLevel.of? level | throwError "unsupported quotient profile universe: {level}"
    pure value.atom
  return s!"(LeanUniverseProfile {name} Type ({" ".intercalate atoms}))"

/-- The receipts of the code-equation slice: theorem and statement digest. -/
def receipts : IO (List (String × String)) := do
  let rows ← IO.FS.lines "artifacts/lean-code-equations/core/receipts.tsv"
  return rows.toList.drop 1 |>.filterMap fun row =>
    match row.splitOn "\t" with
    | _ :: thm :: _ :: digest :: _ => some (thm, digest)
    | _ => none

/-- A constant that is a family or a constructor, not a function. -/
def isData (c : Name) : MetaM Bool := do
  match (← getEnv).find? c with
  | some (.inductInfo _) | some (.ctorInfo _) => return true
  | _ => return false

/-- A matcher's definition: the binders of its value (motive, discriminants,
alternatives) and its body. -/
def readMatcher (c : Name) : FReadM (List FBinder × FTerm) := do
  let info ← getConstInfoDefn c
  let go : MetaM (Except String (List FBinder × FTerm)) := lambdaTelescope info.value fun xs body => do
    let (names, _) ← nameAll {} [] xs "x"
    ExceptT.run do
      let binders ← xs.toList.mapM fun x => do
        return FBinder.term names[x.fvarId!]! (← readTerm names (← inferType x))
      return (binders, ← readTerm names body)
  ExceptT.mk go

/-- The proof terms of one side of an equation, when any was read. -/
def proofTermsOf (record : String) (name : Name) (side : FTerm) : Option String :=
  let proofs := side.proofTerms
  if proofs.any (·.isSome) then
    let entries := proofs.map fun
      | some term => term.atomWithProofs
      | none => "(proof)"
    some s!"({record} {name} ({" ".intercalate entries}))"
  else none

/-- The proof terms of an equation: of its right side, and of the arguments
of its left side (a proof parameter there is the hypothesis it binds). -/
def proofTermsAtoms (eqn : FEquation) : List String :=
  (proofTermsOf "LeanProofTerms" eqn.name eqn.rhs).toList ++
    (proofTermsOf "LeanArgumentProofs" eqn.name eqn.lhs).toList

/-- A theorem's statement with its binders: as `readSignature`, with the
propositions read as statements, so that a proposition given by a definition
stays as Lean writes it; a proposition whose head is a projection at an
instance is in its proposition form, as in the definitions that cite it. -/
def readLemma (type : Expr) : FReadM (List FBinder × FTerm) := do
  let go : MetaM (Except String (List FBinder × FTerm)) := forallTelescope type fun xs body => do
    let (names, _) ← nameAll {} [] xs "x"
    ExceptT.run do
      let binders ← xs.toList.mapM fun x => do
        let name := names[x.fvarId!]!
        let ty ← inferType x
        if let .sort u := ty then
          if u.isZero then return FBinder.term name .prop
          if let .param l := u then return FBinder.sort name l.toString
          match typeLevel? u with
          | some level => return FBinder.type name level
          | none => throwThe String s!"a binder of sort {u}: {name}"
        if ← isProp ty then return FBinder.hyp name (← readStatement names ty (projections := true))
        return FBinder.term name (← readTerm names ty)
      return (binders, ← readStatement names body (projections := true))
  ExceptT.mk go

/-- The definitions a family's fields are written with: a field's type, or a
proof field's proposition as read (`propositionForm`), may apply a definition
that is not an abbreviation (`Multiset α`, `s.Nodup` in `Finset`); the
family's reading applies it too, so it is read as a function. -/
def fieldDefinitions (ctor : Name) : MetaM (Array Name) := do
  let info ← getConstInfoCtor ctor
  forallTelescope info.type fun xs _ => do
    let mut found : Array Name := #[]
    for x in xs.extract info.numParams xs.size do
      let type ← inferType x
      let type ← if ← isProp type then propositionForm type else whnfR type
      for c in type.getUsedConstants do
        if let some (.defnInfo _) := (← getEnv).find? c then
          unless (← isReducible c) || (← getProjectionFnInfo? c).isSome || (← isInstance c) ||
              found.contains c do
            found := found.push c
    return found

/-- An auxiliary theorem Lean abstracts from a definition: `f._proof_1`. -/
def auxiliaryProof (c : Name) : Bool :=
  match c with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

def binderType : FBinder → Option FTerm
  | .term _ t => some t
  | .hyp _ p => some p
  | _ => none

/-- A name in the structural form of a manifest (`["str", parent, "s"]`). -/
partial def nameOfJson : Json → Option Name
  | .arr #[.str "anonymous"] => some .anonymous
  | .arr #[.str "str", p, .str s] => (nameOfJson p).map (·.str s)
  | .arr #[.str "num", p, .num n] => (nameOfJson p).map (·.num n.mantissa.toNat)
  | _ => none

/-- For each constant of a target's manifest: whether Lean unfolds it where it
is used (reducible) and whether it is an instance, whose field projections
reading unfolds to the fields' values. -/
def manifestAttributes (target : String) : TermElabM (Array String) := do
  let path : System.FilePath := s!"artifacts/lean-declarations/{target}/manifest.tsv"
  unless ← path.pathExists do return #[]
  let rows ← IO.FS.lines path
  let header := (rows[0]!.splitOn "\t")
  let some col := header.findIdx? (· == "structural_name") | throwError "manifest: no structural_name column"
  let mut out : Array String := #[]
  for row in rows.toList.drop 1 do
    let cells := row.splitOn "\t"
    let some json := (Json.parse cells[col]!).toOption | throwError "manifest: unreadable name {cells[0]!}"
    let some c := nameOfJson json | throwError "manifest: unreadable name {cells[0]!}"
    if (← getEnv).contains c then
      if ← isReducible c then out := out.push s!"(LeanReducible {c})"
      if ← isInstance c then out := out.push s!"(LeanInstance {c})"
  return out

def exportTerms (target : Option String) : TermElabM String := do
  let slip ← if target.isNone then receipts else pure []
  let mut out : Array String := #[]
  let mut roots : Array Name := #[]
  let mut cited : Array Name := #[]
  if let some t := target then
    let requestedLemmas ← targetLemmas t
    for c in (← targetRoots t) ++ requestedLemmas do
      if let some (.thmInfo info) := (← getEnv).find? c then
        -- A theorem of the development: its statement, to be proved in Egal.
        -- An explicitly requested source equation is an obligation even
        -- though its declaration was generated by Lean's equation compiler.
        unless (← generatedHelper c) && !requestedLemmas.contains c do
          match ← (readStatement {} info.type).run with
          | .ok stmt =>
              out := out.push s!"(EgalName {c} {egalIdent c.toString})"
              out := out.push s!"(LeanTheorem {c} {stmt.atom})"
              for d in stmt.constants do
                unless roots.contains d do roots := roots.push d
          | .error reason => out := out.push s!"(LeanTheoremRefused {c} {reasonText reason})"
        continue
      if ← generatedHelper c then continue
      unless roots.contains c do roots := roots.push c
  for (i, src) in ← testSources (target.getD "core") do
    let e ← elabClosed src
    match ← (readClosed e).run with
    | .ok (term, type) =>
        out := out.push s!"(LeanComputation {i} {term.atom} {type.atom})"
        for c in term.constants do
          unless roots.contains c do roots := roots.push c
    | .error reason => out := out.push s!"(LeanComputationRefused {i} {reasonText reason})"
  let mut queue := roots
  let mut done : NameSet := {}
  let mut k := 0
  let mut j := 0
  let mut lemmaRecords : Array String := #[]
  -- The functions, and the theorems their proofs cite, until neither adds to
  -- the other: a cited statement may apply a function not yet read.
  while k < queue.size || j < cited.size do
    while k < queue.size do
      let c := queue[k]!
      k := k + 1
      if done.contains c then continue
      done := done.insert c
      if ← isData c then
        -- A family's case analysis, for the case trees of nested patterns.
        if let some (.inductInfo info) := (← getEnv).find? c then
          let co := c ++ `casesOn
          unless done.contains co || queue.contains co do queue := queue.push co
          let mut uses : Array Name := #[]
          for ctor in info.ctors do
            for d in ← fieldDefinitions ctor do
              unless uses.contains d do uses := uses.push d
              unless done.contains d || queue.contains d do queue := queue.push d
          unless uses.isEmpty do
            out := out.push s!"(LeanFamilyUses {c} ({" ".intercalate (uses.toList.map toString)}))"
        continue
      out := out.push s!"(EgalName {c} {egalIdent c.toString})"
      if let some kind ← QuotientProfile.kind? c then
        let (signature, levels) ← QuotientProfile.typeInstance c
        match ← (readSignature signature).run, ← (readTerm {} signature).run with
        | .ok (binders, result), .ok functionType =>
            out := out.push s!"(LeanIntrinsic {c} {kind} ({" ".intercalate (binders.map FBinder.atom)}) {result.atom})"
            out := out.push s!"(LeanFunctionType {c} {functionType.atom})"
            out := out.push (← universeProfileAtom c levels)
            let law? := if c == ``Quot.lift then some (``QuotientProfile.lift_beta, false)
              else if c == ``Quot.mk then some (``Quot.sound, true) else none
            if let some (law, specialize) := law? then
              match ← (readEquation law specialize).run with
              | .ok equation =>
                  out := out.push s!"(LeanPrimitiveLaw {c} {law})"
                  out := out.push s!"(EgalName {law} {egalIdent c.toString}_source_law)"
                  out := out.push equation.atom
              | .error reason => throwError "quotient primitive law is not readable: {law}: {reason}"
        | .error reason, _ | _, .error reason =>
            out := out.push s!"(LeanFunctionRefused {c} {reasonText reason})"
        continue
      let typeProfile := c == ``Quot.liftOn
      if typeProfile then
        let (_, levels) ← QuotientProfile.typeInstance c
        out := out.push (← universeProfileAtom c levels)
      -- A reducible abbreviation of a type or a family of propositions
      -- (`Env := List Val`, `Steps := ReflTransGen StepRel`) is unfolded where
      -- it is used, and is not read as a function.
      if let some (.defnInfo info) := (← getEnv).find? c then
        if (← isReducible c) && (← isTypeFormerType info.type) then continue
      if isCasesOnRecursor (← getEnv) c then
        out := out.push s!"(LeanCasesOn {c} {c.getPrefix})"
        continue
      if let some info ← getProjectionFnInfo? c then
        let some structName := (← getEnv).find? info.ctorName |>.bind
            (fun | .ctorInfo v => some v.induct | _ => none)
          | out := out.push s!"(LeanFunctionRefused {c} {reasonText "a projection of no structure"})"
        out := out.push s!"(LeanProjection {c} {structName} {info.ctorName} {info.i} {info.numParams})"
        continue
      -- A matcher is read by its definition, a tree of case analyses over its
      -- discriminants; its uses are that tree at their arguments.
      if (← getMatcherInfo? c).isSome then
        match ← (readMatcher c).run with
        | .ok (binders, body) =>
            out := out.push s!"(LeanMatcher {c} ({" ".intercalate (binders.map FBinder.atom)}) {body.atom})"
            for d in body.constants do
              unless done.contains d || queue.contains d do queue := queue.push d
        | .error reason => out := out.push s!"(LeanFunctionRefused {c} {reasonText reason})"
        continue
      -- A recursor: its family; the reading decides from the family's
      -- elimination whether it computes (a subsingleton's large eliminator).
      if let some (.recInfo info) := (← getEnv).find? c then
        out := out.push s!"(LeanRecursor {c} {info.getMajorInduct})"
        continue
      match ← getEqnsFor? c with
      | none => out := out.push s!"(LeanFunctionRefused {c} {reasonText "no equation theorems"})"
      | some thms =>
          let sourceThms := thms
          -- A constructor case the hypotheses refute has no equation from the
          -- equation compiler; a theorem `c.eq_absent`, proved in Lean, states
          -- it (Mettapedia/Languages/Lean/Recursion/AbsentCases.lean).
          let thms := if (← getEnv).contains (c ++ `eq_absent) then thms.push (c ++ `eq_absent) else thms
          -- A function defined by well-founded recursion is read by `c.eq_fuel`,
          -- proved in Lean: c equals a fuelled function, structural on the fuel
          -- (Mettapedia/Languages/Lean/Recursion/FuelReadings.lean), or through a
          -- source-derived FuelDerive bridge. Original equations remain explicit
          -- evidence obligations; defining a fuel reading does not prove them in Egal.
          let derived := Mettapedia.Languages.Lean.Recursion.FuelDerive.registry.getState (← getEnv)
          let thms := if (← getEnv).contains (c ++ `eq_fuel) then #[c ++ `eq_fuel]
            else match derived.find? (·.source == c) with
              | some entry => #[entry.bridge]
              | none => thms
          let obligations := if thms != sourceThms &&
              ((← getEnv).contains (c ++ `eq_fuel) || (derived.any (·.source == c)))
            then sourceThms else #[]
          unless obligations.isEmpty do
            out := out.push s!"(LeanSourceEquations {c} ({" ".intercalate (obligations.toList.map toString)}))"
            for equationName in obligations do
              match ← (readEquation equationName).run with
              | .error reason =>
                out := out.push s!"(LeanSourceEquationRefused {c} {equationName} {reasonText reason})"
              | .ok equation =>
                out := out.push s!"(EgalName {equationName} {egalIdent equationName.toString})"
                out := out.push equation.atom
                for proofs in proofTermsAtoms equation do out := out.push proofs
                for d in equation.rhs.cited do
                  unless cited.contains d do cited := cited.push d
                if let some (_, digest) := slip.find? (·.1 == equationName.toString) then
                  unless toString (← getConstInfo equationName).type.hash == digest do
                    throwError "source receipt digest differs: {equationName}"
                  out := out.push s!"(LeanReceipt {equationName} {digest})"
                for term in [equation.lhs, equation.rhs, equation.type] ++ equation.binders.filterMap binderType do
                  for dependency in term.constants do
                    unless done.contains dependency || queue.contains dependency do queue := queue.push dependency
          let mut read : Array FEquation := #[]
          let mut refusal : Option String := none
          for thm in thms do
            match ← (readEquation thm typeProfile).run with
            | .ok eqn => read := read.push eqn
            | .error reason =>
                if refusal.isNone then refusal := some s!"{thm}: {reason}"
          match refusal with
          | some reason => out := out.push s!"(LeanFunctionRefused {c} {reasonText reason})"
          | none =>
              out := out.push s!"(LeanFunction {c} ({" ".intercalate (thms.toList.map toString)}))"
              -- The function's declared type: the result type of a decision
              -- procedure depends on its arguments, which closed equations do
              -- not show.
              let sourceType ← if typeProfile then pure (← QuotientProfile.typeInstance c).1
                else pure (← getConstInfo c).type
              if let .ok ty ← (readTerm {} sourceType).run then
                out := out.push s!"(LeanFunctionType {c} {ty.atom})"
              for eqn in read do
                out := out.push s!"(EgalName {eqn.name} {egalIdent eqn.name.toString})"
                out := out.push eqn.atom
                for proofs in proofTermsAtoms eqn do out := out.push proofs
                for d in eqn.rhs.cited do
                  unless cited.contains d do cited := cited.push d
                if let some (_, digest) := slip.find? (·.1 == eqn.name.toString) then
                  let mine := toString (← getConstInfo eqn.name).type.hash
                  unless mine == digest do
                    throwError "receipt {eqn.name}: digest {digest} in receipts.tsv, {mine} here"
                  out := out.push s!"(LeanReceipt {eqn.name} {digest})"
                for t in [eqn.lhs, eqn.rhs, eqn.type] ++ eqn.binders.filterMap binderType do
                  for d in t.constants do
                    unless done.contains d || queue.contains d do queue := queue.push d
    -- The theorems the proof terms cite: their statements, and the terms of the
    -- auxiliary theorems, with what those cite in turn.
    while j < cited.size do
      let c := cited[j]!
      j := j + 1
      let info ← getConstInfo c
      unless (out ++ lemmaRecords).any (·.startsWith s!"(EgalName {c} ") do
        lemmaRecords := lemmaRecords.push s!"(EgalName {c} {egalIdent c.toString})"
      match ← (readLemma info.type).run with
      | .ok (binders, statement) =>
          lemmaRecords := lemmaRecords.push
            s!"(LeanLemma {c} ({" ".intercalate (binders.map FBinder.atom)}) {statement.atom})"
          -- What the statement applies is read too: a proposition given by a
          -- definition stays as written, and the definition is a function.
          for term in statement :: binders.filterMap binderType do
            for d in term.constants do
              unless done.contains d || queue.contains d do queue := queue.push d
      | .error reason => lemmaRecords := lemmaRecords.push s!"(LeanLemmaRefused {c} {reasonText reason})"
      if auxiliaryProof c then
        if let .thmInfo aux := info then
          let attempt : MetaM (Except String FTerm) :=
            try (readTerm.readProof {} aux.value).run catch _ => pure (.error "not readable")
          if let .ok term ← attempt then
            lemmaRecords := lemmaRecords.push s!"(LeanLemmaTerm {c} {term.atomWithProofs})"
            for d in term.cited do
              unless cited.contains d do cited := cited.push d
  -- One identifier for each name: a theorem that is also read as a function
  -- keeps the function's.
  let named (line : String) : Option String :=
    if line.startsWith "(EgalName " then (line.splitOn " ")[1]? else none
  let functionNames := out.filterMap named
  out := out ++ lemmaRecords.filter fun line =>
    match named line with
    | some name => !functionNames.contains name
    | none => true
  if let some t := target then
    out := out ++ (← manifestAttributes t)
  return "\n".intercalate out.toList ++ "\n"

def runExport : TermElabM Unit := do
  let target := (← IO.getEnv "LEAN_TERMS_TARGET").filter (!·.isEmpty)
  let moduleDirectory : System.FilePath := match target with
    | some name => "artifacts/lean-declarations" / name
    | none => "artifacts/lean-declarations"
  discard <| TargetEnvironment.load moduleDirectory
  let text := ";; Generated by scripts/ExportLeanTerms.lean.\n" ++ (← exportTerms target)
  let base : System.FilePath := "artifacts/lean-declarations"
  let defaultDir := match target with | some t => base / t | none => base
  let dir : System.FilePath := (← IO.getEnv "LEAN_TERMS_OUT").map System.FilePath.mk |>.getD defaultDir
  if (← IO.getEnv "LEAN_DECLARATIONS_CHECK") == some "1" then
    let committed ← IO.FS.readFile (dir / "terms.metta")
    if committed != text then throwError "check: terms.metta differs"
    IO.println "check: the committed terms equal a fresh export"
  else
    IO.FS.writeFile (dir / "terms.metta") text
    IO.println "exported terms.metta"

#eval runExport
