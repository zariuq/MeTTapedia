import Lean

/-! Compare public constant types using Lean's definitional equality.
Run with `lean --run` in the package environment, supplying the module
name and the previous compiled module. Pass `--values` to compare the bodies
of public definitions as well. The comparison resolves constants in the
current environment. Use matching dependency versions and `--exact-private`
when local private definitions can differ. This expands their bodies from
each variant's own compiled artifacts before comparing. Retained local
inductives, constructors, and recursors require exact kernel declarations
and exact local dependencies. Pass `--baseline-imports`
when an import has been removed. The type and value comparison can use the
older dependencies once export visibility has been checked through the
current module alone. Use `--omit-proof-matchers` for the theorem
interface. This leaves out only registered matchers under theorem names
that are unreachable from the published types and executable bodies. -/

open Lean Meta

private def isExportedName (name : Name) : Bool :=
  !name.isInternal && !isPrivateName name

private def requireExport (name : Name) : MetaM ConstantInfo := do
  unless (← getEnv).contains name do
    withCurrHeartbeats (executeReservedNameAction name)
  let some declaration := (← getEnv).find? name | throwError "Missing export {name}"
  return declaration

/-- Kernel data that stays behind a local name must retain its exact declaration,
including constructor order and the reduction rules of any recursor used. -/
private def sameLocalDeclaration (before after : ConstantInfo) : Bool :=
  match before, after with
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
      a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | _, _ => false

private def localReferences (info : ConstantInfo) (followProofs := true) : BaseIO (Array Name) := do
  let mut expressions := #[info.type]
  unless !followProofs && (info matches .thmInfo _) do
    if let some body := info.value? (allowOpaque := true) then
      expressions := expressions.push body
  let mut names := #[]
  match info with
  | .inductInfo value => names := (value.all ++ value.ctors).toArray
  | .ctorInfo value => names := #[value.induct]
  | .recInfo value =>
      names := (value.all ++ value.rules.map (·.ctor)).toArray
      expressions := expressions ++ (value.rules.map (·.rhs)).toArray
  | _ => pure ()
  let references ← IO.mkRef names
  for value in expressions do
    value.forEach fun term => do
      match term with
      | .const name _ | .proj name _ _ => references.modify (·.push name)
      | _ => pure ()
  references.get

private def verifyStableLocal (original current : NameMap ConstantInfo) (verified : IO.Ref NameSet)
    (root : Name) : MetaM Unit := do
  let mut seen ← verified.get
  let mut pending := [root]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    let some before := original.find? name | continue
    let some after := current.find? name | throwError "Missing local dependency {name} of {root}"
    unless sameLocalDeclaration before after do
      throwError "Changed local dependency {name} of {root}"
    seen := seen.insert name
    pending := (← localReferences before).toList ++ pending
  verified.set seen

/-- Expand local definitions and validate any baseline data left behind a private name.
Imported names refer to the shared dependency environment. -/
private def expandLocalPrivates (locals : NameMap ConstantInfo) (retain : Name → MetaM Unit)
    (value : Expr) : MetaM Expr :=
  Core.transform value (pre := fun term => do
    if let .proj structureName _ _ := term then
      if !isExportedName structureName && (locals.find? structureName).isSome then
        retain structureName
    let .const name levels := term | return .continue
    if isExportedName name then
      return .continue
    let some definition := locals.find? name | return .continue
    match definition with
    | .defnInfo info => return .visit (info.value.instantiateLevelParams info.levelParams levels)
    | .thmInfo info => return .visit (info.value.instantiateLevelParams info.levelParams levels)
    | _ =>
        retain name
        return .continue)

/-- Only Lean's recorded theorem matchers are eligible for omission. A
matcher read by an exported type or executable body remains in the check. -/
private unsafe def isolatedProofMatchers (baseline : ModuleData)
    (locals : NameMap ConstantInfo) : BaseIO NameSet := do
  let mut candidates : NameSet := {}
  for (extension, entries) in baseline.entries do
    if extension == Lean.Meta.Match.Extension.extension.name then
      for raw in entries do
        let entry : Lean.Meta.Match.Extension.Entry := unsafeCast raw
        if isExportedName entry.name then
          if let some (.thmInfo _) := locals.find? entry.name.getPrefix then
            candidates := candidates.insert entry.name
  if candidates.isEmpty then return {}
  let mut pending := baseline.constNames.toList.filter fun name =>
    isExportedName name && !candidates.contains name
  let mut visible : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    if visible.contains name then continue
    let some info := locals.find? name | continue
    visible := visible.insert name
    pending := (← localReferences info (followProofs := false)).toList ++ pending
  return candidates.foldl (fun absent name =>
    if visible.contains name then absent else absent.insert name) {}

/-- Compare the former module's public declaration types in the current environment. -/
private def checkExports (exports : Array ConstantInfo) (checkValues : Bool)
    (scopes : Option (NameMap ConstantInfo × NameMap ConstantInfo)) : MetaM (Nat × Nat) := do
  let verified ← IO.mkRef ({} : NameSet)
  let expand (isBaseline : Bool) (value : Expr) : MetaM Expr :=
    match scopes with
    | none => pure value
    | some (original, current) =>
        if isBaseline then
          expandLocalPrivates original (verifyStableLocal original current verified) value
        else
          expandLocalPrivates current (fun _ => pure ()) value
  let originalScope := scopes.map Prod.fst
  let currentScope := scopes.map Prod.snd
  let mut definitions : Nat := 0
  let currentExports ← exports.mapM fun declaration => requireExport declaration.name
  for (declaration, current) in exports.zip currentExports do
    let name := declaration.name
    let previousType ← expand true declaration.type
    let currentType ← expand false current.type
    unless ← withCurrHeartbeats (withTransparency .reducible
        (isDefEq previousType currentType)) do
      throwError "Changed type of {name}"
    if checkValues then
      match (originalScope.bind (·.find? name)).getD declaration with
      | .defnInfo previous =>
          let .defnInfo next := (currentScope.bind (·.find? name)).getD current
            | throwError "Changed declaration kind of {name}"
          let body ← expand false (next.value.instantiateLevelParams next.levelParams
            (previous.levelParams.map Level.param))
          let previousBody ← expand true previous.value
          if previousBody != body then
            let equality ← withCurrHeartbeats do
              let env ← getEnv
              pure (Kernel.isDefEq env {} previousBody body)
            match equality with
            | .ok true => pure ()
            | .ok false => throwError "Changed definition {name}"
            | .error _ => throwError "Kernel could not compare definition {name}"
          definitions := definitions + 1
      | _ => pure ()
  return (exports.size, definitions)

private def readLocalScope (path : System.FilePath) (mainPart : ModuleData) :
    IO (NameMap ConstantInfo) := do
  let parts ← if mainPart.isModule then
    readModuleDataParts #[path, OLeanLevel.server.adjustFileName path,
      OLeanLevel.private.adjustFileName path]
  else
    pure #[]
  let mut locals : NameMap ConstantInfo := {}
  for declaration in mainPart.constants do
    locals := locals.insert declaration.name declaration
  for (part, _) in parts do
    for declaration in part.constants do
      locals := locals.insert declaration.name declaration
  return locals

unsafe def main (arguments : List String) : IO Unit := do
  let usage := "Usage: CheckLeanExportTypes MODULE BASELINE_OLEAN [--values] [--exact-private] [--baseline-imports] [--omit-proof-matchers]"
  let moduleName :: baselinePath :: flags := arguments | throw (IO.userError usage)
  unless flags.all (fun flag => flag == "--values" || flag == "--exact-private" || flag == "--baseline-imports" || flag == "--omit-proof-matchers") do
    throw (IO.userError usage)
  let checkValues := flags.contains "--values"
  initSearchPath (← findSysroot)
  let (baseline, _) ← readModuleData baselinePath
  let baselineScope ← if flags.contains "--exact-private" || flags.contains "--omit-proof-matchers" then
    readLocalScope baselinePath baseline
  else pure {}
  let omitted ← if flags.contains "--omit-proof-matchers" then
    isolatedProofMatchers baseline baselineScope
  else pure {}
  let scopes ← if flags.contains "--exact-private" then do
    let candidatePath ← findOLean moduleName.toName
    let (candidate, _) ← readModuleData candidatePath
    let candidateScope ← readLocalScope candidatePath candidate
    pure (some (baselineScope, candidateScope))
  else pure none
  let exports := baseline.constants.filter fun declaration =>
    isExportedName declaration.name && !omitted.contains declaration.name
  let target : Array Import := #[{ module := moduleName.toName }]
  let needsReservedNames (environment : Environment) : Bool :=
    exports.any fun declaration => !environment.contains declaration.name
  let options := if scopes.isSome then maxRecDepth.set {} 65536 else {}
  let context : Core.Context := { fileName := baselinePath, fileMap := default, options }
  let includeBaseline := flags.contains "--baseline-imports"
  if includeBaseline then
    if ← withImportModules target {} (pure ∘ needsReservedNames) then
      enableInitializersExecution
      let environment ← importModules target {} (loadExts := true)
      let checkVisibility : MetaM Unit := do
        for declaration in exports do
          let _ ← requireExport declaration.name
      checkVisibility.run' |>.toIO' context { env := environment }
  let imports := if includeBaseline then target ++ baseline.imports else target
  let verify (environment : Environment) : IO (Nat × Nat) :=
    (checkExports exports checkValues scopes).run' |>.toIO' context { env := environment }
  let immediate ← withImportModules imports {} fun environment => do
    if needsReservedNames environment then
      pure none
    else
      some <$> verify environment
  let (count, values) ← match immediate with
    | some result => pure result
    | none =>
        -- Ordinary Lean name resolution can create reserved equations on demand.
        enableInitializersExecution
        let environment ← importModules imports {} (loadExts := true)
        verify environment
  IO.println s!"{moduleName}: {count} existing exported types agree"
  if checkValues then
    IO.println s!"{moduleName}: {values} existing definition bodies agree"
  unless omitted.isEmpty do
    IO.println s!"{moduleName}: {omitted.toList.length} isolated theorem matchers"
