import Mettapedia.Languages.Lean.Recursion.Inspect4331
import Mettapedia.Languages.Lean.Recursion.AccessibleRecipe

/-!
# Named recursion interfaces derived from actual Lean definitions

The command extracts the compiler's measure and functional, constructs their
accessible interpretation, and proves its equality to the source declaration.
Each recursive call contributes a kernel-checked named decrease theorem.
Branch hypotheses are retained even when the proof uses only some of them.
-/

namespace Mettapedia.Languages.Lean.Recursion.Derive

open _root_.Lean Meta Elab Command

structure ProofUse where
  position : Nat
  proposition : Name
  evidence : Option Name
  forwarded : Option String
  deriving Inhabited

structure CallRecord where
  current : Name
  argument : Name
  decrease : Name
  sourceProofs : Array Name
  sourceCall : Option Name := none
  sourceEquation : Option Name := none
  proofUses : Array ProofUse := #[]
  deriving Inhabited

structure Record where
  source : Name
  implementation : Name
  measure : Option Name
  relation : Name
  wellFounded : Name
  recipe : Name
  accessible : Name
  bridge : Name
  functionBridge : Name
  equations : Array Name
  unfoldings : Array (Name × Name)
  calls : Array CallRecord
  method : Inspect4331.Method := .measure
  proofArguments : Array Nat := #[]
  deriving Inhabited

initialize registry : SimplePersistentEnvExtension Record (Array Record) ←
  registerSimplePersistentEnvExtension {
    name := `Mettapedia.Languages.Lean.Recursion.Derive.registry
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
    addEntryFn := Array.push }

def define (name : Name) (levels : List Name) (value : Expr) : MetaM Unit := do
  checkWithKernel value
  let type ← inferType value
  addDecl (.defnDecl { name, levelParams := levels, type, value, hints := .regular 0, safety := .safe })

def prove (name : Name) (levels : List Name) (type value : Expr) : MetaM Unit := do
  -- The kernel checks the expected type, including compiled recursor bodies.
  -- Meta unification is only a heuristic and may decline a valid conversion.
  try
    checkWithKernel (mkApp (.lam `witness type (.bvar 0) .default) value)
  catch error =>
    throwError "generated proof does not establish {name}: {← error.toMessageData.toString}"
  addDecl (.thmDecl { name, levelParams := levels, type, value })

def transportEquations (source target bridge baseName : Name) : MetaM (Array (Name × Name)) := do
  let sourceInfo ← getConstInfo source
  let levels := sourceInfo.levelParams
  let sourceFunction := mkConst source (levels.map Level.param)
  let targetFunction := mkConst target (levels.map Level.param)
  let mut unfoldings := #[]
  for equation in (← getEqnsFor? source).getD #[] do
    let equationInfo ← getConstInfo equation
    unless equationInfo.levelParams.length == levels.length do
      throwError "source equation has a different universe interface: {equation}"
    let equationType := equationInfo.type.instantiateLevelParams equationInfo.levelParams (levels.map Level.param)
    let predicate ← withLocalDeclD `function sourceInfo.type fun function => do
      let translated := equationType.replace fun expression =>
        if expression == sourceFunction then some function else none
      unless translated.hasFVar do
        throwError "source equation did not mention its function: {equation}"
      mkLambdaFVars #[function] translated
    let equality ← mkCongrArg predicate (mkConst bridge (levels.map Level.param))
    let transported ← mkEqMPR equality (mkConst equation (levels.map Level.param))
    let unfoldingName := Name.str baseName s!"equation{unfoldings.size}"
    prove unfoldingName levels (mkApp predicate targetFunction).headBeta transported
    unfoldings := unfoldings.push (equation, unfoldingName)
  return unfoldings

/-- Preserve actual branch hypotheses, and close their dependency telescope.
Unrelated recursive-capability variables are not added to the proposition. -/
def callContext (call : Inspect4331.Call) : MetaM (Array Expr) := do
  let mut used := collectFVars (collectFVars (collectFVars {} call.argument) call.obligation) call.proof
  if let some expression := call.sourceCall then used := collectFVars used expression
  for x in call.locals do
    if ← isProp (← inferType x) then used := used.add x.fvarId!
  for x in call.locals.reverse do
    if used.fvarSet.contains x.fvarId! then
      let decl ← x.fvarId!.getDecl
      used := collectFVars used decl.type
      if let some value := decl.value? then used := collectFVars used value
  return call.locals.filter (fun x => used.fvarSet.contains x.fvarId!)

partial def sourceCalls (source : Name) (expression : Expr) (locals : Array Expr)
    (visit : Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let expression := expression.consumeMData
  if ← isProof expression then return
  match expression with
  | .lam name type body binder =>
      withLocalDecl name binder type fun x => sourceCalls source (body.instantiate1 x) (locals.push x) visit
  | .letE name type value body _ =>
      sourceCalls source value locals visit
      withLetDecl name type value fun x => sourceCalls source (body.instantiate1 x) (locals.push x) visit
  | .app .. =>
      if expression.getAppFn.isConstOf source then visit expression locals
      if expression.getAppFn.isLambda then sourceCalls source expression.headBeta locals visit
      else for argument in expression.getAppArgs do sourceCalls source argument locals visit
  | .proj _ _ value => sourceCalls source value locals visit
  | _ => pure ()

/-- Source equation calls of a structural natural recursor. A strict
predecessor proof must typecheck at the actual caller/callee major arguments. -/
def structuralCalls (source : Name) (reading : Inspect4331.Measured)
    (visit : Inspect4331.Call → MetaM Unit) : MetaM Unit := do
  let some position := reading.parameters.findIdx? (· == reading.application.getArg! 1)
    | throwError "structural major is not a source parameter: {source}"
  for equation in (← getEqnsFor? source).getD #[] do
    forallTelescope (← getConstInfo equation).type fun parameters body => do
      let some (_, left, right) := body.eq? | throwError "source recursion equation is not an equality: {equation}"
      unless left.getAppFn.isConstOf source && position < left.getAppNumArgs do
        throwError "source recursion equation has the wrong head: {equation}"
      let current := left.getArg! position
      sourceCalls source right parameters fun call locals => do
        unless position < call.getAppNumArgs do throwError "partial recursive source call: {source}"
        let argument := call.getArg! position
        let proof ← mkAppM ``Nat.lt_succ_self #[argument]
        let obligation := mkApp2 reading.relation argument current
        unless ← withTransparency .all (isDefEq (← inferType proof) obligation) do
          throwError "source recursive call is not on the structural predecessor: {source}"
        let levels := (← getConstInfo source).levelParams.map Level.param
        visit ⟨locals, mkConst source levels,
          argument, proof, obligation, some call, some equation⟩

def generate (source baseName : Name)
    (edit : Inspect4331.Measured → MetaM Inspect4331.Measured := pure) : MetaM Unit := do
  let sourceInfo ← getConstInfo source
  let levels := sourceInfo.levelParams
  let proofArguments ← forallTelescope sourceInfo.type fun parameters _ => do
    let mut positions := #[]
    for index in [:parameters.size] do
      if ← isProof parameters[index]! then positions := positions.push index
    return positions
  let some record ← Inspect4331.measured source (fun reading => do
    let reading ← edit reading
    let measureName := baseName ++ `measure
    let relationName := baseName ++ `relation
    let wellFoundedName := baseName ++ `wellFounded
    let recipeName := baseName ++ `recipe
    let accessibleName := baseName ++ `accessible
    let bridgeName := baseName ++ `bridge
    let functionBridgeName := baseName ++ `functionBridge
    if let some measure := reading.measure then
      define measureName levels (← mkLambdaFVars reading.parameters measure (usedOnly := true))
    let relation := reading.relation
    define relationName levels (← mkLambdaFVars reading.parameters relation (usedOnly := true))
    let wellFounded := reading.wellFounded
    let wellFounded ← mkLambdaFVars reading.parameters wellFounded (usedOnly := true)
    let wellFoundedClaim ← mkAppM ``WellFounded #[relation]
    prove wellFoundedName levels
      (← mkForallFVars reading.parameters wellFoundedClaim (usedOnly := true)) wellFounded
    define recipeName levels (← mkLambdaFVars reading.parameters reading.recipe (usedOnly := true))
    let arguments := match reading.method with
      | .measure => #[reading.domain, reading.motive, reading.measure.get!, reading.recipe] ++
          reading.application.getAppArgs.extract 4 reading.application.getAppArgs.size
      | .natBrec => reading.application.getAppArgs
      | .generalRelation => #[reading.domain, reading.motive, reading.relation, reading.wellFounded, reading.recipe] ++
          reading.application.getAppArgs.extract 5 reading.application.getAppArgs.size
    let universeLevels := reading.application.getAppFn.constLevels!
    let interpretation := match reading.method with
      | .measure => ``AccessibleRecipe.evaluate
      | .natBrec => ``AccessibleNatBrec.evaluate
      | .generalRelation => ``AccessibleRecipe.evaluateRelation
    let equation := match reading.method with
      | .measure => ``AccessibleRecipe.function_equals_natFix
      | .natBrec => ``AccessibleNatBrec.equals_brecOn
      | .generalRelation => ``AccessibleRecipe.function_equals_fix
    let arity := match reading.method with | .measure => 4 | .natBrec => 3 | .generalRelation => 5
    let interpreted := mkAppN (mkConst interpretation universeLevels) arguments
    define accessibleName levels (← mkLambdaFVars reading.parameters interpreted)
    let mut proof := mkAppN (mkConst equation universeLevels) (arguments.extract 0 arity)
    for argument in arguments.extract arity arguments.size do
      proof ← mkCongrFun proof argument
    let sourceTerm := mkAppN (mkConst source (levels.map Level.param)) reading.parameters
    let targetTerm := mkAppN (mkConst accessibleName (levels.map Level.param)) reading.parameters
    let claim ← mkForallFVars reading.parameters (← mkEq targetTerm sourceTerm)
    prove bridgeName levels claim (← mkLambdaFVars reading.parameters proof)
    let mut fullProof := proof
    for parameter in reading.parameters.reverse do
      fullProof ← mkFunExt (← mkLambdaFVars #[parameter] fullProof)
    let sourceFunction := mkConst source (levels.map Level.param)
    let targetFunction := mkConst accessibleName (levels.map Level.param)
    prove functionBridgeName levels (← mkEq targetFunction sourceFunction) fullProof
    let equations := (← getEqnsFor? source).getD #[]
    let unfoldings ← transportEquations source accessibleName functionBridgeName baseName
    let records ← IO.mkRef (#[] : Array CallRecord)
    let inspectCalls := match reading.method with
      | .measure | .generalRelation => Inspect4331.calls reading.recipe reading.parameters
      | .natBrec => structuralCalls source reading
    inspectCalls fun call => do
      unless call.obligation.getAppNumArgs ≥ 2 do
        throwError "unclassified proof-taking local call in {source}: {call.obligation}"
      let relationArguments := call.obligation.getAppArgs
      let relation := mkAppN call.obligation.getAppFn (relationArguments.extract 0 (relationArguments.size - 2))
      unless ← withTransparency .all (isDefEq relation reading.relation) do
        throwError "recursive call uses a different relation in {source}"
      unless ← withTransparency .all (isDefEq relationArguments[relationArguments.size - 2]! call.argument) do
        throwError "recursive call evidence describes a different argument in {source}"
      let ordinal := (← records.get).size
      let currentName := Name.str baseName s!"call{ordinal}Current"
      let argumentName := Name.str baseName s!"call{ordinal}Argument"
      let decreaseName := Name.str baseName s!"call{ordinal}Decreases"
      let context ← callContext call
      define currentName levels (← mkLambdaFVars context relationArguments[relationArguments.size - 1]!)
      define argumentName levels (← mkLambdaFVars context call.argument)
      let statement ← mkForallFVars context call.obligation
      prove decreaseName levels statement (← mkLambdaFVars context call.proof)
      let env ← getEnv
      let constants := call.proof.getUsedConstants ++
        (call.sourceCall.map Expr.getUsedConstants).getD #[]
      let sourceProofs := (constants.toList.eraseDups.toArray).filter fun name =>
        (env.find? name).any (fun info => match info with | .thmInfo _ => true | _ => false)
      let sourceCall ← call.sourceCall.mapM fun expression => do
        let name := Name.str baseName s!"call{ordinal}Source"
        define name levels (← mkLambdaFVars context expression)
        return name
      let mut proofUses := #[]
      if let some application := call.sourceCall then
        for position in proofArguments do
          let some supplied := application.getAppArgs[position]?
            | throwError "recursive call is missing a proof argument at {position}"
          let proposition ← inferType supplied
          let propositionName := Name.str baseName s!"call{ordinal}Proof{position}Proposition"
          define propositionName levels (← mkLambdaFVars context proposition (usedOnly := true))
          if supplied.isFVar then
            proofUses := proofUses.push ⟨position, propositionName, none, some (← supplied.fvarId!.getUserName).toString⟩
          else
            let evidenceName := Name.str baseName s!"call{ordinal}Proof{position}Evidence"
            prove evidenceName levels (← mkForallFVars context proposition) (← mkLambdaFVars context supplied)
            proofUses := proofUses.push ⟨position, propositionName, some evidenceName, none⟩
      records.modify (·.push ⟨currentName, argumentName, decreaseName, sourceProofs, sourceCall, call.sourceEquation, proofUses⟩)
    return ({
      source
      implementation := reading.implementation
      measure := reading.measure.map (fun _ => measureName)
      relation := relationName
      wellFounded := wellFoundedName
      recipe := recipeName
      accessible := accessibleName
      bridge := bridgeName
      functionBridge := functionBridgeName
      equations
      unfoldings
      calls := ← records.get
      method := reading.method
      proofArguments } : Record))
    | throwError "no admitted measure recursion implementation for {source}"
  modifyEnv fun env => registry.addEntry env record

syntax (name := deriveRecursion) "derive_recursion_interface " ident " as " ident : command

@[command_elab deriveRecursion] def elabDeriveRecursion : CommandElab
  | `(derive_recursion_interface $source:ident as $baseName:ident) => do
      let source ← liftCoreM (realizeGlobalConstNoOverloadWithInfo source)
      let baseName := (← getCurrNamespace) ++ baseName.getId
      liftTermElabM (generate source baseName)
  | _ => throwUnsupportedSyntax

end Mettapedia.Languages.Lean.Recursion.Derive
