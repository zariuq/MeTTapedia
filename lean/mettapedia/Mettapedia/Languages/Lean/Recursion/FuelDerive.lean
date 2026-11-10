import Mettapedia.Languages.Lean.Recursion.Derive
import Mettapedia.Languages.Lean.Recursion.RecipeFuel
import Mettapedia.Languages.Lean.Recursion.RelationFuel

/-!
# Structural fuel derived from the source recursion implementation

The recipe and measure are read from the source declaration. The seed comes
from an `Inhabited` instance for the result, and a proved measure bound makes
it unobservable. The source bridge uses the accessible interpretation; it
does not define the fuel evaluator to be the source function.
-/

namespace Mettapedia.Languages.Lean.Recursion.FuelDerive

open _root_.Lean Meta Elab Command

structure Record where
  source : Name
  fuel : Name
  zeroEquation : Name
  stepEquation : Name
  curriedFuel : Name
  curriedZeroEquation : Name
  curriedStepEquation : Name
  curriedEquations : Array Name
  adequate : Name
  budget : Name
  budgetAdequate : Name
  reading : Name
  bridge : Name
  deriving Inhabited

initialize registry : SimplePersistentEnvExtension Record (Array Record) ←
  registerSimplePersistentEnvExtension {
    name := `Mettapedia.Languages.Lean.Recursion.FuelDerive.registry
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
    addEntryFn := Array.push }

/-- Recover source arguments from the compiler's single-constructor packing.
The generated equations are kernel checked, including the packing eta law. -/
partial def stateArguments (template value : Expr) : MetaM (Array Expr × Array Expr) := do
  let template := template.consumeMData.headBeta
  if template.isFVar then return (#[template], #[value])
  let .const name _ := template.getAppFn
    | throwError "source state is not a variable or constructor packing"
  let .ctorInfo constructor ← getConstInfo name
    | throwError "source state uses a non-constructor packing: {name}"
  let owner ← getConstInfoInduct constructor.induct
  unless owner.ctors.length == 1 do
    throwError "source state packing has alternative constructors: {constructor.induct}"
  let fields := template.getAppArgs.extract constructor.numParams template.getAppNumArgs
  unless fields.size == constructor.numFields do throwError "partial state constructor: {name}"
  let mut variables := #[]
  let mut values := #[]
  for index in [:fields.size] do
    let (newVariables, newValues) ← stateArguments fields[index]!
      (.proj constructor.induct index value)
    for parameter in newVariables do
      if variables.contains parameter then throwError "source state repeats an argument"
    variables := variables ++ newVariables
    values := values ++ newValues
  return (variables, values)

initialize
  registerGetEqnsFn fun name => do
    for entry in registry.getState (← getEnv) do
      if name == entry.curriedFuel then
        return some entry.curriedEquations
      if name == entry.fuel then return some #[entry.zeroEquation, entry.stepEquation]
    return none

/-- Expose compiler matchers and reduce their administrative beta, let and
projection redexes. Source functions and the recursive fuel call stay named.
Every resulting equation is subsequently checked by the kernel. -/
def normalizeStep (expression : Expr) : MetaM Expr := do
  Meta.transform expression
    (pre := fun term => do
      if ← isProof term then return .done term
      if term.isHeadBetaTarget then return .visit term.headBeta
      if let .letE _ _ value body _ := term then return .visit (body.instantiate1 value)
      if let .const name _ := term.getAppFn then
        if ← isMatcher name then
          if let some unfolded ← unfoldDefinition? term then return .visit unfolded
      return .continue)
    (post := fun term => do
      if term.isHeadBetaTarget then return .visit term.headBeta
      if let some projected ← reduceProj? term then return .visit projected
      if let .const name _ := term.getAppFn then
        if let some info ← getProjectionFnInfo? name then
          if let some record := term.getAppArgs[info.numParams]? then
            if let .const constructor _ := record.getAppFn then
              if let some (.ctorInfo _) := (← getEnv).find? constructor then
                if let some projected ← unfoldDefinition? term then return .visit projected
      if let some reduced ← reduceRecMatcher? term then
        if reduced != term then return .visit reduced
      return .done term)

/-- Find an unrefined source argument on which the compiler still branches. -/
partial def caseVariable (expression : Expr) (parameters : Array Expr) : MetaM (Option Expr) := do
  if ← isProof expression then return none
  if let .const name _ := expression.getAppFn then
    if let some (.recInfo info) := (← getEnv).find? name then
      if let some major := expression.getAppArgs[info.getMajorIdx]? then
        if major.isFVar && parameters.contains major then return some major
  match expression with
  | .app function argument =>
    if let some found ← caseVariable function parameters then return some found
    caseVariable argument parameters
  | .lam name type body binder =>
    withLocalDecl name binder type fun x => caseVariable (body.instantiate1 x) parameters
  | .letE _ _ value body _ => caseVariable (body.instantiate1 value) parameters
  | .mdata _ body => caseVariable body parameters
  | .proj _ _ value => caseVariable value parameters
  | _ => return none

/-- Refine overlapping source equations just far enough to expose their
computational branches. No source equation is used as an assumed fuel law. -/
partial def proveCases (baseName : Name) (levels : List Name) (proof : Expr)
    (parameters : Array Expr) : MetaM (Array Name) := do
  let some (_, left, right) := (← inferType proof).eq?
    | throwError "instantiated fuel equation is not an equality"
  let right ← normalizeStep right
  -- The general fuel successor theorem is independent of side conditions
  -- that the source equation used only to disambiguate overlapping patterns.
  -- Generalize those only when neither this proof nor its claim uses them.
  let mut used := collectFVars (collectFVars (collectFVars {} proof) left) right
  for parameter in parameters.reverse do
    if used.fvarSet.contains parameter.fvarId! then
      used := collectFVars used (← inferType parameter)
  let parameters := parameters.filter fun parameter => used.fvarSet.contains parameter.fvarId!
  if let some argument ← caseVariable right parameters then
    for parameter in parameters do
      if parameter != argument && (← inferType parameter).containsFVar argument.fvarId! then
        throwError "fuel case refinement has a dependent later argument"
    let type ← whnf (← inferType argument)
    let .const owner ownerLevels := type.getAppFn
      | throwError "fuel case refinement needs an inductive argument"
    let info ← getConstInfoInduct owner
    unless info.numIndices == 0 do
      throwError "fuel case refinement needs an unindexed argument"
    let mut names := #[]
    for index in [:info.ctors.length] do
      let constructor := mkAppN (mkConst info.ctors[index]! ownerLevels) type.getAppArgs
      let branch ← forallTelescope (← inferType constructor) fun fields _ => do
        let replacement := mkAppN constructor fields
        let specialized := proof.replaceFVar argument replacement
        let parameters := parameters.flatMap fun parameter =>
          if parameter == argument then fields else #[parameter]
        proveCases (Name.str baseName s!"branch{index}") levels specialized parameters
      names := names ++ branch
    return names
  Derive.prove baseName levels (← mkForallFVars parameters (← mkEq left right))
    (← mkLambdaFVars parameters proof)
  return #[baseName]

/-- A source may return the fixed-point function without applying its state.
Expose that final argument, preserving the source's curried interface. -/
def withState (reading : Inspect4331.Measured)
    (next : Inspect4331.Measured → MetaM α) : MetaM α := do
  let arity ← match reading.method with
    | .measure => pure 4
    | .generalRelation => pure 5
    | .natBrec => throwError "structural brecOn uses its separate recursion interface"
  if reading.application.getAppNumArgs > arity then return ← next reading
  unless reading.application.getAppNumArgs == arity do
    throwError "partially supplied measure recipe"
  withLocalDeclD `state reading.domain fun state =>
    next { reading with
      parameters := reading.parameters.push state
      application := mkApp reading.application state }

def generate (source baseName : Name)
    (edit : Inspect4331.Measured → MetaM Inspect4331.Measured := pure)
    (rankEvidence : Option (Inspect4331.Measured → MetaM (Expr × Expr)) := none)
    (budgetEvidence : Option (Inspect4331.Measured → MetaM (Expr × Expr)) := none) : MetaM Unit := do
  let info ← getConstInfo source
  let levels := info.levelParams
  let some entry ← Inspect4331.measured source (fun reading => withState reading fun reading => do
    let reading ← edit reading
    let (measure, locality, arity) ← match reading.method with
      | .measure => pure (reading.measure.get!, none, 4)
      | .generalRelation =>
        let some evidence := rankEvidence
          | throwError "general relation fuel requires a proved local rank: {source}"
        let (rank, proof) ← evidence reading
        pure (rank, some proof, 5)
      | .natBrec => throwError "structural brecOn uses its separate recursion interface"
    let arguments := reading.application.getAppArgs
    unless arguments.size > arity do
      throwError "fuel derivation needs a fully applied source state: {source}"
    let state := arguments[arity]!
    let trailing := arguments.extract (arity + 1) arguments.size
    let seed ← withLocalDeclD `state reading.domain fun state => do
      let result := (mkApp reading.motive state).headBeta
      let inhabitant ← synthInstance (← mkAppM ``Inhabited #[result])
      mkLambdaFVars #[state] (← mkAppOptM ``default #[some result, some inhabitant])
    let evaluator ← if locality.isSome then
        mkAppM ``RelationFuel.fuel #[reading.relation, reading.recipe, seed]
      else mkAppM ``AccessibleRecipe.fuel #[measure, reading.recipe, seed]
    let fuelName := baseName ++ `fuel
    let relevant := reading.parameters.filter fun parameter =>
      evaluator.containsFVar parameter.fvarId!
    Derive.define fuelName levels (← mkLambdaFVars relevant evaluator)
    let namedFuel := mkAppN (mkConst fuelName (levels.map Level.param)) relevant
    let zeroName := baseName ++ `fuel_zero
    let stepName := baseName ++ `fuel_succ
    withLocalDeclD `state reading.domain fun x => do
      let left := mkApp2 namedFuel (mkNatLit 0) x
      let right := (mkApp seed x).headBeta
      Derive.prove zeroName levels (← mkForallFVars (relevant.push x) (← mkEq left right))
        (← mkLambdaFVars (relevant.push x) (← mkEqRefl left))
      withLocalDeclD `fuel (mkConst ``Nat) fun k => do
        let previous ← withLocalDeclD `smaller reading.domain fun y => do
          let decrease := mkApp2 reading.relation y x
          withLocalDeclD `decrease decrease fun h =>
            mkLambdaFVars #[y, h] (mkApp2 namedFuel k y)
        let left := mkApp2 namedFuel (mkApp (mkConst ``Nat.succ) k) x
        let right := (mkApp2 reading.recipe x previous).headBeta
        let parameters := (relevant.push k).push x
        Derive.prove stepName levels (← mkForallFVars parameters (← mkEq left right))
          (← mkLambdaFVars parameters (← mkEqRefl left))
    let sourceValue := mkAppN (mkConst source (levels.map Level.param)) reading.parameters
    let curriedName := baseName ++ `sourceFuel
    let curriedZeroName := baseName ++ `sourceFuel_zero
    let curriedStepName := baseName ++ `sourceFuel_succ
    withLocalDeclD `fuel (mkConst ``Nat) fun k => do
      let value := mkAppN (mkApp2 namedFuel k state) trailing
      Derive.define curriedName levels (← mkLambdaFVars (#[k] ++ reading.parameters) value)
    let curried := mkConst curriedName (levels.map Level.param)
    let zeroLeft := mkAppN curried (#[mkNatLit 0] ++ reading.parameters)
    let zeroRight ← whnf (mkAppN seed (#[state] ++ trailing))
    Derive.prove curriedZeroName levels
      (← mkForallFVars reading.parameters (← mkEq zeroLeft zeroRight))
      (← mkLambdaFVars reading.parameters (← mkEqRefl zeroLeft))
    withLocalDeclD `fuel (mkConst ``Nat) fun k => do
      let previous ← withLocalDeclD `smaller reading.domain fun y => do
        let (variables, values) ← stateArguments state y
        let parameters := reading.parameters.map (·.replaceFVars variables values)
        let result := mkAppN curried (#[k] ++ parameters)
        let decrease := mkApp2 reading.relation y state
        withLocalDeclD `decrease decrease fun h => mkLambdaFVars #[y, h] result
      let left := mkAppN curried (#[mkApp (mkConst ``Nat.succ) k] ++ reading.parameters)
      let right ← normalizeStep (mkAppN reading.recipe (#[state, previous] ++ trailing))
      let parameters := #[k] ++ reading.parameters
      Derive.prove curriedStepName levels (← mkForallFVars parameters (← mkEq left right))
        (← mkLambdaFVars parameters (← mkEqRefl left))
    let mut curriedEquations := #[curriedZeroName]
    for sourceEquation in (← getEqnsFor? source).getD #[] do
      let equationInfo ← getConstInfo sourceEquation
      unless equationInfo.levelParams.length == levels.length do
        throwError "source fuel equation has a different universe interface: {sourceEquation}"
      let equationType := equationInfo.type.instantiateLevelParams equationInfo.levelParams
        (levels.map Level.param)
      let name := Name.str baseName s!"sourceFuel_case{curriedEquations.size - 1}"
      let cases ← forallTelescope equationType fun parameters body => do
        let some (_, sourceLeft, _) := body.eq?
          | throwError "source fuel equation is not an equality: {sourceEquation}"
        unless sourceLeft.getAppFn.isConstOf source do
          throwError "source fuel equation has a different head: {sourceEquation}"
        withLocalDeclD `fuel (mkConst ``Nat) fun k => do
          let proof := mkAppN (mkConst curriedStepName (levels.map Level.param))
            (#[k] ++ sourceLeft.getAppArgs)
          proveCases name levels proof (#[k] ++ parameters)
      curriedEquations := curriedEquations ++ cases
    let sourceAgreement ← if locality.isSome then do
        let functionEquality ← mkAppM ``AccessibleRecipe.function_equals_fix
          #[reading.relation, reading.wellFounded, reading.recipe]
        mkCongrFun functionEquality state
      else pure (mkAppN
        (mkConst ``AccessibleRecipe.equals_natFix reading.application.getAppFn.constLevels!)
        #[reading.domain, reading.motive, measure, reading.recipe, state])
    let mut sourceAgreement := sourceAgreement
    for argument in trailing do
      sourceAgreement ← mkCongrFun sourceAgreement argument
    let adequateName := baseName ++ `adequate
    withLocalDeclD `fuel (mkConst ``Nat) fun k => do
      let bound ← mkAppM ``LT.lt #[mkApp measure state, k]
      withLocalDeclD `bound bound fun h => do
        let initialAgreement ← match locality with
          | some proof =>
            mkAppM ``RelationFuel.fuel_eq_evaluate
              #[reading.relation, reading.wellFounded, measure, reading.recipe, proof, seed, k, state, h]
          | none =>
            mkAppM ``AccessibleRecipe.fuel_eq_evaluate #[measure, reading.recipe, seed, k, state, h]
        let mut agreement := initialAgreement
        for argument in trailing do
          agreement ← mkCongrFun agreement argument
        agreement ← mkEqTrans agreement sourceAgreement
        let value := mkAppN (mkApp2 namedFuel k state) trailing
        let parameters := (reading.parameters.push k).push h
        Derive.prove adequateName levels
          (← mkForallFVars parameters (← mkEq value sourceValue))
          (← mkLambdaFVars parameters agreement)
    let (bound, boundProof) ← match budgetEvidence with
      | some evidence => evidence reading
      | none => do
        let expandedMeasure := (← unfoldDefinition? measure).getD measure
        let rankAtState ← normalizeStep (mkApp expandedMeasure state)
        let bound := mkApp (mkConst ``Nat.succ) rankAtState
        pure (bound, ← mkAppM ``Nat.lt_succ_self #[mkApp measure state])
    let obligation ← mkAppM ``LT.lt #[mkApp measure state, bound]
    try
      checkWithKernel (mkApp (.lam `budgetBound obligation (.bvar 0) .default) boundProof)
    catch _ => throwError "fuel budget proof does not establish the source rank bound: {source}"
    let budgetName := baseName ++ `budget
    let budgetAdequateName := baseName ++ `budgetAdequate
    Derive.define budgetName levels (← mkLambdaFVars reading.parameters bound)
    let namedBudget := mkAppN (mkConst budgetName (levels.map Level.param)) reading.parameters
    let namedObligation ← mkAppM ``LT.lt #[mkApp measure state, namedBudget]
    Derive.prove budgetAdequateName levels (← mkForallFVars reading.parameters namedObligation)
      (← mkLambdaFVars reading.parameters boundProof)
    let value := mkAppN curried (#[bound] ++ reading.parameters)
    let readingName := baseName ++ `reading
    Derive.define readingName levels (← mkLambdaFVars reading.parameters value)
    let agreement := mkAppN (mkConst adequateName (levels.map Level.param))
      (reading.parameters ++ #[bound, boundProof])
    let bridgeName := baseName ++ `bridge
    let namedReading := mkAppN (mkConst readingName (levels.map Level.param)) reading.parameters
    Derive.prove bridgeName levels
      (← mkForallFVars reading.parameters (← mkEq sourceValue namedReading))
      (← mkLambdaFVars reading.parameters (← mkEqSymm agreement))
    return ({
      source := source
      fuel := fuelName
      zeroEquation := zeroName
      stepEquation := stepName
      curriedFuel := curriedName
      curriedZeroEquation := curriedZeroName
      curriedStepEquation := curriedStepName
      curriedEquations := curriedEquations
      adequate := adequateName
      budget := budgetName
      budgetAdequate := budgetAdequateName
      reading := readingName
      bridge := bridgeName } : Record))
    | throwError "no supported measure recursion found in {source}"
  modifyEnv fun env => registry.addEntry env entry

syntax (name := deriveFuel) "derive_fuel_interface " ident " as " ident : command

@[command_elab deriveFuel] def elabDeriveFuel : CommandElab
  | `(derive_fuel_interface $source:ident as $baseName:ident) => do
      let source ← liftCoreM (realizeGlobalConstNoOverloadWithInfo source)
      let baseName := (← getCurrNamespace) ++ baseName.getId
      liftTermElabM (generate source baseName)
  | _ => throwUnsupportedSyntax

end Mettapedia.Languages.Lean.Recursion.FuelDerive
