import Mettapedia.GSLT.LanguageDef.DeterministicEquations.LeanExtraction

/-!
# Proof production for extracted equations

Symbolic execution constructs proofs using the existing evaluator laws.
Recursive calls must be justified by a source induction hypothesis. The
producer fails if a source case cannot be proved; no unchecked certificate
or assumed simulation is installed in the environment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

open Lean Meta Elab Command

private def listExpr (type : Lean.Expr) (values : List Lean.Expr) : Lean.Expr :=
  values.foldr (fun value rest => mkAppN (mkConst ``List.cons [Level.zero]) #[type, value, rest])
    (mkApp (mkConst ``List.nil [Level.zero]) type)

private partial def listElements (expression : Lean.Expr) : MetaM (List Lean.Expr) := do
  let expression ← whnf expression
  if expression.getAppFn.isConstOf ``List.nil then return []
  if expression.getAppFn.isConstOf ``List.cons then
    return expression.getAppArgs[1]! :: (← listElements expression.getAppArgs[2]!)
  throwError "expected a finite quoted argument vector: {expression}"

private def irType : Lean.Expr := mkConst ``DeterministicEquations.Term

private def reflProof (left right : Lean.Expr) : MetaM Lean.Expr := do
  unless ← isDefEq left right do throwError "nondefinitional extraction obligation: {left} = {right}"
  return ← mkEqRefl left

private def neLiteral (left right : String) : MetaM Lean.Expr := do
  mkDecideProof (← mkAppM ``Ne #[mkStrLit left, mkStrLit right])

private def undefined (program : Lean.Expr) (head : String) : MetaM Lean.Expr := do
  reflProof (← mkAppM ``Program.defines #[program, mkStrLit head]) (mkConst ``Bool.false)

private def encodedNat (expression : Lean.Expr) : MetaM Lean.Expr := do
  let expression ← instantiateMVars expression
  if let some encoded ← whnfUntil expression ``natural then
    return encoded.getAppArgs[0]!
  let expression ← withTransparency .reducible <| whnf expression
  if expression.getAppFn.isConstOf ``natural then return expression.getAppArgs[0]!
  let reduced ← whnf expression
  if reduced.getAppFn.isConstOf ``DeterministicEquations.Term.lit then
    if let .lit (.strVal text) := reduced.getAppArgs[0]! then
      if let some value := text.toNat? then
        let source := mkNatLit value
        unless ← isDefEq expression (mkApp (mkConst ``natural) source) do
          throwError "literal is not the source natural encoding"
        return source
  throwError "scalar proof requires an actual natural encoding: {expression}"

private def encodedSource? (expression : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let registered := codecExtension.getState (← getEnv)
  let isEncoder (function : Lean.Expr) : Bool :=
    function.isConstOf ``natural || function.isConstOf ``boolean ||
      function.isConstOf ``encodeOption || function.isConstOf ``encodeList ||
      function.isConstOf ``encodePair || registered.any (fun entry => function.isConstOf entry.encoder)
  let expression ← whnfHeadPred (← instantiateMVars expression) fun value =>
    pure (!isEncoder value.getAppFn)
  let function := expression.getAppFn
  let arguments := expression.getAppArgs
  if arguments.isEmpty then return none
  if function.isConstOf ``natural || function.isConstOf ``boolean ||
      function.isConstOf ``encodeOption || function.isConstOf ``encodeList ||
      function.isConstOf ``encodePair then return some arguments.back!
  for entry in codecExtension.getState (← getEnv) do
    if function.isConstOf entry.encoder then return some arguments.back!
  return none

/-- Recover the list whose actual encoding was passed to the shared view primitive. -/
private def viewedSource? (expression : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some view ← whnfUntil (← instantiateMVars expression) ``listView | return none
  let some mapped ← whnfUntil view.appArg! ``List.map | return none
  let arguments := mapped.getAppArgs
  unless arguments.size == 4 do return none
  let values := arguments[3]!
  let type ← whnf (← inferType values)
  unless type.getAppFn.isConstOf ``List do return none
  let encoded ← encoder type.getAppArgs[0]!
  unless ← isDefEq arguments[2]! encoded do
    throwError "list view does not retain the actual registered source encoding"
  return some values

private partial def sourceOfEncoding (type value : Lean.Expr) : MetaM Lean.Expr := do
  let type ← whnf type
  if let some source ← encodedSource? value then
    if ← isDefEq (← inferType source) type then return source
  let reduced ← whnf value
  let function := reduced.getAppFn
  let arguments := reduced.getAppArgs
  let source ← if type.isConstOf ``Nat then encodedNat value
    else if type.isConstOf ``Bool then
      if function.isConstOf ``DeterministicEquations.Term.sym && arguments[0]! == mkStrLit "True" then
        pure (mkConst ``Bool.true)
      else if function.isConstOf ``DeterministicEquations.Term.sym && arguments[0]! == mkStrLit "False" then
        pure (mkConst ``Bool.false)
      else throwError "comparison Boolean operand is not an actual source encoding"
    else if type.getAppFn.isConstOf ``Option then
      let elementType := type.getAppArgs[0]!
      if function.isConstOf ``DeterministicEquations.Term.sym && arguments[0]! == mkStrLit "None" then
        mkAppM ``Option.none #[elementType]
      else
        unless function.isConstOf ``DeterministicEquations.Term.expr do
          throwError "comparison optional operand is not encoded constructor data"
        let items ← listElements arguments[0]!
        unless items.length == 2 && items[0]! == mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit "Some") do
          throwError "comparison optional operand has the wrong constructor shape"
        mkSome elementType (← sourceOfEncoding elementType items[1]!)
    else if type.getAppFn.isConstOf ``Prod then
      unless function.isConstOf ``DeterministicEquations.Term.expr do
        throwError "comparison pair operand is not encoded constructor data"
      let items ← listElements arguments[0]!
      unless items.length == 3 && items[0]! == mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit "Pair") do
        throwError "comparison pair operand has the wrong constructor shape"
      mkAppM ``Prod.mk #[← sourceOfEncoding type.getAppArgs[0]! items[1]!,
        ← sourceOfEncoding type.getAppArgs[1]! items[2]!]
    else if type.getAppFn.isConstOf ``List then
      unless function.isConstOf ``DeterministicEquations.Term.list do
        throwError "comparison list operand is not encoded list data"
      let items ← listElements arguments[0]!
      let elementType := type.getAppArgs[0]!
      pure (listExpr elementType (← items.mapM (sourceOfEncoding elementType)))
    else throwError "comparison operand cannot be reconstructed at its exact source type: {type}"
  unless ← isDefEq (← encodeValue source) value do
    throwError "comparison source reconstruction changes the registered encoding"
  return source

private def normalizeEncoded (expression : Lean.Expr) : MetaM Lean.Expr := do
  if let some source ← encodedSource? expression then
    let reduced ← whnfHeadPred source fun expression =>
      pure (!(expression.getAppFn.isConstOf ``ite || expression.getAppFn.isConstOf ``dite ||
        expression.getAppFn.isConstOf ``Option.bind || expression.getAppFn.isConstOf ``Bind.bind ||
        expression.getAppFn.isConstOf ``Bool.and || expression.getAppFn.isConstOf ``decide))
    return ← encodeValue reduced
  return expression

private def helperResult? (head : String) (arguments : List Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  let some helper := (sourceHelperExtension.getState (← getEnv)).find?
      (·.head == head) | return none
  forallTelescopeReducing (← inferType helper.source) fun parameters _ => do
    unless parameters.size == helper.positions.size do
      throwError "source helper metadata has a foreign parameter count"
    let mut actual := #[]
    for position in [:parameters.size] do
      let some encoded := arguments[helper.positions[position]!]?
        | throwError "source helper call is missing its checked captured operand"
      actual := actual.push (← sourceOfEncoding (← inferType parameters[position]!) encoded)
    let source := (mkAppN helper.source actual).headBeta
    return some (← encodeValue source)

structure RunProof where
  value : Lean.Expr
  proof : Lean.Expr

structure PreparedProofs where
  programName : Name
  selections : Array (String × Name)
  library : Array Name
  deriving Inhabited

initialize preparedProofExtension :
    SimplePersistentEnvExtension PreparedProofs (Array PreparedProofs) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·) }

private def sourceConstructor (source : Lean.Expr) : MetaM Bool := do
  let source ← whnf source
  if source.isRawNatLit then return true
  if let some name := source.getAppFn.constName? then
    return (← getConstInfo name).isCtor
  return false

private def refineSourceCases (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut goal := goal
  for declaration in (← getLCtx) do
    let some (_, left, right) := declaration.type.eq? | continue
    let direction ← if ← sourceConstructor right then pure (some false)
      else if ← sourceConstructor left then pure (some true) else pure none
    let some symm := direction | continue
    let saved ← saveState
    try
      let caseFrom := if symm then right else left
      let caseTo := if symm then left else right
      let caseType ← inferType caseFrom
      let evidence ← if symm then mkEqSymm declaration.toExpr else pure declaration.toExpr
      let target ← goal.getType
      let (rewritten, equality) ← withLocalDeclD `caseValue (← inferType caseFrom) fun value => do
        let abstracted ← Meta.transform target (pre := fun expression => do
          if expression.isApp || expression.isFVar || expression.isProj then
            let previous ← getMCtx
            if (← isDefEq (← inferType expression) caseType) &&
                (← isDefEq expression caseFrom) then return .done value
            setMCtx previous
          return .continue)
        let motive ← mkLambdaFVars #[value] abstracted
        let equality ← mkCongrArg motive evidence
        unless ← isDefEq (mkApp motive caseFrom) target do
          throwError "source case abstraction did not retain its actual target"
        return ((mkApp motive caseTo).headBeta, equality)
      goal ← goal.replaceTargetEq rewritten equality
    catch _ => saved.restore
  return goal

private def refineRunProof (computed : RunProof) : MetaM RunProof := do
  let mut computed := computed
  for declaration in (← getLCtx) do
    let some (_, left, right) := declaration.type.eq? | continue
    let saved ← saveState
    let replacement : Option RunProof ← try
      let encode ← encoder (← inferType left)
      let leftValue := mkApp encode left
      let rightValue := mkApp encode right
      if (← sourceConstructor right) && (← isDefEq computed.value leftValue) then
        let equal ← mkCongrArg encode declaration.toExpr
        pure (some ⟨rightValue, ← mkAppM ``applies_result_congr #[computed.proof, equal]⟩)
      else if (← sourceConstructor left) && (← isDefEq computed.value rightValue) then
        let equal ← mkCongrArg encode (← mkEqSymm declaration.toExpr)
        pure (some ⟨leftValue, ← mkAppM ``applies_result_congr #[computed.proof, equal]⟩)
      else pure none
    catch _ => pure none
    if let some replacement := replacement then computed := replacement
    else saved.restore
  return computed

/-- Functional induction retains the exclusion premises of source fallbacks.
Discharge only exclusions contradicted by checked reflexive equalities. -/
private def closeImpossibleSourceCase (goal : MVarId) : MetaM Bool := goal.withContext do
  for declaration in (← getLCtx) do
    let saved ← saveState
    let (parameters, _, conclusion) ← forallMetaTelescopeReducing declaration.type
    unless conclusion.isConstOf ``False do saved.restore; continue
    let mut resolved := true
    for parameter in parameters do
      let type ← instantiateMVars (← inferType parameter)
      unless ← isProp type do continue
      let some (_, left, right) := type.eq? | resolved := false; break
      unless ← isDefEq left right do resolved := false; break
      parameter.mvarId!.assign (← mkEqRefl left)
    let contradiction ← instantiateMVars (mkAppN declaration.toExpr parameters)
    if resolved && !contradiction.hasMVar then
      let proof ← mkAppOptM ``False.elim #[some (← goal.getType), some contradiction]
      goal.assign proof
      return true
    saved.restore
  return false

private def childrenProof (program host environment : Lean.Expr) (proofs : List RunProof) : MetaM Lean.Expr := do
  let relation := mkAppN (mkConst ``Evaluates) #[program, host, environment]
  let mut proof ← mkAppOptM ``List.Forall₂.nil #[some irType, some irType, some relation]
  for child in proofs.reverse do
    proof ← mkAppM ``List.Forall₂.cons #[child.proof, proof]
  return proof

private def callProof (program host environment : Lean.Expr) (head : String)
    (arguments : List Lean.Expr) (children : List RunProof) (result operation : Lean.Expr) :
    MetaM RunProof := do
  let ordinary ← mkAppOptM ``named_not_special #[some (mkStrLit head),
    some (listExpr irType arguments), some (← neLiteral head "let"), some (← neLiteral head "metta-nullary")]
  let proof ← mkAppOptM ``Evaluates.call #[some program, some host, some environment,
    some (mkStrLit head), some (listExpr irType arguments),
    some (listExpr irType (children.map (·.value))), some result,
    some ordinary, some (← childrenProof program host environment children), some operation]
  return ⟨result, proof⟩

/-- A closed head-filter proof is instantiated at the actual argument vector. -/
private def headSelection? (program : Lean.Expr) (head : String)
    (arguments : List Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if let some name := program.constName? then
    if let some prepared := (preparedProofExtension.getState (← getEnv)).find?
        (·.programName == name) then
      if let some (_, theoremName) := prepared.selections.find? (·.1 == head) then
        let proof := mkApp (mkConst theoremName) (listExpr irType arguments)
        let some (_, left, right) := (← inferType proof).eq? |
          throwError "prepared selection fact lost its exact equality"
        let call ← mkAppM ``Program.select #[program, mkStrLit head, listExpr irType arguments]
        unless ← isDefEq left call do
          throwError "prepared selection fact belongs to another call"
        if (← getOptions).getBool `profiler false then
          logInfo m!"FILTER CACHE {head}: {right.getAppArgs[0]!.getAppFn}"
        return some (right, proof)
  for declaration in (← getLCtx) do
    unless declaration.userName == `selectionCache do continue
    let saved ← saveState
    let (parameters, _, type) ← forallMetaTelescopeReducing declaration.type
    let some (_, left, right) := type.eq? | saved.restore; continue
    let parts := left.getAppArgs
    if left.getAppFn.isConstOf ``Program.select && parts.size == 3 &&
        parts[0]! == program && parts[1]! == mkStrLit head &&
        (← isDefEq parts[2]! (listExpr irType arguments)) then
      let proof ← instantiateMVars (mkAppN declaration.toExpr parameters)
      unless proof.hasMVar do return some (← instantiateMVars right, proof)
    saved.restore
  return none

private def selected (program : Lean.Expr) (head : String) (arguments : List Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let call ← mkAppM ``Program.select #[program, mkStrLit head, listExpr irType arguments]
  let (reducedCall, transport) ← if let some (filtered, proof) ← headSelection? program head arguments then
    pure (filtered, some proof)
    else pure (call, none)
  let chosen ← whnf reducedCall
  unless chosen.getAppFn.isConstOf ``Option.some do
    throwError "selected equation is not determined by the checked source case: {call}"
  let pair ← whnf chosen.getAppArgs[1]!
  unless pair.getAppFn.isConstOf ``Prod.mk do throwError "invalid selected equation"
  let row := pair.getAppArgs[2]!
  let environment := pair.getAppArgs[3]!
  let selection ← if let some proof := transport then
    mkEqTrans proof (← mkEqRefl reducedCall)
    else mkEqRefl call
  let defined ← reflProof (← mkAppM ``Program.definesAt
    #[program, mkStrLit head, mkNatLit arguments.length]) (mkConst ``Bool.true)
  return (row, environment, defined, selection)

private def matchInduction (program host : Lean.Expr) (head : String) (arguments : List Lean.Expr)
    (declaration : LocalDecl) : MetaM (Option RunProof) := do
  if declaration.userName == `selectionCache then return none
  let (parameters, _, type) ← forallMetaTelescopeReducing declaration.type
  let type := (← instantiateMVars type).headBeta
  if type.getAppFn.isConstOf ``Applies then
    let parts := type.getAppArgs
    if parts.size == 5 && (← isDefEq parts[0]! program) &&
        (← isDefEq parts[1]! host) && (← isDefEq parts[2]! (mkStrLit head)) &&
        (← isDefEq parts[3]! (listExpr irType arguments)) then
      let proof ← instantiateMVars (mkAppN declaration.toExpr parameters)
      unless proof.hasMVar do
        return some ⟨← instantiateMVars parts[4]!, proof⟩
  return none

private def inductionResult? (program host : Lean.Expr) (head : String) (arguments : List Lean.Expr) :
    MetaM (Option RunProof) := do
  for declaration in (← getLCtx) do
    unless declaration.isImplementationDetail do
      let saved ← saveState
      let found ← matchInduction program host head arguments declaration
      if found.isSome then return found
      saved.restore
  return none

private def primitiveRun (program host : Lean.Expr) (head : String) (arguments : List Lean.Expr) :
    MetaM (Option RunProof) := do
  let result ← match head, arguments with
    | "nik:data-eq", [first, second] =>
        unless host.isConstOf ``dataEqualityHost do
          throwError "structural comparison requires its declared shared host"
        let source ← if let some firstSource ← encodedSource? first then pure firstSource
          else if let some secondSource ← encodedSource? second then pure secondSource
          else throwError "comparison operands lack their actual source type"
        let type ← inferType source
        let left ← sourceOfEncoding type first
        let right ← sourceOfEncoding type second
        pure (← mkAppM ``dataEqualityHost_encoded
          #[← encoder type, ← encoderInjective type, left, right])
    | "nik:nat-add", [first, second]
    | "nik:nat-monus", [first, second]
    | "nik:nat-max", [first, second]
    | "nik:nat-le", [first, second]
    | "nik:nat-lt", [first, second]
    | "nik:nat-eq", [first, second] =>
        let left ← encodedNat first
        let right ← encodedNat second
        let operation := match head with
          | "nik:nat-add" => ``NaturalBinary.add
          | "nik:nat-monus" => ``NaturalBinary.monus
          | "nik:nat-max" => ``NaturalBinary.maximum
          | "nik:nat-le" => ``NaturalBinary.le
          | "nik:nat-lt" => ``NaturalBinary.lt
          | _ => ``NaturalBinary.equal
        let selected ← reflProof (← mkAppM ``naturalBinary? #[mkStrLit head])
          (← mkSome (mkConst ``NaturalBinary) (mkConst operation))
        let prior ← mkAppM ``productDivisionHost_prior #[mkStrLit head, listExpr irType arguments,
          ← reflProof (← mkAppM ``naturalProduct? #[mkStrLit head])
            (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``NaturalProduct))]
        let binary ← mkAppOptM ``computationalHost_binary #[some (mkStrLit head),
          some (mkConst operation), some selected, some left, some right,
          some (← neLiteral head "nik:list-view"), some (← neLiteral head "nik:list-cons")]
        pure (← mkEqTrans prior binary)
    | "nik:nat-zero", [argument] =>
        let source ← encodedNat argument
        pure (← mkAppM ``computationalHost_zero #[source])
    | "nik:nat-pred", [argument] =>
        let source ← encodedNat argument
        pure (← mkAppM ``computationalHost_pred #[source])
    | "nik:nat-mod", [first, second] =>
        let left ← encodedNat first
        let right ← encodedNat second
        pure (← mkAppM ``productDivisionHost_mod
          #[left, right, ← mkDecideProof (← mkAppM ``Ne #[right, mkNatLit 0])])
    | "nik:nat-div", [first, second] =>
        let left ← encodedNat first
        let right ← encodedNat second
        pure (← mkAppM ``productDivisionHost_div
          #[left, right, ← mkDecideProof (← mkAppM ``Ne #[right, mkNatLit 0])])
    | "nik:list-cons", [first, rest] =>
        let rest ← whnf rest
        unless rest.getAppFn.isConstOf ``DeterministicEquations.Term.list do
          throwError "list construction requires the checked source list encoding"
        pure (← mkAppM ``computationalHost_list_cons #[first, rest.getAppArgs[0]!])
    | "nik:list-view", [argument] =>
        let argument ← whnf argument
        unless argument.getAppFn.isConstOf ``DeterministicEquations.Term.list do
          throwError "list view requires the checked source list encoding"
        pure (← mkAppM ``computationalHost_list_view #[argument.getAppArgs[0]!])
    | _, _ => return none
  let result ← if host.isConstOf ``dataEqualityHost && head != "nik:data-eq" then
    let some (_, left, observed) := (← inferType result).eq? |
      throwError "primitive certificate is not an equality"
    let baseCall ← mkAppM ``Host.primitive
      #[mkConst ``productDivisionHost, mkStrLit head, listExpr irType arguments]
    let result ← if ← isDefEq left baseCall then pure result else
      let prior ← mkAppM ``productDivisionHost_prior
        #[mkStrLit head, listExpr irType arguments,
          ← reflProof (← mkAppM ``naturalProduct? #[mkStrLit head])
            (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``NaturalProduct))]
      mkEqTrans prior result
    mkAppOptM ``base_primitive_to_data
      #[some (mkStrLit head), some (listExpr irType arguments), some observed,
        some (← neLiteral head "nik:data-eq"), some result]
    else pure result
  let some (_, _, observed) := (← inferType result).eq? | throwError "primitive law is not equality"
  unless observed.getAppFn.isConstOf ``PrimitiveResult.value do
    throwError "primitive law is not a successful computation"
  let value := observed.getAppArgs[0]!
  let operation ← mkAppOptM ``Applies.primitive #[some program, some host,
    some (mkStrLit head), some (listExpr irType arguments), some value,
    some (← undefined program head), some result]
  return some ⟨value, operation⟩

private def decisionEvidence? (condition : Lean.Expr) : MetaM (Option (Bool × Lean.Expr)) := do
  if let some (_, left, right) := condition.eq? then
    let saved ← saveState
    if ← isDefEq left right then return some (true, ← mkEqRefl left)
    saved.restore
  for declaration in (← getLCtx) do
    let saved ← saveState
    if ← isDefEq declaration.type condition then return some (true, declaration.toExpr)
    if ← isDefEq declaration.type (mkApp (mkConst ``Not) condition) then
      return some (false, declaration.toExpr)
    saved.restore
  return none

mutual

private partial def evaluateIR (program host environment expression : Lean.Expr)
    (expected : Option Lean.Expr := none) : MetaM RunProof := do
  let reduced ← whnf expression
  let constructor := reduced.getAppFn
  let arguments := reduced.getAppArgs
  if constructor.isConstOf ``DeterministicEquations.Term.var then
    let name := arguments[0]!
    let lookup ← mkAppM ``Env.lookup #[environment, name]
    let found ← whnf lookup
    unless found.getAppFn.isConstOf ``Option.some do throwError "unbound generated variable"
    let value := found.getAppArgs[1]!
    return ⟨value, ← mkAppOptM ``Evaluates.variable #[some program, some host, some environment,
      some name, some value, some (← mkEqRefl lookup)]⟩
  if constructor.isConstOf ``DeterministicEquations.Term.lit then
    return ⟨expression, ← mkAppM ``Evaluates.literal #[program, host, environment, arguments[0]!]⟩
  if constructor.isConstOf ``DeterministicEquations.Term.sym then
    return ⟨expression, ← mkAppM ``Evaluates.symbol #[program, host, environment, arguments[0]!]⟩
  if constructor.isConstOf ``DeterministicEquations.Term.list then
    let items ← listElements arguments[0]!
    let children ← items.mapM fun item => evaluateIR program host environment item
    let value := mkApp (mkConst ``DeterministicEquations.Term.list)
      (listExpr irType (children.map (·.value)))
    let proof ← mkAppOptM ``Evaluates.list #[some program, some host, some environment,
      some (listExpr irType items), some (listExpr irType (children.map (·.value))),
      some (← childrenProof program host environment children)]
    return ⟨value, proof⟩
  if constructor.isConstOf ``DeterministicEquations.Term.expr then
    let first :: items ← listElements arguments[0]! | throwError "unsupported empty source call"
    let first ← whnf first
    unless first.getAppFn.isConstOf ``DeterministicEquations.Term.sym do
      throwError "unsupported dynamic source call"
    let .lit (.strVal head) := first.getAppArgs[0]! | throwError "dynamic target head"
    let children ← items.mapM fun item => evaluateIR program host environment item
    let operation ← applyIR program host head (children.map (·.value)) expected
    return ← callProof program host environment head items children operation.value operation.proof
  throwError "unsupported generated node in proof production: {reduced}"

private partial def applyIR (program host : Lean.Expr) (head : String) (arguments : List Lean.Expr)
    (expected : Option Lean.Expr := none) :
    MetaM RunProof := do profileitM Exception ("extraction apply " ++ head) (← getOptions) do
  if let some recursive ← inductionResult? program host head arguments then return ← refineRunProof recursive
  if let some primitive ← primitiveRun program host head arguments then return primitive
  for (argument, position) in arguments.zipIdx do
    let some source ← encodedSource? argument | continue
    unless source.getAppFn.isConstOf ``decide && source.getAppNumArgs == 2 do continue
    let sourceArguments := source.getAppArgs
    let condition := sourceArguments[0]!
    let some (holds, evidence) ← decisionEvidence? condition | continue
    let equal ← mkAppOptM (if holds then ``boolean_decision_true else ``boolean_decision_false)
      #[some condition, some sourceArguments[1]!, some evidence]
    let some (_, left, right) := (← inferType equal).eq? |
      throwError "source branch decision is not an exact equality"
    unless ← isDefEq left argument do
      throwError "source decision refinement changes its actual encoded operand"
    let reduced := arguments.toArray.set! position right |>.toList
    let computed ← applyIR program host head reduced expected
    let vectorEqual ← withLocalDeclD `branchValue irType fun value => do
      let rebuilt := arguments.toArray.set! position value |>.toList
      let abstracted ← mkLambdaFVars #[value] (listExpr irType rebuilt)
      mkCongrArg abstracted equal
    return ⟨computed.value, ← mkAppM ``applies_arguments_congr #[computed.proof, vectorEqual]⟩
  let defines ← whnf (← mkAppM ``Program.defines #[program, mkStrLit head])
  if defines.isConstOf ``Bool.false then
    let computed := mkAppN (mkConst ``Host.primitive) #[host, mkStrLit head, listExpr irType arguments]
    let unhandled ← reflProof computed (mkConst ``PrimitiveResult.unhandled)
    let value := mkApp (mkConst ``DeterministicEquations.Term.expr)
      (listExpr irType (mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit head) :: arguments))
    let proof ← mkAppOptM ``Applies.constructor #[some program, some host, some (mkStrLit head),
      some (listExpr irType arguments), some (← undefined program head), some unhandled]
    return ⟨value, proof⟩
  let expected ← if expected.isSome then pure expected else helperResult? head arguments
  if let some result := expected then
    let result ← normalizeEncoded (← instantiateMVars result).headBeta
    if let some source ← encodedSource? result then
      let source := source.headBeta
      let sourceArguments := source.getAppArgs
      if source.getAppFn.isConstOf ``decide && sourceArguments.size == 2 then
        let condition := sourceArguments[0]!
        let function := condition.getAppFn
        let inputs := condition.getAppArgs
        let rewrite ← if function.isConstOf ``Not && inputs.size == 1 then
            pure (some (← mkAppM ``decision_not #[inputs[0]!]))
          else if function.isConstOf ``And && inputs.size == 2 then
            pure (some (← mkAppM ``decision_and #[inputs[0]!, inputs[1]!]))
          else if function.isConstOf ``Or && inputs.size == 2 then
            pure (some (← mkAppM ``decision_or #[inputs[0]!, inputs[1]!]))
          else pure none
        if let some rewrite := rewrite then
          let some (_, left, right) := (← inferType rewrite).eq? |
            throwError "decision decomposition lost its source equality"
          unless ← isDefEq left source do
            throwError "decision decomposition changes the actual source instance"
          let wanted := mkApp (mkConst ``boolean) right
          let computed ← applyIR program host head arguments (some wanted)
          let equal ← mkCongrArg (mkConst ``boolean) (← mkEqSymm rewrite)
          return ⟨result, ← mkAppM ``applies_result_congr #[computed.proof, equal]⟩
      if source.getAppFn.isConstOf ``Bool.and && sourceArguments.size == 2 then
        let first :: captures := arguments | throwError "missing conjunction source operand"
        let left := sourceArguments[0]!
        let right := sourceArguments[1]!
        if ← isDefEq first (mkApp (mkConst ``boolean) left) then
          let noneValue := mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit "False")
          let falseRun ← applyIR program host head (noneValue :: captures) (some noneValue)
          let trueValue := mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit "True")
          let wanted := mkApp (mkConst ``boolean) right
          let trueRun ← applyIR program host head (trueValue :: captures) (some wanted)
          unless ← isDefEq trueRun.value wanted do
            throwError "conjunction branch changes the actual second operand"
          let operation ← mkAppM ``applies_and_elimination
            #[mkStrLit head, listExpr irType captures, left, right, falseRun.proof, trueRun.proof]
          return ⟨result, operation⟩
      if (source.getAppFn.isConstOf ``ite || source.getAppFn.isConstOf ``dite) &&
          sourceArguments.size == 5 then
        let condition := sourceArguments[1]!
        let dependent := source.getAppFn.isConstOf ``dite
        let first :: captures := arguments | throwError "missing conditional source result"
        let conditionBoolean := mkAppN (mkConst ``decide)
          #[condition, sourceArguments[2]!]
        if ← isDefEq first (mkApp (mkConst ``boolean) conditionBoolean) then
          let resultEncoder ← encoder (← inferType source)
          let branch (holds : Bool) : MetaM Lean.Expr := do
            let proposition ← if holds then pure condition else mkAppM ``Not #[condition]
            withLocalDeclD `branchProof proposition fun proof => do
              let value := sourceArguments[if holds then 3 else 4]!
              let value := if dependent then (mkApp value proof).headBeta else value
              let wanted ← encodeValue value
              let input := mkApp (mkConst ``DeterministicEquations.Term.sym)
                (mkStrLit (if holds then "True" else "False"))
              let computed ← applyIR program host head (input :: captures) (some wanted)
              unless ← isDefEq computed.value wanted do
                throwError "conditional branch does not return its actual source encoding"
              mkLambdaFVars #[proof] computed.proof
          let theoremName := if dependent then ``applies_dite_elimination else ``applies_ite_elimination
          let operation ← mkAppOptM theoremName #[none, some program, some host,
            some resultEncoder, some (mkStrLit head), some (listExpr irType captures),
            some condition, some sourceArguments[2]!, some sourceArguments[3]!,
            some sourceArguments[4]!, some (← branch true), some (← branch false)]
          return ⟨result, operation⟩
    if result.getAppFn.isConstOf ``encodeOption then
      let encoded := result.getAppArgs
      let source := encoded[encoded.size - 1]!.headBeta
      if source.getAppFn.isConstOf ``Option.bind || source.getAppFn.isConstOf ``Bind.bind then
        let sourceArguments := source.getAppArgs
        let optional := sourceArguments[sourceArguments.size - 2]!
        let continuation := sourceArguments[sourceArguments.size - 1]!
        let optionalType ← whnf (← inferType optional)
        unless optionalType.getAppFn.isConstOf ``Option do throwError "foreign source sequencing"
        let elementType := optionalType.getAppArgs[0]!
        let encodedOptional ← encodeValue optional
        let first :: captures := arguments | throwError "missing optional source result"
        if ← isDefEq first encodedOptional then
          let noneValue := mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit "None")
          let noneRun ← applyIR program host head (noneValue :: captures) (some noneValue)
          let someRun ← withLocalDeclD `selectedValue elementType fun value => do
            let sourceSome ← mkSome elementType value
            let continuationCall := (mkApp continuation value).headBeta
            let branch ← applyIR program host head ((← encodeValue sourceSome) :: captures)
              (some (← encodeValue continuationCall))
            let wanted ← encodeValue continuationCall
            unless ← isDefEq branch.value wanted do
              throwError "optional continuation does not return its actual source encoding: {branch.value} / {wanted}"
            return ← mkLambdaFVars #[value] branch.proof
          let encodeElement ← encoder elementType
          let operation ← mkAppOptM ``applies_option_cases #[none, none, some program, some host,
            some encodeElement, some encoded[encoded.size - 2]!, some (mkStrLit head),
            some (listExpr irType captures), some optional, some continuation,
            some noneRun.proof, some someRun]
          return ⟨result, operation⟩
  let choice ← try
    pure (some (← selected program head arguments))
  catch _ => pure none
  let some (row, environment, defined, selection) := choice |
    if let some result := expected then return ← eliminateEncoded program host head arguments result
    let details := MessageData.joinSep (arguments.map fun value => m!"{value}") "; "
    let mut premises : Array MessageData := #[]
    for declaration in (← getLCtx) do
      if ← isProp declaration.type then
        premises := premises.push m!"{declaration.userName}: {declaration.type}"
    let premiseDetails := MessageData.joinSep premises.toList "\n"
    throwError "symbolic equation selection lacks an actual source result:\nhead: {head}\narguments: {details}\nconstraints: {premiseDetails}"
  let body ← mkAppM ``Equation.body #[row]
  let computed ← evaluateIR program host environment body expected
  let proof ← mkAppOptM ``Applies.equation #[some program, some host, some (mkStrLit head),
    some (listExpr irType arguments), some row, some environment, some computed.value,
    some defined, some selection, some computed.proof]
  return ⟨computed.value, proof⟩

private partial def eliminateEncoded (program host : Lean.Expr) (head : String)
    (arguments : List Lean.Expr) (result : Lean.Expr) : MetaM RunProof := do
  let rows := (← readProgram program).filter fun row =>
    row.head == head && row.params.length == arguments.length
  for position in List.range arguments.length do
    unless rows.any (fun row => match row.params[position]! with
      | .var _ => false
      | _ => true) do continue
    let argument := arguments[position]!
    let source ← if let some source ← viewedSource? argument then pure (some source)
      else encodedSource? argument
    if let some source := source then
      let sourceType ← whnf (← inferType source)
      let some typeName := sourceType.getAppFn.constName? | continue
      let .inductInfo information ← getConstInfo typeName | continue
      if information.numIndices != 0 then continue
      let reduced ← whnf source
      if let some name := reduced.getAppFn.constName? then
        if (← getConstInfo name).isCtor then continue
      let target ← mkAppM ``Applies #[program, host, mkStrLit head,
        listExpr irType (← arguments.mapM normalizeEncoded), ← normalizeEncoded result]
      let goal ← mkFreshExprSyntheticOpaqueMVar target
      let cases ← if source.isFVar then goal.mvarId!.cases source.fvarId!
        else
          let (generalized, branchGoal) ← goal.mvarId!.generalize
            #[{ expr := source, xName? := some `selectedSource, hName? := some `sourceCase }]
          branchGoal.cases generalized[0]!
      for branch in cases do
        branch.mvarId.withContext do
          let branchGoal ← refineSourceCases branch.mvarId
          if ← closeImpossibleSourceCase branchGoal then return
          let parts := (← branchGoal.getType).getAppArgs
          let branchArguments ← listElements parts[3]!
          let computed ← applyIR program host head branchArguments (some parts[4]!)
          unless ← isDefEq (← inferType computed.proof) (← branchGoal.getType) do
            let mut constraints : Array MessageData := #[]
            for declaration in (← getLCtx) do
              if ← isProp declaration.type then
                constraints := constraints.push m!"{declaration.userName}: {declaration.type}"
            throwError "constructor branch does not prove its actual source observation:\nproduced: {← inferType computed.proof}\nrequired: {← branchGoal.getType}\nconstraints: {MessageData.joinSep constraints.toList "\n"}"
          branchGoal.assign computed.proof
      let proof ← instantiateMVars goal
      unless !proof.hasMVar do throwError "constructor elimination left an unresolved branch"
      return ⟨result, proof⟩
  let mut constraints : Array MessageData := #[]
  for declaration in (← getLCtx) do
    if ← isProp declaration.type then
      constraints := constraints.push m!"{declaration.userName}: {declaration.type}"
  let argumentDetails := MessageData.joinSep (arguments.map fun value => m!"{value}") "; "
  let constraintDetails := MessageData.joinSep constraints.toList "\n"
  throwError "equation selection is not justified by a supported source elimination:\nhead: {head}\narguments: {argumentDetails}\nsource result: {result}\nconstraints: {constraintDetails}"

end

private def finishCase (program host : Lean.Expr) (head : String) (goal : MVarId) :
    Elab.Term.TermElabM Unit := goal.withContext do profileitM Exception "extraction source branch" (← getOptions) (decl := ← goal.getTag) do
  if (← getOptions).getBool `profiler false then logInfo m!"SOURCE CASE {← goal.getTag}"
  let goal ← refineSourceCases goal
  if ← closeImpossibleSourceCase goal then return
  let target := (← instantiateMVars (← goal.getType)).headBeta
  unless target.getAppFn.isConstOf ``Applies do throwError "source induction changed the observation: {target}"
  let parts := target.getAppArgs
  let arguments ← listElements parts[3]!
  let computed ← applyIR program host head arguments (some parts[4]!)
  let producedType ← inferType computed.proof
  if ← isDefEq producedType target then
    goal.assign computed.proof
  else
    withLetDecl `extractedRun producedType computed.proof fun witness => do
      let goals ← Tactic.run goal <| Tactic.withoutRecover <| Tactic.evalTactic
        (← `(tactic| simpa only [encodeList, encodeByte, List.map_cons, List.map_nil,
          UInt8.toNat_ofNat'] using $(mkIdent (← witness.fvarId!.getUserName))))
      unless goals.isEmpty do throwError "generated result does not equal the actual source result"
  if (← getOptions).getBool `profiler false then logInfo m!"SOURCE CASE CLOSED {← goal.getTag}"

private def dependencyProofs (programName : Name) (host : Lean.Expr) : Elab.Term.TermElabM (Array Lean.Expr) := do profileitM Exception "extraction dependencies" (← getOptions) do
  let combined ← readProgram (mkConst programName)
  let mut proofs := #[]
  for entry in dependencyExtension.getState (← getEnv) do
    if let some offset := (combined.findIdx? (·.head == entry.head)) then
      let retained ← readProgram (mkConst entry.programName)
      let leading := quoteProgram (combined.take offset)
      let trailing := quoteProgram (combined.drop (offset + retained.length))
      let source := mkConst entry.programName
      let before ← mkDecideProof (← mkEq
        (← mkAppM ``avoidsCalls #[source, leading]) (mkConst ``Bool.true))
      let after ← mkDecideProof (← mkEq
        (← mkAppM ``avoidsCalls #[source, trailing]) (mkConst ``Bool.true))
      let contains ← mkDecideProof (← mkEq (← mkAppM ``List.contains
        #[← mkAppM ``Program.calledHeads #[source], mkStrLit entry.head]) (mkConst ``Bool.true))
      let used ← mkAppM ``calledHead_of_contains #[source, mkStrLit entry.head, contains]
      let certificate := mkConst entry.certificateName
      let proof ← forallTelescopeReducing (← inferType certificate) fun parameters proposition => do
        let parts := proposition.getAppArgs
        unless proposition.getAppFn.isConstOf ``Applies && parts.size == 5 do
          throwError "dependency certificate lost its checked observation type"
        let computed := mkAppN certificate parameters
        let computed ← if ← isDefEq parts[1]! host then pure computed else
          if parts[1]!.isConstOf ``productDivisionHost && host.isConstOf ``dataEqualityHost then
            let notContains ← mkDecideProof (← mkEq (← mkAppM ``List.contains
              #[← mkAppM ``Program.calledHeads #[source], mkStrLit "nik:data-eq"])
              (mkConst ``Bool.false))
            let absent ← mkAppM ``data_head_absent #[source, notContains]
            mkAppM ``base_computation_to_data
              #[source, absent, parts[2]!, used, parts[3]!, parts[4]!, computed]
          else throwError "dependency primitive catalogue cannot be transported to this program"
        let transported ← mkAppM ``linked_computes #[source, leading, trailing, host,
          before, after, parts[2]!, used, parts[3]!, parts[4]!, computed]
        let expected ← mkAppM ``Applies #[mkConst programName, host,
          parts[2]!, parts[3]!, parts[4]!]
        unless ← isDefEq (← inferType transported) expected do
          throwError "dependency occurrence is not the retained program in the actual linked artifact"
        mkLambdaFVars parameters transported
      proofs := proofs.push proof
  return proofs

/-- Introduce proved computations without adding logical assumptions. -/
partial def withRunCertificates (proofs : List Lean.Expr)
    (action : Elab.Term.TermElabM Lean.Expr) (localName : Name := `dependencyRun) :
    Elab.Term.TermElabM Lean.Expr := do
  match proofs with
  | [] => action
  | proof :: rest =>
      let proof ← if proof.hasFVar then
        let mut caches := #[]
        for declaration in (← getLCtx) do
          if declaration.userName == `selectionCache && declaration.isLet then
            caches := caches.push declaration.fvarId
        zetaDeltaFVars proof caches
        else pure proof
      if proof.hasMVar || proof.hasFVar || proof.hasSorry then
        throwError "dependency proof is not closed and complete"
      withLetDecl localName (← inferType proof) proof fun localProof => do
        let result ← withRunCertificates rest action localName
        mkLetFVars #[localProof] result

/-- Cache only kernel-checked equalities; selection still uses the existing matcher. -/
private def selectionCertificates (programName : Name) : Elab.Term.TermElabM (List Lean.Expr) := do
  if let some prepared := (preparedProofExtension.getState (← getEnv)).find?
      (·.programName == programName) then
    return prepared.selections.toList.map (fun entry => mkConst entry.2)
  let program := mkConst programName
  let rows ← readProgram program
  let mut proofs := []
  for head in (rows.map (·.head)).eraseDups do
    let retained := quoteProgram (rows.filter (·.head == head))
    let proof ← withLocalDeclD `selectedArguments (mkApp (mkConst ``List [Level.zero]) irType)
      fun arguments => do
        let selection ← mkAppM ``selection_head_filter #[program, mkStrLit head, arguments]
        let expected ← mkEq
          (← mkAppM ``Program.select #[program, mkStrLit head, arguments])
          (← mkAppM ``Program.select #[retained, mkStrLit head, arguments])
        unless ← isDefEq (← inferType selection) expected do
          throwError "cached head rows differ from the actual program filter"
        let selection ← mkExpectedTypeHint selection expected
        mkLambdaFVars #[arguments] selection
    proofs := proofs ++ [proof]
  return proofs

private def withSelectionCertificates (programName : Name)
    (action : Elab.Term.TermElabM Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do
  if (preparedProofExtension.getState (← getEnv)).any (·.programName == programName) then
    return ← action
  withRunCertificates (← selectionCertificates programName) action `selectionCache

private def sourceNeedsInduction (sourceName : Name) : MetaM Bool := do
  let some equations ← getEqnsFor? sourceName |
    throwError "source has no checked defining equations"
  for name in equations do
    let information ← getConstInfo name
    let recursive ← forallTelescopeReducing information.type fun _ equation => do
      let some (_, _, body) := equation.eq? |
        throwError "source equation does not state equality"
      pure ((body.find? fun expression => expression.isConstOf sourceName).isSome)
    if recursive then return true
  return false

def certify (programName sourceName : Name) (head : String)
    (additionalCertificates : Array Lean.Expr := #[]) : Elab.Term.TermElabM Lean.Expr := do
  let host ← extractionHost programName
  withSelectionCertificates programName do
    withRunCertificates ((← dependencyProofs programName host) ++ additionalCertificates).toList do
      certifyBody programName sourceName host head
where
 certifyBody (programName sourceName : Name) (host : Lean.Expr) (head : String) : Elab.Term.TermElabM Lean.Expr := do
  let program := mkConst programName
  let source := mkConst sourceName
  let info ← getConstInfo sourceName
  forallTelescopeReducing info.type fun parameters _ => do
    let sourceCall := mkAppN source parameters
    let arguments ← parameters.toList.mapM fun value => encodeValue value
    let result ← encodeValue sourceCall
    let target ← mkAppM ``Applies #[program, host, mkStrLit head, listExpr irType arguments, result]
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let goals ← if ← sourceNeedsInduction sourceName then
      Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
        (← `(tactic| fun_induction $(mkIdent sourceName)))
    else pure [goal.mvarId!]
    for child in goals do finishCase program host head child
    let proof ← instantiateMVars goal
    if proof.hasMVar then throwError "proof producer left unresolved obligations"
    return ← mkLambdaFVars parameters proof

private def certifyLookup (programName : Name) (head : String) (elementType : Lean.Expr) :
    Elab.Term.TermElabM Lean.Expr := do profileitM Exception "extraction indexed lookup" (← getOptions) do
  let program := mkConst programName
  let host ← extractionHost programName
  let valuesType ← mkAppM ``List #[elementType]
  withLocalDeclD `lookupValues valuesType fun values => do
    withLocalDeclD `lookupIndex (mkConst ``Nat) fun index => do
      let source ← mkAppM ``List.get?Internal #[values, index]
      let target ← mkAppM ``Applies #[program, host, mkStrLit head,
        listExpr irType [← encodeValue values, ← encodeValue index], ← encodeValue source]
      let goal ← mkFreshExprSyntheticOpaqueMVar target
      let valuesTarget ← `(Parser.Tactic.elimTarget| $(mkIdent `lookupValues):term)
      let goals ← Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
        (← `(tactic| induction $valuesTarget generalizing $(mkIdent `lookupIndex)))
      for child in goals do
        if (← child.getTag).toString.endsWith "cons" then
          let indexTarget ← `(Parser.Tactic.elimTarget| $(mkIdent `lookupIndex):term)
          let branches ← Tactic.run child <| Tactic.withoutRecover <| Tactic.evalTactic
            (← `(tactic| cases $indexTarget))
          for branch in branches do finishCase program host head branch
        else finishCase program host head child
      let proof ← instantiateMVars goal
      if proof.hasMVar then throwError "lookup lowering left unresolved obligations"
      return ← mkLambdaFVars #[values, index] proof

private def certifyAssociation (programName : Name) (head : String)
    (keyType valueType : Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do profileitM Exception "extraction association lookup" (← getOptions) do
  let program := mkConst programName
  let host ← extractionHost programName
  let pairType ← mkAppM ``Prod #[keyType, valueType]
  let valuesType ← mkAppM ``List #[pairType]
  withLocalDeclD `lookupTable valuesType fun values => do
    withLocalDeclD `lookupKey keyType fun key => do
      let source ← mkAppM ``List.lookup #[key, values]
      let target ← mkAppM ``Applies #[program, host, mkStrLit head,
        listExpr irType [← encodeValue values, ← encodeValue key], ← encodeValue source]
      let goal ← mkFreshExprSyntheticOpaqueMVar target
      let valuesTarget ← `(Parser.Tactic.elimTarget| $(mkIdent `lookupTable):term)
      let goals ← Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
        (← `(tactic| induction $valuesTarget generalizing $(mkIdent `lookupKey)))
      for child in goals do
        if (← child.getTag).toString.endsWith "cons" then
          child.withContext do
            let mut pair : Option FVarId := none
            for declaration in (← getLCtx) do
              if declaration.isImplementationDetail then continue
              if ← isDefEq declaration.type pairType then pair := some declaration.fvarId
            let some pairId := pair | throwError "association induction did not expose its source pair"
            let branches ← child.cases pairId
            for branch in branches do
              let rewrites ← Tactic.run branch.mvarId <| Tactic.withoutRecover <| Tactic.evalTactic
                (← `(tactic| rw [association_lookup_cons]))
              for rewritten in rewrites do finishCase program host head rewritten
        else finishCase program host head child
      let proof ← instantiateMVars goal
      if proof.hasMVar then throwError "association lowering left unresolved source obligations"
      return ← mkLambdaFVars #[values, key] proof

private def certifySourceHelper (programName : Name) (helper : SourceHelper) :
    Elab.Term.TermElabM Lean.Expr := do
  let some position := helper.inductionPosition |
    throwError "source helper has no structural library induction"
  let program := mkConst programName
  let host ← extractionHost programName
  forallTelescopeReducing (← inferType helper.source) fun parameters _ => do
    unless position < parameters.size && helper.positions == Array.range parameters.size do
      throwError "structural library helper has a foreign argument map"
    let source := (mkAppN helper.source parameters).headBeta
    let target ← mkAppM ``Applies #[program, host, mkStrLit helper.head,
      listExpr irType (← parameters.toList.mapM fun value => encodeValue value), ← encodeValue source]
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let type ← whnf (← inferType parameters[position]!)
    unless type.getAppFn.isConstOf ``List do
      throwError "structural library induction is not over actual source list data"
    let name ← parameters[position]!.fvarId!.getUserName
    let valuesTarget ← `(Parser.Tactic.elimTarget| $(mkIdent name):term)
    let goals ← if helper.generalizedParameters.isEmpty then
        Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
          (← `(tactic| induction $valuesTarget))
      else
        unless helper.generalizedParameters.size == 1 && helper.generalizedParameters[0]! < parameters.size do
          throwError "structural library generalization has an unsupported parameter map"
        let generalized ← parameters[helper.generalizedParameters[0]!]!.fvarId!.getUserName
        Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
          (← `(tactic| induction $valuesTarget generalizing $(mkIdent generalized)))
    for child in goals do finishCase program host helper.head child
    let proof ← instantiateMVars goal
    if proof.hasMVar then throwError "structural library proof left unresolved source obligations"
    return ← mkLambdaFVars parameters proof

private def structuralHelpers (head : String) : MetaM (Array SourceHelper) := do
  return (sourceHelperExtension.getState (← getEnv)).filter fun helper =>
    helper.head.startsWith (head ++ ":resume:") && helper.inductionPosition.isSome

private def standardLibraryProofs (programName : Name) (head : String) :
    Elab.Term.TermElabM (Array Lean.Expr) := do
  if let some prepared := (preparedProofExtension.getState (← getEnv)).find?
      (·.programName == programName) then
    return prepared.library.map mkConst
  let mut proofs := #[]
  if let some lookup := (lookupExtension.getState (← getEnv)).find? (·.head == head) then
    for elementType in lookup.elementTypes do
      proofs := proofs.push (← certifyLookup programName (head ++ ":lookup") elementType)
    for (keyType, valueType) in lookup.associationTypes do
      proofs := proofs.push (← certifyAssociation programName (head ++ ":association") keyType valueType)
  for helper in ← structuralHelpers head do
    let dependencies ← dependencyProofs programName (← extractionHost programName)
    let proof ← withRunCertificates (dependencies ++ proofs).toList do
      certifySourceHelper programName helper
    proofs := proofs.push proof
  return proofs

syntax (name := prepareExtraction) "prepare_extraction " ident : command

/-- Separate reusable library proofs from the source function's induction. -/
@[command_elab prepareExtraction] def elaboratePreparation : CommandElab := fun stx => do
  liftTermElabM do
    let programName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    if (preparedProofExtension.getState (← getEnv)).any (·.programName == programName) then
      throwError "this program's checked library facts are already prepared"
    let install (name : Name) (proof : Lean.Expr) : Elab.Term.TermElabM Unit := do
      if proof.hasFVar || proof.hasMVar || proof.hasSorry then
        throwError "prepared extraction fact is not closed and complete"
      addDecl <| .thmDecl { name, levelParams := [], type := ← inferType proof, value := proof }
    let mut selections := #[]
    let mut proofs := []
    let heads := ((← readProgram (mkConst programName)).map (·.head)).eraseDups
    for (proof, index) in (← selectionCertificates programName).zipIdx do
      let name := programName ++ Name.mkSimple ("selection_" ++ toString index)
      install name proof
      selections := selections.push (heads[index]!, name)
      proofs := proofs ++ [mkConst name]
    let environment ← getEnv
    let lookupCount := if let some lookup := (lookupExtension.getState environment).find?
        (·.head == "nik:extracted:" ++ programName.toString) then
      lookup.elementTypes.size + lookup.associationTypes.size else 0
    let count := lookupCount + (← structuralHelpers ("nik:extracted:" ++ programName.toString)).size
    let library := (List.range count).toArray.map fun index =>
      programName ++ Name.mkSimple ("library_" ++ toString index)
    let action : Elab.Term.TermElabM Lean.Expr := do
      let libraryProofs ← standardLibraryProofs programName ("nik:extracted:" ++ programName.toString)
      unless libraryProofs.size == library.size do
        throwError "prepared library inventory differs from the actual compiler metadata"
      let caches := (← getLCtx).foldl (init := #[]) fun result declaration =>
        if declaration.userName == `selectionCache && declaration.isLet then
          result.push declaration.fvarId else result
      for (proof, index) in libraryProofs.toList.zipIdx do
        let closed ← zetaDeltaFVars proof caches
        install library[index]! closed
      pure (mkConst programName)
    discard <| withRunCertificates proofs action `selectionCache
    modifyEnv fun environment => preparedProofExtension.addEntry environment
      { programName, selections, library }

def certifySpecialized (programName sourceName adapterName : Name) (head : String) :
    Elab.Term.TermElabM Lean.Expr := do
  let host ← extractionHost programName
  withSelectionCertificates programName do
    withRunCertificates ((← dependencyProofs programName host) ++ (← standardLibraryProofs programName head)).toList do
      certifyBody programName sourceName adapterName host head
where
 certifyBody (programName sourceName adapterName : Name) (host : Lean.Expr) (head : String) :
    Elab.Term.TermElabM Lean.Expr := do
  let program := mkConst programName
  let adapterInfo ← getConstInfo adapterName
  let .forallE _ valuesType _ _ := adapterInfo.type | throwError "invalid source adapter"
  let valuesType ← whnf valuesType
  unless valuesType.getAppFn.isConstOf ``List do throwError "source adapter is not a list specialization"
  let prove : Elab.Term.TermElabM Lean.Expr := do
    let info ← getConstInfo sourceName
    forallTelescopeReducing info.type fun original _ => do
      withLocalDeclD `replacementValues valuesType fun values => do
        let parameters := original.set! 0 values
        let sourceParameters := original.set! 0 (mkApp (mkConst adapterName) values)
        let sourceCall := mkAppN (mkConst sourceName) sourceParameters
        let arguments ← parameters.toList.mapM fun value => encodeValue value
        let target ← mkAppM ``Applies #[program, host, mkStrLit head,
          listExpr irType arguments, ← encodeValue sourceCall]
        let goal ← mkFreshExprSyntheticOpaqueMVar target
        let goals ← if ← sourceNeedsInduction sourceName then
            Tactic.run goal.mvarId! <| Tactic.withoutRecover <| Tactic.evalTactic
              (← `(tactic| fun_induction $(mkIdent sourceName)))
          else pure [goal.mvarId!]
        for child in goals do finishCase program host head child
        let proof ← instantiateMVars goal
        if proof.hasMVar then throwError "specialized extraction left unresolved obligations"
        return ← mkLambdaFVars parameters proof
  prove

syntax (name := certifyExtraction) "certify_extraction " ident " from " ident " as " ident : command

private def installCertificate (theoremName : Name) (proof : Lean.Expr) : Elab.Term.TermElabM Unit := do
  if (← getOptions).getBool `profiler false then logInfo m!"CERTIFICATE INSTALL {theoremName}"
  if proof.hasFVar || proof.hasMVar || proof.hasSorry then
    throwError "extraction proof is not closed and complete"
  let type ← inferType proof
  addDecl <| .thmDecl { name := theoremName, levelParams := [], type := type, value := proof }
  let exactProof ← forallTelescopeReducing type fun parameters observation => do
    let parts := observation.getAppArgs
    unless observation.getAppFn.isConstOf ``Applies && parts.size == 5 do
      throwError "certificate does not state an actual equation computation"
    withLocalDeclD `observedResult irType fun observed => do
      let computed := mkAppN (mkConst theoremName) parameters
      let reflected ← mkAppOptM ``result_exact #[some parts[0]!, some parts[1]!, some parts[2]!,
        some parts[3]!, some parts[4]!, some observed, some computed]
      return ← mkLambdaFVars (parameters.push observed) reflected
  let exactType ← inferType exactProof
  addDecl <| .thmDecl {
    name := theoremName.appendAfter "_result_exact"
    levelParams := []
    type := exactType
    value := exactProof }
  let completedProof ← forallTelescopeReducing type fun parameters observation => do
    let parts := observation.getAppArgs
    withLocalDeclD `fuel (mkConst ``Nat) fun fuel => do
      let applied ← mkAppM ``apply #[parts[0]!, parts[1]!, fuel, parts[2]!, parts[3]!]
      let completedType ← mkAppM ``Ne #[applied, mkConst ``Outcome.exhausted]
      withLocalDeclD `completed completedType fun completed => do
        let computed := mkAppN (mkConst theoremName) parameters
        let exact ← mkAppM ``completed_exact #[computed, fuel, completed]
        return ← mkLambdaFVars (parameters ++ #[fuel, completed]) exact
  let completedType ← inferType completedProof
  addDecl <| .thmDecl {
    name := theoremName.appendAfter "_completed_exact"
    levelParams := []
    type := completedType
    value := completedProof }

@[command_elab certifyExtraction] def elaborateCertificate : CommandElab := fun stx => do
  let theoremName := (← getCurrNamespace) ++ stx[5].getId
  liftTermElabM do
    let programName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let sourceName ← realizeGlobalConstNoOverloadWithInfo stx[3]
    let head := "nik:extracted:" ++ programName.toString
    let proof ← certify programName sourceName head (← standardLibraryProofs programName head)
    installCertificate theoremName proof

syntax (name := certifySpecializedExtraction)
  "certify_specialized_extraction " ident " from " ident " using " ident " as " ident : command

@[command_elab certifySpecializedExtraction] def elaborateSpecializedCertificate : CommandElab := fun stx => do
  let theoremName := (← getCurrNamespace) ++ stx[7].getId
  liftTermElabM do
    let programName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let sourceName ← realizeGlobalConstNoOverloadWithInfo stx[3]
    let adapterName ← realizeGlobalConstNoOverloadWithInfo stx[5]
    let proof ← certifySpecialized programName sourceName adapterName
      ("nik:extracted:" ++ programName.toString)
    installCertificate theoremName proof

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
