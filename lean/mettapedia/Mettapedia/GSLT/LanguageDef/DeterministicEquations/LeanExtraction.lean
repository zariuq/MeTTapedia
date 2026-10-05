import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionDependencyLaws
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionLibraryLaws
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalSetLibrary
import Lean

/-!
# Extraction from kernel-checked defining equations

This elaborator reads actual Lean equation theorems. Constructors, variables,
recursive calls and the supported scalar operations become the existing
equation IR. Metadata supplies data encodings, never function behavior.
Unsupported source nodes are rejected rather than delegated to a callback.

The compiler is elaboration code, not part of the logical trust boundary.
An extracted program requires a separately kernel-checked proof assembled
by the proof producer below; quotation or inspection is not that proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

open Lean Meta Elab Command

structure CodecEntry where
  typeName : Name
  encoder : Name
  injective : Name
  deriving Inhabited, Repr

initialize codecExtension : SimplePersistentEnvExtension CodecEntry (Array CodecEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (init := #[]) (· ++ ·)
  }

def registerCodec (entry : CodecEntry) : Elab.Term.TermElabM Unit := do
  let type := mkConst entry.typeName
  let encoder := mkConst entry.encoder
  let expected ← mkArrow type (mkConst ``DeterministicEquations.Term)
  unless ← isDefEq (← inferType encoder) expected do
    throwError "data encoder {entry.encoder} does not have the declared type"
  let injected ← mkAppM ``Function.Injective #[encoder]
  unless ← isDefEq (← inferType (mkConst entry.injective)) injected do
    throwError "data encoder {entry.encoder} lacks its exact injectivity proof"
  modifyEnv fun env => codecExtension.addEntry env entry

private def codecEntry? (type : Lean.Expr) : MetaM (Option CodecEntry) := do
  let type ← whnf type
  for entry in codecExtension.getState (← getEnv) do
    if ← isDefEq type (mkConst entry.typeName) then return some entry
  return none

partial def encoder (type : Lean.Expr) : MetaM Lean.Expr := do
  let type ← whnf type
  if type.isConstOf ``Nat then return mkConst ``natural
  if type.isConstOf ``UInt8 then return mkConst ``encodeByte
  if type.isConstOf ``Bool then return mkConst ``boolean
  if type.getAppFn.isConstOf ``Prod then
    let arguments := type.getAppArgs
    return ← mkAppM ``encodePair #[← encoder arguments[0]!, ← encoder arguments[1]!]
  if type.getAppFn.isConstOf ``List then
    let element := type.getAppArgs[0]!
    return ← mkAppM ``encodeList #[← encoder element]
  if type.getAppFn.isConstOf ``Option then
    let element := type.getAppArgs[0]!
    return ← mkAppM ``encodeOption #[← encoder element]
  if let some entry ← codecEntry? type then return mkConst entry.encoder
  throwError "unsupported extraction data type: {type}"

def encodeValue (value : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp (← encoder (← inferType value)) value

partial def encoderInjective (type : Lean.Expr) : MetaM Lean.Expr := do
  let type ← whnf type
  if type.isConstOf ``Nat then return mkConst ``natural_injective
  if type.isConstOf ``UInt8 then return mkConst ``encodeByte_injective
  if type.isConstOf ``Bool then return mkConst ``boolean_injective
  if type.getAppFn.isConstOf ``Prod then
    let arguments := type.getAppArgs
    return ← mkAppM ``encodePair_injective
      #[← encoderInjective arguments[0]!, ← encoderInjective arguments[1]!]
  if type.getAppFn.isConstOf ``List then
    return ← mkAppM ``encodeList_injective #[← encoderInjective type.getAppArgs[0]!]
  if type.getAppFn.isConstOf ``Option then
    return ← mkAppM ``encodeOption_injective #[← encoderInjective type.getAppArgs[0]!]
  if let some entry ← codecEntry? type then return mkConst entry.injective
  throwError "comparison lacks a checked injective source codec: {type}"

/-- A source dependency has a checked source-call certificate, not a callback. -/
structure DependencyEntry where
  sourceName : Name
  programName : Name
  certificateName : Name
  adapter : Option Name := none
  deriving Inhabited, Repr

def DependencyEntry.head (entry : DependencyEntry) : String :=
  "nik:extracted:" ++ entry.programName.toString

initialize dependencyExtension :
    SimplePersistentEnvExtension DependencyEntry (Array DependencyEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (init := #[]) (· ++ ·)
  }

private def quotedList (type : Lean.Expr) (values : List Lean.Expr) : Lean.Expr :=
  values.foldr (fun value rest => mkAppN (mkConst ``List.cons [Level.zero]) #[type, value, rest])
    (mkApp (mkConst ``List.nil [Level.zero]) type)

private def quoteTerm : DeterministicEquations.Term → Lean.Expr
  | .sym value => mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit value)
  | .lit value => mkApp (mkConst ``DeterministicEquations.Term.lit) (mkStrLit value)
  | .var value => mkApp (mkConst ``DeterministicEquations.Term.var) (mkStrLit value)
  | .expr values => mkApp (mkConst ``DeterministicEquations.Term.expr)
      (quotedList (mkConst ``DeterministicEquations.Term) (values.map quoteTerm))
  | .list values => mkApp (mkConst ``DeterministicEquations.Term.list)
      (quotedList (mkConst ``DeterministicEquations.Term) (values.map quoteTerm))

private def quoteEquation (row : Equation) : Lean.Expr :=
  mkAppN (mkConst ``Equation.mk) #[mkStrLit row.name, mkStrLit row.head,
    quotedList (mkConst ``DeterministicEquations.Term) (row.params.map quoteTerm), quoteTerm row.body]

def quoteProgram (program : Program) : Lean.Expr :=
  quotedList (mkConst ``Equation) (program.map quoteEquation)

private partial def readList (value : Lean.Expr) : MetaM (List Lean.Expr) := do
  let value ← whnf value
  if value.getAppFn.isConstOf ``List.nil then return []
  if value.getAppFn.isConstOf ``List.cons then
    return value.getAppArgs[1]! :: (← readList value.getAppArgs[2]!)
  throwError "dependency is not a closed quoted program list"

private def readString (value : Lean.Expr) : MetaM String := do
  let .lit (.strVal text) ← whnf value | throwError "dependency has an unquoted string"
  return text

private def readClosedString (value : Lean.Expr) : MetaM String := do
  let reduced ← whnf value
  if let some text := getStringValue? reduced then return text
  let some encoded ← whnfUntil value ``String.ofList |
    throwError "constructor literal does not reduce to closed string data: {value}"
  let characters ← (← readList encoded.appArg!).mapM fun character => do
    let some encoded ← whnfUntil character ``Char.ofNat |
      throwError "constructor string contains a nonliteral character"
    let some code ← getNatValue? (← whnf encoded.appArg!) |
      throwError "constructor string contains an open character code"
    pure (Char.ofNat code)
  let text := String.ofList characters
  unless ← isDefEq value (mkStrLit text) do
    throwError "constructor string quotation differs from the actual source encoding"
  return text

private partial def readTerm (value : Lean.Expr) : MetaM DeterministicEquations.Term := do
  let value ← whnf value
  let constructor := value.getAppFn
  let arguments := value.getAppArgs
  if constructor.isConstOf ``DeterministicEquations.Term.sym then
    return .sym (← readString arguments[0]!)
  if constructor.isConstOf ``DeterministicEquations.Term.lit then
    return .lit (← readString arguments[0]!)
  if constructor.isConstOf ``DeterministicEquations.Term.var then
    return .var (← readString arguments[0]!)
  if constructor.isConstOf ``DeterministicEquations.Term.list then
    return .list (← (← readList arguments[0]!).mapM readTerm)
  if constructor.isConstOf ``DeterministicEquations.Term.expr then
    return .expr (← (← readList arguments[0]!).mapM readTerm)
  throwError "dependency contains an unsupported quoted term"

def readProgram (value : Lean.Expr) : MetaM Program := do
  (← readList value).mapM fun row => do
    let row ← whnf row
    unless row.getAppFn.isConstOf ``Equation.mk do
      throwError "dependency is not a quoted equation"
    let arguments := row.getAppArgs
    return ⟨← readString arguments[0]!, ← readString arguments[1]!,
      ← (← readList arguments[2]!).mapM readTerm, ← readTerm arguments[3]!⟩

/-- Host selection follows the actual compiled calls, retaining the old catalogue
for programs that do not require structural comparison. -/
def extractionHost (programName : Name) : MetaM Lean.Expr := do
  let program ← readProgram (mkConst programName)
  return mkConst (if program.calledHeads.contains "nik:data-eq"
    then ``dataEqualityHost else ``productDivisionHost)

private def constantName? (expression : Lean.Expr) : Option Name :=
  expression.getAppFn.constName?

private structure ConstructorShape where
  tag : String
  container : Nat

private def ConstructorShape.encode (shape : ConstructorShape)
    (fields : List DeterministicEquations.Term) : DeterministicEquations.Term :=
  if shape.container == 0 then .sym shape.tag
  else if shape.container == 1 then .expr (.sym shape.tag :: fields)
  else if shape.container == 2 then .list (.sym shape.tag :: fields)
  else .lit shape.tag

private def ConstructorShape.quote (shape : ConstructorShape)
    (fields : List Lean.Expr) : Lean.Expr :=
  if shape.container == 0 then
    mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit shape.tag)
  else if shape.container == 3 then
    mkApp (mkConst ``DeterministicEquations.Term.lit) (mkStrLit shape.tag)
  else mkApp (mkConst (if shape.container == 1 then
      ``DeterministicEquations.Term.expr else ``DeterministicEquations.Term.list))
    (quotedList (mkConst ``DeterministicEquations.Term)
      (mkApp (mkConst ``DeterministicEquations.Term.sym) (mkStrLit shape.tag) :: fields))

private partial def constructorShape (value : Lean.Expr) : MetaM ConstructorShape := do
  let encoded ← whnf (← encodeValue value)
  if encoded.getAppFn.isConstOf ``DeterministicEquations.Term.lit then
    let literal := encoded.getAppArgs[0]!
    unless !literal.hasFVar && !literal.hasMVar do
      throwError "constructor literal is not closed data"
    let text ← readClosedString literal
    return ⟨text, 3⟩
  if encoded.getAppFn.isConstOf ``DeterministicEquations.Term.sym then
    let tag ← readClosedString encoded.getAppArgs[0]!
    return ⟨tag, 0⟩
  let isExpression := encoded.getAppFn.isConstOf ``DeterministicEquations.Term.expr
  if isExpression || encoded.getAppFn.isConstOf ``DeterministicEquations.Term.list then
    let values ← whnf encoded.getAppArgs[0]!
    unless values.getAppFn.isConstOf ``List.cons do
      throwError "constructor encoding is not headed data: {encoded}"
    let head ← whnf values.getAppArgs[1]!
    unless head.getAppFn.isConstOf ``DeterministicEquations.Term.sym do
      throwError "constructor encoding lacks a symbol head: {encoded}"
    if let .lit (.strVal name) := head.getAppArgs[0]! then
      return ⟨name, if isExpression then 1 else 2⟩
  throwError "unsupported constructor encoding: {encoded}"

structure Binding where
  source : Lean.Expr
  target : DeterministicEquations.Term
  deriving Inhabited

abbrev Bindings := Array Binding

inductive AdapterKind where
  | indexed | association
  deriving Inhabited, BEq

structure Root where
  sourceName : Name
  head : String
  parameters : Nat
  argumentTypes : Array Lean.Expr
  resultType : Lean.Expr
  equationNames : Array Name
  adapter : Option Name := none
  adapterKind : AdapterKind := .indexed
  dependencies : Array DependencyEntry := #[]
  deriving Inhabited

/-- Actual typed source observations for generated helper calls. This is proof
producer metadata; it grants no evaluator correspondence by itself. -/
structure SourceHelper where
  head : String
  source : Lean.Expr
  positions : Array Nat
  inductionPosition : Option Nat := none
  generalizedParameters : Array Nat := #[]
  deriving Inhabited

initialize sourceHelperExtension :
    SimplePersistentEnvExtension SourceHelper (Array SourceHelper) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (init := #[]) (· ++ ·) }

structure BodyState where
  next : Nat := 0
  helpers : Array Equation := #[]
  usedDependencies : Array DependencyEntry := #[]
  usesAdapterLookup : Bool := false
  lookupTypes : Array Lean.Expr := #[]
  associationTypes : Array (Lean.Expr × Lean.Expr) := #[]
  sourceHelpers : Array SourceHelper := #[]
  deriving Inhabited

structure LookupEntry where
  head : String
  elementTypes : Array Lean.Expr
  associationTypes : Array (Lean.Expr × Lean.Expr) := #[]
  deriving Inhabited

initialize lookupExtension : SimplePersistentEnvExtension LookupEntry (Array LookupEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (init := #[]) (· ++ ·)
  }

abbrev CompileM := StateRefT BodyState MetaM

private def freshHead (root : Root) : CompileM String := do
  let index := (← get).next
  modify fun state => { state with next := index + 1 }
  return root.head ++ ":resume:" ++ toString index

private partial def sourceTemplate (root : Root) (bindings : Bindings)
    (source : Lean.Expr) : MetaM Lean.Expr := do
  let replace (value : Lean.Expr) (replacements : Array Lean.Expr) : Lean.Expr :=
    value.replace fun expression => do
      let position ← bindings.findIdx? fun binding => binding.source == expression
      replacements[position]?
  let rec build (position : Nat) (parameters replacements : Array Lean.Expr) :
      MetaM Lean.Expr := do
    if position == bindings.size then
      let body := replace source replacements
      let template ← mkLambdaFVars parameters body
      -- Checking the captured binder types resolves their universe constraints.
      check template
      let template ← instantiateMVars template
      if template.hasFVar || template.hasMVar then
        let unresolved := template.find? fun value => value.isFVar || value.isMVar
        throwError "source helper captures unsupported or unbound source data: {template}; remaining {reprStr unresolved}; unresolved universes: {template.hasLevelMVar}"
      return template
    let type ← inferType bindings[position]!.source
    let type ← whnf (replace type replacements)
    let adapted := type.isForall
    let runtimeType ← if adapted then
        let some adapter := root.adapter |
          throwError "source helper captures an unregistered function"
        let info ← getConstInfo adapter
        let .forallE _ dataType returned _ := info.type |
          throwError "invalid source helper data adapter"
        unless ← isDefEq type returned do
          throwError "source helper captures a foreign function adapter"
        pure dataType
      else pure type
    let _ ← encoder runtimeType
    withLocalDeclD (Name.mkSimple ("captured:" ++ toString position)) runtimeType fun parameter => do
      let replacement := if adapted then mkApp (mkConst root.adapter.get!) parameter else parameter
      build (position + 1) (parameters.push parameter) (replacements.push replacement)
  build 0 #[] #[]

private def recordSourceHelper (root : Root) (bindings : Bindings)
    (head : String) (source : Lean.Expr) (positions : Array Nat) : CompileM Unit := do
  unless positions.size == bindings.size do throwError "source helper argument map has wrong arity"
  let template ← sourceTemplate root bindings source
  let entry : SourceHelper := { head, source := template, positions }
  modify fun state => { state with sourceHelpers := state.sourceHelpers.push entry }

private def fields (value : Lean.Expr) : MetaM (Name × Array Lean.Expr) := do
  let .const name _ := value.getAppFn | throwError "expected a source constructor: {value}"
  let .ctorInfo info ← getConstInfo name | throwError "unsupported source call: {value}"
  let arguments := value.getAppArgs
  unless arguments.size == info.numParams + info.numFields do
    throwError "partially applied source constructor: {value}"
  return (name, arguments.extract info.numParams arguments.size)

private def bound? (bindings : Bindings) (value : Lean.Expr) : MetaM (Option DeterministicEquations.Term) := do
  for binding in bindings do
    if ← isDefEq binding.source value then return some binding.target
  return none

private partial def sourceNormal (value : Lean.Expr) : MetaM Lean.Expr := do
  match value with
  | .mdata _ value => sourceNormal value
  | .letE _ _ assigned body _ => sourceNormal (body.instantiate1 assigned)
  | _ => return value

private def isOptionBind (value : Lean.Expr) : Bool :=
  (constantName? value == some ``Option.bind) || (constantName? value == some ``Bind.bind)

private def isOptionPure (value : Lean.Expr) : Bool :=
  (constantName? value == some ``Option.some) || (constantName? value == some ``Pure.pure)

private def sparseMatcher? (value : Lean.Expr) : MetaM (Option MatcherApp) := do
  let some name := value.getAppFn.constName? | return none
  unless isSparseCasesOn (← getEnv) name do return none
  let some information ← getCasesInfo? name |
    throwError "sparse source elimination has no checked case metadata"
  let arguments := value.getAppArgs
  unless arguments.size == information.arity && information.discrPos > 0 do
    throwError "overapplied sparse source elimination is outside the data profile"
  let positions := information.altsRange.toArray
  unless positions[0]? == some (information.discrPos + 1) do
    throwError "side-conditioned source elimination is outside the data profile"
  let altInfos := information.altNumParams.map fun alternative =>
    { numFields := match alternative with
        | .ctor _ count => count
        | .default count => count
      numOverlaps := 0
      hasUnitThunk := false : Match.AltParamInfo }
  return some {
    matcherName := name
    matcherLevels := value.getAppFn.constLevels!.toArray
    numParams := information.discrPos - 1
    numDiscrs := 1
    discrInfos := #[{}]
    uElimPos? := none
    params := arguments.extract 0 (information.discrPos - 1)
    motive := arguments[information.discrPos - 1]!
    discrs := #[arguments[information.discrPos]!]
    alts := positions.map fun position => arguments[position]!
    remaining := #[]
    altInfos := altInfos
    overlaps := {} }

private def nonrecursiveRecursor? (value : Lean.Expr) : MetaM (Option MatcherApp) := do
  let some name := value.getAppFn.constName? | return none
  let .recInfo recursor ← getConstInfo name | return none
  unless recursor.all.length == 1 && recursor.numIndices == 0 && recursor.numMotives == 1 do
    throwError "indexed or mutual source recursor is outside the elimination profile"
  let .inductInfo data ← getConstInfo recursor.all[0]! | return none
  unless !data.isRec && recursor.numMinors == data.ctors.length do
    throwError "recursive recursor cannot be used as a constructor elimination"
  let arguments := value.getAppArgs
  let major := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless arguments.size == major + 1 do
    throwError "overapplied source recursor is outside the elimination profile"
  let altInfos ← data.ctors.toArray.mapM fun constructor => do
    let .ctorInfo information ← getConstInfo constructor | throwError "invalid data constructor"
    pure {
      numFields := information.numFields
      numOverlaps := 0
      hasUnitThunk := false : Match.AltParamInfo }
  return some {
    matcherName := name
    matcherLevels := value.getAppFn.constLevels!.toArray
    numParams := recursor.numParams
    numDiscrs := 1
    discrInfos := #[{}]
    uElimPos? := none
    params := arguments.extract 0 recursor.numParams
    motive := arguments[recursor.numParams]!
    discrs := #[arguments[major]!]
    alts := arguments.extract (recursor.numParams + 1) major
    remaining := #[]
    altInfos := altInfos
    overlaps := {} }

mutual

partial def compileBody (root : Root) (bindings : Bindings) (original : Lean.Expr) :
    CompileM DeterministicEquations.Term := do
  let value ← sourceNormal original
  if let some target ← bound? bindings value then return target
  if let some numeral := value.rawNatLit? then return natural numeral
  if let some numeral ← getNatValue? value then
    unless ← isDefEq value (mkNatLit numeral) do
      throwError "foreign natural literal instance"
    return natural numeral
  let function := value.getAppFn
  let arguments := value.getAppArgs
  if function.isConstOf root.sourceName then
    unless arguments.size == root.parameters do throwError "unsaturated recursive source call"
    return named root.head (← compileBodies root bindings arguments).toList
  if let some dependency := root.dependencies.find? fun entry =>
      function.isConstOf entry.sourceName then
    let info ← getConstInfo dependency.sourceName
    let arity ← forallTelescopeReducing info.type fun parameters _ => pure parameters.size
    unless arguments.size == arity do throwError "unsaturated certified dependency call"
    let mut runtimeArguments := arguments
    if let some adapter := dependency.adapter then
      if dependency.adapter == root.adapter && arguments[0]!.isFVar &&
          (← bound? bindings arguments[0]!).isSome then pure ()
      else
        let specialized := arguments[0]!
        unless specialized.getAppFn.isConstOf adapter && specialized.getAppNumArgs == 1 do
          throwError "dependency function argument is not its checked data adapter"
        runtimeArguments := runtimeArguments.set! 0 specialized.getAppArgs[0]!
    modify fun state =>
      if state.usedDependencies.any (·.programName == dependency.programName) then state
      else { state with usedDependencies := state.usedDependencies.push dependency }
    return named dependency.head (← compileBodies root bindings runtimeArguments).toList
  if let .proj structureName index record := value then
    return ← compileProjection root bindings structureName index record
  if let some projection ← getProjectionFnInfo? (function.constName?.getD Name.anonymous) then
    if !projection.fromClass then
      unless arguments.size == projection.numParams + 1 do
        throwError "overapplied source projection is outside the data profile"
      let .ctorInfo constructor ← getConstInfo projection.ctorName |
        throwError "source projection does not refer to a checked constructor"
      return ← compileProjection root bindings constructor.induct projection.i arguments.back!
  if let some matcher ← nonrecursiveRecursor? value then
    return ← compileMatcher root bindings matcher
  if let some matcher ← sparseMatcher? value then
    return ← compileMatcher root bindings matcher
  if let some matcher ← matchMatcherApp? value (alsoCasesOn := true) then
    return ← compileMatcher root bindings matcher
  if function.isConstOf ``ite || function.isConstOf ``dite then
    unless arguments.size == 5 do throwError "unsaturated source conditional"
    return ← compileGuard root bindings arguments[1]! arguments[3]! arguments[4]!
      (function.isConstOf ``dite) value
  if function.isConstOf ``Bool.and then
    unless arguments.size == 2 do throwError "unsaturated Boolean conjunction"
    let condition ← mkEq arguments[0]! (mkConst ``Bool.true)
    return ← compileGuard root bindings condition arguments[1]! (mkConst ``Bool.false) false value
  if function.isConstOf ``decide then
    unless arguments.size == 2 do throwError "unsaturated source decision"
    let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) arguments[0]!)
    let expected := mkAppN (mkConst ``decide) #[arguments[0]!, decisionInstance]
    unless ← isDefEq value expected do throwError "foreign source decision instance"
    return ← compileCondition root bindings arguments[0]!
  if isOptionBind value then
    unless arguments.size ≥ 2 do throwError "unsaturated optional sequencing"
    let first := arguments[arguments.size - 2]!
    let continuation ← whnf arguments[arguments.size - 1]!
    unless continuation.isLambda do throwError "optional continuation is not a source lambda"
    unless (← whnf (← inferType value)).getAppFn.isConstOf ``Option do
      throwError "source bind is not an Option computation"
    let actual ← mkAppM ``Option.bind #[first, continuation]
    unless ← isDefEq value actual do throwError "foreign optional bind instance"
    let head ← freshHead root
    let captures := bindings.map fun binding => binding.target
    let firstIR ← compileBody root bindings first
    return ← lambdaTelescope continuation fun parameters body => do
      unless parameters.size == 1 do throwError "optional continuation has wrong arity"
      let name := "bound:" ++ toString (← get).next
      let captureNames := bindings.toList.zipIdx.map fun (_, index) => "capture:" ++ toString index
      let rebound := bindings.zip captureNames.toArray |>.map fun (binding, name) =>
        { binding with target := DeterministicEquations.Term.var name }
      let childIR ← compileBody root (rebound.push ⟨parameters[0]!, .var name⟩) body
      let capturePatterns := captureNames.map DeterministicEquations.Term.var
      modify fun state => { state with helpers := state.helpers ++ #[
        ⟨head ++ ":none", head, .sym "None" :: capturePatterns, .sym "None"⟩,
        ⟨head ++ ":some", head, named "Some" [.var name] :: capturePatterns, childIR⟩] }
      recordSourceHelper root bindings head value
        ((Array.range bindings.size).map (· + 1))
      return named head (firstIR :: captures.toList)
  if isOptionPure value then
    unless arguments.size > 0 do throwError "unsaturated source pure"
    unless (← whnf (← inferType value)).getAppFn.isConstOf ``Option do
      throwError "source pure is not an Option computation"
    let actual ← mkAppM ``Option.some #[arguments[arguments.size - 1]!]
    unless ← isDefEq value actual do throwError "foreign optional pure instance"
    let someIR ← compileBody root bindings arguments[arguments.size - 1]!
    return named "Some" [someIR]
  let type ← whnf (← inferType value)
  if type.getAppFn.isConstOf ``Finset && type.getAppArgs[0]!.isConstOf ``Nat then
    if function.isConstOf ``Union.union then
      unless arguments.size ≥ 2 do throwError "unsaturated finite-set union"
      let left := arguments[arguments.size - 2]!
      let right := arguments[arguments.size - 1]!
      let actual := mkAppN (mkConst ``natSetUnion) #[left, right]
      unless ← isDefEq value actual do throwError "foreign finite-set union instance"
      return ← compileBody root bindings actual
    if function.isConstOf ``Singleton.singleton then
      unless arguments.size ≥ 1 do throwError "unsaturated finite-set singleton"
      let index := arguments.back!
      unless ← isDefEq value (mkApp (mkConst ``natSetSingleton) index) do
        throwError "foreign finite-set singleton instance"
      return .list [← compileBody root bindings index]
    if function.isConstOf ``EmptyCollection.emptyCollection then
      unless ← isDefEq value (mkConst ``natSetEmpty) do
        throwError "foreign finite-set empty instance"
      return .list []
  if type.isConstOf ``Nat then
    let operation ← if function.isConstOf ``HAdd.hAdd || function.isConstOf ``Nat.add then
      pure (some (``Nat.add, "nik:nat-add"))
    else if function.isConstOf ``HSub.hSub || function.isConstOf ``Nat.sub then
      pure (some (``Nat.sub, "nik:nat-monus"))
    else if function.isConstOf ``Max.max || function.isConstOf ``Nat.max then
      pure (some (``Nat.max, "nik:nat-max"))
    else pure none
    if let some (source, head) := operation then
      unless arguments.size ≥ 2 do throwError "unsaturated natural operation"
      let left := arguments[arguments.size - 2]!
      let right := arguments[arguments.size - 1]!
      let expected ← mkAppM source #[left, right]
      unless ← isDefEq value expected do throwError "foreign natural arithmetic instance"
      return named head [← compileBody root bindings left, ← compileBody root bindings right]
  if type.isConstOf ``Nat &&
      (function.isConstOf ``HMod.hMod || function.isConstOf ``HDiv.hDiv ||
       function.isConstOf ``Nat.mod || function.isConstOf ``Nat.div) then
    unless arguments.size ≥ 2 do throwError "unsaturated arithmetic source call"
    let left := arguments[arguments.size - 2]!
    let right := arguments[arguments.size - 1]!
    let some divisor := (← whnf right).rawNatLit? | throwError "division extraction currently requires a nonzero literal divisor"
    if divisor == 0 then throwError "zero-divisor source arithmetic is outside this primitive profile"
    let remainder := function.isConstOf ``HMod.hMod || function.isConstOf ``Nat.mod
    let expected ← mkAppM (if remainder then ``Nat.mod else ``Nat.div) #[left, right]
    unless ← isDefEq value expected do throwError "foreign arithmetic instance"
    return named (if remainder then "nik:nat-mod" else "nik:nat-div")
      [← compileBody root bindings left, natural divisor]
  if function.isConstOf ``UInt8.ofNat then
    unless arguments.size == 1 do throwError "unsaturated byte conversion"
    return named "nik:nat-mod" [← compileBody root bindings arguments[0]!, natural 256]
  if function.isConstOf ``List.all then
    unless arguments.size ≥ 2 do throwError "unsaturated ordered list test"
    return ← compileListAll root bindings arguments[arguments.size - 2]! arguments.back! value
  if function.isConstOf ``List.zip then
    unless arguments.size ≥ 2 do throwError "unsaturated list zip"
    return ← compileListZip root bindings arguments[arguments.size - 2]! arguments.back! value
  if function.isConstOf ``List.zipIdx then
    unless arguments.size ≥ 2 do throwError "unsaturated indexed list zip"
    return ← compileListZipIdx root bindings arguments[arguments.size - 2]! arguments.back! value
  if function.isConstOf ``GetElem?.getElem? || function.isConstOf ``List.get?Internal then
    unless arguments.size ≥ 2 do throwError "unsaturated list lookup"
    let values := arguments[arguments.size - 2]!
    let index := arguments[arguments.size - 1]!
    let valuesType ← whnf (← inferType values)
    unless valuesType.getAppFn.isConstOf ``List do
      throwError "lookup is outside the standard list profile"
    let expected ← mkAppM ``List.get?Internal #[values, index]
    unless ← isDefEq value expected do throwError "foreign list lookup instance"
    let elementType ← instantiateMVars valuesType.getAppArgs[0]!
    unless !elementType.hasFVar && !elementType.hasMVar do
      throwError "lookup element type is not closed supported data"
    modify fun state => { state with
      usesAdapterLookup := true
      lookupTypes := if state.lookupTypes.contains elementType then state.lookupTypes
        else state.lookupTypes.push elementType }
    return named (root.head ++ ":lookup")
      [← compileBody root bindings values, ← compileBody root bindings index]
  if function.isConstOf ``List.lookup then
    unless arguments.size ≥ 2 do throwError "unsaturated association lookup"
    let key := arguments[arguments.size - 2]!
    let values := arguments[arguments.size - 1]!
    let expected ← mkAppM ``List.lookup #[key, values]
    unless ← isDefEq value expected do throwError "foreign association lookup instance"
    let keyType ← instantiateMVars (← inferType key)
    let _ ← synthInstance (← mkAppOptM ``LawfulBEq #[some keyType, none])
    let valuesType ← whnf (← inferType values)
    let pairType ← whnf valuesType.getAppArgs[0]!
    unless valuesType.getAppFn.isConstOf ``List && pairType.getAppFn.isConstOf ``Prod do
      throwError "association lookup is outside the checked list-of-pairs profile"
    let elementType ← instantiateMVars pairType.getAppArgs[1]!
    unless !keyType.hasFVar && !keyType.hasMVar && !elementType.hasFVar && !elementType.hasMVar do
      throwError "association lookup requires closed supported key and value types"
    let _ ← encoderInjective keyType
    modify fun state => { state with
      associationTypes := if state.associationTypes.contains (keyType, elementType)
        then state.associationTypes else state.associationTypes.push (keyType, elementType) }
    return named (root.head ++ ":association")
      [← compileBody root bindings values, ← compileBody root bindings key]
  if root.adapter.isSome && function.isFVar && arguments.size == 1 then
    if let some values ← bound? bindings function then
      let inputType ← inferType arguments[0]!
      let expected ← mkArrow inputType (← inferType value)
      unless ← isDefEq (← inferType function) expected do
        throwError "the declared adapter has a foreign function type"
      let valuesType ← whnf root.argumentTypes[0]!
      let elementType ← instantiateMVars valuesType.getAppArgs[0]!
      match root.adapterKind with
      | .indexed =>
          unless ← isDefEq inputType (mkConst ``Nat) do
            throwError "indexed adapter has a foreign key type"
          modify fun state => { state with
            usesAdapterLookup := true
            lookupTypes := if state.lookupTypes.contains elementType then state.lookupTypes
              else state.lookupTypes.push elementType }
          return named (root.head ++ ":lookup") [values, ← compileBody root bindings arguments[0]!]
      | .association =>
          let pairType ← whnf elementType
          let types := (pairType.getAppArgs[0]!, pairType.getAppArgs[1]!)
          modify fun state => { state with
            associationTypes := if state.associationTypes.contains types then state.associationTypes
              else state.associationTypes.push types }
          return named (root.head ++ ":association") [values, ← compileBody root bindings arguments[0]!]
  if let some name := function.constName? then
    if (← getConstInfo name).isCtor then
      let (name, values) ← fields value
      if name == ``Option.none then return .sym "None"
      if name == ``List.nil then return .list []
      if name == ``List.cons then
        return named "nik:list-cons" (← compileBodies root bindings values).toList
      if name == ``Nat.succ then
        return named "nik:nat-add" [← compileBody root bindings values[0]!, natural 1]
      let shape ← constructorShape value
      let encodedFields ← values.toList.mapM fun value => encodeValue value
      if (shape.container == 0 || shape.container == 3) && !values.isEmpty then
        throwError "symbol codec hides constructor fields"
      let expected := shape.quote encodedFields
      unless ← isDefEq (← encodeValue value) expected do
        throwError "constructor encoding does not preserve its declared field order"
      return shape.encode (← compileBodies root bindings values).toList
  throwError "unsupported source expression in extraction: {value}"

partial def compileBodies (root : Root) (bindings : Bindings) (values : Array Lean.Expr) :
    CompileM (Array DeterministicEquations.Term) := do
  values.mapM (compileBody root bindings)

private partial def compileCondition (root : Root) (bindings : Bindings)
    (condition : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let function := condition.getAppFn
  let arguments := condition.getAppArgs
  if (function.isConstOf ``LT.lt || function.isConstOf ``Nat.lt ||
      function.isConstOf ``LE.le || function.isConstOf ``Nat.le) && arguments.size ≥ 2 then
    let left := arguments[arguments.size - 2]!
    let right := arguments[arguments.size - 1]!
    unless (← whnf (← inferType left)).isConstOf ``Nat do
      throwError "non-natural comparison is outside the checked scalar profile"
    let less := function.isConstOf ``LT.lt || function.isConstOf ``Nat.lt
    let expected ← mkAppM (if less then ``Nat.lt else ``Nat.le) #[left, right]
    unless ← isDefEq condition expected do throwError "foreign scalar ordering instance"
    return named (if less then "nik:nat-lt" else "nik:nat-le")
      [← compileBody root bindings left, ← compileBody root bindings right]
  if function.isConstOf ``Eq && arguments.size == 3 then
    if (← whnf arguments[0]!).isConstOf ``Nat then
      return named "nik:nat-eq"
        [← compileBody root bindings arguments[1]!, ← compileBody root bindings arguments[2]!]
    if (← whnf arguments[0]!).isConstOf ``Bool && arguments[2]!.isConstOf ``Bool.true then
      return ← compileBody root bindings arguments[1]!
    let _ ← encoderInjective arguments[0]!
    return named "nik:data-eq"
      [← compileBody root bindings arguments[1]!, ← compileBody root bindings arguments[2]!]
  if function.isConstOf ``Not && arguments.size == 1 then
    let source := mkAppN (mkConst ``decide)
      #[condition, ← synthInstance (mkApp (mkConst ``Decidable) condition)]
    return ← compileGuard root bindings arguments[0]!
      (mkConst ``Bool.false) (mkConst ``Bool.true) false source
  if (function.isConstOf ``And || function.isConstOf ``Or) && arguments.size == 2 then
    let second := mkAppN (mkConst ``decide)
      #[arguments[1]!, ← synthInstance (mkApp (mkConst ``Decidable) arguments[1]!)]
    let source := mkAppN (mkConst ``decide)
      #[condition, ← synthInstance (mkApp (mkConst ``Decidable) condition)]
    if function.isConstOf ``And then
      return ← compileGuard root bindings arguments[0]! second (mkConst ``Bool.false) false source
    else
      return ← compileGuard root bindings arguments[0]! (mkConst ``Bool.true) second false source
  if function.isConstOf ``Membership.mem && arguments.size ≥ 2 then
    let values := arguments[arguments.size - 2]!
    let index := arguments.back!
    let valuesType ← whnf (← inferType values)
    unless valuesType.getAppFn.isConstOf ``Finset &&
        valuesType.getAppArgs[0]!.isConstOf ``Nat do
      throwError "membership is outside the checked finite-natural-set profile"
    let expected ← mkAppM ``Membership.mem #[values, index]
    unless ← isDefEq condition expected do throwError "foreign finite-set membership instance"
    return ← compileBody root bindings (mkAppN (mkConst ``natSetMember) #[index, values])
  if let some sourceName := function.constName? then
    if let some equations ← getEqnsFor? sourceName then
      for equationName in equations do
        let information ← getConstInfo equationName
        let recursive ← forallTelescopeReducing information.type fun _ statement => do
          let some (_, _, body) := statement.eq? | return false
          return (body.find? fun expression => expression.isConstOf sourceName).isSome
        if recursive then
          throwError "recursive source propositions require a certified computational dependency"
  let reduced ← whnf condition
  let decision := mkAppN (mkConst ``decide)
    #[condition, ← synthInstance (mkApp (mkConst ``Decidable) condition)]
  if let some matcher ← nonrecursiveRecursor? reduced then
    return ← compileMatcher root bindings matcher (some decision)
  if let some matcher ← sparseMatcher? reduced then
    return ← compileMatcher root bindings matcher (some decision)
  if let some matcher ← matchMatcherApp? reduced (alsoCasesOn := true) then
    return ← compileMatcher root bindings matcher (some decision)
  throwError "unsupported source condition: {condition}"

private partial def compileGuard (root : Root) (bindings : Bindings) (condition yes no : Lean.Expr)
    (dependent : Bool) (source : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let head ← freshHead root
  let test ← compileCondition root bindings condition
  let captures := bindings.map (·.target)
  let names := bindings.toList.zipIdx.map fun (_, index) => "capture:" ++ toString index
  let rebound := bindings.zip names.toArray |>.map fun (binding, name) =>
    { binding with target := DeterministicEquations.Term.var name }
  let branch (body : Lean.Expr) : CompileM DeterministicEquations.Term := do
    if !dependent then compileBody root rebound body
    else
      lambdaTelescope body fun proofs value => do
        unless proofs.size == 1 && (← isProp (← inferType proofs[0]!)) do
          throwError "dependent conditional does not carry exactly its checked proof"
        compileBody root rebound value
  let trueBody ← branch yes
  let falseBody ← branch no
  let patterns := names.map DeterministicEquations.Term.var
  modify fun state => { state with helpers := state.helpers ++ #[
    ⟨head ++ ":true", head, .sym "True" :: patterns, trueBody⟩,
    ⟨head ++ ":false", head, .sym "False" :: patterns, falseBody⟩] }
  recordSourceHelper root bindings head source ((Array.range bindings.size).map (· + 1))
  return named head (test :: captures.toList)

/-- The predicate is compiled from its actual typed source body, not delegated
to a host callback. Captures remain fixed while the list is traversed. -/
private partial def compileListAll (root : Root) (bindings : Bindings)
    (values predicate original : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let actual ← mkAppM ``List.all #[values, predicate]
  unless ← isDefEq actual original do throwError "foreign ordered-list test"
  let listType ← whnf (← inferType values)
  unless listType.getAppFn.isConstOf ``List do throwError "list test requires source list data"
  let elementType ← instantiateMVars listType.getAppArgs[0]!
  unless !elementType.hasFVar && !elementType.hasMVar do
    throwError "list test element type is not closed supported data"
  let _ ← encoder elementType
  let head ← freshHead root
  let encodedValues ← compileBody root bindings values
  let captureNames := bindings.toList.zipIdx.map fun (_, index) => "capture:" ++ toString index
  let capturePatterns := captureNames.map DeterministicEquations.Term.var
  let rebound := bindings.zip captureNames.toArray |>.map fun (binding, name) =>
    { binding with target := DeterministicEquations.Term.var name }
  let items := DeterministicEquations.Term.var "items"
  let first := DeterministicEquations.Term.var "first"
  let rest := DeterministicEquations.Term.var "rest"
  withLocalDeclD `listElement elementType fun element => do
    let test ← compileBody root (rebound.push ⟨element, first⟩) (mkApp predicate element).headBeta
    modify fun state => { state with helpers := state.helpers ++ #[
      ⟨head ++ ":entry", head, capturePatterns ++ [items],
        named (head ++ ":case") (named "nik:list-view" [items] :: capturePatterns)⟩,
      ⟨head ++ ":nil", head ++ ":case", .sym "List:Nil" :: capturePatterns, .sym "True"⟩,
      ⟨head ++ ":cons", head ++ ":case", named "List:Cons" [first, rest] :: capturePatterns,
        named (head ++ ":choose") (test :: (capturePatterns ++ [rest]))⟩,
      ⟨head ++ ":false", head ++ ":choose", .sym "False" :: (capturePatterns ++ [rest]), .sym "False"⟩,
      ⟨head ++ ":true", head ++ ":choose", .sym "True" :: (capturePatterns ++ [rest]),
        named head (capturePatterns ++ [rest])⟩] }
  withLocalDeclD `listItems listType fun sourceValues => do
    let source ← mkAppM ``List.all #[sourceValues, predicate]
    let captures := bindings.push ⟨sourceValues, items⟩
    let template ← sourceTemplate root captures source
    let entry : SourceHelper := {
      head, source := template, positions := Array.range captures.size
      inductionPosition := some bindings.size }
    modify fun state => { state with sourceHelpers := state.sourceHelpers.push entry }
  return named head ((bindings.map (·.target)).toList ++ [encodedValues])

/-- Exact truncating zip; list constructors are inspected through the existing
shared view, retaining source order and multiplicity. -/
private partial def compileListZip (root : Root) (bindings : Bindings)
    (left right original : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let actual ← mkAppM ``List.zip #[left, right]
  unless ← isDefEq actual original do throwError "foreign list zip"
  let leftType ← whnf (← inferType left)
  let rightType ← whnf (← inferType right)
  unless leftType.getAppFn.isConstOf ``List && rightType.getAppFn.isConstOf ``List do
    throwError "zip requires two source lists"
  let _ ← encoder leftType
  let _ ← encoder rightType
  unless !leftType.hasFVar && !rightType.hasFVar && !leftType.hasMVar && !rightType.hasMVar do
    throwError "zip list types are not closed supported data"
  let head ← freshHead root
  let leftIR ← compileBody root bindings left
  let rightIR ← compileBody root bindings right
  let xs := DeterministicEquations.Term.var "left"
  let ys := DeterministicEquations.Term.var "right"
  let x := DeterministicEquations.Term.var "first:left"
  let y := DeterministicEquations.Term.var "first:right"
  let xt := DeterministicEquations.Term.var "rest:left"
  let yt := DeterministicEquations.Term.var "rest:right"
  modify fun state => { state with helpers := state.helpers ++ #[
    ⟨head ++ ":entry", head, [xs, ys],
      named (head ++ ":case") [named "nik:list-view" [xs], named "nik:list-view" [ys]]⟩,
    ⟨head ++ ":nil-left", head ++ ":case", [.sym "List:Nil", ys], .list []⟩,
    ⟨head ++ ":nil-right", head ++ ":case", [xs, .sym "List:Nil"], .list []⟩,
    ⟨head ++ ":cons", head ++ ":case", [named "List:Cons" [x, xt], named "List:Cons" [y, yt]],
      named "nik:list-cons" [named "Pair" [x, y], named head [xt, yt]]⟩] }
  withLocalDeclD `zipLeft leftType fun xs => do
    withLocalDeclD `zipRight rightType fun ys => do
      let source ← mkAppM ``List.zip #[xs, ys]
      let template ← instantiateMVars (← mkLambdaFVars #[xs, ys] source)
      let entry : SourceHelper := {
        head, source := template, positions := #[0, 1]
        inductionPosition := some 0, generalizedParameters := #[1] }
      modify fun state => { state with sourceHelpers := state.sourceHelpers.push entry }
  return named head [leftIR, rightIR]

/-- Source `zipIdx` keeps the arbitrary initial natural index. -/
private partial def compileListZipIdx (root : Root) (bindings : Bindings)
    (values initial original : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let actual ← mkAppM ``List.zipIdx #[values, initial]
  unless ← isDefEq actual original do throwError "foreign indexed list zip"
  let listType ← whnf (← inferType values)
  unless listType.getAppFn.isConstOf ``List do throwError "indexed zip requires source list data"
  let _ ← encoder listType
  unless !listType.hasFVar && !listType.hasMVar do
    throwError "indexed zip element type is not closed supported data"
  unless (← whnf (← inferType initial)).isConstOf ``Nat do
    throwError "indexed zip requires a natural initial index"
  let head ← freshHead root
  let valuesIR ← compileBody root bindings values
  let initialIR ← compileBody root bindings initial
  let items := DeterministicEquations.Term.var "items"
  let index := DeterministicEquations.Term.var "index"
  let first := DeterministicEquations.Term.var "first"
  let rest := DeterministicEquations.Term.var "rest"
  modify fun state => { state with helpers := state.helpers ++ #[
    ⟨head ++ ":entry", head, [items, index],
      named (head ++ ":case") [named "nik:list-view" [items], index]⟩,
    ⟨head ++ ":nil", head ++ ":case", [.sym "List:Nil", index], .list []⟩,
    ⟨head ++ ":cons", head ++ ":case", [named "List:Cons" [first, rest], index],
      named "nik:list-cons" [named "Pair" [first, index],
        named head [rest, named "nik:nat-add" [index, natural 1]]]⟩] }
  withLocalDeclD `zipItems listType fun xs => do
    withLocalDeclD `zipIndex (mkConst ``Nat) fun n => do
      let source ← mkAppM ``List.zipIdx #[xs, n]
      let template ← instantiateMVars (← mkLambdaFVars #[xs, n] source)
      let entry : SourceHelper := {
        head, source := template, positions := #[0, 1]
        inductionPosition := some 0, generalizedParameters := #[1] }
      modify fun state => { state with sourceHelpers := state.sourceHelpers.push entry }
  return named head [valuesIR, initialIR]

private partial def sourcePattern (pattern : Lean.Expr) (base : DeterministicEquations.Term)
    (bindings : Bindings) : MetaM (DeterministicEquations.Term × Bindings) := do
  if pattern.isFVar then return (base, bindings.push ⟨pattern, base⟩)
  if (← whnf pattern).rawNatLit? == some 0 then return (.sym "True", bindings)
  let (name, arguments) ← fields pattern
  if name == ``Nat.zero then return (.sym "True", bindings)
  if name == ``Nat.succ then
    unless arguments.size == 1 && arguments[0]!.isFVar do throwError "unsupported nested natural pattern"
    return (.sym "False", bindings.push ⟨arguments[0]!, named "nik:nat-pred" [base]⟩)
  if name == ``List.nil then return (.sym "List:Nil", bindings)
  if name == ``List.cons then
    unless arguments.size == 2 do throwError "malformed source list pattern"
    unless arguments.all (·.isFVar) do
      throwError "nested source list patterns require additional checked views"
    let .var baseName := base | throwError "unsupported nested source list pattern"
    let mut patterns : Array DeterministicEquations.Term := #[]
    let mut bindings := bindings
    for index in [:arguments.size] do
      let field := DeterministicEquations.Term.var (baseName ++ ":field:" ++ toString index)
      let (pattern, updated) ← sourcePattern arguments[index]! field bindings
      patterns := patterns.push pattern
      bindings := updated
    return (named "List:Cons" patterns.toList, bindings)
  let shape ← constructorShape pattern
  if (shape.container == 0 || shape.container == 3) && !arguments.isEmpty then
    throwError "symbol codec hides pattern constructor fields"
  let encodedFields ← arguments.toList.mapM encodeValue
  let expected := shape.quote encodedFields
  unless ← isDefEq (← encodeValue pattern) expected do
    throwError "pattern encoding does not preserve its declared field order"
  let mut patterns : Array DeterministicEquations.Term := #[]
  let mut bindings := bindings
  for index in [:arguments.size] do
    let .var baseName := base | throwError "unsupported nested source pattern view"
    let field := DeterministicEquations.Term.var (baseName ++ ":field:" ++ toString index)
    let (pattern, updated) ← sourcePattern arguments[index]! field bindings
    patterns := patterns.push pattern
    bindings := updated
  return (shape.encode patterns.toList, bindings)

private partial def compileProjection (root : Root) (bindings : Bindings)
    (structureName : Name) (index : Nat) (record : Lean.Expr) : CompileM DeterministicEquations.Term := do
  let .inductInfo info ← getConstInfo structureName |
    throwError "projection source is not an inductive data type"
  unless info.ctors.length == 1 && info.numIndices == 0 do
    throwError "projection requires one non-indexed data constructor"
  let recordType ← whnf (← inferType record)
  let constructor ← mkConstWithFreshMVarLevels info.ctors[0]!
  let applied := mkAppN constructor (recordType.getAppArgs.extract 0 info.numParams)
  let head ← freshHead root
  let recordIR ← compileBody root bindings record
  forallTelescopeReducing (← inferType applied) fun fields _ => do
    unless index < fields.size do throwError "source field index is out of bounds"
    let constructed := mkAppN applied fields
    let (pattern, fieldBindings) ← sourcePattern constructed (.var "record") #[]
    let some selected ← bound? fieldBindings fields[index]! |
      throwError "source field is not preserved by its actual codec"
    modify fun state => { state with
      helpers := state.helpers.push ⟨head ++ ":projection", head, [pattern], selected⟩ }
    recordSourceHelper root #[⟨record, .var "record"⟩] head
      (.proj structureName index record) #[0]
    return named head [recordIR]

private partial def compileMatcher (root : Root) (bindings : Bindings)
    (matcher : MatcherApp) (decision : Option Lean.Expr := none) : CompileM DeterministicEquations.Term := do
  unless matcher.remaining.isEmpty && matcher.numDiscrs > 0 do
    throwError "overapplied source matcher is outside the data profile"
  let head ← freshHead root
  let originalIR ← compileBodies root bindings matcher.discrs
  let captureNames := bindings.toList.zipIdx.map fun (_, index) => "capture:" ++ toString index
  let rebound := bindings.zip captureNames.toArray |>.map fun (binding, name) =>
    { binding with target := DeterministicEquations.Term.var name }
  let mut views : Array Nat := #[]
  for discriminator in matcher.discrs do
    let type ← whnf (← inferType discriminator)
    views := views.push (if type.isConstOf ``Nat then 1
      else if type.getAppFn.isConstOf ``List then 2 else 0)
  let rows ← compileMatcherRows root head matcher rebound 0 #[] #[] captureNames decision.isSome
  modify fun state => { state with helpers := state.helpers ++ rows }
  -- Recursors place their major argument after the minor premises, unlike matchers.
  let source ← if (← getConstInfo matcher.matcherName) matches .recInfo _ then
      pure (mkAppN (mkConst matcher.matcherName matcher.matcherLevels.toList)
        (matcher.params ++ #[matcher.motive] ++ matcher.alts ++ matcher.discrs))
    else pure matcher.toExpr
  recordSourceHelper root bindings head (decision.getD source)
    ((Array.range bindings.size).map (· + matcher.discrs.size))
  let selected := originalIR.toList.zipIdx.map fun (input, index) =>
    if views[index]! == 1 then named "nik:nat-zero" [input]
    else if views[index]! == 2 then named "nik:list-view" [input]
    else input
  return named head (selected ++ (bindings.map (·.target)).toList ++ originalIR.toList)

private partial def compileMatcherRows (root : Root) (head : String) (matcher : MatcherApp)
    (bindings : Bindings) (index : Nat) (known : Array Lean.Expr)
    (patterns : Array DeterministicEquations.Term)
    (captureNames : List String) (decision : Bool) : CompileM (Array Equation) := do
  if index == matcher.discrs.size then
    let selected := { matcher with discrs := known }
    let body ← if (← getConstInfo matcher.matcherName) matches .recInfo _ then
        let actual := mkAppN (mkConst matcher.matcherName matcher.matcherLevels.toList)
          (matcher.params ++ #[matcher.motive] ++ matcher.alts ++ known)
        whnfCore actual
      else if let some body ← reduceRecMatcher? selected.toExpr then whnfCore body
      else
        let .defnInfo information ← getConstInfo matcher.matcherName |
          throwError "source constructor case is not a defined matcher: {selected.toExpr}"
        let actual ← instantiateValueLevelParams (.defnInfo information)
          matcher.matcherLevels.toList
        pure (← whnfCore (mkAppN actual selected.toExpr.getAppArgs).headBeta)
    let encoded ← if decision then compileCondition root bindings body
      else compileBody root bindings body
    let originals := (List.range known.size).map fun position =>
      DeterministicEquations.Term.var ("scrutinee:" ++ toString position)
    return #[⟨head ++ ":case:" ++ toString (← get).helpers.size, head,
      patterns.toList ++ captureNames.map DeterministicEquations.Term.var ++ originals, encoded⟩]
  let type ← whnf (← inferType matcher.discrs[index]!)
  let .const typeName _ := type.getAppFn | throwError "source discriminator is not declared data"
  let .inductInfo info ← getConstInfo typeName | throwError "source discriminator is not inductive"
  unless info.numIndices == 0 do throwError "indexed source elimination is unsupported"
  let mut rows := #[]
  for constructorName in info.ctors do
    let constructor ← mkConstWithFreshMVarLevels constructorName
    let applied := mkAppN constructor (type.getAppArgs.extract 0 info.numParams)
    let branch ← forallTelescopeReducing (← inferType applied) fun fields _ => do
      let value := mkAppN applied fields
      let (pattern, updated) ← sourcePattern value (.var ("scrutinee:" ++ toString index)) bindings
      compileMatcherRows root head matcher updated (index + 1) (known.push value)
        (patterns.push pattern) captureNames decision
    rows := rows ++ branch
  return rows

end

def inspectRoot (name : Name) (head : String) (adapter : Option Name := none) : MetaM Root := do
  let info ← getConstInfo name
  unless info.isDefinition do throwError "extraction requires a transparent definition"
  let some equations ← getEqnsFor? name | throwError "source has no checked defining equations"
  forallTelescopeReducing info.type fun parameters resultType => do
    let mut argumentTypes ← parameters.mapM inferType
    let mut adapterKind := AdapterKind.indexed
    if let some adapterName := adapter then
      unless parameters.size > 0 do throwError "adapter has no source parameter"
      let adapterInfo ← getConstInfo adapterName
      let .forallE _ adaptedType returned _ := adapterInfo.type |
        throwError "only a one-argument data adapter is supported"
      unless ← isDefEq returned argumentTypes[0]! do
        throwError "adapter does not produce the exact first source parameter"
      let dataType ← whnf adaptedType
      unless dataType.getAppFn.isConstOf ``List do
        throwError "adapter requires a checked finite list representation"
      adapterKind ← withLocalDeclD `values adaptedType fun values => do
        forallTelescopeReducing argumentTypes[0]! fun input result => do
          unless input.size == 1 && (← whnf result).getAppFn.isConstOf ``Option do
            throwError "adapter must expose one checked lookup key and optional result"
          let actual := mkAppN (mkConst adapterName) #[values, input[0]!]
          let indexed ← if (← whnf (← inferType input[0]!)).isConstOf ``Nat then
            try isDefEq actual (← mkAppM ``List.get?Internal #[values, input[0]!])
            catch _ => pure false
            else pure false
          if indexed then return .indexed
          let elementType ← whnf dataType.getAppArgs[0]!
          unless elementType.getAppFn.isConstOf ``Prod do
            throwError "adapter is neither an indexed list nor an association table"
          let expected ← mkAppM ``List.lookup #[input[0]!, values]
          unless ← isDefEq actual expected do
            throwError "adapter is not the actual checked association lookup"
          let keyType ← inferType input[0]!
          let _ ← synthInstance (← mkAppOptM ``LawfulBEq #[some keyType, none])
          let _ ← encoderInjective keyType
          return .association
      argumentTypes := argumentTypes.set! 0 adaptedType
    for type in argumentTypes do
      let _ ← encoder type
    let _ ← encoder resultType
    return { sourceName := name
             head := head
             parameters := parameters.size
             argumentTypes := argumentTypes
             resultType := resultType
             equationNames := equations
             adapter := adapter
             adapterKind := adapterKind
             dependencies := dependencyExtension.getState (← getEnv) }

def registerDependency (entry : DependencyEntry) : Elab.Term.TermElabM Unit := do
  if (dependencyExtension.getState (← getEnv)).any (·.sourceName == entry.sourceName) then
    throwError "source dependency already has a registered realization"
  unless ← isDefEq (← inferType (mkConst entry.programName)) (mkConst ``Program) do
    throwError "dependency does not name an equation program"
  let info ← getConstInfo entry.certificateName
  unless info matches .thmInfo _ do throwError "dependency certificate must be a checked theorem"
  let root ← inspectRoot entry.sourceName entry.head entry.adapter
  let sourceInfo ← getConstInfo entry.sourceName
  let expected ← forallTelescopeReducing sourceInfo.type fun original _ => do
    let build (parameters sourceParameters : Array Lean.Expr) : MetaM Lean.Expr := do
      let arguments ← parameters.toList.mapM encodeValue
      let source := mkAppN (mkConst entry.sourceName) sourceParameters
      let proposition ← mkAppM ``Applies #[mkConst entry.programName,
        ← extractionHost entry.programName, mkStrLit entry.head,
        ← mkListLit (mkConst ``DeterministicEquations.Term) arguments, ← encodeValue source]
      mkForallFVars parameters proposition
    if let some adapter := entry.adapter then
      withLocalDeclD `dependencyValues root.argumentTypes[0]! fun values => do
        build (original.set! 0 values) (original.set! 0 (mkApp (mkConst adapter) values))
    else build original original
  unless ← isDefEq info.type expected do
    throwError "dependency theorem does not state the exact universal encoded source computation"
  modifyEnv fun env => dependencyExtension.addEntry env entry

inductive PatternView where
  | none | natural | list
  deriving Inhabited

def lookupRows (head : String) : Program :=
  let values := DeterministicEquations.Term.var "values"
  let index := DeterministicEquations.Term.var "index"
  let first := DeterministicEquations.Term.var "first"
  let rest := DeterministicEquations.Term.var "rest"
  [⟨head ++ ":entry", head, [values, index],
      named (head ++ ":case") [named "nik:list-view" [values], named "nik:nat-zero" [index], index]⟩,
   ⟨head ++ ":nil", head ++ ":case", [.sym "List:Nil", .var "zero", index], .sym "None"⟩,
   ⟨head ++ ":zero", head ++ ":case", [named "List:Cons" [first, rest], .sym "True", index],
      named "Some" [first]⟩,
   ⟨head ++ ":successor", head ++ ":case", [named "List:Cons" [first, rest], .sym "False", index],
      named head [rest, named "nik:nat-pred" [index]]⟩]

/-- First-key association lookup; comparison occurs before the chosen branch. -/
def associationRows (head : String) : Program :=
  let values := DeterministicEquations.Term.var "values"
  let key := DeterministicEquations.Term.var "key"
  let found := DeterministicEquations.Term.var "found"
  let value := DeterministicEquations.Term.var "value"
  let rest := DeterministicEquations.Term.var "rest"
  [⟨head ++ ":entry", head, [values, key],
      named (head ++ ":case") [named "nik:list-view" [values], key]⟩,
   ⟨head ++ ":nil", head ++ ":case", [.sym "List:Nil", key], .sym "None"⟩,
   ⟨head ++ ":cons", head ++ ":case", [named "List:Cons" [named "Pair" [found, value], rest], key],
      named (head ++ ":choose") [named "nik:data-eq" [key, found], value, rest, key]⟩,
   ⟨head ++ ":found", head ++ ":choose", [.sym "True", value, rest, key], named "Some" [value]⟩,
   ⟨head ++ ":next", head ++ ":choose", [.sym "False", value, rest, key], named head [rest, key]⟩]

def compileRoot (root : Root) : MetaM Program := do
  let mut rows : Array Equation := #[]
  let mut state : BodyState := {}
  let mut viewed : Array PatternView := Array.replicate root.parameters .none
  for equationName in root.equationNames do
    let info ← getConstInfo equationName
    let (row, next, views) ← forallTelescopeReducing info.type fun parameters equationType => do
      let some (_, left, right) := equationType.eq? | throwError "source equation is not equality"
      unless left.getAppFn.isConstOf root.sourceName do throwError "source equation names another function"
      let arguments := left.getAppArgs
      unless arguments.size == root.parameters do throwError "source equation has wrong arity"
      let mut patterns : Array DeterministicEquations.Term := #[]
      let mut bindings : Bindings := #[]
      let mut views : Array PatternView := Array.replicate root.parameters .none
      for index in [:arguments.size] do
        let target := DeterministicEquations.Term.var ("argument:" ++ toString index)
        if arguments[index]!.isFVar then
          patterns := patterns.push target
          bindings := bindings.push ⟨arguments[index]!, target⟩
        else
          let (pattern, nextBindings) ← sourcePattern arguments[index]! target bindings
          patterns := patterns.push pattern
          bindings := nextBindings
          let type ← whnf (← inferType arguments[index]!)
          views := views.set! index (if type.isConstOf ``Nat then .natural
            else if type.getAppFn.isConstOf ``List then .list else .none)
      let (body, next) ← (compileBody root bindings right).run state
      let _ := parameters
      return (⟨equationName.toString, root.head ++ ":case", patterns.toList, body⟩, next, views)
    rows := rows.push row
    state := next
    viewed := viewed.zip views |>.map fun (left, right) =>
      match right with | .none => left | _ => right
  let inputs := (List.range root.parameters).map fun index =>
    DeterministicEquations.Term.var ("argument:" ++ toString index)
  let selectedInputs := inputs.zipIdx.map fun (input, index) =>
    match viewed[index]! with
    | .none => input
    | .natural => named "nik:nat-zero" [input]
    | .list => named "nik:list-view" [input]
  -- Original arguments are retained for predecessor projections in successor rows.
  rows := rows.map fun row =>
    { row with params := row.params ++ inputs }
  let lookup := if state.usesAdapterLookup then lookupRows (root.head ++ ":lookup") else []
  let association := if state.associationTypes.isEmpty then [] else associationRows (root.head ++ ":association")
  let mut program := ⟨root.head ++ ":entry", root.head, inputs,
    named (root.head ++ ":case") (selectedInputs ++ inputs)⟩ :: rows.toList ++ state.helpers.toList ++ lookup ++ association
  let retainedPrograms ← state.usedDependencies.toList.mapM fun dependency => do
    return (dependency, ← readProgram (mkConst dependency.programName))
  let retainedPrograms := retainedPrograms.mergeSort fun left right =>
    left.2.length ≥ right.2.length
  for (_, retained) in retainedPrograms do
    let mut alreadyRetained := false
    for offset in [:program.length] do
      if ← isDefEq (quoteProgram (program.drop offset |>.take retained.length))
          (quoteProgram retained) then
        alreadyRetained := true
        break
    if alreadyRetained then continue
    unless avoidsCalls retained program do
      throwError "linking captures a dependency call, constructor or primitive head"
    unless retained.all (fun row => !program.any (·.head == row.head)) do
      throwError "linked dependency duplicates an existing dispatch head"
    program := program ++ retained
  if !state.lookupTypes.isEmpty || !state.associationTypes.isEmpty then
    modifyEnv fun environment => lookupExtension.addEntry environment
      { head := root.head, elementTypes := state.lookupTypes, associationTypes := state.associationTypes }
  for helper in state.sourceHelpers do
    modifyEnv fun environment => sourceHelperExtension.addEntry environment helper
  return program

syntax (name := extractCandidate) "extract_candidate " ident " from " ident : command

@[command_elab extractCandidate] def elaborateCandidate : CommandElab := fun stx => do
  let name := stx[1].getId
  let source := stx[3].getId
  liftTermElabM do
    let source ← realizeGlobalConstNoOverloadWithInfo (mkIdent source)
    let declarationName := (← getCurrNamespace) ++ name
    let root ← inspectRoot source ("nik:extracted:" ++ declarationName.toString)
    let program ← compileRoot root
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := mkConst ``Program
      value := quoteProgram program
      hints := .abbrev
      safety := .safe }

syntax (name := extractSpecializedCandidate)
  "extract_specialized_candidate " ident " from " ident " using " ident : command

@[command_elab extractSpecializedCandidate] def elaborateSpecializedCandidate : CommandElab := fun stx => do
  let name := stx[1].getId
  liftTermElabM do
    let source ← realizeGlobalConstNoOverloadWithInfo stx[3]
    let adapter ← realizeGlobalConstNoOverloadWithInfo stx[5]
    let declarationName := (← getCurrNamespace) ++ name
    let root ← inspectRoot source ("nik:extracted:" ++ declarationName.toString) (some adapter)
    let program ← compileRoot root
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := mkConst ``Program
      value := quoteProgram program
      hints := .abbrev
      safety := .safe }

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
