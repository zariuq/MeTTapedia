import Mettapedia.Languages.HOLLight.ExportCodec
import Lean.Data.Json

/-!
# Numbered HOL source replay

The same source event is read against the receiving state's registered
signature and ordered parent lookup. An installation consumes the actual
replay equation for that state. Inference completion has a separate
entry point so a receiver can reuse an already checked primitive result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NumberedReplay

open Lean Mettapedia.Languages.OpenTheory
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay

abbrev Read (State : Type) := StateT State (Except String)

def fail {State : Type} {A : Type} (message : String) : Read State A := throw message

def jsonNat {State : Type} (value : Json) : Read State Nat :=
  match value.getNat? with
  | .ok value => pure value
  | .error error => fail error

def jsonText {State : Type} (value : Json) : Read State String :=
  match value.getStr? with
  | .ok value => pure value
  | .error error => fail error

def jsonArray {State : Type} (value : Json) : Read State (Array Json) :=
  match value.getArr? with
  | .ok value => pure value
  | .error error => fail error

def field {State : Type} (value : Json) (key : String) : Read State Json :=
  match value.getObjVal? key with
  | .ok value => pure value
  | .error error => fail error

def arrayAt {State : Type} (values : Array Json) (index : Nat) : Read State Json :=
  match values[index]? with
  | some value => pure value
  | none => fail s!"missing array position {index}"

def option {State : Type} {A : Type} (value : Option A) (message : String) : Read State A :=
  match value with
  | some value => pure value
  | none => fail message

private theorem get_bind_apply {State A : Type} (next : State → Read State A) (state : State) :
    ((get : Read State State) >>= next) state = next state state := rfl

structure Table (State Entry : Type) where
  rows : State → Array Json
  cache : State → Array (Option Entry)
  store : State → Nat → Entry → State

/-- A cache hit takes precedence over the source row. On a miss, decoding can
fill other entries before installing this result into the resulting state. -/
def Table.read {State Entry : Type} (table : Table State Entry) (kind : String) (index : Nat)
    (decode : State → Array Json → Read State Entry) : Read State Entry := do
  let before ← get
  if let some cached := (table.cache before)[index]?.join then return cached
  let row ← jsonArray (← option (table.rows before)[index]? s!"missing {kind} {index}")
  let entry ← decode before row
  modify fun state => table.store state index entry
  return entry

theorem Table.read_cached {State Entry : Type} (table : Table State Entry)
    (kind : String) (index : Nat) (decode : State → Array Json → Read State Entry)
    (before : State) (entry : Entry) (cached : (table.cache before)[index]?.join = some entry) :
    (table.read kind index decode).run before = .ok (entry, before) := by
  simp only [Table.read, StateT.run, get_bind_apply, cached]
  rfl

structure Syntax (State : Type) where
  types : Table State Ty
  terms : Table State SourceTerm
  symbols : State → ExportCodec.Symbols
  checkRowArity : Bool

def Syntax.readType {State : Type} (decoder : Syntax State) (index : Nat) : Read State Ty :=
  decoder.types.read "type" index fun before row => do
    let tag ← jsonText (← arrayAt row 0)
    if decoder.checkRowArity then
      unless row.size == (if tag == "var" then 2 else 3) do fail "wrong type row arity"
    let name ← jsonText (← arrayAt row 1)
    if tag == "var" then return .var (Name.global name)
    unless tag == "op" do fail s!"bad type tag {tag}"
    let operator ← option (List.lookup name (decoder.symbols before).operators) s!"unregistered type {name}"
    let arguments ← jsonArray (← arrayAt row 2)
    let arguments ← arguments.toList.mapM fun argument => do
      let child ← jsonNat argument
      if _earlier : child < index then decoder.readType child
      else fail s!"non-earlier type edge {index}->{child}"
    return .op operator arguments
termination_by index

def Syntax.readTerm {State : Type} (decoder : Syntax State) (index : Nat) : Read State SourceTerm :=
  decoder.terms.read "term" index fun before row => do
    let tag ← jsonText (← arrayAt row 0)
    if decoder.checkRowArity then
      unless row.size == 3 do fail "wrong term row arity"
    match tag with
    | "var" | "const" => do
      let name ← jsonText (← arrayAt row 1)
      let type ← decoder.readType (← jsonNat (← arrayAt row 2))
      if tag == "var" then return .var (Name.global name) type
      let constant ← option (List.lookup name (decoder.symbols before).constants) s!"unregistered constant {name}"
      return .const constant type
    | "app" => do
      let left ← jsonNat (← arrayAt row 1)
      let right ← jsonNat (← arrayAt row 2)
      if _earlier : left < index ∧ right < index then return .app (← decoder.readTerm left) (← decoder.readTerm right)
      else fail s!"non-earlier application edge {index}"
    | "abs" => do
      let binder ← jsonNat (← arrayAt row 1)
      let body ← jsonNat (← arrayAt row 2)
      if _earlier : binder < index ∧ body < index then
        match ← decoder.readTerm binder with
        | .var name type => return .abs name type (← decoder.readTerm body)
        | _ => fail s!"non-variable binder arrayAt {index}"
      else fail s!"non-earlier abstraction edge {index}"
    | _ => fail s!"bad term tag {tag}"
termination_by index

structure TermReader (State : Type) where
  sourceType : Nat → Read State Ty
  sourceTerm : Nat → Read State SourceTerm
  canonical : Nat → Read State CanonicalTerm
  checked : Nat → Read State CheckedSourceTerm

structure Registry (State : Type) where
  registered : State → ExportReplay.State
  symbols : State → ExportCodec.Symbols
  withSymbols : State → ExportCodec.Symbols → State
  sourceConclusions : State → Std.TreeMap Nat SourceTerm
  policy : State → AxiomPolicy
  decidePolicy : (state : State) → DecidablePred (policy state)
  install : (before : State) → (event : Event) → (after : ExportReplay.State) →
    @ExportReplay.apply (policy before) (decidePolicy before) (registered before) event = some after →
    List SourceTerm → Nat → State
  registered_install : ∀ before event after accepted claims refusals,
    registered (install before event after accepted claims refusals) = after

abbrev Registry.apply {State : Type} (registry : Registry State) (before : State)
    (event : Event) : Option ExportReplay.State :=
  @ExportReplay.apply (registry.policy before) (registry.decidePolicy before)
    (registry.registered before) event

structure RefusalMessages where
  definition : Nat → String
  typeDefinition : Nat → String → String
  inference : String → Nat → String

def RefusalMessages.registered : RefusalMessages where
  definition _ := "registered source event refused"
  typeDefinition _ _ := "registered source event refused"
  inference _ _ := "registered source event refused"

def RefusalMessages.selectedProfile : RefusalMessages where
  definition serial := s!"registered definition replay refused at {serial}"
  typeDefinition serial name := s!"registered type replay refused at {serial}: {name}"
  inference rule serial := s!"registered replay refused {rule} at {serial}"

abbrev Finish (State : Type) :=
  RuleRequest → String → Nat → List (Nat × Theorem) → List Nat → Array Json →
    Origin → InstanceWitnesses → Read State Unit

def claim {State : Type} (reader : TermReader State) (value : Json) : Read State (Nat × Sequent × SourceTerm) := do
  let id ← jsonNat (← field value "id")
  let hypotheses ← jsonArray (← field value "hypotheses")
  let hypotheses ← hypotheses.toList.mapM fun item => do reader.canonical (← jsonNat item)
  let conclusionId ← jsonNat (← field value "conclusion")
  let source ← reader.sourceTerm conclusionId
  let conclusion ← reader.canonical conclusionId
  let sequent ← option (Sequent.ofObjectTerms? hypotheses conclusion) s!"non-Boolean claim {id}"
  return (id,sequent,source)

def parent {State : Type} (registry : Registry State) (source : Nat) : Read State (Nat × Theorem) := do
  let state ← get
  let address ← option (registry.registered state).addresses[source]? s!"missing parent {source}"
  let fact ← option (registry.registered state).registered.cache[address]? s!"missing cached parent {source}"
  return (address,fact)

def Registry.complete {State : Type} (registry : Registry State) (before : State)
    (event : Event) (result : Option ExportReplay.State)
    (replayed : registry.apply before event = result) (claims : List SourceTerm)
    (message : String) : Read State Unit :=
  match result, replayed with
  | none, _ => fail message
  | some after, accepted =>
      modify fun _ => registry.install before event after accepted claims 0

/-- A receiver with an already computed replay result can finish the event
using that result and its equality to the registered replay. -/
theorem Registry.complete_eq {State : Type} (registry : Registry State) (before : State)
    (event : Event) (result : Option ExportReplay.State)
    (replayed : registry.apply before event = result) (claims : List SourceTerm) (message : String) :
    registry.complete before event result replayed claims message =
      registry.complete before event (registry.apply before event) rfl claims message := by
  subst result
  rfl

private theorem Registry.complete_registered {State : Type} (registry : Registry State)
    (before : State) (event : Event) (result : Option ExportReplay.State)
    (replayed : registry.apply before event = result) (claims : List SourceTerm) (message : String)
    (current after : State)
    (accepted : (registry.complete before event result replayed claims message).run current =
      .ok ((), after)) : result = some (registry.registered after) := by
  cases result with
  | none =>
      change Except.error message = Except.ok ((), after) at accepted
      contradiction
  | some result =>
      change Except.ok ((), registry.install before event result replayed claims 0) =
        Except.ok ((), after) at accepted
      obtain rfl : registry.install before event result replayed claims 0 = after :=
        congrArg Prod.snd (Except.ok.inj accepted)
      exact congrArg some (registry.registered_install before event result replayed claims 0).symm

def acceptEvent {State : Type} (registry : Registry State) (event : Event)
    (claims : List SourceTerm) (message : String) : Read State Unit := do
  let before ← get
  registry.complete before event (registry.apply before event) rfl claims message

/-- A successful installation records the actual result of registered replay. -/
theorem acceptEvent_registered {State : Type} (registry : Registry State) (event : Event)
    (claims : List SourceTerm) (message : String) (before after : State)
    (accepted : (acceptEvent registry event claims message).run before = .ok ((), after)) :
    registry.apply before event = some (registry.registered after) := by
  simp only [acceptEvent, StateT.run, get_bind_apply] at accepted
  exact registry.complete_registered before event _ rfl claims message before after accepted

theorem acceptEvent_refused {State : Type} (registry : Registry State) (event : Event)
    (claims : List SourceTerm) (message : String) (before : State)
    (refused : registry.apply before event = none) :
    (acceptEvent registry event claims message).run before = .error message := by
  simp only [acceptEvent, StateT.run, get_bind_apply]
  exact (congrFun (registry.complete_eq before event none refused claims message) before).symm

def finish {State : Type} (reader : TermReader State) (registry : Registry State)
    (refusal : RefusalMessages) : Finish State :=
  fun request rule serial inputs sourceParents outputs origin witnesses => do
    let before ← get
    let actual ← option
      (@RuleRequest.check (registry.policy before) (registry.decidePolicy before) request)
      s!"primitive check refused {rule} at {serial}"
    let claims ← outputs.toList.mapM (claim reader)
    let node : Receipt := ⟨actual,request,inputs.map (·.1),origin⟩
    let event : Event := ⟨claims.map (·.1),sourceParents,.proof node witnesses,claims.map (·.2.1)⟩
    acceptEvent registry event (claims.map (·.2.2)) (refusal.inference rule serial)

def receiveEvent {State : Type} (reader : TermReader State) (registry : Registry State)
    (checkArity : Bool) (refusal : RefusalMessages) (finishProof : Finish State)
    (source : Json) : Read State Unit := do
  let rule ← jsonText (← field source "rule")
  let serial ← jsonNat (← field source "event")
  let payload ← jsonArray (← field source "payload")
  let parents ← jsonArray (← field source "parents")
  let sourceParents ← parents.toList.mapM jsonNat
  let readBody (expectedOutputs : Option Nat) : Read State Unit := do
    let inputs ← sourceParents.mapM (parent registry)
    let witnesses := ExportReplay.instanceCertificates (registry.registered (← get)).registered.context.signature
    let outputs ← jsonArray (← field source "outputs")
    if let some count := expectedOutputs then
      unless outputs.size == count do fail s!"wrong source output arity: {rule}"
    let origin := ("indexed-hol-source-export",serial)
    if rule == "TYPE_DECLARATION" then
      let name ← jsonText (← arrayAt payload 0)
      let arity ← jsonNat (← arrayAt payload 1)
      let context := (registry.registered (← get)).registered.context
      let operator : TypeOp := .mk (sourceOperatorName (Name.global name)) .undefined
      unless context.signature.typeOperators operator == some arity do
        fail s!"primitive type is outside selected basis: {name}"
      unless outputs.isEmpty && sourceParents.isEmpty do fail "primitive declaration has proof outputs or parents"
    else if rule == "CONSTANT_DECLARATION" then
      let name ← jsonText (← arrayAt payload 0)
      let type ← reader.sourceType (← jsonNat (← arrayAt payload 1))
      let context := (registry.registered (← get)).registered.context
      let constant : Const := .mk (Name.global name) .undefined
      unless ((context.signature.constants constant).map (fun schema => schema.same type)).getD false do
        fail s!"primitive constant is outside selected basis: {name}"
      unless outputs.isEmpty && sourceParents.isEmpty do fail "primitive declaration has proof outputs or parents"
    else if rule == "DEFINITION" then
      let equation ← reader.sourceTerm (← jsonNat (← arrayAt payload 0))
      let (name, body) ← match equation with
        | .app (.app (.const constant _) (.var name _)) body =>
          if constant.same Const.equality then pure (name,body) else fail "definition head is not equality"
        | _ => fail "malformed definition equation"
      let state ← get
      let defined ← option (admitConstantInTheory (registry.registered state).registered.context witnesses name body)
        s!"constant admission refused at {serial}"
      modify fun state => registry.withSymbols state { registry.symbols state with
        constants := (name.component,defined.output.constant) :: (registry.symbols state).constants }
      let claims ← outputs.toList.mapM (claim reader)
      let event : Event := ⟨claims.map (·.1), [],
        .constant origin name body (ExportReplay.instanceCertificates defined.context.signature),
        claims.map (·.2.1)⟩
      acceptEvent registry event (claims.map (·.2.2)) (refusal.definition serial)
    else if rule == "TYPE_DEFINITION" then
      let state ← get
      let (address,existence) ← option inputs.head? "missing type existence parent"
      let parentId ← option sourceParents.head? "missing type existence address"
      let existenceSource ← option (registry.sourceConclusions state)[parentId]? "missing existence source"
      let predicate ← match existenceSource with
        | .app predicate _ => pure predicate
        | _ => fail "existence source is not an application"
      let typeName ← jsonText (← arrayAt payload 0)
      let absName ← jsonText (← arrayAt payload 1)
      let repName ← jsonText (← arrayAt payload 2)
      let request : TypeOperatorDefinitionRequest :=
        ⟨sourceOperatorName (Name.global typeName), Name.global absName, Name.global repName,
         sortedParameters predicate, predicate, existence⟩
      let defined ← option (admitSourceTypeInTheory (registry.registered state).registered.context witnesses request)
        s!"type admission refused at {serial}: {typeName}"
      modify fun state => registry.withSymbols state
        ⟨(typeName,defined.core.output.typeOperator) :: (registry.symbols state).operators,
         (absName,defined.core.output.abstractionConstant) ::
         (repName,defined.core.output.representationConstant) :: (registry.symbols state).constants⟩
      let claims ← outputs.toList.mapM (claim reader)
      let event : Event := ⟨claims.map (·.1), sourceParents,
        .typeDefinition origin request address (ExportReplay.instanceCertificates defined.context.signature),
        claims.map (·.2.1)⟩
      let state ← get
      let wrongClaim : Sequent := ⟨∅,CanonicalTerm.free ⟨Name.global "forged_type_definition_conclusion",Ty.bool⟩⟩
      let changedClaim : Event := { event with claims := wrongClaim :: event.claims.drop 1 }
      unless (registry.apply state changedClaim).isNone do
        fail s!"forged type conclusion accepted: {typeName}"
      let missingParent : Event := { event with sourceParents := [] }
      unless (registry.apply state missingParent).isNone do
        fail s!"missing type existence parent accepted: {typeName}"
      match accepted : registry.apply state event with
      | none => fail (refusal.typeDefinition serial typeName)
      | some after =>
          unless (admitSourceTypeInTheory after.registered.context
              (ExportReplay.instanceCertificates after.registered.context.signature) request).isNone do
            fail s!"repeated type declaration accepted: {typeName}"
          modify fun _ => registry.install state event after accepted (claims.map (·.2.2)) 3
    else
      let request ← match rule with
        | "REFL" => pure (.inference (.refl (← reader.canonical (← jsonNat (← arrayAt payload 0)))))
        | "BETA" => pure (.inference (.beta (← reader.checked (← jsonNat (← arrayAt payload 0)))))
        | "ASSUME" => pure (.inference (.assume (← reader.canonical (← jsonNat (← arrayAt payload 0)))))
        | "TRANS" | "MK_COMB" | "EQ_MP" | "DEDUCT_ANTISYM_RULE" => do
          let first ← option inputs[0]? "missing left premise"
          let second ← option inputs[1]? "missing right premise"
          let inference := if rule == "TRANS" then InferenceRequest.trans first.2 second.2
            else if rule == "MK_COMB" then .mkComb first.2 second.2
            else if rule == "EQ_MP" then .eqMp first.2 second.2
            else .deductAntisym first.2 second.2
          pure (.inference inference)
        | "ABS" => do
          let premise ← option inputs.head? "missing abstraction premise"
          match ← reader.sourceTerm (← jsonNat (← arrayAt payload 0)) with
          | .var name type => pure (.inference (.abs ⟨name,type⟩ premise.2))
          | _ => fail "bad abstraction binder"
        | "INST_TYPE" => do
          let premise ← option inputs.head? "missing type substitution premise"
          let entries ← payload.toList.mapM fun entry => do
            let row ← jsonArray entry
            pure (← reader.sourceType (← jsonNat (← arrayAt row 0)), ← reader.sourceType (← jsonNat (← arrayAt row 1)))
          pure (.inference (.instType entries premise.2))
        | "INST" => do
          let premise ← option inputs.head? "missing term substitution premise"
          let entries ← payload.toList.mapM fun entry => do
            let row ← jsonArray entry
            pure (← reader.checked (← jsonNat (← arrayAt row 0)), ← reader.sourceTerm (← jsonNat (← arrayAt row 1)))
          pure (.inference (.inst entries premise.2))
        | "AXIOM" => do
          let conclusion ← reader.canonical (← jsonNat (← arrayAt payload 0))
          let sequent : Sequent := ⟨∅,conclusion⟩
          pure (RuleRequest.axiom sequent)
        | _ => fail s!"unsupported event {rule} at {serial}"
      finishProof request rule serial inputs sourceParents outputs origin witnesses
  if checkArity then
    let arity ← match rule with
      | "TYPE_DECLARATION" | "CONSTANT_DECLARATION" => pure (2,0,0)
      | "DEFINITION" => pure (1,0,1)
      | "TYPE_DEFINITION" => pure (3,1,2)
      | "REFL" | "BETA" | "ASSUME" | "AXIOM" => pure (1,0,1)
      | "TRANS" | "MK_COMB" | "EQ_MP" | "DEDUCT_ANTISYM_RULE" => pure (0,2,1)
      | "ABS" => pure (1,1,1)
      | "INST" | "INST_TYPE" => do
          for entry in payload do
            unless (← jsonArray entry).size == 2 do fail "wrong substitution row arity"
          pure (payload.size,1,1)
      | _ => fail s!"unsupported source rule {rule}"
    unless payload.size == arity.1 && parents.size == arity.2.1 do
      fail s!"wrong source payload or premise arity: {rule}"
    readBody (some arity.2.2)
  else readBody none

end Mettapedia.Languages.HOLLight.NumberedReplay
