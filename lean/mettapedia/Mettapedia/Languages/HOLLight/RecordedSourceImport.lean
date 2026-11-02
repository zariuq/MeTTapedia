import Mettapedia.Languages.HOLLight.SourceProfile
import Lean.Data.Json
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight Lean
open DefinitionAdapters SignatureFormation ProofExecution ExportReplay

/-!
# Numbered source-record intake

This untrusted source adapter expands numbered type and term nodes into the
existing source syntax. Every proof and definition is checked by the registered
HOL receiver. A separately supplied source profile fixes the primitive basis
and permitted axioms; the proof document cannot extend that policy.

The partial functions decode finite input graphs and reject non-earlier syntax
edges. They add no theorem or checker authority. Successful runs qualify the
selected inputs and receiver artifact, with no implementation-refinement claim.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RecordedSourceImport

structure Input where
  types : Array Json
  terms : Array Json
  events : Array Json

structure Reading where
  input : Input
  types : Array (Option Ty)
  terms : Array (Option SourceTerm)
  registered : ExportReplay.State
  symbols : ExportCodec.Symbols
  sourceConclusions : Std.TreeMap Nat SourceTerm := {}
  axioms : List Sequent := []
  refusalChecks : Nat := 0

abbrev Read := StateT Reading (Except String)

def fail {A : Type} (message : String) : Read A := throw message

def jsonNat (value : Json) : Read Nat :=
  match value.getNat? with
  | .ok value => pure value
  | .error error => fail error

def jsonText (value : Json) : Read String :=
  match value.getStr? with
  | .ok value => pure value
  | .error error => fail error

def jsonArray (value : Json) : Read (Array Json) :=
  match value.getArr? with
  | .ok value => pure value
  | .error error => fail error

def field (value : Json) (key : String) : Read Json :=
  match value.getObjVal? key with
  | .ok value => pure value
  | .error error => fail error

def arrayAt (values : Array Json) (index : Nat) : Read Json :=
  match values[index]? with
  | some value => pure value
  | none => fail s!"missing array position {index}"

def option {A : Type} (value : Option A) (message : String) : Read A :=
  match value with
  | some value => pure value
  | none => fail message

partial def sourceType (index : Nat) : Read Ty := do
  let state ← get
  if let some cached := state.types[index]?.join then return cached
  let row ← jsonArray (← option state.input.types[index]? s!"missing type {index}")
  let tag ← jsonText (← arrayAt row 0)
  unless row.size == (if tag == "var" then 2 else 3) do fail "wrong type row arity"
  let name ← jsonText (← arrayAt row 1)
  let type ← if tag == "var" then pure (Ty.var (Name.global name)) else do
    unless tag == "op" do fail s!"bad type tag {tag}"
    let operator ← option (List.lookup name state.symbols.operators) s!"unregistered type {name}"
    let arguments ← jsonArray (← arrayAt row 2)
    let arguments ← arguments.toList.mapM fun argument => do
      let child ← jsonNat argument
      unless child < index do fail s!"non-earlier type edge {index}->{child}"
      sourceType child
    pure (.op operator arguments)
  modify fun (state : Reading) => { state with types := state.types.set! index (some type) }
  return type

partial def sourceTerm (index : Nat) : Read SourceTerm := do
  let state ← get
  if let some cached := state.terms[index]?.join then return cached
  let row ← jsonArray (← option state.input.terms[index]? s!"missing term {index}")
  let tag ← jsonText (← arrayAt row 0)
  unless row.size == 3 do fail "wrong term row arity"
  let term ← match tag with
    | "var" | "const" => do
      let name ← jsonText (← arrayAt row 1)
      let type ← sourceType (← jsonNat (← arrayAt row 2))
      if tag == "var" then pure (.var (Name.global name) type) else do
        let constant ← option (List.lookup name state.symbols.constants) s!"unregistered constant {name}"
        pure (.const constant type)
    | "app" => do
      let left ← jsonNat (← arrayAt row 1)
      let right ← jsonNat (← arrayAt row 2)
      unless left < index && right < index do fail s!"non-earlier application edge {index}"
      return .app (← sourceTerm left) (← sourceTerm right)
    | "abs" => do
      let binder ← jsonNat (← arrayAt row 1)
      let body ← jsonNat (← arrayAt row 2)
      unless binder < index && body < index do fail s!"non-earlier abstraction edge {index}"
      match ← sourceTerm binder with
      | .var name type => return .abs name type (← sourceTerm body)
      | _ => fail s!"non-variable binder arrayAt {index}"
    | _ => fail s!"bad term tag {tag}"
  modify fun (state : Reading) => { state with terms := state.terms.set! index (some term) }
  return term

def canonical (index : Nat) : Read CanonicalTerm := do
  option (← sourceTerm index).check s!"ill-typed term {index}"

def checked (index : Nat) : Read CheckedSourceTerm := do
  option (ExportReplay.checkedSource? (← sourceTerm index)) s!"ill-typed source {index}"

def claim (value : Json) : Read (Nat × Sequent × SourceTerm) := do
  let id ← jsonNat (← field value "id")
  let hypotheses ← jsonArray (← field value "hypotheses")
  let hypotheses ← hypotheses.toList.mapM fun item => do canonical (← jsonNat item)
  let conclusionId ← jsonNat (← field value "conclusion")
  let source ← sourceTerm conclusionId
  let conclusion ← canonical conclusionId
  let sequent ← option (Sequent.ofObjectTerms? hypotheses conclusion) s!"non-Boolean claim {id}"
  return (id,sequent,source)

def parent (source : Nat) : Read (Nat × Theorem) := do
  let state ← get
  let address ← option state.registered.addresses[source]? s!"missing parent {source}"
  let fact ← option state.registered.registered.cache[address]? s!"missing cached parent {source}"
  return (address,fact)

def finitePolicy (allowed : List Sequent) : AxiomPolicy := fun sequent => sequent ∈ allowed
instance (allowed : List Sequent) : DecidablePred (finitePolicy allowed) :=
  fun _ => inferInstanceAs (Decidable (_ ∈ allowed))

def receiveEvent (source : Json) : Read Unit := do
  let rule ← jsonText (← field source "rule")
  let serial ← jsonNat (← field source "event")
  let payload ← jsonArray (← field source "payload")
  let parents ← jsonArray (← field source "parents")
  let sourceParents ← parents.toList.mapM jsonNat
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
  let inputs ← sourceParents.mapM parent
  let witnesses := ExportReplay.instanceCertificates (← get).registered.registered.context.signature
  let outputs ← jsonArray (← field source "outputs")
  unless outputs.size == arity.2.2 do fail s!"wrong source output arity: {rule}"
  let origin := ("indexed-hol-source-export",serial)
  if rule == "TYPE_DECLARATION" then
    let name ← jsonText (← arrayAt payload 0)
    let arity ← jsonNat (← arrayAt payload 1)
    let context := (← get).registered.registered.context
    let operator : TypeOp := .mk (sourceOperatorName (Name.global name)) .undefined
    unless context.signature.typeOperators operator == some arity do
      fail s!"primitive type is outside selected basis: {name}"
    unless outputs.isEmpty && sourceParents.isEmpty do fail "primitive declaration has proof outputs or parents"
  else if rule == "CONSTANT_DECLARATION" then
    let name ← jsonText (← arrayAt payload 0)
    let type ← sourceType (← jsonNat (← arrayAt payload 1))
    let context := (← get).registered.registered.context
    let constant : Const := .mk (Name.global name) .undefined
    unless ((context.signature.constants constant).map (fun schema => schema.same type)).getD false do
      fail s!"primitive constant is outside selected basis: {name}"
    unless outputs.isEmpty && sourceParents.isEmpty do fail "primitive declaration has proof outputs or parents"
  else if rule == "DEFINITION" then
    let equation ← sourceTerm (← jsonNat (← arrayAt payload 0))
    let (name, body) ← match equation with
      | .app (.app (.const constant _) (.var name _)) body =>
        if constant.same Const.equality then pure (name,body) else fail "definition head is not equality"
      | _ => fail "malformed definition equation"
    let state ← get
    let defined ← option (admitConstantInTheory state.registered.registered.context witnesses name body)
      s!"constant admission refused at {serial}"
    modify fun (state : Reading) => { state with symbols := { state.symbols with
      constants := (name.component,defined.output.constant) :: state.symbols.constants } }
    let claims ← outputs.toList.mapM claim
    let event : Event := ⟨claims.map (·.1), [],
      .constant origin name body (ExportReplay.instanceCertificates defined.context.signature),
      claims.map (·.2.1)⟩
    let state ← get
    let after ← option (ExportReplay.apply (finitePolicy state.axioms) state.registered event)
      s!"registered definition replay refused at {serial}"
    modify fun _ => { state with
      registered := after
      sourceConclusions := ExportCodec.addConclusions state.sourceConclusions event.sourceIds (claims.map (·.2.2)) }
  else if rule == "TYPE_DEFINITION" then
    let state ← get
    let (address,existence) ← option inputs.head? "missing type existence parent"
    let parentId ← option sourceParents.head? "missing type existence address"
    let existenceSource ← option state.sourceConclusions[parentId]? "missing existence source"
    let predicate ← match existenceSource with
      | .app predicate _ => pure predicate
      | _ => fail "existence source is not an application"
    let typeName ← jsonText (← arrayAt payload 0)
    let absName ← jsonText (← arrayAt payload 1)
    let repName ← jsonText (← arrayAt payload 2)
    let request : TypeOperatorDefinitionRequest :=
      ⟨sourceOperatorName (Name.global typeName), Name.global absName, Name.global repName,
       sortedParameters predicate, predicate, existence⟩
    let defined ← option (admitSourceTypeInTheory state.registered.registered.context witnesses request)
      s!"type admission refused at {serial}: {typeName}"
    modify fun (state : Reading) => { state with symbols :=
      ⟨(typeName,defined.core.output.typeOperator) :: state.symbols.operators,
       (absName,defined.core.output.abstractionConstant) ::
       (repName,defined.core.output.representationConstant) :: state.symbols.constants⟩ }
    let claims ← outputs.toList.mapM claim
    let event : Event := ⟨claims.map (·.1), sourceParents,
      .typeDefinition origin request address (ExportReplay.instanceCertificates defined.context.signature),
      claims.map (·.2.1)⟩
    let state ← get
    let wrongClaim : Sequent := ⟨∅,CanonicalTerm.free ⟨Name.global "forged_type_definition_conclusion",Ty.bool⟩⟩
    let changedClaim : Event := { event with claims := wrongClaim :: event.claims.drop 1 }
    unless (ExportReplay.apply (finitePolicy state.axioms) state.registered changedClaim).isNone do
      fail s!"forged type conclusion accepted: {typeName}"
    let missingParent : Event := { event with sourceParents := [] }
    unless (ExportReplay.apply (finitePolicy state.axioms) state.registered missingParent).isNone do
      fail s!"missing type existence parent accepted: {typeName}"
    let after ← option (ExportReplay.apply (finitePolicy state.axioms) state.registered event)
      s!"registered type replay refused at {serial}: {typeName}"
    unless (admitSourceTypeInTheory after.registered.context
        (ExportReplay.instanceCertificates after.registered.context.signature) request).isNone do
      fail s!"repeated type declaration accepted: {typeName}"
    modify fun _ => { state with
      refusalChecks := state.refusalChecks + 3
      registered := after
      sourceConclusions := ExportCodec.addConclusions state.sourceConclusions event.sourceIds (claims.map (·.2.2)) }
  else
    let request ← match rule with
      | "REFL" => pure (.inference (.refl (← canonical (← jsonNat (← arrayAt payload 0)))))
      | "BETA" => pure (.inference (.beta (← checked (← jsonNat (← arrayAt payload 0)))))
      | "ASSUME" => pure (.inference (.assume (← canonical (← jsonNat (← arrayAt payload 0)))))
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
        match ← sourceTerm (← jsonNat (← arrayAt payload 0)) with
        | .var name type => pure (.inference (.abs ⟨name,type⟩ premise.2))
        | _ => fail "bad abstraction binder"
      | "INST_TYPE" => do
        let premise ← option inputs.head? "missing type substitution premise"
        let entries ← payload.toList.mapM fun entry => do
          let row ← jsonArray entry
          pure (← sourceType (← jsonNat (← arrayAt row 0)), ← sourceType (← jsonNat (← arrayAt row 1)))
        pure (.inference (.instType entries premise.2))
      | "INST" => do
        let premise ← option inputs.head? "missing term substitution premise"
        let entries ← payload.toList.mapM fun entry => do
          let row ← jsonArray entry
          pure (← checked (← jsonNat (← arrayAt row 0)), ← sourceTerm (← jsonNat (← arrayAt row 1)))
        pure (.inference (.inst entries premise.2))
      | "AXIOM" => do
        let conclusion ← canonical (← jsonNat (← arrayAt payload 0))
        let sequent : Sequent := ⟨∅,conclusion⟩
        pure (RuleRequest.axiom sequent)
      | _ => fail s!"unsupported event {rule} at {serial}"
    let state ← get
    let actual ← option (request.check (finitePolicy state.axioms)) s!"primitive check refused {rule} at {serial}"
    let claims ← outputs.toList.mapM claim
    let node : Receipt := ⟨actual,request,inputs.map (·.1),origin⟩
    let event : Event := ⟨claims.map (·.1),sourceParents,.proof node witnesses,claims.map (·.2.1)⟩
    let state ← get
    let after ← option (ExportReplay.apply (finitePolicy state.axioms) state.registered event)
      s!"registered replay refused {rule} at {serial}"
    modify fun _ => { state with
      registered := after
      sourceConclusions := ExportCodec.addConclusions state.sourceConclusions event.sourceIds (claims.map (·.2.2)) }

end Mettapedia.Languages.HOLLight.RecordedSourceImport
namespace Mettapedia.Languages.HOLLight.RecordedSourceImport
def loadSource (path profilePath : String) (limit : Option Nat := none) : IO Reading := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let types ← IO.ofExcept ((json.getObjVal? "types").bind Json.getArr?)
  let terms ← IO.ofExcept ((json.getObjVal? "terms").bind Json.getArr?)
  let allEvents ← IO.ofExcept ((json.getObjVal? "events").bind Json.getArr?)
  if let some requested := limit then
    unless requested ≤ allEvents.size do throw (IO.userError "source prefix exceeds the supplied history")
  let events := allEvents.extract 0 (limit.getD allEvents.size)
  let input : Input := ⟨types, terms, events⟩
  let profileJson ← IO.ofExcept (Json.parse (← IO.FS.readFile profilePath))
  let some profile := SourceProfile.load? SourceProfile.primitiveBasis profileJson |
    throw (IO.userError "selected source profile refused")
  let mut state : Reading := ⟨input, Array.replicate types.size none, Array.replicate terms.size none,
    profile.initial.received, profile.initial.symbols, {}, profile.commitments, 0⟩
  let mut processed := 0
  for event in events do
    let (_, after) ← IO.ofExcept ((receiveEvent event).run state)
    state := after
    processed := processed + 1
    if processed % 8192 == 0 then
      (← IO.getStderr).putStrLn s!"source events {processed}/{events.size}"
      (← IO.getStderr).flush
  (← IO.getStderr).putStrLn s!"received {events.size} events; {state.registered.registered.cache.size} theorems"
  return state
end Mettapedia.Languages.HOLLight.RecordedSourceImport
