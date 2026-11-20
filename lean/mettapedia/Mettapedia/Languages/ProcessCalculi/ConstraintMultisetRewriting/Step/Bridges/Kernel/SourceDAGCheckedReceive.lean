import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CheckedRequestIngress

/-! Numbered-source reception with one checked inference result reused.
The complete parser is proved equal to SourceDAGReceive.receiveEvent. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGCheckedReceive

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open DefinitionAdapters SignatureFormation ProofExecution ExportReplay SourceDAGReceive

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
    acceptEvent event (claims.map (·.2.2))
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
    unless (ExportReplay.apply SourceProfileModels.policy state.registered changedClaim).isNone do
      fail s!"forged type conclusion accepted: {typeName}"
    let missingParent : Event := { event with sourceParents := [] }
    unless (ExportReplay.apply SourceProfileModels.policy state.registered missingParent).isNone do
      fail s!"missing type existence parent accepted: {typeName}"
    acceptEvent event (claims.map (·.2.2))
    let after ← get
    unless (admitSourceTypeInTheory after.registered.registered.context
        (ExportReplay.instanceCertificates after.registered.registered.context.signature) request).isNone do
      fail s!"repeated type declaration accepted: {typeName}"
    modify fun state => { state with refusalChecks := state.refusalChecks + 3 }
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
    CheckedRequestIngress.finish request rule serial inputs sourceParents outputs origin witnesses


def start (input : Input) : Reading where
  input := input
  types := Array.replicate input.types.size none
  terms := Array.replicate input.terms.size none
  registered := SourceProfile.primitiveBasis.received
  symbols := SourceProfile.primitiveBasis.symbols
  history := ExportReceiptHistory.empty_history SourceProfile.primitiveContext SourceProfileModels.policy

theorem registered_history (reading : Reading) :
    Registered.replayFrom SourceProfileModels.policy (Registered.empty SourceProfile.primitiveContext)
      (reading.registered.receipts.toList.map ExportReplay.Event.command) = some reading.registered.registered :=
  ExportReceiptHistory.registered_history SourceProfile.primitiveContext SourceProfileModels.policy
    reading.registered reading.history


/-- Reusing the checked inference output changes nothing observable: `finish` is
`originalFinish`, which is by definition the inline tail of `SourceDAGReceive.receiveEvent`. -/
theorem receiveEvent_eq (source : Json) :
    receiveEvent source = SourceDAGReceive.receiveEvent source := by
  unfold receiveEvent SourceDAGReceive.receiveEvent
  simp only [CheckedRequestIngress.finish_eq]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGCheckedReceive
