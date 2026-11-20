import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceMetadata
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceProofMetadata

/-!
# Total numbered declaration reception

The raw constant-definition equation has a variable on its left. Its body is
admitted before the new constant is used to resolve the independent output
claim. Type declarations retain their actual parent and named source
application, then resolve both ordered claims with the new symbols.

These operations use the total numbered reference queries and the existing
registered checker. Metadata coherence and literal-file identity are separate
licences; neither is manufactured by declaration admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceDeclarations

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay

abbrev Reading := SourceDAGReceive.Reading

abbrev currentContext (before : Reading) : TheoryContext := before.registered.registered.context

abbrev currentInstances (before : Reading) : InstanceWitnesses :=
  ExportReplay.instanceCertificates (currentContext before).signature

def typeRequest (typeName absName repName : String) (predicate : SourceTerm)
    (existence : Theorem) : TypeOperatorDefinitionRequest :=
  ⟨sourceOperatorName (.global typeName), .global absName, .global repName,
    sortedParameters predicate, predicate, existence⟩

structure ConstantAdmission (before : Reading) where
  name : Mettapedia.Languages.OpenTheory.Name
  body : SourceTerm
  result : ContextConstantDefinitionResult
  admitted : admitConstantInTheory (currentContext before) (currentInstances before) name body = some result

structure TypeAdmission (before : Reading) where
  parentId : Nat
  address : Nat
  existence : Theorem
  predicate : SourceTerm
  sourceWitness : SourceTerm
  typeName : String
  absName : String
  repName : String
  result : SourceTypeDefinitionResult
  parentAt : NumberedSourceProofs.parent? before parentId = some (address, existence)
  sourceAt : before.sourceConclusions[parentId]? = some (.app predicate sourceWitness)
  admitted : admitSourceTypeInTheory (currentContext before) (currentInstances before)
    (typeRequest typeName absName repName predicate existence) = some result

def TypeAdmission.request {before : Reading} (data : TypeAdmission before) : TypeOperatorDefinitionRequest :=
  typeRequest data.typeName data.absName data.repName data.predicate data.existence

inductive Admission (before : Reading) where
  | constant (data : ConstantAdmission before)
  | typeDefinition (data : TypeAdmission before)

def Admission.typeData? {before : Reading} : Admission before → Option (TypeAdmission before)
  | .constant _ => none
  | .typeDefinition data => some data

def Admission.context {before : Reading} : Admission before → TheoryContext
  | .constant data => data.result.context
  | .typeDefinition data => data.result.context

def Admission.outputs {before : Reading} : Admission before → List Theorem
  | .constant data => [data.result.output.definitionTheorem]
  | .typeDefinition data => [data.result.output.abstractionRepresentationTheorem,
      data.result.output.representationAbstractionTheorem]

def Admission.symbols {before : Reading} : Admission before → ExportCodec.Symbols
  | .constant data => { before.symbols with
      constants := (data.name.component, data.result.output.constant) :: before.symbols.constants }
  | .typeDefinition data =>
      ⟨(data.typeName, data.result.core.output.typeOperator) :: before.symbols.operators,
        (data.absName, data.result.core.output.abstractionConstant) ::
        (data.repName, data.result.core.output.representationConstant) :: before.symbols.constants⟩

def Admission.command {before : Reading} (serial : Nat) : Admission before → Registered.Command
  | .constant data => .constant ("indexed-hol-source-export", serial) data.name data.body
      (ExportReplay.instanceCertificates data.result.context.signature)
  | .typeDefinition data => .typeDefinition ("indexed-hol-source-export", serial) data.request data.address
      (ExportReplay.instanceCertificates data.result.context.signature)

def Admission.parents {before : Reading} : Admission before → List Nat
  | .constant _ => []
  | .typeDefinition data => [data.parentId]

def Admission.refusalBump {before : Reading} : Admission before → Nat
  | .constant _ => 0
  | .typeDefinition _ => 3

structure Prepared (before : Reading) (raw : Json) where
  header : NumberedSourceProofs.Header
  parsed : NumberedSourceProofs.header? raw = some header
  admission : Admission before
  claims : List NumberedSourceProofs.Claim
  claimChecks : List.Forall₂ (fun source sequent => source.check = some sequent.concl)
    (claims.map (·.source)) (claims.map (·.sequent))

def Prepared.symbols {before : Reading} {raw : Json} (prepared : Prepared before raw) : ExportCodec.Symbols :=
  prepared.admission.symbols

def Prepared.event {before : Reading} {raw : Json} (prepared : Prepared before raw) : Event :=
  ⟨prepared.claims.map (·.id), prepared.admission.parents,
    prepared.admission.command prepared.header.serial, prepared.claims.map (·.sequent)⟩

def Prepared.sources {before : Reading} {raw : Json} (prepared : Prepared before raw) : List SourceTerm :=
  prepared.claims.map (·.source)

/-- The returned candidate retains actual admission. Consumers also retain
the successful preparation equation, which binds it to this input and state. -/
def prepare? (before : Reading) (raw : Json) : Option (Prepared before raw) := do
  match parsed : NumberedSourceProofs.header? raw with
  | none => none
  | some header =>
      match header.rule, header.payload, header.parents, header.outputs with
      | "DEFINITION", [equationIndex], [], [claim] => do
          let equation ← NumberedSourceProofs.sourceTerm? before (← ExportCodec.natural? equationIndex)
          match equation with
          | .app (.app (.const constant _) (.var name _)) body =>
              if constant.same Const.equality then
                match admitted : admitConstantInTheory (currentContext before) (currentInstances before) name body with
                | none => none
                | some result => do
                    let admission : Admission before := .constant ⟨name, body, result, admitted⟩
                    match claimAt : NumberedSourceProofs.claim? { before with symbols := admission.symbols } claim with
                    | none => none
                    | some claim => pure ⟨header, parsed, admission, [claim],
                        .cons (NumberedSourceProofMetadata.claim_checked _ _ _ claimAt) .nil⟩
              else none
          | _ => none
      | "TYPE_DEFINITION", [typeName, absName, repName], [parentId], [absClaim, repClaim] => do
          match parentAt : NumberedSourceProofs.parent? before parentId with
          | none => none
          | some (address, existence) =>
              match sourceAt : before.sourceConclusions[parentId]? with
              | some (.app predicate sourceWitness) => do
                  let typeName ← ExportCodec.string? typeName
                  let absName ← ExportCodec.string? absName
                  let repName ← ExportCodec.string? repName
                  match admitted : admitSourceTypeInTheory (currentContext before) (currentInstances before)
                      (typeRequest typeName absName repName predicate existence) with
                  | none => none
                  | some result => do
                      let data : TypeAdmission before :=
                        ⟨parentId, address, existence, predicate, sourceWitness, typeName, absName, repName,
                          result, parentAt, sourceAt, admitted⟩
                      let admission : Admission before := .typeDefinition data
                      let decoding : Reading := { before with symbols := admission.symbols }
                      match absAt : NumberedSourceProofs.claim? decoding absClaim with
                      | none => none
                      | some absClaim =>
                          match repAt : NumberedSourceProofs.claim? decoding repClaim with
                          | none => none
                          | some repClaim => pure ⟨header, parsed, admission, [absClaim, repClaim],
                              .cons (NumberedSourceProofMetadata.claim_checked _ _ _ absAt)
                                (.cons (NumberedSourceProofMetadata.claim_checked _ _ _ repAt) .nil)⟩
              | _ => none
      | _, _, _, _ => none

def preChecks {before : Reading} {raw : Json} (prepared : Prepared before raw) : Bool :=
  match prepared.admission with
  | .constant _ => true
  | .typeDefinition _ =>
      let wrong : Sequent := ⟨∅, CanonicalTerm.free ⟨.global "forged_type_definition_conclusion", Ty.bool⟩⟩
      let changed : Event := { prepared.event with claims := wrong :: prepared.event.claims.drop 1 }
      let missing : Event := { prepared.event with sourceParents := [] }
      (ExportReplay.apply SourceProfileModels.policy before.registered changed).isNone &&
        (ExportReplay.apply SourceProfileModels.policy before.registered missing).isNone

def postChecks {before : Reading} {raw : Json} (prepared : Prepared before raw)
    (after : Reading) : Bool :=
  match prepared.admission with
  | .constant _ => true
  | .typeDefinition data =>
      (admitSourceTypeInTheory (currentContext after) (currentInstances after) data.request).isNone

def applyPrepared? {before : Reading} {raw : Json} (prepared : Prepared before raw) : Option Reading :=
  match accepted : ExportReplay.apply SourceProfileModels.policy before.registered prepared.event with
  | none => none
  | some after => some { before with
      registered := after
      symbols := prepared.symbols
      sourceConclusions := ExportCodec.addConclusions before.sourceConclusions prepared.event.sourceIds prepared.sources
      history := ExportReceiptHistory.apply_history SourceProfile.primitiveContext
        SourceProfileModels.policy before.history accepted
      refusalChecks := before.refusalChecks + prepared.admission.refusalBump }

def receive? (before : Reading) (raw : Json) : Option Reading := do
  let prepared ← prepare? before raw
  if preChecks prepared then
    let after ← applyPrepared? prepared
    if postChecks prepared after then some after else none
  else none

theorem applyPrepared_checked {before after : Reading} {raw : Json} (prepared : Prepared before raw)
    (accepted : applyPrepared? prepared = some after) :
    ExportReplay.apply SourceProfileModels.policy before.registered prepared.event = some after.registered ∧
      Registered.apply SourceProfileModels.policy before.registered.registered prepared.event.command =
        some after.registered.registered ∧
      after.input = before.input ∧ after.symbols = prepared.symbols ∧
      after.sourceConclusions = ExportCodec.addConclusions before.sourceConclusions prepared.event.sourceIds prepared.sources ∧
      after.refusalChecks = before.refusalChecks + prepared.admission.refusalBump := by
  unfold applyPrepared? at accepted
  split at accepted
  · cases accepted
  · rename_i state checked
    have equal := Option.some.inj accepted
    subst after
    exact ⟨checked, (ExportReplay.apply_checked SourceProfileModels.policy checked).1,
      rfl, rfl, rfl, rfl⟩

theorem receive_checked (before after : Reading) (raw : Json)
    (received : receive? before raw = some after) :
    ∃ prepared : Prepared before raw,
      prepare? before raw = some prepared ∧
      ExportReplay.apply SourceProfileModels.policy before.registered prepared.event = some after.registered ∧
      Registered.apply SourceProfileModels.policy before.registered.registered prepared.event.command =
        some after.registered.registered ∧
      after.input = before.input ∧ after.symbols = prepared.symbols ∧
      after.sourceConclusions = ExportCodec.addConclusions before.sourceConclusions prepared.event.sourceIds prepared.sources ∧
      after.refusalChecks = before.refusalChecks + prepared.admission.refusalBump := by
  unfold receive? at received
  cases preparedAt : prepare? before raw with
  | none => simp only [preparedAt, bind, Option.bind] at received; cases received
  | some prepared =>
      simp only [preparedAt, bind, Option.bind] at received
      split at received
      · cases applied : applyPrepared? prepared with
        | none => simp only [applied] at received; cases received
        | some state =>
            simp only [applied] at received
            split at received
            · have equal := Option.some.inj received
              subst after
              exact ⟨prepared, rfl, applyPrepared_checked prepared applied⟩
            · cases received
      · cases received

/-- The checker may propose instance certificates in the extended signature;
successful rechecking still returns the exact initially admitted result. -/
theorem Admission.checked_output {before : Reading} (admission : Admission before)
    (serial : Nat) (output : Registered.Output)
    (checked : (admission.command serial).check SourceProfileModels.policy
      (currentContext before) before.registered.registered.cache = some output) :
    output.context = admission.context ∧ output.theorems = admission.outputs := by
  cases admission with
  | constant data =>
      cases admitted : admitConstantInTheory (currentContext before)
          (ExportReplay.instanceCertificates data.result.context.signature) data.name data.body with
      | none => simp [Admission.command, Registered.Command.check, admitted] at checked
      | some result =>
          simp only [Admission.command, Registered.Command.check, admitted, bind, Option.bind] at checked
          split at checked
          · have same := admitConstantInTheory_unique data.admitted admitted
            subst result
            have equal := Option.some.inj checked
            cases equal
            exact ⟨rfl,rfl⟩
          · cases checked
  | typeDefinition data =>
      cases found : before.registered.registered.cache[data.address]? with
      | none => simp [Admission.command, Registered.Command.check, found] at checked
      | some existence =>
          simp only [Admission.command, Registered.Command.check, found, bind, Option.bind] at checked
          split at checked
          · cases admitted : admitSourceTypeInTheory (currentContext before)
                (ExportReplay.instanceCertificates data.result.context.signature) data.request with
            | none => simp [admitted] at checked
            | some result =>
                simp only [admitted] at checked
                split at checked
                · have same := admitSourceTypeInTheory_unique (currentContext before) (currentInstances before)
                    (ExportReplay.instanceCertificates data.result.context.signature) data.request data.result result
                    data.admitted admitted
                  subst result
                  have equal := Option.some.inj checked
                  cases equal
                  exact ⟨rfl,rfl⟩
                · cases checked
          · cases checked

theorem receive_result (before after : Reading) (raw : Json)
    (received : receive? before raw = some after) :
    ∃ prepared : Prepared before raw, prepare? before raw = some prepared ∧
      currentContext after = prepared.admission.context ∧
      after.registered.registered.cache = before.registered.registered.cache ++ prepared.admission.outputs.toArray ∧
      after.registered.registered.receipts = before.registered.registered.receipts.push
        ⟨prepared.event.command, prepared.admission.outputs⟩ := by
  obtain ⟨prepared,preparedAt,_,registered,_,_,_,_⟩ := receive_checked before after raw received
  obtain ⟨output,checked,contextEq,cacheEq,receiptsEq⟩ :=
    Registered.apply_result SourceProfileModels.policy registered
  have outputShape := Admission.checked_output prepared.admission prepared.header.serial output checked
  exact ⟨prepared,preparedAt,contextEq.trans outputShape.1,
    by simpa only [outputShape.2] using cacheEq,
    by simpa only [outputShape.2] using receiptsEq⟩

abbrev ConclusionsChecked (reading : Reading) : Prop :=
  NumberedSourceMetadata.ConclusionsChecked reading.registered reading.sourceConclusions

theorem receive_preserves_conclusions (before after : Reading) (raw : Json)
    (coherent : ConclusionsChecked before) (received : receive? before raw = some after) :
    ConclusionsChecked after := by
  obtain ⟨prepared,_,accepted,_,_,_,sourcesEq,_⟩ := receive_checked before after raw received
  have sourceChecks : List.Forall₂ (fun source sequent => source.check = some sequent.concl)
      prepared.sources prepared.event.claims := prepared.claimChecks
  have preserved := NumberedSourceMetadata.apply_preserves_conclusions SourceProfileModels.policy
    before.registered after.registered prepared.event before.sourceConclusions prepared.sources
    coherent sourceChecks accepted
  change NumberedSourceMetadata.ConclusionsChecked after.registered after.sourceConclusions
  rw [sourcesEq]
  exact preserved

theorem TypeAdmission.source_checked {before : Reading} (data : TypeAdmission before)
    (coherent : ConclusionsChecked before) :
    (SourceTerm.app data.predicate data.sourceWitness).check = some data.existence.sequent.concl := by
  obtain ⟨position,fact,addressAt,factAt,sourceChecked⟩ := coherent _ _ data.sourceAt
  have recovered : NumberedSourceProofs.parent? before data.parentId = some (position,fact) := by
    simp [NumberedSourceProofs.parent?,addressAt,factAt]
  have equal := Option.some.inj (recovered.symm.trans data.parentAt)
  have factEqual := congrArg Prod.snd equal
  change fact = data.existence at factEqual
  rw [factEqual] at sourceChecked
  exact sourceChecked

/-- Coherent named metadata identifies the witness actually recovered from
the cached existence theorem; admission alone does not identify that metadata. -/
theorem TypeAdmission.source_checks {before : Reading} (data : TypeAdmission before)
    (coherent : ConclusionsChecked before) :
    data.predicate.check = some data.result.core.predicate ∧
      data.sourceWitness.check = some data.result.core.witness := by
  have sourceChecked := data.source_checked coherent
  have encoded := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  have core := (admitSourceTypeInTheory_result data.admitted).2.1
  obtain ⟨_,_,_,_,shape⟩ := (admitTypeInTheory_result core).1
  simp only [SourceTerm.toDB] at encoded
  change data.existence.sequent.concl.term =
    DBTerm.app data.result.core.predicate.term data.result.core.witness.term at shape
  rw [shape] at encoded
  have parts := DBTerm.app.inj encoded
  exact ⟨(SourceTerm.check_eq_some_iff _ _).mpr parts.1,
    (SourceTerm.check_eq_some_iff _ _).mpr parts.2⟩

/-- This optional visible-registry property concerns source interpretation.
It is not an extra declaration-acceptance test. Hidden entries are unrestricted. -/
def SymbolsAligned (reading : Reading) : Prop :=
  (∀ key operator, List.lookup key reading.symbols.operators = some operator →
    operatorName operator = sourceOperatorName (.global key) ∧
      ∃ arity, (currentContext reading).signature.typeOperators operator = some arity) ∧
  (∀ key constant, List.lookup key reading.symbols.constants = some constant →
    constantName constant = .global key ∧
      ∃ schema, (currentContext reading).signature.constants constant = some schema)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceDeclarations
