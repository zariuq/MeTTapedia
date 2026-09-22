import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveContextSourceObstruction
import Mettapedia.GSLT.LanguageDef.NIKServiceInvocation

/-!
# Raw service operations attached to the same native interpretation

The four raw faces contain operations, not their correctness laws. Their
qualification reconstructs the existing NIK service at the unchanged target;
erasing that reconstruction recovers the submitted operations exactly. The
target and its meaning are supplied independently. An application must still
pin the intended request, theory, revision and required service scopes there;
qualification does not establish that an arbitrary target is the intended one.

A native attachment supplies actual claim-indexed context, payload and type
representations, together with semantic type/value sections indexed by formed
contexts in the same assembly's interpretation. Rejected and unfinished raw
contexts remain representable. Native admission and meaning compatibility are independent
requirements. Accepted-response transport uses the original NIK invocation
and its exact returned artifact, retaining the source premise for operations.
Formed native substitutions then transport both judgments and semantic values.
Only a qualified direct decision turns rejection into target falsity; failure
of one proof or certificate is not a refutation of the target claim.

The concrete controls use the existing intrinsic HOL guest and the actual
native wire constructor algebra. Intrinsic proof inputs have already been
admitted by the surrounding calculus; their binding checker is not a checker
for arbitrary external proof bytes. The wire interpretation is a constructor
fragment, not a model of all native terms or universes. No service registry,
global proof-irrelevance choice, full model or coverage closure is supplied.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceInterpretation

open Mettapedia.GSLT.LanguageDef
open KernelAuthority NIKMetalogic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive
open SharedJudgmentFragment SharedJudgmentInterpretation

universe uArtifact uEvidence u v w w'

/-- Operational data for the four existing NIK faces. The native guest's
judgment is stated independently of its submitted Boolean checker. -/
inductive RawService (target : AdmissionObject.{uArtifact}) :
    Type (max (uArtifact + 1) (uEvidence + 1)) where
  | directDecision (decide : target.Carrier → Bool)
  | nativeProof (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
      (check : target.Carrier → guest.ProofObject → Bool)
  | nativeOperation (source : AdmissionObject.{uArtifact})
      (run : source.Carrier → target.Carrier)
  | certificateBoundary (Certificate : Type uEvidence)
      (checker : Checker target.Carrier Certificate)

namespace RawService

variable {target : AdmissionObject.{uArtifact}}

/-- Qualification is separate from raw data. Operation qualification is
preservation, not surjectivity; certificate completeness quantifies over
evidence and is not a decision procedure for its existence. -/
def Qualified : RawService.{uArtifact, uEvidence} target → Prop
  | .directDecision decide => ∀ claim, decide claim = true ↔ target.Meaning claim
  | .nativeProof guest check =>
      (∀ claim proof, check claim proof = true ↔ guest.Judges proof claim) ∧
      (∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
  | .nativeOperation source run =>
      ∀ input, source.Meaning input → target.Meaning (run input)
  | .certificateBoundary _ checker => checker.Authority target.Meaning

/-- Reconstruct the existing service, keeping its fixed target and all raw
functions. No claim predicate is inferred from acceptance. -/
def toService (raw : RawService.{uArtifact, uEvidence} target)
    (qualified : raw.Qualified) : NIK.Service.{uArtifact, uEvidence} target :=
  match raw with
  | .directDecision decide => .directDecision ⟨decide, qualified⟩
  | .nativeProof guest check =>
      .nativeProof guest ⟨check, qualified.1⟩ qualified.2
  | .nativeOperation source run => .nativeOperation source ⟨run, qualified⟩
  | .certificateBoundary Certificate checker =>
      .certificateBoundary Certificate checker qualified

/-- Forget only the laws carried by an existing NIK service. -/
def erase : NIK.Service.{uArtifact, uEvidence} target → RawService target
  | .directDecision kernel => .directDecision kernel.decide
  | .nativeProof guest kernel _ => .nativeProof guest kernel.decide
  | .nativeOperation source operation => .nativeOperation source operation.run
  | .certificateBoundary Certificate checker _ => .certificateBoundary Certificate checker

theorem erase_toService (raw : RawService.{uArtifact, uEvidence} target)
    (qualified : raw.Qualified) : erase (raw.toService qualified) = raw := by
  cases raw <;> rfl

theorem erased_qualified (service : NIK.Service.{uArtifact, uEvidence} target) :
    (erase service).Qualified := by
  cases service with
  | directDecision kernel => exact kernel.correct
  | nativeProof guest kernel exactMeaning => exact ⟨kernel.correct, exactMeaning⟩
  | nativeOperation source operation => exact operation.preserves
  | certificateBoundary Certificate checker authority => exact authority

/-- Change only the proposed target meaning. All submitted operations and
guest judgments stay fixed; qualification must be justified again. -/
def withMeaning (raw : RawService.{uArtifact, uEvidence} target)
    (meaning : target.Carrier → Prop) : RawService ⟨target.Carrier, meaning⟩ :=
  match raw with
  | .directDecision decide => .directDecision decide
  | .nativeProof guest check => .nativeProof guest check
  | .nativeOperation source run => .nativeOperation source run
  | .certificateBoundary Certificate checker => .certificateBoundary Certificate checker

end RawService

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}
variable {target : AdmissionObject.{uArtifact}}

/-- Raw representation maps for actual returned claims. This does not assert
that the payload inhabits the proposition it may represent: `nativeType`
states the native judgment that is separately required. Only semantic sections
require a formed context; raw context data remains unrestricted. -/
structure NativeAttachment (target : AdmissionObject.{uArtifact})
    (interpretation : Data assembly C) where
  scope : target.Carrier → Nat
  context : (claim : target.Carrier) → Tower.Ctx (scope claim)
  payload : (claim : target.Carrier) → Tower.Tm (scope claim)
  nativeType : (claim : target.Carrier) → Tower.Tm (scope claim)
  semanticType : (claim : target.Carrier) →
    (formed : ContextFormation assembly.rules (context claim)) →
      C.Ty (interpretation.ctx ⟨context claim, formed⟩)
  value : (claim : target.Carrier) →
    (formed : ContextFormation assembly.rules (context claim)) →
      C.Tm (interpretation.ctx ⟨context claim, formed⟩) (semanticType claim formed)

namespace NativeAttachment

variable {interpretation : Data assembly C}

def NativeAdmitted (attachment : NativeAttachment target interpretation) : Prop :=
  ∀ claim, target.Meaning claim →
    Judgment assembly.rules (attachment.context claim)
      (attachment.payload claim) (attachment.nativeType claim)

/-- Native admission supplies the semantic domain only for meaningful claims.
The raw context of every other request remains available without such a law. -/
def admittedContext (attachment : NativeAttachment target interpretation)
    (native : attachment.NativeAdmitted) (claim : target.Carrier)
    (meaningful : target.Meaning claim) : Context assembly (attachment.scope claim) :=
  Context.ofJudgment (native claim meaningful)

def MeaningCompatible (attachment : NativeAttachment target interpretation) : Prop :=
  ∀ claim (formed : ContextFormation assembly.rules (attachment.context claim)),
    target.Meaning claim →
    interpretation.ty ⟨attachment.context claim, formed⟩ (attachment.nativeType claim)
      (attachment.semanticType claim formed) ∧
    interpretation.term ⟨attachment.context claim, formed⟩ (attachment.payload claim)
      (attachment.nativeType claim) (attachment.semanticType claim formed) (attachment.value claim formed)

/-- The original invocation determines the exact accepted artifact. Its
operation face still requires the independently stated source meaning. -/
theorem accepted_native_and_meaning
    (raw : RawService.{uArtifact, uEvidence} target) (qualified : raw.Qualified)
    (attachment : NativeAttachment target interpretation)
    (native : attachment.NativeAdmitted) (meaning : attachment.MeaningCompatible)
    (request : NIKServiceInvocation.Request (raw.toService qualified))
    (input : NIKServiceInvocation.InputAdmission request)
    {claim : target.Carrier}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim) :
    let context := attachment.admittedContext native claim
      (NIKServiceInvocation.accepted_meaning request input accepted)
    Judgment assembly.rules (attachment.context claim)
      (attachment.payload claim) (attachment.nativeType claim) ∧
    interpretation.ty context (attachment.nativeType claim)
      (attachment.semanticType claim context.formed) ∧
    interpretation.term context (attachment.payload claim)
      (attachment.nativeType claim) (attachment.semanticType claim context.formed)
      (attachment.value claim context.formed) := by
  have meaningful := NIKServiceInvocation.accepted_meaning request input accepted
  exact ⟨native claim meaningful, meaning claim (native claim meaningful).context meaningful⟩

/-- Accepted payloads commute with an actual formed native environment and
its related semantic substitution. Neither raw substitutions nor semantic
context maps are silently admitted. -/
theorem accepted_substitution
    (raw : RawService.{uArtifact, uEvidence} target) (qualified : raw.Qualified)
    (attachment : NativeAttachment target interpretation)
    (native : attachment.NativeAdmitted) (meaning : attachment.MeaningCompatible)
    (stable : SubstitutionStable interpretation)
    (request : NIKServiceInvocation.Request (raw.toService qualified))
    (input : NIKServiceInvocation.InputAdmission request)
    {claim : target.Carrier}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim)
    {m : Nat} (context : Context assembly m)
    (sigma : Sub Tower.Head (attachment.scope claim) m)
    (semantic : C.Sub (interpretation.ctx context)
      (interpretation.ctx (attachment.admittedContext native claim
        (NIKServiceInvocation.accepted_meaning request input accepted))))
    (typed : FormationSensitive.CtxMor assembly.rules (attachment.context claim) context sigma)
    (related : interpretation.sub (attachment.admittedContext native claim
      (NIKServiceInvocation.accepted_meaning request input accepted)) context sigma semantic) :
    let source := attachment.admittedContext native claim
      (NIKServiceInvocation.accepted_meaning request input accepted)
    Judgment assembly.rules context (subst sigma (attachment.payload claim))
      (subst sigma (attachment.nativeType claim)) ∧
    interpretation.ty context (subst sigma (attachment.nativeType claim))
      (C.tySub (attachment.semanticType claim source.formed) semantic) ∧
    interpretation.term context (subst sigma (attachment.payload claim))
      (subst sigma (attachment.nativeType claim))
      (C.tySub (attachment.semanticType claim source.formed) semantic)
      (C.tmSub (attachment.value claim source.formed) semantic) := by
  obtain ⟨admitted, typeMeaning, termMeaning⟩ :=
    attachment.accepted_native_and_meaning raw qualified native meaning request input accepted
  exact ⟨admitted.substitute context.formed typed,
    stable.1 _ _ _ _ _ _ _ _ context.formed typed related typeMeaning,
    stable.2 _ _ _ _ _ _ _ _ _ _ context.formed typed admitted related typeMeaning termMeaning⟩

end NativeAttachment

namespace HOLControls

open Mettapedia.Logic HOL HOL.UniformListInduction
open UniformListChartNIKService

def raw (gamma : HOL.Ctx BaseSort) : RawService (sourceTarget gamma) :=
  .nativeProof (intrinsicProofSystem gamma) (intrinsicKernel gamma).decide

theorem qualified (gamma : HOL.Ctx BaseSort) : (raw gamma).Qualified :=
  ⟨(intrinsicKernel gamma).correct, intrinsic_meaning_exact gamma⟩

theorem service_unchanged (gamma : HOL.Ctx BaseSort) :
    (raw gamma).toService (qualified gamma) = nativeProofService gamma := rfl

/-- The actual induction proof, reconstructed from the submitted equational
leaves, is accepted by the recovered intrinsic service at its full claim. -/
theorem actual_accepted (gamma : HOL.Ctx BaseSort) :
    (NIKServiceInvocation.invoke
      (NIKServiceInvocation.Request.nativeProof
        (target := sourceTarget gamma)
        (guest := intrinsicProofSystem gamma)
        (kernel := ⟨(intrinsicKernel gamma).decide, (qualified gamma).1⟩)
        (exactMeaning := (qualified gamma).2)
        (mapLengthClaim gamma) (actualNativeProof gamma))).acceptedValue =
      some (mapLengthClaim gamma) := by
  simp only [NIKServiceInvocation.invoke, NIKServiceInvocation.Response.acceptedValue,
    actual_native_accepted, ↓reduceIte]
  rfl

/-- The same raw checker and guest cannot acquire unconditional junk-model
truth as target meaning. Submitted assumptions have not disappeared. -/
theorem changed_meaning_not_qualified :
    ¬ ((raw []).withMeaning (fun claim => JunkModel.model.models claim.2)).Qualified := by
  intro qualifies
  exact unconditional_junk_meaning_not_adequate qualifies.2

end HOLControls

namespace WireControls

open NativeWireDataDenotation

def commonContext : Context common 3 :=
  ⟨OpaqueRelatorScopedComputation.Common.context, OpaqueRelatorScopedComputation.Common.context_formed⟩

def parameterContext : Context common 4 :=
  ⟨NativeMatchedTransportDenotation.parameterContext, NativeMatchedTransportDenotation.parameterContext_formed⟩

/-- A concrete nontrivial target on the existing wire carrier. This tests a
wire constructor classification, not proof or receipt validity. -/
def applicationTarget : AdmissionObject where
  Carrier := NativeWireData.Wire
  Meaning wire := ∃ head arguments, wire = .application head arguments

def applicationDecision : NativeWireData.Wire → Bool
  | .application _ _ => true
  | .symbol _ | .string _ | .natural _ => false

def raw : RawService.{0, 0} applicationTarget := .directDecision applicationDecision

theorem qualified : raw.Qualified := by
  intro wire
  cases wire <;> simp [applicationDecision, applicationTarget]

/-- Data observations of scoped variables. Non-Data fields of a mixed
context have no denotation law merely because this raw map assigns them a
coordinate. The relation below only consults independently Data-typed ones. -/
def environment {n : Nat} (index : Fin n) (state : Fin n → Value) : Value := state index

/-- The existing total constructor algebra supplies a partial raw native
interpretation. In particular it does not interpret Pi, J or universe heads,
and it is not asserted to satisfy global admission or comprehension laws. -/
def interpretation : Data common familiesCwf where
  ctx {n} _ := Fin n → Value
  ty _ nativeType semanticType :=
    nativeType = NativeWireData.dataType ∧ semanticType = (fun _ => Value)
  term context term nativeType _ value :=
    nativeType = NativeWireData.dataType ∧
      ∃ denotation, Denotes context environment term denotation ∧ HEq value denotation
  sub source target sigma semantic :=
    ∀ index, Typing HOLNativeRelatorCompatibility.rules source (.var index) NativeWireData.dataType →
      Denotes target environment (sigma index) (fun state => semantic state index)

theorem interpretation_substitution : SubstitutionStable interpretation := by
  constructor
  · intro n m source target sigma semantic type semanticType _ _ _ typeMeaning
    obtain ⟨rfl, rfl⟩ := typeMeaning
    exact ⟨rfl, rfl⟩
  · intro n m source target sigma semantic term type semanticType value
      _ _ _ related typeMeaning termMeaning
    obtain ⟨rfl, rfl⟩ := typeMeaning
    obtain ⟨_, denotation, denotes, same⟩ := termMeaning
    have equal : value = denotation := eq_of_heq same
    subst value
    exact ⟨rfl, denotation ∘ semantic, denotes.substitute sigma semantic related, HEq.rfl⟩

/-- The representation retains the entire accepted wire, not an acceptance
bit or a proof identity. Its type is native Data, never an identity fibre. -/
def attachment {n : Nat} (context : Tower.Ctx n) :
    NativeAttachment applicationTarget interpretation where
  scope _ := n
  context _ := context
  payload := NativeWireData.encode
  nativeType _ := NativeWireData.dataType
  semanticType _ _ := fun _ => Value
  value wire _ := fun _ => ofWire wire

theorem attachment_native {n : Nat} (context : Tower.Ctx n)
    (formed : ContextFormation common.rules context) : (attachment context).NativeAdmitted := by
  intro wire _
  change Judgment HOLNativeRelatorCompatibility.rules context
    (NativeWireData.encode wire) NativeWireData.dataType
  exact ⟨formed, HOLNativeRelatorCompatibility.wire_typing
    (NativeWireData.encode_typing context wire)⟩

theorem attachment_meaning {n : Nat} (context : Tower.Ctx n) :
    (attachment context).MeaningCompatible := by
  intro wire _ _
  exact ⟨⟨rfl, rfl⟩, rfl, _, encode_denotes context environment wire, HEq.rfl⟩

def actualWire : NativeWireData.Wire :=
  .application "native-input" [.symbol "opaque-payload", .natural 7]

def actualRequest : NIKServiceInvocation.Request (raw.toService qualified) :=
  .directDecision actualWire

theorem actual_accepted :
    (NIKServiceInvocation.invoke actualRequest).acceptedValue = some actualWire := rfl

/-- Nonempty acceptance, actual native admission and retained constructor
meaning occur together in the existing mixed HOL/wire/List/J context. -/
theorem actual_native_and_meaning :
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (NativeWireData.encode actualWire) NativeWireData.dataType ∧
    interpretation.ty commonContext NativeWireData.dataType
      (fun _ => Value) ∧
    interpretation.term commonContext
      (NativeWireData.encode actualWire) NativeWireData.dataType
      (fun _ => Value) (fun _ => ofWire actualWire) :=
  (attachment _).accepted_native_and_meaning raw qualified
    (attachment_native _ OpaqueRelatorScopedComputation.Common.context_formed)
    (attachment_meaning _) actualRequest .directDecision actual_accepted

/-- This is a genuinely rejected but still natively admitted Data payload.
Admission of its representation does not establish the service predicate. -/
theorem nonapplication_rejected_but_admitted :
    (NIKServiceInvocation.invoke
      (NIKServiceInvocation.Request.directDecision
        (target := applicationTarget)
        (kernel := ⟨applicationDecision, qualified⟩) (.natural 7))).acceptedValue = none ∧
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (NativeWireData.encode (.natural 7)) NativeWireData.dataType := by
  refine ⟨rfl, ?_⟩
  exact ⟨OpaqueRelatorScopedComputation.Common.context_formed,
    HOLNativeRelatorCompatibility.wire_typing
      (NativeWireData.encode_typing _ (.natural 7))⟩

/-- Native admission alone also tolerates a changed payload; semantic
compatibility with the actual returned wire does not. -/
theorem changed_payload_not_meaning :
    ¬ interpretation.term commonContext
      (NativeWireData.encode (.natural 7)) NativeWireData.dataType
      (fun _ => Value) (fun _ => ofWire actualWire) := by
  rintro ⟨_, denotation, denotes, same⟩
  have equal : (fun _ : Fin 3 → Value => ofWire actualWire) = denotation := eq_of_heq same
  have determined := denotes.functional
    (encode_denotes OpaqueRelatorScopedComputation.Common.context environment (.natural 7))
  have changed := congrFun (equal.trans determined) (fun _ => .nil)
  simp only [actualWire, ofWire] at changed
  cases changed

/-- The accepted wire and an independent Data variable are both retained in
this payload. Its semantic section is nonconstant in the new context field. -/
def parameterPayload (wire : NativeWireData.Wire) : Tower.Tm 4 :=
  .app (.app (.const NativeWireData.consName) (NativeWireData.encode wire)) (.var 0)

def parameterAttachment : NativeAttachment applicationTarget interpretation where
  scope _ := 4
  context _ := NativeMatchedTransportDenotation.parameterContext
  payload := parameterPayload
  nativeType _ := NativeWireData.dataType
  semanticType _ _ := fun _ => Value
  value wire _ := fun state => .cons (ofWire wire) (state 0)

theorem parameter_denotes (wire : NativeWireData.Wire) :
    Denotes NativeMatchedTransportDenotation.parameterContext environment (parameterPayload wire)
      (fun state => .cons (ofWire wire) (state 0)) :=
  .cons (encode_denotes _ environment wire)
    (.variable 0 NativeMatchedTransportDenotation.parameter_typed)

theorem parameter_native : parameterAttachment.NativeAdmitted := by
  intro wire _
  exact ⟨NativeMatchedTransportDenotation.parameterContext_formed, (parameter_denotes wire).typed⟩

theorem parameter_meaning : parameterAttachment.MeaningCompatible := by
  intro wire _ _
  exact ⟨⟨rfl, rfl⟩, rfl, _, parameter_denotes wire, HEq.rfl⟩

def fillEnvironment (value : Value) (state : Fin 3 → Value) : Fin 4 → Value :=
  Fin.cases value state

theorem fill_related (value : Value) :
    interpretation.sub parameterContext commonContext (fillParameter value) (fillEnvironment value) := by
  intro index typed
  change Denotes OpaqueRelatorScopedComputation.Common.context environment (fillParameter value index)
    (fun state => fillEnvironment value state index)
  have component := fillParameter_components environment value index typed
  convert component using 1
  funext state
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-- An actual accepted response is transported through a nonidentity formed
environment. The result retains both the accepted wire and the arbitrary
substituted Data argument, including noncanonical constructor values. -/
theorem actual_parameter_substitution (value : Value) :
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (subst (fillParameter value) (parameterPayload actualWire)) NativeWireData.dataType ∧
    interpretation.ty commonContext NativeWireData.dataType
      (fun _ => Value) ∧
    interpretation.term commonContext
      (subst (fillParameter value) (parameterPayload actualWire)) NativeWireData.dataType
      (fun _ => Value) (fun _ => .cons (ofWire actualWire) value) := by
  exact parameterAttachment.accepted_substitution raw qualified parameter_native parameter_meaning
    interpretation_substitution actualRequest .directDecision actual_accepted
    commonContext (fillParameter value) (fillEnvironment value)
    (fillParameter_typed value) (fill_related value)

theorem changed_parameter_changes_value {first second : Value} (different : first ≠ second) :
    (fun _ : Fin 3 → Value => Value.cons (ofWire actualWire) first) ≠
      (fun _ : Fin 3 → Value => Value.cons (ofWire actualWire) second) := by
  intro same
  exact different (Value.cons.inj (congrFun same (fun _ => .nil))).2

end WireControls

namespace RawContextControls

open FormationSensitiveContextSourceObstruction

/-- An unfinished native context remains exactly expressible as attachment
data; forming its semantic sections is a separate boundary. -/
theorem unformed_raw_context_retained :
    (WireControls.attachment source).context WireControls.actualWire = source := rfl

/-- The real application target is nonempty, so its raw attachment at the
unformed source cannot satisfy native qualification. -/
theorem unformed_attachment_not_native_admitted :
    ¬ (WireControls.attachment source).NativeAdmitted := by
  intro admitted
  have typed := admitted WireControls.actualWire
    ⟨"native-input", [.symbol "opaque-payload", .natural 7], rfl⟩
  exact source_unformed typed.context

end RawContextControls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceInterpretation
