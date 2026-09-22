import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry

/-!
# The required four-face service specimen on the shared native quotient

The existing targets, service operations, submitted requests, input interfaces
and scoped native surfaces are unchanged. Only their semantic attachment is
constructed here, using actual independently admitted native terms in the
same formed quotient interpretation as the declaration/universe interfaces.

All four faces retain their original inputs: a decision claim, a native guest
witness, a meaningful operation input, or an external certificate. The native
operation produces its real wrapped application. The common payload retains
both the returned wire and an independent Data variable; actual admitted
caller substitution changes that variable without changing the service call.

The semantic values below are native conversion classes, not the earlier
external wire-algebra values. The unchanged caller contract fixes the required
native representation. A different admitted payload can have its own quotient
meaning without satisfying that contract. Qualification is only for this
existing constructor-classification specimen, not all future services or a
full shared semantic-requirement record.

The semantic attachment is noncomputable quotient data. The original raw
service operations and submitted request computations are unchanged.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientServices

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive FormationSensitiveContextual SharedJudgmentFragment
open SharedJudgmentQuotientInterpretation (data context)
open SharedJudgmentServiceInterpretation (NativeAttachment)
open SharedJudgmentServiceRegistry (specification requiredSpecification satisfies_iff required_satisfies_iff)
open SharedJudgmentServiceRegistry.Controls (targets raw raw_qualified contract expected)

/-- The real Data declaration is formed in every admitted caller. -/
def nativeDataType {n : Nat} (source : SharedJudgmentInterpretation.Context common n) :
    TypeOver (context source) where
  code := NativeWireData.dataType
  level := .sort Tower.zero
  universeWitness := .sort Tower.zero
  formed := HOLNativeRelatorCompatibility.wire_typing
    (NativeWireData.dataType_formed source.raw)

def literalTerm {n : Nat} (source : SharedJudgmentInterpretation.Context common n)
    (wire : NativeWireData.Wire) : Term (context source) (nativeDataType source) where
  code := NativeWireData.encode wire
  typed := HOLNativeRelatorCompatibility.wire_typing
    (NativeWireData.encode_typing source.raw wire)

def parameterTerm (wire : NativeWireData.Wire) :
    Term (context SharedJudgmentServiceInterpretation.WireControls.parameterContext)
      (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext) where
  code := SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire
  typed := (SharedJudgmentServiceInterpretation.WireControls.parameter_denotes wire).typed

/-- Raw scope/context/payload/type maps are exactly the original surface.
Formation witnesses only index its actual semantic type and term classes. -/
noncomputable def attachment : NativeAttachment (targets .directDecision) (data common) where
  scope := SharedJudgmentServiceInterpretation.WireControls.parameterAttachment.scope
  context := SharedJudgmentServiceInterpretation.WireControls.parameterAttachment.context
  payload := SharedJudgmentServiceInterpretation.WireControls.parameterAttachment.payload
  nativeType := SharedJudgmentServiceInterpretation.WireControls.parameterAttachment.nativeType
  semanticType _ _ := QType.mk
    (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext)
  value wire _ := TermFibre.mk (parameterTerm wire)

theorem attachment_native : attachment.NativeAdmitted :=
  SharedJudgmentServiceInterpretation.WireControls.parameter_native

theorem attachment_meaning : attachment.MeaningCompatible := by
  intro wire _ _
  exact ⟨QuotientInterpretation.type_meaning _
      (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext),
    QuotientInterpretation.term_meaning _ (parameterTerm wire)⟩

noncomputable def registry : SharedJudgmentServiceRegistry.Data targets (data common) where
  service := raw
  attachment _ := attachment

theorem registry_qualified : (specification targets id (data common)).Satisfies registry := by
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, raw_qualified, fun _ => attachment_native, fun _ => attachment_meaning⟩
  intro face
  cases face <;> rfl

theorem required_registry_qualified :
    (requiredSpecification contract (data common)).Satisfies registry := by
  apply (required_satisfies_iff _ _).mpr
  refine ⟨raw_qualified, fun _ => attachment_native, fun _ => attachment_meaning,
    ?_, fun _ => rfl⟩
  intro face
  cases face <;> constructor

/-- Only the representation's semantic attachment changed. The original
typed request can therefore be used without a new classifier or decoder. -/
theorem service_unchanged (face : NIK.Face) :
    registry.serviceAt registry_qualified face =
      SharedJudgmentServiceRegistry.Controls.registry.serviceAt
        SharedJudgmentServiceRegistry.Controls.registry_qualified face := rfl

theorem accepted_native_and_meaning (face : NIK.Face)
    (request : NIKServiceInvocation.Request (registry.serviceAt registry_qualified face))
    (input : NIKServiceInvocation.InputAdmission request) {wire : NativeWireData.Wire}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some wire) :
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire)
        NativeWireData.dataType ∧
      (data common).ty SharedJudgmentServiceInterpretation.WireControls.parameterContext
        NativeWireData.dataType
        (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext)) ∧
      (data common).term SharedJudgmentServiceInterpretation.WireControls.parameterContext
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire)
        NativeWireData.dataType
        (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext))
        (TermFibre.mk (parameterTerm wire)) :=
  registry.accepted_native_and_meaning registry_qualified face request input accepted

/-- Every original request, including the face-specific submitted witness
or operation source premise, reaches its actual native quotient meaning. -/
theorem four_calls (face : NIK.Face) :
    (NIKServiceInvocation.invoke (SharedJudgmentServiceRegistry.Controls.request face)).acceptedValue =
        some (expected face) ∧
      (data common).term SharedJudgmentServiceInterpretation.WireControls.parameterContext
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload (expected face))
        NativeWireData.dataType
        (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext))
        (TermFibre.mk (parameterTerm (expected face))) :=
  ⟨SharedJudgmentServiceRegistry.Controls.four_invocations face,
    (accepted_native_and_meaning face (SharedJudgmentServiceRegistry.Controls.request face)
      (SharedJudgmentServiceRegistry.Controls.request_input face)
      (SharedJudgmentServiceRegistry.Controls.four_invocations face)).2.2⟩

/-- The operation source premise is still required; no target meaning or
accepted response is inferred merely from a well-formed encoded input. -/
theorem accepted_substitution (face : NIK.Face)
    (request : NIKServiceInvocation.Request (registry.serviceAt registry_qualified face))
    (input : NIKServiceInvocation.InputAdmission request) {wire : NativeWireData.Wire}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some wire)
    {m : Nat} (target : SharedJudgmentInterpretation.Context common m)
    (sigma : Sub Tower.Head 4 m)
    (semantic : (QuotientCwf.cwf common.rules).Sub ((data common).ctx target)
      ((data common).ctx SharedJudgmentServiceInterpretation.WireControls.parameterContext))
    (typed : FormationSensitive.CtxMor common.rules
      NativeMatchedTransportDenotation.parameterContext target.raw sigma)
    (related : (data common).sub SharedJudgmentServiceInterpretation.WireControls.parameterContext
      target sigma semantic) :
    Judgment common.rules target.raw
        (subst sigma (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire))
        NativeWireData.dataType ∧
      (data common).ty target NativeWireData.dataType
        (QuotientCwf.tySub
          (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext))
          semantic) ∧
      (data common).term target
        (subst sigma (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire))
        NativeWireData.dataType
        (QuotientCwf.tySub
          (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext))
          semantic)
        (QuotientCwf.tmSub (TermFibre.mk (parameterTerm wire)) semantic) :=
  registry.accepted_substitution registry_qualified SharedJudgmentQuotientInterpretation.substitution_stable
    face request input accepted target sigma semantic typed related

/-- This is the existing nonidentity Data-parameter substitution, with its
actual refined typing proof and quotient arrow. -/
def fillHom (value : NativeWireDataDenotation.Value) :
    Hom (context SharedJudgmentServiceInterpretation.WireControls.commonContext)
      (context SharedJudgmentServiceInterpretation.WireControls.parameterContext) :=
  ⟨NativeWireDataDenotation.fillParameter value, NativeWireDataDenotation.fillParameter_typed value⟩

theorem fill_related (value : NativeWireDataDenotation.Value) :
    (data common).sub SharedJudgmentServiceInterpretation.WireControls.parameterContext
      SharedJudgmentServiceInterpretation.WireControls.commonContext
      (NativeWireDataDenotation.fillParameter value) (QuotientCwf.project (fillHom value)) :=
  ⟨(fillHom value).typed, rfl⟩

theorem filled_payload (wire : NativeWireData.Wire) (value : NativeWireDataDenotation.Value) :
    subst (NativeWireDataDenotation.fillParameter value)
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire) =
      .app (.app (.const NativeWireData.consName) (NativeWireData.encode wire))
        (NativeWireDataDenotation.quote value) := by
  simp only [SharedJudgmentServiceInterpretation.WireControls.parameterPayload, subst,
    NativeWireData.subst_encode, NativeWireDataDenotation.fillParameter, consSub_zero]

theorem four_filled_calls (face : NIK.Face) (value : NativeWireDataDenotation.Value) :
    (data common).term SharedJudgmentServiceInterpretation.WireControls.commonContext
      (.app (.app (.const NativeWireData.consName) (NativeWireData.encode (expected face)))
        (NativeWireDataDenotation.quote value)) NativeWireData.dataType
      (QuotientCwf.tySub
        (QType.mk (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext))
        (QuotientCwf.project (fillHom value)))
      (QuotientCwf.tmSub (TermFibre.mk (parameterTerm (expected face)))
        (QuotientCwf.project (fillHom value))) := by
  have transported := (accepted_substitution face
    (SharedJudgmentServiceRegistry.Controls.request face)
    (SharedJudgmentServiceRegistry.Controls.request_input face)
    (SharedJudgmentServiceRegistry.Controls.four_invocations face)
    SharedJudgmentServiceInterpretation.WireControls.commonContext
    (NativeWireDataDenotation.fillParameter value) (QuotientCwf.project (fillHom value))
    (fillHom value).typed (fill_related value)).2.2
  rw [filled_payload] at transported
  exact transported

/-- The actual filled native payload retains its Data argument. This is
injectivity of retained raw syntax, not an extra quotient-separation claim. -/
theorem filled_native_payload_injective (wire : NativeWireData.Wire)
    {first second : NativeWireDataDenotation.Value}
    (same : subst (NativeWireDataDenotation.fillParameter first)
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire) =
      subst (NativeWireDataDenotation.fillParameter second)
        (SharedJudgmentServiceInterpretation.WireControls.parameterPayload wire)) : first = second := by
  rw [filled_payload, filled_payload] at same
  have quoted := (Tm.app.inj same).2
  have denotes := NativeWireDataDenotation.quote_denotes (State := Unit)
    OpaqueRelatorScopedComputation.Common.context (fun _ _ => .nil) first
  rw [quoted] at denotes
  exact congrFun (denotes.functional (NativeWireDataDenotation.quote_denotes
    OpaqueRelatorScopedComputation.Common.context (fun _ _ => .nil) second)) ()

namespace Controls

/-- Reuse the earlier wrong-face operation data, with the genuinely new
quotient attachment. It is a negative fixture, not the proposed registry. -/
noncomputable def wrongFace : SharedJudgmentServiceRegistry.Data targets (data common) where
  service := SharedJudgmentServiceRegistry.Controls.wrongFace.service
  attachment := registry.attachment

theorem wrong_face_other_laws :
    SharedJudgmentServiceRegistry.ServicesQualified wrongFace ∧
      SharedJudgmentServiceRegistry.NativeAdmitted wrongFace ∧
      SharedJudgmentServiceRegistry.MeaningCompatible wrongFace :=
  ⟨fun _ => SharedJudgmentServiceInterpretation.WireControls.qualified,
    fun _ => attachment_native, fun _ => attachment_meaning⟩

theorem wrong_face_rejected :
    ¬ (requiredSpecification contract (data common)).Satisfies wrongFace := by
  intro qualified
  have inputs := ((required_satisfies_iff _ _).mp qualified).2.2.2.1 .nativeProof
  cases inputs

/-- The existing unusable-source fixture retains its target and face, but
it does not meet the caller's unchanged nonempty operation input interface. -/
noncomputable def vacuousSource : SharedJudgmentServiceRegistry.Data targets (data common) where
  service := SharedJudgmentServiceRegistry.Controls.vacuousSource.service
  attachment := registry.attachment

theorem vacuous_source_base_laws :
    (specification targets id (data common)).Satisfies vacuousSource := by
  have original := (satisfies_iff _ _).mp
    SharedJudgmentServiceRegistry.Controls.target_and_face_do_not_fix_inputs
  exact (satisfies_iff _ _).mpr
    ⟨original.1, original.2.1, fun _ => attachment_native, fun _ => attachment_meaning⟩

theorem vacuous_source_rejected :
    ¬ (requiredSpecification contract (data common)).Satisfies vacuousSource := by
  intro qualified
  have inputs := ((required_satisfies_iff _ _).mp qualified).2.2.2.1 .nativeOperation
  have same := inputs.operation_source
  have carriers : Empty = NativeWireData.Wire :=
    congrArg Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionObject.Carrier same
  exact Empty.elim (cast carriers.symm SharedJudgmentServiceInterpretation.WireControls.actualWire)

/-- A different actual Data term can have a valid quotient meaning without
being the native representation requested for this service response. -/
noncomputable def changedPayload : NativeAttachment (targets .directDecision) (data common) where
  scope := attachment.scope
  context := attachment.context
  payload _ := NativeWireData.encode (.natural 7)
  nativeType := attachment.nativeType
  semanticType := attachment.semanticType
  value _ _ := TermFibre.mk
    (literalTerm SharedJudgmentServiceInterpretation.WireControls.parameterContext (.natural 7))

theorem changed_payload_native : changedPayload.NativeAdmitted := by
  intro _ _
  exact (literalTerm SharedJudgmentServiceInterpretation.WireControls.parameterContext (.natural 7)).judgment

theorem changed_payload_meaning : changedPayload.MeaningCompatible := by
  intro _ _ _
  exact ⟨QuotientInterpretation.type_meaning _
      (nativeDataType SharedJudgmentServiceInterpretation.WireControls.parameterContext),
    QuotientInterpretation.term_meaning _
    (literalTerm SharedJudgmentServiceInterpretation.WireControls.parameterContext (.natural 7))⟩

noncomputable def wrongPayload : SharedJudgmentServiceRegistry.Data targets (data common) where
  service := registry.service
  attachment _ := changedPayload

theorem changed_payload_base_laws :
    (specification targets id (data common)).Satisfies wrongPayload := by
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, raw_qualified, fun _ => changed_payload_native, fun _ => changed_payload_meaning⟩
  intro face
  cases face <;> rfl

theorem changed_payload_rejected :
    ¬ (requiredSpecification contract (data common)).Satisfies wrongPayload := by
  intro qualified
  have surface := ((required_satisfies_iff _ _).mp qualified).2.2.2.2 .directDecision
  have codes := congrArg
    (fun actual => match actual.payload SharedJudgmentServiceInterpretation.WireControls.actualWire with
      | .const _ => true
      | _ => false) surface
  simp [SharedJudgmentServiceRegistry.nativeSurface, wrongPayload, changedPayload,
    contract, NativeWireData.encode] at codes

def badProof : NIKServiceInvocation.Request (registry.serviceAt registry_qualified .nativeProof) :=
  .nativeProof SharedJudgmentServiceInterpretation.WireControls.actualWire
    ("other-head", [.natural 7])

def badCertificate :
    NIKServiceInvocation.Request (registry.serviceAt registry_qualified .certificateBoundary) :=
  .certificateBoundary SharedJudgmentServiceInterpretation.WireControls.actualWire
    ("other-head", [.natural 7])

/-- Rejection of the submitted evidence does not negate the original
meaningful claim. Both checkers still bind the exact submitted claim. -/
theorem rejected_evidence_meaningful :
    (targets .nativeProof).Meaning SharedJudgmentServiceInterpretation.WireControls.actualWire ∧
      (NIKServiceInvocation.invoke badProof).acceptedValue = none ∧
      (NIKServiceInvocation.invoke badCertificate).acceptedValue = none :=
  ⟨SharedJudgmentServiceRegistry.Controls.changed_witness_rejected.2, rfl, rfl⟩

def negativeDecision :
    NIKServiceInvocation.Request (registry.serviceAt registry_qualified .directDecision) :=
  .directDecision (.natural 7)

/-- Unlike the failed witness controls, this actual complete decision
rejects an artifact outside the target predicate. -/
theorem negative_decision_not_meaningful :
    (NIKServiceInvocation.invoke negativeDecision).acceptedValue = none ∧
      ¬ (targets .directDecision).Meaning (.natural 7) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨head, arguments, impossible⟩
  cases impossible

theorem native_operation_changes_result :
    expected .nativeOperation ≠ expected .directDecision :=
  SharedJudgmentServiceRegistry.Controls.operation_not_identity

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientServices
