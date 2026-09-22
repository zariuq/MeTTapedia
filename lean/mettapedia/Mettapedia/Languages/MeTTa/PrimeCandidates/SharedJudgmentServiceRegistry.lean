import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceInterpretation
import Mettapedia.GSLT.LanguageDef.NIKServiceFamily

/-!
# Required services on one candidate interpretation

The caller supplies the required indices, semantic targets and input interfaces.
A proposed registry supplies operations and native representations at every
such index; it cannot qualify by replacing the requested family with an empty
list or by choosing a weaker target meaning. Face agreement alone does not fix
an operation's source or the format of submitted evidence. `Contract` therefore
also fixes those interfaces and the scoped native syntax to which each claim
must be attached. Agreement, service correctness, native admission and
interpretation compatibility remain separate predicates.

All representations refer to the same assembly and CwF interpretation. The
qualification theorem transports actual accepted invocations and their formed
substitutions, without changing the claim or silently admitting an operation's
source. Restriction to a caller-selected subfamily preserves qualification;
coverage is needed to infer qualification of the original family in return.

The inhabited four-face control is a wire-constructor classification package.
Its proof and certificate witnesses retain the actual head and arguments, and
its native operation constructs a new application. It is not a realization of
general theorem proving, a full native model, or a selection of draft services.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry

open Mettapedia.GSLT.LanguageDef
open KernelAuthority NIKMetalogic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DesignStudy
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive
open SharedJudgmentFragment SharedJudgmentServiceInterpretation

universe uIndex uOther uArtifact uEvidence u v w w'

section General

variable {Index : Type uIndex} {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- The existing face classifier, applied before correctness is supplied. -/
def rawFace {target : AdmissionObject.{uArtifact}} :
    RawService.{uArtifact, uEvidence} target → NIK.Face
  | .directDecision _ => .directDecision
  | .nativeProof .. => .nativeProof
  | .nativeOperation .. => .nativeOperation
  | .certificateBoundary .. => .certificateBoundary

theorem toService_face {target : AdmissionObject.{uArtifact}}
    (raw : RawService.{uArtifact, uEvidence} target) (qualified : raw.Qualified) :
    (raw.toService qualified).face = rawFace raw := by
  cases raw <;> rfl

/-- Raw operations and representations for an independently required family.
There are no correctness proofs in this data record. -/
structure Data (targets : Index → AdmissionObject.{uArtifact})
    (interpretation : SharedJudgmentInterpretation.Data assembly C) where
  service : (index : Index) → RawService.{uArtifact, uEvidence} (targets index)
  attachment : (index : Index) → NativeAttachment (targets index) interpretation

/-- Required request data, independently of the proposed implementation.
The native guest includes its judgment; an operation source includes its
meaning. Changing either requires an explicit interface translation. -/
inductive Interface (target : AdmissionObject.{uArtifact}) :
    Type (max (uArtifact + 1) (uEvidence + 1)) where
  | directDecision
  | nativeProof (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
  | nativeOperation (source : AdmissionObject.{uArtifact})
  | certificateBoundary (Certificate : Type uEvidence)

def Interface.face {target : AdmissionObject.{uArtifact}} :
    Interface.{uArtifact, uEvidence} target → NIK.Face
  | .directDecision => .directDecision
  | .nativeProof _ => .nativeProof
  | .nativeOperation _ => .nativeOperation
  | .certificateBoundary _ => .certificateBoundary

/-- Exact request-interface agreement leaves the checker/run unqualified.
Equivalent but differently represented requests need an explicit adapter;
this relation does not invent one. -/
inductive InterfaceMatches {target : AdmissionObject.{uArtifact}} :
    RawService.{uArtifact, uEvidence} target → Interface target → Prop where
  | directDecision (decide : target.Carrier → Bool) :
      InterfaceMatches (.directDecision decide) .directDecision
  | nativeProof (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
      (check : target.Carrier → guest.ProofObject → Bool) :
      InterfaceMatches (.nativeProof guest check) (.nativeProof guest)
  | nativeOperation (source : AdmissionObject.{uArtifact})
      (run : source.Carrier → target.Carrier) :
      InterfaceMatches (.nativeOperation source run) (.nativeOperation source)
  | certificateBoundary (Certificate : Type uEvidence)
      (checker : Checker target.Carrier Certificate) :
      InterfaceMatches (.certificateBoundary Certificate checker) (.certificateBoundary Certificate)

theorem InterfaceMatches.face {target : AdmissionObject.{uArtifact}}
    {raw : RawService.{uArtifact, uEvidence} target} {interface : Interface target}
    (agrees : InterfaceMatches raw interface) : rawFace raw = interface.face := by
  cases agrees <;> rfl

theorem InterfaceMatches.operation_source {target source expected : AdmissionObject.{uArtifact}}
    {run : source.Carrier → target.Carrier}
    (agrees : InterfaceMatches (.nativeOperation source run : RawService.{uArtifact, uEvidence} target)
      (.nativeOperation expected)) : source = expected := by
  cases agrees
  rfl

/-- The required native syntax, before assigning its semantic type/value. -/
structure NativeSurface (target : AdmissionObject.{uArtifact}) where
  scope : target.Carrier → Nat
  context : (claim : target.Carrier) → Tower.Ctx (scope claim)
  payload : (claim : target.Carrier) → Tower.Tm (scope claim)
  nativeType : (claim : target.Carrier) → Tower.Tm (scope claim)

def nativeSurface {target : AdmissionObject.{uArtifact}}
    {interpretation : SharedJudgmentInterpretation.Data assembly C}
    (attachment : NativeAttachment target interpretation) : NativeSurface target :=
  ⟨attachment.scope, attachment.context, attachment.payload, attachment.nativeType⟩

/-- The consumer fixes required requests and representations, not just labels.
The record has no implementation and no acceptance predicate. -/
structure Contract (targets : Index → AdmissionObject.{uArtifact}) where
  request : (index : Index) → Interface.{uArtifact, uEvidence} (targets index)
  surface : (index : Index) → NativeSurface (targets index)

variable {targets : Index → AdmissionObject.{uArtifact}}
  {interpretation : SharedJudgmentInterpretation.Data assembly C}

/-- A caller selects a subfamily without replacing its requests or surfaces. -/
def Contract.restrict (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    {Other : Type uOther} (select : Other → Index) : Contract (targets ∘ select) where
  request index := contract.request (select index)
  surface index := contract.surface (select index)

def FacesMatch (requiredFace : Index → NIK.Face)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, rawFace (registry.service index) = requiredFace index

def ServicesQualified (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, (registry.service index).Qualified

def NativeAdmitted (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, (registry.attachment index).NativeAdmitted

def MeaningCompatible (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, (registry.attachment index).MeaningCompatible

inductive Requirement
  | faces
  | services
  | native
  | meaning
  deriving DecidableEq

/-- The requirement collection is fixed outside the proposed operations. -/
def specification (targets : Index → AdmissionObject.{uArtifact})
    (requiredFace : Index → NIK.Face)
    (interpretation : SharedJudgmentInterpretation.Data assembly C) :
    Specification (Data.{uIndex, uArtifact, uEvidence} targets interpretation) Requirement where
  holds
    | .faces => FacesMatch requiredFace
    | .services => ServicesQualified
    | .native => NativeAdmitted
    | .meaning => MeaningCompatible
  required := [.faces, .services, .native, .meaning]

theorem satisfies_iff (requiredFace : Index → NIK.Face)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) :
    (specification targets requiredFace interpretation).Satisfies registry ↔
      FacesMatch requiredFace registry ∧ ServicesQualified registry ∧
      NativeAdmitted registry ∧ MeaningCompatible registry := by
  constructor
  · intro qualified
    exact ⟨qualified .faces (by simp [specification]),
      qualified .services (by simp [specification]),
      qualified .native (by simp [specification]),
      qualified .meaning (by simp [specification])⟩
  · rintro ⟨faces, services, native, meaning⟩ requirement _
    cases requirement
    · exact faces
    · exact services
    · exact native
    · exact meaning

def InterfacesMatch (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, InterfaceMatches (registry.service index) (contract.request index)

def SurfacesMatch (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) : Prop :=
  ∀ index, nativeSurface (registry.attachment index) = contract.surface index

inductive BindingRequirement
  | requests
  | surfaces
  deriving DecidableEq

def bindingSpecification (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (interpretation : SharedJudgmentInterpretation.Data assembly C) :
    Specification (Data.{uIndex, uArtifact, uEvidence} targets interpretation) BindingRequirement where
  holds
    | .requests => InterfacesMatch contract
    | .surfaces => SurfacesMatch contract
  required := [.requests, .surfaces]

theorem binding_satisfies_iff (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) :
    (bindingSpecification contract interpretation).Satisfies registry ↔
      InterfacesMatch contract registry ∧ SurfacesMatch contract registry := by
  constructor
  · intro qualified
    exact ⟨qualified .requests (by simp [bindingSpecification]),
      qualified .surfaces (by simp [bindingSpecification])⟩
  · rintro ⟨requests, surfaces⟩ requirement _
    cases requirement
    · exact requests
    · exact surfaces

/-- Qualification of the actual required interfaces, conjoined on the same
registry using the reusable specification operation. -/
def requiredSpecification (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (interpretation : SharedJudgmentInterpretation.Data assembly C) :=
  (specification targets (fun index => (contract.request index).face) interpretation).conjoin
    (bindingSpecification contract interpretation)

theorem required_satisfies_iff (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation) :
    (requiredSpecification contract interpretation).Satisfies registry ↔
      ServicesQualified registry ∧ NativeAdmitted registry ∧ MeaningCompatible registry ∧
      InterfacesMatch contract registry ∧ SurfacesMatch contract registry := by
  rw [requiredSpecification, Specification.satisfies_conjoin_iff,
    satisfies_iff, binding_satisfies_iff]
  constructor
  · rintro ⟨⟨_, services, native, meaning⟩, inputs, surfaces⟩
    exact ⟨services, native, meaning, inputs, surfaces⟩
  · rintro ⟨services, native, meaning, inputs, surfaces⟩
    exact ⟨⟨fun index => (inputs index).face, services, native, meaning⟩, inputs, surfaces⟩

namespace Data

variable (registry : Data.{uIndex, uArtifact, uEvidence} targets interpretation)
  {requiredFace : Index → NIK.Face}

/-- Recover the existing NIK service at the original required target. -/
def serviceAt
    (qualified : (specification targets requiredFace interpretation).Satisfies registry)
    (index : Index) : NIK.Service.{uArtifact, uEvidence} (targets index) :=
  (registry.service index).toService (((satisfies_iff requiredFace registry).mp qualified).2.1
    index)

theorem serviceAt_face
    (qualified : (specification targets requiredFace interpretation).Satisfies registry)
    (index : Index) : (registry.serviceAt qualified index).face = requiredFace index := by
  rw [serviceAt, toService_face]
  exact ((satisfies_iff requiredFace registry).mp qualified).1 index

/-- The original native qualification supplies a formed interpretation
index for a meaningful claim, without restricting the raw request surface. -/
def admittedContext
    (qualified : (specification targets requiredFace interpretation).Satisfies registry)
    (index : Index) (claim : (targets index).Carrier) (meaningful : (targets index).Meaning claim) :
    SharedJudgmentInterpretation.Context assembly ((registry.attachment index).scope claim) :=
  (registry.attachment index).admittedContext
    (((satisfies_iff requiredFace registry).mp qualified).2.2.1 index) claim meaningful

theorem accepted_native_and_meaning
    (qualified : (specification targets requiredFace interpretation).Satisfies registry)
    (index : Index) (request : NIKServiceInvocation.Request (registry.serviceAt qualified index))
    (input : NIKServiceInvocation.InputAdmission request)
    {claim : (targets index).Carrier}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim) :
    let context := registry.admittedContext qualified index claim
      (NIKServiceInvocation.accepted_meaning request input accepted)
    Judgment assembly.rules ((registry.attachment index).context claim)
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim) ∧
    interpretation.ty context
      ((registry.attachment index).nativeType claim) ((registry.attachment index).semanticType claim context.formed) ∧
    interpretation.term context
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim)
      ((registry.attachment index).semanticType claim context.formed)
      ((registry.attachment index).value claim context.formed) := by
  have laws := (satisfies_iff requiredFace registry).mp qualified
  exact (registry.attachment index).accepted_native_and_meaning
    (registry.service index) (laws.2.1 index) (laws.2.2.1 index) (laws.2.2.2 index)
    request input accepted

theorem accepted_substitution
    (qualified : (specification targets requiredFace interpretation).Satisfies registry)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (index : Index) (request : NIKServiceInvocation.Request (registry.serviceAt qualified index))
    (input : NIKServiceInvocation.InputAdmission request)
    {claim : (targets index).Carrier}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim)
    {m : Nat} (context : SharedJudgmentInterpretation.Context assembly m)
    (sigma : Sub Tower.Head ((registry.attachment index).scope claim) m)
    (semantic : C.Sub (interpretation.ctx context)
      (interpretation.ctx (registry.admittedContext qualified index claim
        (NIKServiceInvocation.accepted_meaning request input accepted))))
    (typed : FormationSensitive.CtxMor assembly.rules
      ((registry.attachment index).context claim) context sigma)
    (related : interpretation.sub (registry.admittedContext qualified index claim
      (NIKServiceInvocation.accepted_meaning request input accepted)) context sigma semantic) :
    let source := registry.admittedContext qualified index claim
      (NIKServiceInvocation.accepted_meaning request input accepted)
    Judgment assembly.rules context (subst sigma ((registry.attachment index).payload claim))
      (subst sigma ((registry.attachment index).nativeType claim)) ∧
    interpretation.ty context (subst sigma ((registry.attachment index).nativeType claim))
      (C.tySub ((registry.attachment index).semanticType claim source.formed) semantic) ∧
    interpretation.term context (subst sigma ((registry.attachment index).payload claim))
      (subst sigma ((registry.attachment index).nativeType claim))
      (C.tySub ((registry.attachment index).semanticType claim source.formed) semantic)
      (C.tmSub ((registry.attachment index).value claim source.formed) semantic) := by
  have laws := (satisfies_iff requiredFace registry).mp qualified
  exact (registry.attachment index).accepted_substitution
    (registry.service index) (laws.2.1 index) (laws.2.2.1 index) (laws.2.2.2 index)
    stable request input accepted context sigma semantic typed related

/-- A client chooses a subfamily, keeping the original operations and meanings. -/
def restrict {Other : Type uOther} (select : Other → Index) :
    Data (targets ∘ select) interpretation where
  service index := registry.service (select index)
  attachment index := registry.attachment (select index)

theorem restrict_satisfies {Other : Type uOther} (select : Other → Index)
    (qualified : (specification targets requiredFace interpretation).Satisfies registry) :
    (specification (targets ∘ select) (requiredFace ∘ select) interpretation).Satisfies
      (registry.restrict select) := by
  obtain ⟨faces, services, native, meaning⟩ := (satisfies_iff requiredFace registry).mp qualified
  exact (satisfies_iff _ _).mpr
    ⟨fun index => faces (select index), fun index => services (select index),
      fun index => native (select index), fun index => meaning (select index)⟩

/-- Subfamily tests qualify the entire registry only when every required
index is covered. The coverage premise cannot be replaced by nonemptiness. -/
theorem satisfies_of_restrict {Other : Type uOther} (select : Other → Index)
    (covers : Function.Surjective select)
    (qualified :
      (specification (targets ∘ select) (requiredFace ∘ select) interpretation).Satisfies
        (registry.restrict select)) :
    (specification targets requiredFace interpretation).Satisfies registry := by
  obtain ⟨faces, services, native, meaning⟩ := (satisfies_iff _ _).mp qualified
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index
    obtain ⟨other, rfl⟩ := covers index
    exact faces other
  · intro index
    obtain ⟨other, rfl⟩ := covers index
    exact services other
  · intro index
    obtain ⟨other, rfl⟩ := covers index
    exact native other
  · intro index
    obtain ⟨other, rfl⟩ := covers index
    exact meaning other

/-- Restriction retains the complete caller contract, not just face labels. -/
theorem required_restrict_satisfies (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    {Other : Type uOther} (select : Other → Index)
    (qualified : (requiredSpecification contract interpretation).Satisfies registry) :
    (requiredSpecification (contract.restrict select) interpretation).Satisfies
      (registry.restrict select) := by
  obtain ⟨services, native, meaning, inputs, surfaces⟩ :=
    (required_satisfies_iff contract registry).mp qualified
  exact (required_satisfies_iff _ _).mpr
    ⟨fun index => services (select index), fun index => native (select index),
      fun index => meaning (select index), fun index => inputs (select index),
      fun index => surfaces (select index)⟩

theorem required_satisfies_of_restrict (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    {Other : Type uOther} (select : Other → Index) (covers : Function.Surjective select)
    (qualified : (requiredSpecification (contract.restrict select) interpretation).Satisfies
      (registry.restrict select)) :
    (requiredSpecification contract interpretation).Satisfies registry := by
  obtain ⟨services, native, meaning, inputs, surfaces⟩ :=
    (required_satisfies_iff _ _).mp qualified
  apply (required_satisfies_iff _ _).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro index
    obtain ⟨other, rfl⟩ := covers index
  · exact services other
  · exact native other
  · exact meaning other
  · exact inputs other
  · exact surfaces other

end Data

end General

namespace Controls

open NativeWireData

/-- A submitted constructor witness, checked against the whole requested wire. -/
def guest : NativeProofSystem.{0, 0} Wire where
  ProofObject := String × List Wire
  Judges proof claim := claim = .application proof.1 proof.2

def check (claim : Wire) (proof : guest.ProofObject) : Bool :=
  decide (claim = .application proof.1 proof.2)

theorem check_exact (claim : Wire) (proof : guest.ProofObject) :
    check claim proof = true ↔ guest.Judges proof claim := by
  simp [check, guest]

theorem meaning_exact (claim : Wire) :
    WireControls.applicationTarget.Meaning claim ↔ Nonempty (guest.ProofFibre claim) := by
  constructor
  · rintro ⟨head, arguments, same⟩
    exact ⟨⟨(head, arguments), same⟩⟩
  · rintro ⟨⟨⟨head, arguments⟩, judged⟩⟩
    exact ⟨head, arguments, judged⟩

def checker : Checker Wire guest.ProofObject := ⟨check⟩

theorem authority : checker.Authority WireControls.applicationTarget.Meaning where
  sound claim proof accepted := meaning_exact claim |>.mpr
    ⟨⟨proof, (check_exact claim proof).mp accepted⟩⟩
  complete claim meaningful := by
    obtain ⟨proof, judged⟩ := (meaning_exact claim).mp meaningful
    exact ⟨proof, (check_exact claim proof).mpr judged⟩

/-- All four required faces have the same nontrivial constructor target. -/
def targets (_ : NIK.Face) : AdmissionObject := WireControls.applicationTarget

def raw : (face : NIK.Face) → RawService.{0, 0} (targets face)
  | .directDecision => WireControls.raw
  | .nativeProof => .nativeProof guest check
  | .nativeOperation => .nativeOperation WireControls.applicationTarget
      (fun input => .application "wrapped" [input])
  | .certificateBoundary => .certificateBoundary guest.ProofObject checker

theorem raw_qualified (face : NIK.Face) : (raw face).Qualified := by
  cases face with
  | directDecision => exact WireControls.qualified
  | nativeProof => exact ⟨check_exact, meaning_exact⟩
  | nativeOperation => exact fun input _ => ⟨"wrapped", [input], rfl⟩
  | certificateBoundary => exact authority

def registry : Data targets WireControls.interpretation where
  service := raw
  attachment _ := WireControls.parameterAttachment

theorem registry_qualified :
    (specification targets id WireControls.interpretation).Satisfies registry := by
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, raw_qualified, fun _ => WireControls.parameter_native,
    fun _ => WireControls.parameter_meaning⟩
  intro face
  cases face <;> rfl

def contract : Contract targets where
  request
    | .directDecision => .directDecision
    | .nativeProof => .nativeProof guest
    | .nativeOperation => .nativeOperation WireControls.applicationTarget
    | .certificateBoundary => .certificateBoundary guest.ProofObject
  surface _ :=
    { scope := fun _ => 4
      context := fun _ => NativeMatchedTransportDenotation.parameterContext
      payload := fun wire =>
        .app (.app (.const NativeWireData.consName) (NativeWireData.encode wire)) (.var 0)
      nativeType := fun _ => NativeWireData.dataType }

theorem required_registry_qualified :
    (requiredSpecification contract WireControls.interpretation).Satisfies registry := by
  apply (required_satisfies_iff _ _).mpr
  refine ⟨raw_qualified, fun _ => WireControls.parameter_native,
    fun _ => WireControls.parameter_meaning, ?_, fun _ => rfl⟩
  intro face
  cases face <;> constructor

/-- Four actual request forms run through the unchanged NIK dispatcher. -/
def request : (face : NIK.Face) →
    NIKServiceInvocation.Request (registry.serviceAt registry_qualified face)
  | .directDecision => .directDecision WireControls.actualWire
  | .nativeProof => .nativeProof WireControls.actualWire
      ("native-input", [.symbol "opaque-payload", .natural 7])
  | .nativeOperation => .nativeOperation WireControls.actualWire
  | .certificateBoundary => .certificateBoundary WireControls.actualWire
      ("native-input", [.symbol "opaque-payload", .natural 7])

def expected : NIK.Face → Wire
  | .nativeOperation => .application "wrapped" [WireControls.actualWire]
  | _ => WireControls.actualWire

theorem request_input (face : NIK.Face) : NIKServiceInvocation.InputAdmission (request face) := by
  cases face with
  | directDecision => exact .directDecision
  | nativeProof => exact .nativeProof
  | nativeOperation =>
      exact .nativeOperation
        ⟨"native-input", [.symbol "opaque-payload", .natural 7], rfl⟩
  | certificateBoundary => exact .certificateBoundary

theorem four_invocations (face : NIK.Face) :
    (NIKServiceInvocation.invoke (request face)).acceptedValue = some (expected face) := by
  cases face <;> rfl

theorem four_native_representations (face : NIK.Face) :
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext
      (WireControls.parameterPayload (expected face)) NativeWireData.dataType :=
  (registry.accepted_native_and_meaning registry_qualified face (request face)
    (request_input face) (four_invocations face)).1

/-- Evidence checking may reject a malformed witness for a meaningful claim. -/
theorem changed_witness_rejected :
    check WireControls.actualWire ("other-head", [.natural 7]) = false ∧
    WireControls.applicationTarget.Meaning WireControls.actualWire := by
  constructor
  · decide
  · exact ⟨"native-input", [.symbol "opaque-payload", .natural 7], rfl⟩

theorem operation_not_identity :
    (.application "wrapped" [WireControls.actualWire] : Wire) ≠ WireControls.actualWire := by
  decide

/-- Keeping the correct target and native representation does not excuse
silently replacing a required native-proof interface by a decision interface. -/
def wrongFace : Data targets WireControls.interpretation where
  service _ := WireControls.raw
  attachment := registry.attachment

theorem wrong_face_other_laws :
    ServicesQualified wrongFace ∧ NativeAdmitted wrongFace ∧ MeaningCompatible wrongFace :=
  ⟨fun _ => WireControls.qualified, fun _ => WireControls.parameter_native,
    fun _ => WireControls.parameter_meaning⟩

theorem wrong_face_not_qualified :
    ¬ (specification targets id WireControls.interpretation).Satisfies wrongFace := by
  intro qualifies
  have faces := ((satisfies_iff _ _).mp qualifies).1 .nativeProof
  cases faces

/-- One successful face test cannot qualify the untested required faces. -/
theorem incomplete_subfamily_passes :
    (specification (targets ∘ fun _ : Bool => NIK.Face.directDecision)
      (id ∘ fun _ : Bool => NIK.Face.directDecision) WireControls.interpretation).Satisfies
      (wrongFace.restrict (fun _ : Bool => NIK.Face.directDecision)) := by
  apply (satisfies_iff _ _).mpr
  exact ⟨fun _ => rfl, fun _ => WireControls.qualified,
    fun _ => WireControls.parameter_native, fun _ => WireControls.parameter_meaning⟩

/-- A deliberately unusable source is a negative control, not a service
implementation of the requested nonempty constructor domain. -/
def emptySource : AdmissionObject where
  Carrier := Empty
  Meaning _ := False

def emptyOperation : RawService.{0, 0} WireControls.applicationTarget :=
  .nativeOperation emptySource Empty.elim

theorem empty_operation_qualified : emptyOperation.Qualified := by
  intro input
  exact Empty.elim input

def vacuousSource : Data targets WireControls.interpretation where
  service face := match face with
    | .nativeOperation => emptyOperation
    | _ => raw face
  attachment := registry.attachment

theorem target_and_face_do_not_fix_inputs :
    (specification targets id WireControls.interpretation).Satisfies vacuousSource := by
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, ?_, fun _ => WireControls.parameter_native, fun _ => WireControls.parameter_meaning⟩
  · intro face
    cases face <;> rfl
  · intro face
    cases face with
    | nativeOperation => exact empty_operation_qualified
    | directDecision => exact raw_qualified .directDecision
    | nativeProof => exact raw_qualified .nativeProof
    | certificateBoundary => exact raw_qualified .certificateBoundary

theorem empty_source_cannot_meet_contract :
    ¬ (requiredSpecification contract WireControls.interpretation).Satisfies vacuousSource := by
  intro qualified
  have inputs := ((required_satisfies_iff _ _).mp qualified).2.2.2.1 .nativeOperation
  have sameSource : emptySource = WireControls.applicationTarget := inputs.operation_source
  have sameCarrier : Empty = Wire := congrArg AdmissionObject.Carrier sameSource
  exact Empty.elim (cast sameCarrier.symm WireControls.actualWire)

/-- An interpretation may validly denote a different native representation;
it still does not meet a caller's requested scoped payload contract. -/
def wrongSurface : Data targets WireControls.interpretation where
  service := registry.service
  attachment _ := WireControls.attachment OpaqueRelatorScopedComputation.Common.context

theorem changed_surface_other_laws :
    (specification targets id WireControls.interpretation).Satisfies wrongSurface := by
  apply (satisfies_iff _ _).mpr
  refine ⟨?_, raw_qualified, ?_, ?_⟩
  · intro face
    cases face <;> rfl
  · exact fun _ => WireControls.attachment_native _
      OpaqueRelatorScopedComputation.Common.context_formed
  · exact fun _ => WireControls.attachment_meaning _

theorem changed_surface_cannot_meet_contract :
    ¬ (requiredSpecification contract WireControls.interpretation).Satisfies wrongSurface := by
  intro qualified
  have surfaces := ((required_satisfies_iff _ _).mp qualified).2.2.2.2 .directDecision
  have count := congrArg (fun surface => surface.scope WireControls.actualWire) surfaces
  cases count

end Controls

#print axioms Data.accepted_native_and_meaning
#print axioms Data.accepted_substitution
#print axioms Data.satisfies_of_restrict
#print axioms Controls.registry_qualified
#print axioms required_satisfies_iff
#print axioms Controls.required_registry_qualified
#print axioms Controls.four_native_representations
#print axioms Controls.empty_source_cannot_meet_contract
#print axioms Controls.changed_surface_cannot_meet_contract
#print axioms Controls.changed_witness_rejected
#print axioms Controls.wrong_face_not_qualified
#print axioms Controls.incomplete_subfamily_passes
#print axioms Data.required_restrict_satisfies
#print axioms Data.required_satisfies_of_restrict

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry
