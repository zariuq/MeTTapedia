import Mettapedia.GSLT.LanguageDef.NIKAdmissionDoctrineCrown
import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission

/-!
# Native Inference Kernel services

This is the canonical entry point for the Native Inference Kernel (NIK)
doctrine.  NIK selects, hosts, composes, and revises the most appropriate
semantically admitted native calculus for each request.  It is not a synonym
for certificate replay.

One independently stated semantic target may be served in four different
ways:

* a direct decision kernel decides its judgment;
* a native proof kernel checks the guest calculus's intrinsic proof objects;
* a native operation constructs, transforms, computes, or searches while
  preserving the target meaning by construction;
* an external certificate boundary checks untrusted evidence when that is the
  appropriate trust or computability boundary.

These faces are capabilities, not a global priority list.  The
request-indexed `MaximalNativeCalculus` order compares only admitted services
with the same semantic contract and only by capabilities relevant to that
request.  An external certificate boundary is therefore one possible NIK
service, while the generic OSLF/NTT replay machinery is a fallback for guests
without a stronger admitted native calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIK

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

universe uArtifact uEvidence uIndex uCapability

/-! ## One semantic target, four non-collapsed service faces -/

/-- A semantically exact NIK service for one independently stated target.

`nativeOperation` includes correct-by-construction term and proof
construction, type and set computation, native inference/search, and admitted
transformations.  Its executable arrow contains its preservation law.
`certificateBoundary` is reserved for a genuinely external evidence boundary;
it is not the definition of the other three constructors. -/
inductive Service
    (target : AdmissionObject.{uArtifact}) : Type (max (uArtifact + 1) (uEvidence + 1))
  | directDecision
      (kernel : Checker.DecisionKernel target.Carrier target.Meaning)
  | nativeProof
      (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
      (kernel : NativeProofKernel guest)
      (meaning_exact : ∀ claim,
        target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
  | nativeOperation
      (source : AdmissionObject.{uArtifact})
      (operation : source ⟶ target)
  | certificateBoundary
      (Certificate : Type uEvidence)
      (checker : Checker target.Carrier Certificate)
      (authority : checker.Authority target.Meaning)

namespace Service

variable {target : AdmissionObject.{uArtifact}}

/-- Only an explicit external boundary exposes a separate submitted
certificate language.  Native proof objects remain objects of their guest
calculus; native operations receive their own typed source values. -/
def ExternalCertificate : Service.{uArtifact, uEvidence} target → Type uEvidence
  | .certificateBoundary Certificate _ _ => Certificate
  | _ => PEmpty

/-- Public discriminator for the external trust-boundary capability. -/
def hasExternalCertificateBoundary :
    Service.{uArtifact, uEvidence} target → Bool
  | .certificateBoundary .. => true
  | _ => false

@[simp] theorem directDecision_has_no_external_boundary
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning) :
    hasExternalCertificateBoundary (Service.directDecision kernel) = false :=
  rfl

@[simp] theorem nativeProof_has_no_external_boundary
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (meaning_exact : ∀ claim,
      target.Meaning claim ↔ Nonempty (guest.ProofFibre claim)) :
    hasExternalCertificateBoundary
      (Service.nativeProof guest kernel meaning_exact) = false :=
  rfl

@[simp] theorem nativeOperation_has_no_external_boundary
    (source : AdmissionObject.{uArtifact}) (operation : source ⟶ target) :
    hasExternalCertificateBoundary
      (Service.nativeOperation source operation) = false :=
  rfl

@[simp] theorem certificateBoundary_is_external
    (Certificate : Type uEvidence)
    (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning) :
    hasExternalCertificateBoundary
      (Service.certificateBoundary Certificate checker authority) = true :=
  rfl

/-- A native operation constructs a meaningful target whenever its typed
source input is meaningful.  There is no certificate argument to this
execution or theorem. -/
theorem nativeOperation_preserves
    {source : AdmissionObject.{uArtifact}}
    (operation : source ⟶ target)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning (operation.run input) :=
  operation.preserves input meaningful

/-- A native proof kernel decides exactly its intrinsic proof judgment, and
the service's adequacy field connects that judgment to the common semantic
target. -/
theorem nativeProof_accepts_iff_meaning
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (meaning_exact : ∀ claim,
      target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) :
    target.Meaning claim ↔
      ∃ proof, kernel.decide claim proof = true := by
  rw [meaning_exact]
  constructor
  · rintro ⟨⟨proof, judged⟩⟩
    exact ⟨proof, (kernel.correct claim proof).mpr judged⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨⟨proof, (kernel.correct claim proof).mp accepted⟩⟩

/-- An external boundary is semantically exact precisely through existence of
accepted external evidence. -/
theorem certificateBoundary_accepts_iff_meaning
    (Certificate : Type uEvidence)
    (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) :
    target.Meaning claim ↔
      ∃ certificate, checker.check claim certificate = true :=
  authority.meaning_iff_exists_certificate claim

/-! ## Maximal-native selection produces a native service directly -/

/-- Reify a strongest request-local admitted operation as a native NIK
service.  Selection adds neither an external certificate type nor a replay
call. -/
def ofStrongest
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject.{uArtifact}}
    {family : RecognizedFamily.{uIndex, uCapability, uArtifact}
      Index source target}
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple) :
    Service.{uArtifact, uEvidence} target :=
  .nativeOperation source (request.strongestOperation selection)

@[simp] theorem ofStrongest_has_no_external_boundary
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject.{uArtifact}}
    {family : RecognizedFamily.{uIndex, uCapability, uArtifact}
      Index source target}
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple) :
    hasExternalCertificateBoundary
      (ofStrongest request selection : Service.{uArtifact, uEvidence} target) =
        false :=
  rfl

end Service

/-! ## Nondegenerate separation controls -/

namespace Canary

open NIKMetalogic.AdmissionCanary

/-- Direct decision of the positive-natural semantic fibre. -/
def nonzeroDecision :
    Checker.DecisionKernel Nat (fun value => value ≠ 0) where
  decide value := decide (value ≠ 0)
  correct value := by simp

def direct : Service positiveNaturals :=
  .directDecision nonzeroDecision

/-- A genuine nonidentity native construction on the same semantic fibre. -/
def native : Service positiveNaturals :=
  .nativeOperation positiveNaturals successor

/-- The same semantic target exposed at an external evidence boundary. -/
def boundary : Service positiveNaturals :=
  .certificateBoundary Unit nonzeroDecision.toChecker nonzeroDecision.authority

/-- Native execution performs the original meaning-preserving construction. -/
theorem native_constructs_meaning :
    successor.run (1 : Nat) = (2 : Nat) ∧
      positiveNaturals.Meaning (successor.run (1 : Nat)) := by
  apply And.intro rfl
  apply successor.preserves (1 : Nat)
  change (1 : Nat) ≠ 0
  decide

/-- No external certificate can even be supplied to the native-operation
face. -/
theorem native_has_no_external_certificate :
    IsEmpty (Service.ExternalCertificate native) := by
  change IsEmpty PEmpty
  infer_instance

/-- The external-boundary face really has a submitted certificate fibre. -/
theorem boundary_has_external_certificate :
    Nonempty (Service.ExternalCertificate boundary) :=
  ⟨()⟩

/-- Native construction and external certificate checking are different NIK
service constructors even when they serve the same semantic target. -/
theorem native_ne_boundary : native ≠ boundary := by
  intro equal
  cases equal

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus.Canary
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission.Canary

/-- The existing strongest-calculus canary enters the canonical NIK service
as the selected native operation and still runs the original nonidentity map. -/
def selectedNative : Service positiveNaturals :=
  Service.ofStrongest secondCapabilityRequest strongestLinearSelection

theorem selectedNative_runs_original_operation :
    (secondCapabilityRequest.strongestOperation
      strongestLinearSelection).run (1 : Nat) = (3 : Nat) :=
  rfl

theorem selectedNative_has_no_external_certificate :
    IsEmpty (Service.ExternalCertificate selectedNative) := by
  change IsEmpty PEmpty
  infer_instance

end Canary

#print axioms Service.nativeOperation_preserves
#print axioms Service.nativeProof_accepts_iff_meaning
#print axioms Service.certificateBoundary_accepts_iff_meaning
#print axioms Service.ofStrongest_has_no_external_boundary
#print axioms Canary.native_constructs_meaning
#print axioms Canary.native_has_no_external_certificate
#print axioms Canary.boundary_has_external_certificate
#print axioms Canary.native_ne_boundary
#print axioms Canary.selectedNative_runs_original_operation
#print axioms Canary.selectedNative_has_no_external_certificate

end Mettapedia.GSLT.LanguageDef.NIK
