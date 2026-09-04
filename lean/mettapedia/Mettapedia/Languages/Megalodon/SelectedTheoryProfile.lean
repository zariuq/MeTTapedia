import Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView
import Mettapedia.Languages.Megalodon.NIKNativeProof

/-!
# Megalodon selected theories as NIK authority profiles

Megalodon's Mathdata kernel is shared by several selected theories.  The
selected environment is therefore authority data, not an incidental field to
erase.  This module factors the existing native claim into a theory-profile
index and a profile-local query, then reconstructs the same Mathdata decision
inside a dependent NIK authority family.

The canonical service below remains an intrinsic native-proof kernel.  The
later `AuthorityContract` is a separate certificate-facing projection for
clients that actually need a packed external boundary; it is not the identity
of NIK or of the Mathdata kernel.

The resulting profile family does not assert HOTG validity or identify the
Egal, Mizar, HF, and HOAS theories.  Such claims require source-theory
admission and semantic adequacy theorems.  Here the exact scope is only native
Mathdata theoremhood in the selected finite environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SelectedTheoryProfile

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIK
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.NIKNativeProof

/-- The part of a native Megalodon query that is local to a selected theory
environment. -/
structure ProfileClaim where
  fuel : Nat
  typeDepth : Nat
  termContext : List Tp
  proofContext : List Tm
  proposition : Tm
deriving DecidableEq, Repr

/-- Attach the selected theory environment to a profile-local query. -/
def attach (environment : Environment) (claim : ProfileClaim) : Claim where
  environment := environment
  fuel := claim.fuel
  typeDepth := claim.typeDepth
  termContext := claim.termContext
  proofContext := claim.proofContext
  proposition := claim.proposition

/-- Forget only the selected environment, retaining every local query field. -/
def detach (claim : Claim) : ProfileClaim where
  fuel := claim.fuel
  typeDepth := claim.typeDepth
  termContext := claim.termContext
  proofContext := claim.proofContext
  proposition := claim.proposition

/-- A native Megalodon claim is exactly a selected environment paired with a
profile-local query. -/
def claimEquiv : (Sigma fun _ : Environment => ProfileClaim) ≃ Claim where
  toFun := fun selected => attach selected.1 selected.2
  invFun := fun claim => ⟨claim.environment, detach claim⟩
  left_inv := by
    rintro ⟨environment, claim⟩
    cases claim
    rfl
  right_inv := by
    intro claim
    cases claim
    rfl

@[simp] theorem claimEquiv_apply (environment : Environment)
    (claim : ProfileClaim) :
    claimEquiv ⟨environment, claim⟩ = attach environment claim :=
  rfl

@[simp] theorem attach_detach (claim : Claim) :
    attach claim.environment (detach claim) = claim := by
  cases claim
  rfl

/-- Native theoremhood in one selected Mathdata environment.  This is an
intensional proof-object scope, not yet an external model-theoretic meaning. -/
def NativeTheoremScope (environment : Environment)
    (claim : ProfileClaim) : Prop :=
  exists proof : Pf, Judges proof (attach environment claim)

/-! ## Native selected-theory service -/

/-- Megalodon's intrinsic proof system specialized to one selected theory
environment. -/
def profileProofSystem (environment : Environment) :
    NativeProofSystem ProfileClaim where
  ProofObject := Pf
  Judges proof claim :=
    NIKNativeProof.Judges proof (attach environment claim)

/-- Specialization of the executable Mathdata proof kernel preserves its exact
native proof judgment. -/
def profileNativeKernel (environment : Environment) :
    NativeProofKernel (profileProofSystem environment) where
  decide claim proof :=
    NIKNativeProof.nativeKernel.decide (attach environment claim) proof
  correct claim proof :=
    NIKNativeProof.nativeKernel.correct (attach environment claim) proof

/-- Intrinsic theoremhood target for one selected environment. -/
def profileTarget (environment : Environment) : AdmissionObject where
  Carrier := ProfileClaim
  Meaning := fun claim =>
    Nonempty ((profileProofSystem environment).ProofFibre claim)

/-- The selected Mathdata environment is served directly by its native proof
kernel. -/
def nativeService (environment : Environment) :
    Mettapedia.GSLT.LanguageDef.NIK.Service (profileTarget environment) :=
  .nativeProof (profileProofSystem environment)
    (profileNativeKernel environment) (fun _ => Iff.rfl)

@[simp] theorem nativeService_has_no_external_boundary
    (environment : Environment) :
    Mettapedia.GSLT.LanguageDef.NIK.Service.hasExternalCertificateBoundary
      (nativeService environment) = false :=
  rfl

/-- The selected-theory family exposes the environment as the theory
signature/profile index rather than burying it inside every claim. -/
def theory : TheoryFamily Environment where
  Signature := Environment
  signatureOf := id
  Claim := fun _ => ProfileClaim
  Scope := NativeTheoremScope
  Meaning := NativeTheoremScope
  scope_sound := by
    intro environment claim theoremhood
    exact theoremhood

/-- The same Mathdata kernel specialized to one selected environment. -/
def checker (environment : Environment) : Checker ProfileClaim Pf where
  check claim proof := nativeKernel.toChecker.check (attach environment claim) proof

/-- Specializing the existing native proof kernel at an environment remains
exact for that profile's native theorem scope. -/
theorem checker_authority (environment : Environment) :
    (checker environment).Authority (NativeTheoremScope environment) where
  sound := by
    intro claim proof accepted
    exact ⟨proof,
      (nativeKernel.correct (attach environment claim) proof).mp accepted⟩
  complete := by
    intro claim theoremhood
    obtain ⟨proof, judged⟩ := theoremhood
    exact ⟨proof,
      (nativeKernel.correct (attach environment claim) proof).mpr judged⟩

/-- An external proof-object contract for clients that require a packed
certificate-facing projection of the selected native theory. -/
def contract : AuthorityContract theory where
  Certificate := fun _ => Pf
  checker := checker
  scopeAuthority := checker_authority

/-- The external-certificate family obtained from the separated theory and
boundary contract. -/
def family : AuthorityFamily Environment :=
  contract.toAuthorityFamily

/-- The certificate-facing profile projection does not change the Mathdata
decision. -/
@[simp] theorem profile_check_eq_native (environment : Environment)
    (claim : ProfileClaim) (proof : Pf) :
    (family.checker environment).check claim proof =
      nativeKernel.toChecker.check (attach environment claim) proof :=
  rfl

/-! ## Definition-sensitive positive and negative controls -/

def definitionClaim : ProfileClaim :=
  detach definitionConversionClaim

def opaqueClaim : ProfileClaim :=
  detach opaqueIdentityClaim

@[simp] theorem definitionClaim_attaches :
    attach definitionConversionEnvironment definitionClaim =
      definitionConversionClaim :=
  rfl

@[simp] theorem opaqueClaim_attaches :
    attach opaqueIdentityEnvironment opaqueClaim = opaqueIdentityClaim :=
  rfl

/-- The local queries coincide; the selected theory environment is the only
material difference. -/
theorem definitionClaim_eq_opaqueClaim : definitionClaim = opaqueClaim :=
  rfl

/-- Positive control: the definition-bearing profile accepts the native
proof. -/
theorem definition_profile_accepts :
    (family.checker definitionConversionEnvironment).check definitionClaim
      definitionConversionProof = true := by
  simpa using definition_conversion_native_accepted

/-- Negative control: the same query and proof are rejected by the profile
where the needed definition is opaque. -/
theorem opaque_profile_rejects :
    (family.checker opaqueIdentityEnvironment).check opaqueClaim
      definitionConversionProof = false := by
  simpa using opaque_identity_native_rejected

theorem opaqueEnvironment_ne_definitionEnvironment :
    opaqueIdentityEnvironment ≠ definitionConversionEnvironment := by
  decide

/-- Same-profile evidence enters the packed external-certificate dispatcher
unchanged. -/
theorem packed_definition_profile_accepts :
    family.packedChecker.check
        ⟨definitionConversionEnvironment, definitionClaim⟩
        ⟨definitionConversionEnvironment, definitionConversionProof⟩ = true := by
  rw [family.packedChecker_sameKind]
  exact definition_profile_accepts

/-- A proof tagged as belonging to the opaque profile cannot be replayed as
evidence for the definition-bearing profile.  An authored profile view is
required even though both certificate payloads are `Pf`. -/
theorem packed_wrong_profile_rejected :
    family.packedChecker.check
        ⟨definitionConversionEnvironment, definitionClaim⟩
        ⟨opaqueIdentityEnvironment, definitionConversionProof⟩ = false := by
  exact family.packedChecker_rejects_wrongKind
    opaqueEnvironment_ne_definitionEnvironment definitionClaim
      definitionConversionProof

/-! ## The exact current view boundary -/

/-- Every selected environment has its identity proof-carrying view. -/
def identityView (environment : Environment) :
    Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView.AuthorityView
      contract environment environment :=
  Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView.AuthorityView.identity
    environment

/-- Environment equality transports profile-local evidence without changing
the native decision.  Nontrivial imports or renamings require separate
monotonicity/adequacy theorems and are intentionally not inferred from the
shared Mathdata representation. -/
def viewOfEnvironmentEq {source target : Environment}
    (equalEnvironment : source = target) :
    Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView.AuthorityView
      contract source target := by
  subst target
  exact identityView source

#print axioms claimEquiv
#print axioms checker_authority
#print axioms profileNativeKernel
#print axioms nativeService
#print axioms nativeService_has_no_external_boundary
#print axioms definition_profile_accepts
#print axioms opaque_profile_rejects
#print axioms packed_wrong_profile_rejected

end Mettapedia.Languages.Megalodon.SelectedTheoryProfile
