import Mettapedia.Computability.ComputationalTrinityCrown
import Mettapedia.Languages.Megalodon.NIKNativeProof
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Megalodon as an independent computational-trinity authority

This module gives a nontrivial calibration of the intentional
computational-trinity crown against the real Megalodon `Mathdata` proof
kernel.  The operational face retains submitted proof occurrences, while the
logical and spatial faces expose their native Megalodon claims over a
one-point context.  Every material presentation remains an explicit GSLT.

The ambient section contains a source-shaped definition-conversion theorem
whose retained certificate is Megalodon's own proof term.  A second material
claim rejects that same submitted proof, so merely appearing in the material
presentation does not mint ambient authority.  The ambient scope is nonempty
but not global.

This is a Megalodon authority instance, not a HOTG adequacy claim.  A HOTG
instance requires its own independently verified source-faithfulness bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ComputationalTrinityAuthority

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.GSLT
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity
open Mettapedia.Computability.ComputationalTrinityCrown
open Mettapedia.Languages.Megalodon.NIKNativeProof
open Mettapedia.Languages.Megalodon.MathdataKernel

abbrev Context := CategoryTheory.Discrete Unit

private def here : Contextᵒᵖ :=
  Opposite.op (CategoryTheory.Discrete.mk Unit.unit)

/-- One submitted native proof occurrence.  The occurrence identifier is not
part of Megalodon's theoremhood judgment and must not disappear silently. -/
structure Submission where
  occurrence : Nat
  claim : Claim
  proof : Pf
deriving DecidableEq, Repr

def submissionFace : Face Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj Submission

/-- The currently exposed ambient claim face.  It is a presheaf even though
this calibration context has one object. -/
def claimFace : Face Context :=
  (CategoryTheory.Functor.const Contextᵒᵖ).obj Claim

/-- Forget the proof occurrence while retaining the submitted native claim. -/
def submissionClaim : submissionFace ⟶ claimFace where
  app _ := TypeCat.ofHom Submission.claim
  naturality := by
    intro source target substitution
    rfl

/-- The calibration is intentionally non-exact: the operational face retains
proof occurrences, while the current logic-to-space leg retains the complete
native claim. -/
def comparison : Comparison Context where
  program := submissionFace
  logic := claimFace
  space := claimFace
  programToLogic := submissionClaim
  logicToSpace := CategoryTheory.CategoryStruct.id claimFace
  programToSpace := submissionClaim
  coherence := rfl

def definitionSubmission (occurrence : Nat) : Submission where
  occurrence := occurrence
  claim := definitionConversionClaim
  proof := definitionConversionProof

/-- Operational fragment retaining every occurrence of the selected native
proof submission. -/
def definitionSubmissionFragment : Constraint submissionFace where
  holds _ submission :=
    submission.claim = definitionConversionClaim ∧
      submission.proof = definitionConversionProof
  map_closed := by
    intro source target substitution submission admitted
    exact admitted

/-- The nonempty fragment certified by the concrete native theorem. -/
def definitionFragment : Constraint claimFace where
  holds _ claim := claim = definitionConversionClaim
  map_closed := by
    intro source target substitution claim admitted
    exact admitted

/-- Identity interpretation of the explicit discrete claim presentation. -/
def claimMaterial : MaterialPresentation claimFace where
  presentation := GSLT.discrete Claim
  realize := CategoryTheory.CategoryStruct.id claimFace
  equation_sound := by
    intro context left right equivalent
    exact equivalent

/-- Identity interpretation of the explicit submitted-occurrence
presentation. -/
def submissionMaterial : MaterialPresentation submissionFace where
  presentation := GSLT.discrete Submission
  realize := CategoryTheory.CategoryStruct.id submissionFace
  equation_sound := by
    intro context left right equivalent
    exact equivalent

/-- Fragmentwise compatibility is proved without asserting global exactness
of the three complete faces. -/
def fragments : ComputationalTrinity.FragmentwiseComparison comparison where
  programFragment := definitionSubmissionFragment
  logicFragment := definitionFragment
  spaceFragment := definitionFragment
  programLogicCompatible := by
    intro context claim represented
    rcases represented with ⟨submission, admitted, rfl⟩
    exact admitted.1
  logicSpaceCompatible := by
    intro context claim represented
    rcases represented with ⟨sourceClaim, admitted, rfl⟩
    exact admitted

/-- The exact native Megalodon proof object for the selected ambient claim. -/
private def definitionWitness :
    proofSystem.ProofFibre definitionConversionClaim := by
  refine ⟨definitionConversionProof, ?_⟩
  exact (nativeKernel.correct _ _).1 definition_conversion_native_accepted

/-! ## A polymorphic ambient calibration -/

/-- A complete native query for Megalodon's accepted polymorphic theorem
reuse specimen.  This exercises `typeAll`, a retained known theorem, proof
type application, and proof term application. -/
def polymorphicReuseClaim : Claim where
  environment := polymorphicReuseEnvironment
  fuel := 16
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := polymorphicReuseGoal

/-- Megalodon's native checker accepts the retained polymorphic proof.  This
is a polymorphism calibration, not a claim of HOTG source adequacy. -/
theorem polymorphic_reuse_native_accepted :
    nativeKernel.toChecker.check polymorphicReuseClaim
      polymorphicReuseProof = true := by
  change checkProof polymorphicReuseEnvironment 16 0 [] []
    polymorphicReuseProof polymorphicReuseGoal = true
  unfold checkProof
  rw [show MathdataKernel.normalize polymorphicReuseEnvironment 16
    polymorphicReuseGoal = some polymorphicReuseGoal by
      simp [polymorphicReuseEnvironment, polymorphicReuseGoal,
        polymorphicReuseBody, polymorphicReuseType,
        MathdataKernel.normalize, deltaNormalize, Tm.normalize,
        Tm.normalizeOne]]
  simp [checkNormalizedProof, polymorphic_known_reuse_accepted]

/-- The singleton spatial fragment named by the polymorphic calibration. -/
def polymorphicFragment : Constraint claimFace where
  holds _ claim := claim = polymorphicReuseClaim
  map_closed := by
    intro source target substitution claim admitted
    exact admitted

private def polymorphicWitness :
    proofSystem.ProofFibre polymorphicReuseClaim := by
  refine ⟨polymorphicReuseProof, ?_⟩
  exact (nativeKernel.correct _ _).1 polymorphic_reuse_native_accepted

/-- A second ambient section, showing that the generic authority interface
does not depend on the simpler definition-conversion specimen. -/
def polymorphicAmbient : AmbientAuthoritySection claimFace where
  Claim := Claim
  proofSystem := proofSystem
  kernel := nativeKernel
  claimAt := fun _ claim => claim
  claim_natural := by
    intro source target substitution claim
    rfl
  scope := polymorphicFragment
  nonempty_scope := ⟨here, polymorphicReuseClaim, rfl⟩
  witness := by
    intro context claim inScope
    subst claim
    exact polymorphicWitness

/-- The polymorphic spatial point is checked through the same independent
ambient-authority interface. -/
theorem polymorphic_reuse_scoped_and_checked :
    polymorphicAmbient.kernel.toChecker.check polymorphicReuseClaim
      polymorphicReuseProof = true := by
  simpa [polymorphicAmbient, polymorphicWitness] using
    (polymorphicAmbient.checked here polymorphicReuseClaim rfl)

/-- A nonempty spatial section checked by the real Megalodon kernel. -/
def ambient : AmbientAuthoritySection claimFace where
  Claim := Claim
  proofSystem := proofSystem
  kernel := nativeKernel
  claimAt := fun _ claim => claim
  claim_natural := by
    intro source target substitution claim
    rfl
  scope := definitionFragment
  nonempty_scope := ⟨here, definitionConversionClaim, rfl⟩
  witness := by
    intro context claim inScope
    subst claim
    exact definitionWitness

/-- The concrete, non-exact calibration crown. -/
def calibrationCrown : AmbientCrown comparison where
  toCrown :=
    { fragments := fragments
      programMaterial := submissionMaterial
      logicMaterial := claimMaterial
      spaceMaterial := claimMaterial }
  ambient := ambient
  ambient_within_space := by
    intro context claim inScope
    exact inScope

/-- Positive control: the selected point is spatially admitted and its exact
native proof is accepted through the generic ambient-crown theorem. -/
theorem definition_conversion_scoped_and_checked :
    calibrationCrown.fragments.spaceFragment.holds here
        definitionConversionClaim ∧
      calibrationCrown.ambient.kernel.toChecker.check definitionConversionClaim
        definitionConversionProof = true := by
  simpa [calibrationCrown, ambient, definitionWitness] using
    (calibrationCrown.scoped_point_is_spatial_and_checked here
      definitionConversionClaim rfl)

/-- Positive and negative occurrence control: two distinct submitted proof
occurrences have the same logical and spatial claim. -/
theorem comparison_loses_submission_occurrence :
    comparison.LosesProgramInformation := by
  refine ⟨here, definitionSubmission 0, definitionSubmission 1, ?_, rfl⟩
  intro equal
  have occurrenceEqual := congrArg Submission.occurrence equal
  simp [definitionSubmission] at occurrenceEqual

/-- The rejected claim differs from the admitted definition-conversion claim.
The distinction follows from the independent kernel's opposite decisions,
not from inspecting record fields. -/
theorem opaque_claim_ne_definition :
    opaqueIdentityClaim ≠ definitionConversionClaim := by
  intro sameClaim
  have accepted :
      nativeKernel.toChecker.check opaqueIdentityClaim
        definitionConversionProof = true := by
    rw [sameClaim]
    exact definition_conversion_native_accepted
  rw [opaque_identity_native_rejected] at accepted
  exact Bool.noConfusion accepted

/-- Negative control: the ambient section is intentionally not a closed-world
claim covering every material Megalodon query. -/
theorem opaque_claim_not_in_ambient_scope :
    ¬ definitionFragment.holds here opaqueIdentityClaim := by
  exact opaque_claim_ne_definition

/-- A claim can be present in the inspectable material syntax while a
submitted native proof is rejected.  Materiality and authority are distinct
capabilities. -/
theorem material_point_does_not_force_certificate_acceptance :
    (∃ term : claimMaterial.presentation.Term,
      claimMaterial.realize.app here term = opaqueIdentityClaim) ∧
      nativeKernel.toChecker.check opaqueIdentityClaim
        definitionConversionProof = false := by
  constructor
  · exact ⟨opaqueIdentityClaim, rfl⟩
  · exact opaque_identity_native_rejected

/-! ## Nontrivial structural re-presentation -/

/-- A wrapper syntax used to test transport across a genuine change of term
carrier rather than reflexive equality. -/
structure WrappedClaim where
  value : Claim
deriving DecidableEq, Repr

def claimEquiv : Claim ≃ WrappedClaim where
  toFun := WrappedClaim.mk
  invFun := WrappedClaim.value
  left_inv := by intro claim; rfl
  right_inv := by intro claim; cases claim; rfl

/-- The wrapper changes syntax while preserving and reflecting both authored
equations and primitive steps of the discrete presentation. -/
def claimPresentationIso : StructuralIsomorphism
    (GSLT.discrete Claim) (GSLT.discrete WrappedClaim) where
  termEquiv := claimEquiv
  equiv_iff := by
    intro left right
    constructor
    · intro equal
      exact claimEquiv.injective equal
    · intro equal
      exact congrArg claimEquiv equal
  step_iff := by
    intro left right
    constructor <;> intro impossible <;> exact impossible.elim

def wrappedMaterial : MaterialPresentation claimFace :=
  claimMaterial.transport claimPresentationIso

/-- Structural re-presentation preserves the semantic claim exactly. -/
theorem wrapped_claim_realizes (claim : Claim) :
    wrappedMaterial.realize.app here (WrappedClaim.mk claim) = claim := by
  change (claimMaterial.transport claimPresentationIso).realize.app here
      (claimPresentationIso.termEquiv claim) =
    claimMaterial.realize.app here claim
  exact MaterialPresentation.transport_realize_forward claimMaterial
    claimPresentationIso here claim

#print axioms definition_conversion_scoped_and_checked
#print axioms comparison_loses_submission_occurrence
#print axioms opaque_claim_ne_definition
#print axioms opaque_claim_not_in_ambient_scope
#print axioms material_point_does_not_force_certificate_acceptance
#print axioms polymorphic_reuse_native_accepted
#print axioms polymorphic_reuse_scoped_and_checked
#print axioms wrapped_claim_realizes

end Mettapedia.Languages.Megalodon.ComputationalTrinityAuthority
