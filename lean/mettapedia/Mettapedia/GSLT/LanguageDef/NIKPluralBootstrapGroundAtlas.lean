import Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding
import Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification

/-!
# A plural bootstrap atlas for model soundness and native refinement

No single lower authority needs to impersonate every kind of bootstrap
evidence.  This level-one atlas combines two already qualified but logically
different grounds:

* atomless Boolean first-order decision supplies `modelSound`; and
* finite truth-table comparison supplies `nativeRefines`.

The statement and certificate languages are tagged.  A model certificate
cannot certify a refinement claim, a refinement certificate cannot certify a
model claim, and every unsupported contract kind fails closed.  The combined
layer is therefore plural without collapsing either semantic meaning or
evidence provenance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge
open Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification

/-! ## Tagged statements and evidence -/

/-- Every level may discuss either an atomless first-order formula or a finite
native-refinement claim. -/
def Statement : Nat -> Type := fun _level =>
  Sum (Formula 0) RefinementMetaAuthority.Claim

/-- Evidence provenance is retained at the bootstrap boundary. -/
inductive Certificate where
  | semanticDecision
  | refinementEvidence (certificate : RefinementMetaAuthority.Certificate)
  deriving DecidableEq

/-- Only well-tagged model-soundness and native-refinement statements have
meaning in this selected atlas. -/
def Meaning (claim : LowerContract Statement 1) : Prop :=
  match claim.kind, claim.statement with
  | .modelSound, .inl formula => ColdMeaning formula
  | .nativeRefines, .inr refinement =>
      RefinementMetaAuthority.Refines refinement
  | _, _ => False

/-- The two qualified lower kernels are dispatched by both contract kind and
statement tag.  The evidence tag must agree as well. -/
def checker : Checker (LowerContract Statement 1) Certificate where
  check claim certificate :=
    match claim.kind, claim.statement, certificate with
    | .modelSound, .inl formula, .semanticDecision =>
        decisionKernel.decide formula
    | .nativeRefines, .inr refinement, .refinementEvidence evidence =>
        RefinementMetaAuthority.checker.check refinement evidence
    | _, _, _ => false

theorem checker_sound : checker.Sound Meaning := by
  intro claim certificate accepted
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases kind <;> cases statement <;> cases certificate <;>
    simp only [checker, Meaning] at accepted ⊢
  all_goals first
    | exact RefinementMetaAuthority.checker_sound _ _ accepted
    | exact
        (AtomlessBooleanFirstOrderNIKAuthority.decisionKernel.correct _).mp
          accepted
    | simp at accepted

theorem checker_complete : checker.CertificateComplete Meaning := by
  intro claim meaningful
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases kind <;> cases statement <;>
    simp only [Meaning] at meaningful
  · obtain ⟨evidence, accepted⟩ :=
      RefinementMetaAuthority.checker_complete _ meaningful
    exact ⟨.refinementEvidence evidence, accepted⟩
  · refine ⟨.semanticDecision, ?_⟩
    exact (decisionKernel.correct _).mpr meaningful

theorem checker_authority : checker.Authority Meaning where
  sound := checker_sound
  complete := checker_complete

def layer : BootstrapLayer Statement 1 where
  Certificate := Certificate
  Scope := Meaning
  Meaning := Meaning
  scope_sound := fun _claim meaningful => meaningful
  checker := checker
  scopeAuthority := checker_authority

/-! ## Exact semantic qualification of the selected atlas -/

/-- This selected atlas is semantically complete by construction: its native
scope is exactly the disjoint union of the two independently justified
meaning predicates. -/
theorem layer_semantically_complete :
    SemanticallyComplete layer.toTheoryFamily := by
  intro _kind _claim meaningful
  exact meaningful

/-- Reattaching the selected meanings to the derivability shadow is
conservative for this atlas.  This uses semantic completeness; it is not a
generic consequence of checker soundness. -/
theorem layer_qualification_conservative :
    (qualification layer.toAuthorityContract).toTheoryTranslation.Conservative :=
  (qualification_conservative_iff layer.toAuthorityContract).mpr
    layer_semantically_complete

/-- Semantic qualification preserves the exact plural checker replay. -/
theorem layer_qualification_check_commutes
    (claim : LowerContract Statement 1) (certificate : Certificate) :
    layer.checker.check claim certificate =
      ((derivabilityContract layer.toAuthorityContract).checker ()).check
        claim certificate :=
  rfl

/-! ## Selected claims -/

def modelClaim (formula : Formula 0) : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .modelSound
  statement := .inl formula

def refinementClaim (refinement : RefinementMetaAuthority.Claim) :
    LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .nativeRefines
  statement := .inr refinement

def sourceSoundClaim (formula : Formula 0) : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := .inl formula

/-! ## Positive and negative controls -/

theorem gunk_modelSound_accepted :
    checker.check (modelClaim gunkSentence) .semanticDecision = true := by
  exact
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding.gunk_modelSound_accepted

theorem identity_nativeRefines_accepted
    (implementation : RefinementMetaAuthority.BinaryChecker) :
    checker.check
      (refinementClaim (RefinementMetaAuthority.identityClaim implementation))
      (.refinementEvidence
        (RefinementMetaAuthority.computedCertificate
          (RefinementMetaAuthority.identityClaim implementation))) = true :=
  RefinementMetaAuthority.identity_certificate_accepted implementation

/-- A refinement receipt cannot be replayed as model evidence. -/
theorem model_claim_rejects_refinement_certificate
    (evidence : RefinementMetaAuthority.Certificate) :
    checker.check (modelClaim gunkSentence) (.refinementEvidence evidence) =
      false :=
  rfl

/-- The semantic-decision receipt cannot be replayed as refinement evidence. -/
theorem refinement_claim_rejects_semantic_certificate
    (refinement : RefinementMetaAuthority.Claim) :
    checker.check (refinementClaim refinement) .semanticDecision = false :=
  rfl

/-- Changing only the contract kind does not allow model evidence to claim
source-calculus soundness. -/
theorem gunk_sourceSound_rejected :
    checker.check (sourceSoundClaim gunkSentence) .semanticDecision = false :=
  rfl

/-- Any meaningful claim exposes which of the two selected contract kinds
licensed it. -/
theorem meaningful_kind_selected (claim : LowerContract Statement 1)
    (meaningful : Meaning claim) :
    claim.kind = .modelSound ∨ claim.kind = .nativeRefines := by
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases kind <;> cases statement <;> simp [Meaning] at meaningful ⊢

/-- The plural evidence carrier is not thin: provenance survives even when
the semantic boundary uses a unit receipt. -/
theorem certificates_not_subsingleton : ¬ Subsingleton Certificate := by
  intro thin
  have impossible :
      Certificate.semanticDecision =
        Certificate.refinementEvidence
          (RefinementMetaAuthority.computedCertificate
            RefinementMetaAuthority.badClaim) :=
    thin.elim _ _
  cases impossible

#print axioms checker_sound
#print axioms checker_complete
#print axioms checker_authority
#print axioms layer
#print axioms layer_semantically_complete
#print axioms layer_qualification_conservative
#print axioms layer_qualification_check_commutes
#print axioms gunk_modelSound_accepted
#print axioms identity_nativeRefines_accepted
#print axioms model_claim_rejects_refinement_certificate
#print axioms refinement_claim_rejects_semantic_certificate
#print axioms gunk_sourceSound_rejected
#print axioms meaningful_kind_selected
#print axioms certificates_not_subsingleton

end Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas
