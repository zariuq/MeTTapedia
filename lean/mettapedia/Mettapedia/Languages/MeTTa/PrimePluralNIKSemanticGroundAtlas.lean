import Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas
import Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority

/-!
# A plural Prime semantic-ground atlas with a partial set-core lane

The existing lower atlas combines a complete atomless model decision with a
finite native-refinement checker.  This module extends its statement and
certificate languages with the independently meaningful Megalodon set-core
authority.

The old atlas enters exactly through a tagged prior lane.  Set-core formulas
enter `modelSound` with ordinary Mathdata proof certificates.  Their native
scope is the structurally covered reflexive-implication fragment, while their
meaning is validity in every selected extensional membership model.  Hence
the combined layer is sound but intentionally not semantically complete.

This is a proper set-core fragment, not the full HOTG preamble.  Evidence and
contract tags remain disjoint, and unsupported contract kinds fail closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

private abbrev priorStatement :=
  Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Statement

private abbrev priorCertificate :=
  Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Certificate

private abbrev priorLayer :=
  Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.layer

private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory

private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

/-! ## Extended statements, meanings, and evidence -/

/-- Retain every old lower statement and add an external set-core formula. -/
def Statement : Nat -> Type := fun level =>
  Sum (priorStatement level)
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula

/-- Evidence provenance remains visible at the plural boundary. -/
inductive Certificate where
  | prior (certificate : priorCertificate)
  | setCore
      (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf)

/-- Native scope is inherited on old claims.  The set-core lane exposes only
the fragment covered by its qualified native checker. -/
def Scope (claim : LowerContract Statement 1) : Prop :=
  match claim with
  | ⟨targetLevel, kind, .inl statement⟩ =>
      Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Meaning
        ⟨targetLevel, kind, statement⟩
  | ⟨_targetLevel, .modelSound, .inr formula⟩ =>
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.Covered formula
  | ⟨_targetLevel, _kind, .inr _formula⟩ => False

/-- Meaning is inherited on old claims.  Set-core `modelSound` means external
validity, which is strictly broader than the selected native scope. -/
def Meaning (claim : LowerContract Statement 1) : Prop :=
  match claim with
  | ⟨targetLevel, kind, .inl statement⟩ =>
      Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Meaning
        ⟨targetLevel, kind, statement⟩
  | ⟨_targetLevel, .modelSound, .inr formula⟩ =>
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.Valid formula
  | ⟨_targetLevel, _kind, .inr _formula⟩ => False

def checker : Checker (LowerContract Statement 1) Certificate where
  check claim certificate :=
    match claim, certificate with
    | ⟨targetLevel, kind, .inl statement⟩, .prior priorEvidence =>
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker.check
          ⟨targetLevel, kind, statement⟩ priorEvidence
    | ⟨_targetLevel, .modelSound, .inr formula⟩, .setCore proof =>
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.checker.check
          formula proof
    | _, _ => false

theorem checker_sound : checker.Sound Scope := by
  intro claim certificate accepted
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;> cases certificate <;>
    simp only [checker, Scope] at accepted ⊢
  all_goals first
    | exact
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker_sound
          _ _ accepted
    | exact
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.checker_authority.sound
          _ _ accepted
    | simp at accepted

theorem checker_complete : checker.CertificateComplete Scope := by
  intro claim inScope
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;>
    simp only [Scope] at inScope ⊢
  all_goals first
    | obtain ⟨certificate, accepted⟩ :=
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker_complete
          _ inScope
      exact ⟨.prior certificate, accepted⟩
    | obtain ⟨proof, accepted⟩ :=
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.checker_authority.complete
          _ inScope
      exact ⟨.setCore proof, accepted⟩

theorem scope_sound : forall claim, Scope claim -> Meaning claim := by
  intro claim inScope
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;>
    simp only [Scope, Meaning] at inScope ⊢
  all_goals first
    | exact inScope
    | exact
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.covered_valid
          inScope

theorem checker_authority : checker.Authority Scope where
  sound := checker_sound
  complete := checker_complete

def layer : BootstrapLayer Statement 1 where
  Certificate := Certificate
  Scope := Scope
  Meaning := Meaning
  scope_sound := scope_sound
  checker := checker
  scopeAuthority := checker_authority

/-! ## Exact inclusions -/

def liftPriorClaim
    (claim : LowerContract priorStatement 1) : LowerContract Statement 1 where
  targetLevel := claim.targetLevel
  kind := claim.kind
  statement := .inl claim.statement

def priorInclusion : AuthorityTranslation
    priorLayer.toAuthorityContract layer.toAuthorityContract where
  mapKind := id
  mapSignature := fun _signature => layer.toTheoryFamily.signatureOf ()
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind claim => liftPriorClaim claim
  mapCertificate := fun _kind certificate => .prior certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    rcases claim with ⟨targetLevel, contractKind, statement⟩
    rfl
  meaning_preserved := by
    intro kind claim meaningful
    cases kind
    rcases claim with ⟨targetLevel, contractKind, statement⟩
    exact meaningful

theorem priorInclusion_conservative :
    priorInclusion.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro kind claim inScope
    cases kind
    rcases claim with ⟨targetLevel, contractKind, statement⟩
    exact inScope
  meaning_reflecting := by
    intro kind claim meaningful
    cases kind
    rcases claim with ⟨targetLevel, contractKind, statement⟩
    exact meaningful

def setCoreModelClaim
    (formula :
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula) :
    LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .modelSound
  statement := .inr formula

def setCoreSourceSoundClaim
    (formula :
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula) :
    LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := .inr formula

/-- The external set-core authority enters the atlas at exactly the
`modelSound` contract kind. -/
def setCoreToAtlas : AuthorityTranslation
    setCoreContract layer.toAuthorityContract where
  mapKind := id
  mapSignature := fun _signature => layer.toTheoryFamily.signatureOf ()
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind formula => setCoreModelClaim formula
  mapCertificate := fun _kind proof => .setCore proof
  check_commutes := by
    intro kind formula proof
    cases kind
    rfl
  meaning_preserved := by
    intro kind formula meaningful
    cases kind
    exact meaningful

theorem setCoreToAtlas_conservative :
    setCoreToAtlas.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro kind formula inScope
    cases kind
    exact inScope
  meaning_reflecting := by
    intro kind formula meaningful
    cases kind
    exact meaningful

/-! ## Semantic incompleteness is retained honestly -/

/-- A valid quantified identity which is not a top-level reflexive
implication and therefore lies outside the current set-core proof scope. -/
def quantifiedIdentity :
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula :=
  .all (.imp (.predicate (.var 0)) (.predicate (.var 0)))

theorem quantifiedIdentity_valid :
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.Valid
      quantifiedIdentity := by
  intro model value predicateHolds
  exact predicateHolds

theorem quantifiedIdentity_not_covered :
    Not (Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.Covered
      quantifiedIdentity) := by
  rintro ⟨body, equality⟩
  cases equality

theorem quantifiedIdentity_meaning :
    Meaning (setCoreModelClaim quantifiedIdentity) :=
  quantifiedIdentity_valid

theorem quantifiedIdentity_not_scope :
    Not (Scope (setCoreModelClaim quantifiedIdentity)) :=
  quantifiedIdentity_not_covered

/-- One sound partial lane makes global derivability-to-semantics
qualification nonconservative.  The exact set-core inclusion itself remains
conservative. -/
theorem layer_qualification_not_conservative :
    Not ((qualification layer.toAuthorityContract).toTheoryTranslation.Conservative) :=
  qualification_not_conservative_of_semantic_gap
    layer.toAuthorityContract () (setCoreModelClaim quantifiedIdentity)
    quantifiedIdentity_meaning quantifiedIdentity_not_scope

/-! ## Positive and negative controls -/

namespace Canary

theorem setCore_identity_replays :
    checker.check
        (setCoreModelClaim
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (.setCore
          (Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
            Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula)) =
      true :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

theorem setCore_claim_rejects_prior_certificate
    (certificate : priorCertificate) :
    checker.check
        (setCoreModelClaim
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (.prior certificate) = false :=
  rfl

theorem prior_claim_rejects_setCore_certificate
    (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf) :
    checker.check
        (liftPriorClaim
          (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
            Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence))
        (.setCore proof) = false :=
  rfl

theorem setCore_sourceSound_rejected
    (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf) :
    checker.check
        (setCoreSourceSoundClaim
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (.setCore proof) = false :=
  rfl

end Canary

#print axioms checker_sound
#print axioms checker_complete
#print axioms scope_sound
#print axioms layer
#print axioms priorInclusion
#print axioms priorInclusion_conservative
#print axioms setCoreToAtlas
#print axioms setCoreToAtlas_conservative
#print axioms quantifiedIdentity_valid
#print axioms quantifiedIdentity_not_covered
#print axioms layer_qualification_not_conservative
#print axioms Canary.setCore_identity_replays
#print axioms Canary.setCore_claim_rejects_prior_certificate
#print axioms Canary.prior_claim_rejects_setCore_certificate
#print axioms Canary.setCore_sourceSound_rejected

end Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas
