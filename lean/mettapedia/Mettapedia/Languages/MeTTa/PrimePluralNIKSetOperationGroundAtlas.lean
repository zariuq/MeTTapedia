import Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification
import Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas
import Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority

/-!
# A Prime bootstrap atlas with a selected set-operation lane

This module conservatively extends the existing semantic-ground atlas with a
separate external authority for empty set, big union, and powerset.  Earlier
atomless, native-refinement, and set-core statements retain their exact tagged
representations.  Operation formulas enter only the `modelSound` contract
kind, with ordinary Mathdata proof certificates and independent extensional
model validity.

The selected operation scope is sound but intentionally incomplete.  A valid
formula outside the five authored rules remains meaningful without acquiring
a native certificate, and unsupported contract kinds fail closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

private abbrev priorStatement :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.Statement

private abbrev priorCertificate :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.Certificate

private abbrev priorLayer :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.layer

private abbrev operationTheory :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.theory

private abbrev operationContract :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.contract

/-! ## Extended statements, meanings, and evidence -/

def Statement : Nat -> Type := fun level =>
  Sum (priorStatement level)
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.ClosedFormula

inductive Certificate where
  | prior (certificate : priorCertificate)
  | setOperation
      (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf)

def Scope (claim : LowerContract Statement 1) : Prop :=
  match claim with
  | ⟨targetLevel, kind, .inl statement⟩ =>
      Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.Scope
        ⟨targetLevel, kind, statement⟩
  | ⟨_targetLevel, .modelSound, .inr formula⟩ =>
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Covered
        formula
  | ⟨_targetLevel, _kind, .inr _formula⟩ => False

def Meaning (claim : LowerContract Statement 1) : Prop :=
  match claim with
  | ⟨targetLevel, kind, .inl statement⟩ =>
      Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.Meaning
        ⟨targetLevel, kind, statement⟩
  | ⟨_targetLevel, .modelSound, .inr formula⟩ =>
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Valid
        formula
  | ⟨_targetLevel, _kind, .inr _formula⟩ => False

def checker : Checker (LowerContract Statement 1) Certificate where
  check claim certificate :=
    match claim, certificate with
    | ⟨targetLevel, kind, .inl statement⟩, .prior priorEvidence =>
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.checker.check
          ⟨targetLevel, kind, statement⟩ priorEvidence
    | ⟨_targetLevel, .modelSound, .inr formula⟩, .setOperation proof =>
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.checker.check
          formula proof
    | _, _ => false

theorem checker_sound : checker.Sound Scope := by
  intro claim certificate accepted
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;> cases certificate <;>
    simp only [checker, Scope] at accepted ⊢
  all_goals first
    | exact
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.checker_sound
          _ _ accepted
    | exact
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.checker_authority.sound
          _ _ accepted
    | simp at accepted

theorem checker_complete : checker.CertificateComplete Scope := by
  intro claim inScope
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;>
    simp only [Scope] at inScope ⊢
  all_goals first
    | obtain ⟨certificate, accepted⟩ :=
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.checker_complete
          _ inScope
      exact ⟨.prior certificate, accepted⟩
    | obtain ⟨proof, accepted⟩ :=
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.checker_authority.complete
          _ inScope
      exact ⟨.setOperation proof, accepted⟩

theorem scope_sound : forall claim, Scope claim -> Meaning claim := by
  intro claim inScope
  rcases claim with ⟨targetLevel, kind, statement⟩
  cases statement <;> cases kind <;>
    simp only [Scope, Meaning] at inScope ⊢
  all_goals first
    | exact
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.scope_sound
          _ inScope
    | exact
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.covered_valid
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
  signature_commutes := by
    intro kind
    cases kind
    rfl
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

def operationModelClaim
    (formula : operationTheory.Claim ()) : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .modelSound
  statement := .inr formula

def operationSourceSoundClaim
    (formula : operationTheory.Claim ()) : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := .inr formula

def operationToAtlas : AuthorityTranslation
    operationContract layer.toAuthorityContract where
  mapKind := id
  mapSignature := fun _signature => layer.toTheoryFamily.signatureOf ()
  signature_commutes := by
    intro kind
    cases kind
    rfl
  mapClaim := fun _kind formula => operationModelClaim formula
  mapCertificate := fun _kind proof => .setOperation proof
  check_commutes := by
    intro kind formula proof
    cases kind
    rfl
  meaning_preserved := by
    intro kind formula meaningful
    cases kind
    exact meaningful

theorem operationToAtlas_conservative :
    operationToAtlas.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro kind formula inScope
    cases kind
    exact inScope
  meaning_reflecting := by
    intro kind formula meaningful
    cases kind
    exact meaningful

/-! ## The selected semantic gap remains visible -/

theorem identity_meaning :
    Meaning (operationModelClaim
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula) :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_valid

theorem identity_not_scope :
    Not (Scope (operationModelClaim
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)) :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_not_covered

theorem layer_qualification_not_conservative :
    Not ((qualification layer.toAuthorityContract).toTheoryTranslation.Conservative) :=
  qualification_not_conservative_of_semantic_gap
    layer.toAuthorityContract ()
    (operationModelClaim
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)
    identity_meaning identity_not_scope

/-! ## Positive and negative controls -/

namespace Canary

theorem unionIntroduction_replays :
    checker.check
      (operationModelClaim
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (.setOperation
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.AxiomTag.unionIntro.proof) =
      true :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem operation_claim_rejects_prior_certificate
    (certificate : priorCertificate) :
    checker.check
      (operationModelClaim
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (.prior certificate) = false :=
  rfl

theorem prior_claim_rejects_operation_certificate
    (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf) :
    checker.check
      (liftPriorClaim
        (Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.setCoreModelClaim
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula))
      (.setOperation proof) = false :=
  rfl

theorem operation_sourceSound_rejected
    (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf) :
    checker.check
      (operationSourceSoundClaim
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (.setOperation proof) = false :=
  rfl

theorem universalMembership_not_meaning :
    Not (Meaning (operationModelClaim
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership)) :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership_not_valid

end Canary

#print axioms checker_sound
#print axioms checker_complete
#print axioms scope_sound
#print axioms layer
#print axioms priorInclusion
#print axioms priorInclusion_conservative
#print axioms operationToAtlas
#print axioms operationToAtlas_conservative
#print axioms identity_meaning
#print axioms identity_not_scope
#print axioms layer_qualification_not_conservative
#print axioms Canary.unionIntroduction_replays
#print axioms Canary.operation_claim_rejects_prior_certificate
#print axioms Canary.prior_claim_rejects_operation_certificate
#print axioms Canary.operation_sourceSound_rejected
#print axioms Canary.universalMembership_not_meaning

end Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas
