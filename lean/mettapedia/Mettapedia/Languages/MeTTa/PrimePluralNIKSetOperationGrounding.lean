import Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding
import Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas
import Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist

/-!
# Shared Prime grounds after adding selected set operations

The current full Prime waist and lower bootstrap atlas are different hosts.
Both now retain exact conservative routes for three semantic guests:

* finite-stage Cantor semantics;
* the externally interpreted Megalodon set core; and
* the selected empty/union/powerset authority.

The first two routes are transported through the new conservative outer
layers.  The operation authority enters each host directly.  Meaning and
checker replay are host-independent along these exact conservative routes,
while claim and certificate representations remain host-specific.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u v

private abbrev stagedTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev stagedContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory

private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

private abbrev operationTheory :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.theory

private abbrev operationContract :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.contract

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.contract.{u, v}

private abbrev atlasLayer :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.layer

/-! ## The two retained guests enter both new hosts -/

def stagedToPrime : AuthorityTranslation stagedContract primeContract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}

theorem stagedToPrime_conservative :
    stagedToPrime.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def setCoreToPrime : AuthorityTranslation setCoreContract primeContract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToPrime.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}

theorem setCoreToPrime_conservative :
    setCoreToPrime.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToPrime.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToPrime_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def stagedToAtlas : AuthorityTranslation
    stagedContract atlasLayer.toAuthorityContract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.stagedToExtendedAtlas
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion

theorem stagedToAtlas_conservative :
    stagedToAtlas.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.stagedToExtendedAtlas.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.stagedToExtendedAtlas_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion_conservative

def setCoreToAtlas : AuthorityTranslation
    setCoreContract atlasLayer.toAuthorityContract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToExtendedAtlas
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion

theorem setCoreToAtlas_conservative :
    setCoreToAtlas.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToExtendedAtlas.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding.setCoreToExtendedAtlas_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.priorInclusion_conservative

/-! ## The operation guest enters both hosts directly -/

def operationToPrime : AuthorityTranslation operationContract primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.operationInclusion.{u, v}

theorem operationToPrime_conservative :
    operationToPrime.{u, v}.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationWaist.operationInclusion_conservative.{u, v}

def operationToAtlas : AuthorityTranslation
    operationContract atlasLayer.toAuthorityContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.operationToAtlas

theorem operationToAtlas_conservative :
    operationToAtlas.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.operationToAtlas_conservative

/-! ## Semantic and operational host irrelevance -/

theorem staged_meaning_is_host_irrelevant
    (formula : stagedTheory.Claim ()) :
    primeTheory.Meaning
        (stagedToPrime.{u, v}.mapKind ())
        (stagedToPrime.{u, v}.mapClaim () formula) <->
      atlasLayer.toTheoryFamily.Meaning
        (stagedToAtlas.mapKind ())
        (stagedToAtlas.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    stagedToPrime.{u, v}.toTheoryTranslation
    stagedToAtlas.toTheoryTranslation
    stagedToPrime_conservative.{u, v} stagedToAtlas_conservative
    () formula

theorem staged_replay_is_host_irrelevant
    (formula : stagedTheory.Claim ())
    (certificate : stagedContract.Certificate ()) :
    (primeContract.checker (stagedToPrime.{u, v}.mapKind ())).check
        (stagedToPrime.{u, v}.mapClaim () formula)
        (stagedToPrime.{u, v}.mapCertificate () certificate) =
      (atlasLayer.toAuthorityContract.checker
        (stagedToAtlas.mapKind ())).check
        (stagedToAtlas.mapClaim () formula)
        (stagedToAtlas.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    stagedToPrime.{u, v} stagedToAtlas () formula certificate

theorem setCore_meaning_is_host_irrelevant
    (formula : setCoreTheory.Claim ()) :
    primeTheory.Meaning
        (setCoreToPrime.{u, v}.mapKind ())
        (setCoreToPrime.{u, v}.mapClaim () formula) <->
      atlasLayer.toTheoryFamily.Meaning
        (setCoreToAtlas.mapKind ())
        (setCoreToAtlas.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    setCoreToPrime.{u, v}.toTheoryTranslation
    setCoreToAtlas.toTheoryTranslation
    setCoreToPrime_conservative.{u, v} setCoreToAtlas_conservative
    () formula

theorem setCore_replay_is_host_irrelevant
    (formula : setCoreTheory.Claim ())
    (certificate : setCoreContract.Certificate ()) :
    (primeContract.checker (setCoreToPrime.{u, v}.mapKind ())).check
        (setCoreToPrime.{u, v}.mapClaim () formula)
        (setCoreToPrime.{u, v}.mapCertificate () certificate) =
      (atlasLayer.toAuthorityContract.checker
        (setCoreToAtlas.mapKind ())).check
        (setCoreToAtlas.mapClaim () formula)
        (setCoreToAtlas.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    setCoreToPrime.{u, v} setCoreToAtlas () formula certificate

theorem operation_meaning_is_host_irrelevant
    (formula : operationTheory.Claim ()) :
    primeTheory.Meaning
        (operationToPrime.{u, v}.mapKind ())
        (operationToPrime.{u, v}.mapClaim () formula) <->
      atlasLayer.toTheoryFamily.Meaning
        (operationToAtlas.mapKind ())
        (operationToAtlas.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    operationToPrime.{u, v}.toTheoryTranslation
    operationToAtlas.toTheoryTranslation
    operationToPrime_conservative.{u, v} operationToAtlas_conservative
    () formula

theorem operation_replay_is_host_irrelevant
    (formula : operationTheory.Claim ())
    (certificate : operationContract.Certificate ()) :
    (primeContract.checker (operationToPrime.{u, v}.mapKind ())).check
        (operationToPrime.{u, v}.mapClaim () formula)
        (operationToPrime.{u, v}.mapCertificate () certificate) =
      (atlasLayer.toAuthorityContract.checker
        (operationToAtlas.mapKind ())).check
        (operationToAtlas.mapClaim () formula)
        (operationToAtlas.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    operationToPrime.{u, v} operationToAtlas () formula certificate

/-! ## Positive, negative, and retention controls -/

namespace Canary

private def unionCertificate : operationContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.AxiomTag.unionIntro.proof

private def setCoreIdentityCertificate : setCoreContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula

theorem unionIntroduction_replays_in_prime :
    (primeContract.checker (operationToPrime.{u, v}.mapKind ())).check
      (operationToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (operationToPrime.{u, v}.mapCertificate () unionCertificate) = true := by
  calc
    _ = (operationContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula
          unionCertificate :=
      operationToPrime.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem unionIntroduction_replays_in_atlas :
    (atlasLayer.toAuthorityContract.checker
      (operationToAtlas.mapKind ())).check
      (operationToAtlas.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (operationToAtlas.mapCertificate () unionCertificate) = true := by
  calc
    _ = (operationContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula
          unionCertificate :=
      operationToAtlas.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem operation_identity_meaning_in_prime :
    primeTheory.Meaning
      (operationToPrime.{u, v}.mapKind ())
      (operationToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula) :=
  operationToPrime.{u, v}.meaning_preserved () _
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_valid

theorem operation_identity_not_scope_in_prime :
    Not (primeTheory.Scope
      (operationToPrime.{u, v}.mapKind ())
      (operationToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)) := by
  intro inScope
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_not_covered
      (operationToPrime_conservative.{u, v}.scope_reflecting () _ inScope)

theorem operation_identity_meaning_in_atlas :
    atlasLayer.toTheoryFamily.Meaning
      (operationToAtlas.mapKind ())
      (operationToAtlas.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula) :=
  operationToAtlas.meaning_preserved () _
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_valid

theorem operation_identity_not_scope_in_atlas :
    Not (atlasLayer.toTheoryFamily.Scope
      (operationToAtlas.mapKind ())
      (operationToAtlas.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)) := by
  intro inScope
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_not_covered
      (operationToAtlas_conservative.scope_reflecting () _ inScope)

theorem operation_universalMembership_not_meaning_in_prime :
    Not (primeTheory.Meaning
      (operationToPrime.{u, v}.mapKind ())
      (operationToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership)) := by
  intro meaningful
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership_not_valid
      (operationToPrime_conservative.{u, v}.meaning_reflecting () _ meaningful)

theorem operation_route_has_no_sourceSound_image
    (formula : operationTheory.Claim ()) :
    Not (Exists fun sourceFormula : operationTheory.Claim () =>
      operationToAtlas.mapClaim () sourceFormula =
        Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGroundAtlas.operationSourceSoundClaim
          formula) := by
  rintro ⟨sourceFormula, equality⟩
  cases equality

/-- The earlier finite-stage decision route survives both outer extensions. -/
theorem staged_properPart_replays_in_prime :
    (primeContract.checker (stagedToPrime.{u, v}.mapKind ())).check
      (stagedToPrime.{u, v}.mapClaim ()
        Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence)
      (stagedToPrime.{u, v}.mapCertificate () ()) = true := by
  calc
    _ = (stagedContract.checker ()).check
          Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence
          () :=
      stagedToPrime.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

/-- The earlier external set-core route also remains exact in the new atlas. -/
theorem setCore_identity_replays_in_atlas :
    (atlasLayer.toAuthorityContract.checker
      (setCoreToAtlas.mapKind ())).check
      (setCoreToAtlas.mapClaim ()
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
      (setCoreToAtlas.mapCertificate () setCoreIdentityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          setCoreIdentityCertificate :=
      setCoreToAtlas.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

end Canary

#print axioms stagedToPrime_conservative
#print axioms setCoreToPrime_conservative
#print axioms stagedToAtlas_conservative
#print axioms setCoreToAtlas_conservative
#print axioms operationToPrime_conservative
#print axioms operationToAtlas_conservative
#print axioms staged_meaning_is_host_irrelevant
#print axioms staged_replay_is_host_irrelevant
#print axioms setCore_meaning_is_host_irrelevant
#print axioms setCore_replay_is_host_irrelevant
#print axioms operation_meaning_is_host_irrelevant
#print axioms operation_replay_is_host_irrelevant
#print axioms Canary.unionIntroduction_replays_in_prime
#print axioms Canary.unionIntroduction_replays_in_atlas
#print axioms Canary.operation_identity_meaning_in_prime
#print axioms Canary.operation_identity_not_scope_in_prime
#print axioms Canary.operation_identity_meaning_in_atlas
#print axioms Canary.operation_identity_not_scope_in_atlas
#print axioms Canary.operation_universalMembership_not_meaning_in_prime
#print axioms Canary.operation_route_has_no_sourceSound_image
#print axioms Canary.staged_properPart_replays_in_prime
#print axioms Canary.setCore_identity_replays_in_atlas

end Mettapedia.Languages.MeTTa.PrimePluralNIKSetOperationGrounding
