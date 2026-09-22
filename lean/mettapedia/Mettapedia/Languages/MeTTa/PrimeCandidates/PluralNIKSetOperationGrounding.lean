import Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding
import Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation
import Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist

/-!
# Shared candidate grounds after adding selected set operations

The current full candidate waist and base checker are different hosts.
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

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
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
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.contract.{u, v}

private abbrev baseCheckerLayer :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.layer

/-! ## The two retained guests enter both new hosts -/

def stagedToCandidate : CertifiedTranslation stagedContract primeContract :=
  CertifiedTranslation.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion.{u, v}

theorem stagedToCandidate_conservative :
    stagedToCandidate.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def setCoreToCandidate : CertifiedTranslation setCoreContract primeContract :=
  CertifiedTranslation.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToCandidate.{u, v}
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion.{u, v}

theorem setCoreToCandidate_conservative :
    setCoreToCandidate.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToCandidate.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToCandidate_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.priorInclusion_conservative.{u, v}

def stagedToBaseChecker : CertifiedTranslation
    stagedContract baseCheckerLayer.toAuthorityContract :=
  CertifiedTranslation.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.stagedToExtendedBaseChecker
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion

theorem stagedToBaseChecker_conservative :
    stagedToBaseChecker.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.stagedToExtendedBaseChecker.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.stagedToExtendedBaseChecker_conservative
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion_conservative

def setCoreToBaseChecker : CertifiedTranslation
    setCoreContract baseCheckerLayer.toAuthorityContract :=
  CertifiedTranslation.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToExtendedBaseChecker
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion

theorem setCoreToBaseChecker_conservative :
    setCoreToBaseChecker.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToExtendedBaseChecker.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSemanticGrounding.setCoreToExtendedBaseChecker_conservative
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.priorInclusion_conservative

/-! ## The operation guest enters both hosts directly -/

def operationToCandidate : CertifiedTranslation operationContract primeContract :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.operationInclusion.{u, v}

theorem operationToCandidate_conservative :
    operationToCandidate.{u, v}.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationWaist.operationInclusion_conservative.{u, v}

def operationToBaseChecker : CertifiedTranslation
    operationContract baseCheckerLayer.toAuthorityContract :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.operationToBaseChecker

theorem operationToBaseChecker_conservative :
    operationToBaseChecker.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.operationToBaseChecker_conservative

/-! ## Semantic and operational host irrelevance -/

theorem staged_meaning_is_host_irrelevant
    (formula : stagedTheory.Claim ()) :
    primeTheory.Meaning
        (stagedToCandidate.{u, v}.mapKind ())
        (stagedToCandidate.{u, v}.mapClaim () formula) <->
      baseCheckerLayer.toTheoryFamily.Meaning
        (stagedToBaseChecker.mapKind ())
        (stagedToBaseChecker.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    stagedToCandidate.{u, v}.toTheoryTranslation
    stagedToBaseChecker.toTheoryTranslation
    stagedToCandidate_conservative.{u, v} stagedToBaseChecker_conservative
    () formula

theorem staged_replay_is_host_irrelevant
    (formula : stagedTheory.Claim ())
    (certificate : stagedContract.Certificate ()) :
    (primeContract.checker (stagedToCandidate.{u, v}.mapKind ())).check
        (stagedToCandidate.{u, v}.mapClaim () formula)
        (stagedToCandidate.{u, v}.mapCertificate () certificate) =
      (baseCheckerLayer.toAuthorityContract.checker
        (stagedToBaseChecker.mapKind ())).check
        (stagedToBaseChecker.mapClaim () formula)
        (stagedToBaseChecker.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    stagedToCandidate.{u, v} stagedToBaseChecker () formula certificate

theorem setCore_meaning_is_host_irrelevant
    (formula : setCoreTheory.Claim ()) :
    primeTheory.Meaning
        (setCoreToCandidate.{u, v}.mapKind ())
        (setCoreToCandidate.{u, v}.mapClaim () formula) <->
      baseCheckerLayer.toTheoryFamily.Meaning
        (setCoreToBaseChecker.mapKind ())
        (setCoreToBaseChecker.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    setCoreToCandidate.{u, v}.toTheoryTranslation
    setCoreToBaseChecker.toTheoryTranslation
    setCoreToCandidate_conservative.{u, v} setCoreToBaseChecker_conservative
    () formula

theorem setCore_replay_is_host_irrelevant
    (formula : setCoreTheory.Claim ())
    (certificate : setCoreContract.Certificate ()) :
    (primeContract.checker (setCoreToCandidate.{u, v}.mapKind ())).check
        (setCoreToCandidate.{u, v}.mapClaim () formula)
        (setCoreToCandidate.{u, v}.mapCertificate () certificate) =
      (baseCheckerLayer.toAuthorityContract.checker
        (setCoreToBaseChecker.mapKind ())).check
        (setCoreToBaseChecker.mapClaim () formula)
        (setCoreToBaseChecker.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    setCoreToCandidate.{u, v} setCoreToBaseChecker () formula certificate

theorem operation_meaning_is_host_irrelevant
    (formula : operationTheory.Claim ()) :
    primeTheory.Meaning
        (operationToCandidate.{u, v}.mapKind ())
        (operationToCandidate.{u, v}.mapClaim () formula) <->
      baseCheckerLayer.toTheoryFamily.Meaning
        (operationToBaseChecker.mapKind ())
        (operationToBaseChecker.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    operationToCandidate.{u, v}.toTheoryTranslation
    operationToBaseChecker.toTheoryTranslation
    operationToCandidate_conservative.{u, v} operationToBaseChecker_conservative
    () formula

theorem operation_replay_is_host_irrelevant
    (formula : operationTheory.Claim ())
    (certificate : operationContract.Certificate ()) :
    (primeContract.checker (operationToCandidate.{u, v}.mapKind ())).check
        (operationToCandidate.{u, v}.mapClaim () formula)
        (operationToCandidate.{u, v}.mapCertificate () certificate) =
      (baseCheckerLayer.toAuthorityContract.checker
        (operationToBaseChecker.mapKind ())).check
        (operationToBaseChecker.mapClaim () formula)
        (operationToBaseChecker.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    operationToCandidate.{u, v} operationToBaseChecker () formula certificate

/-! ## Positive, negative, and retention controls -/

namespace Canary

private def unionCertificate : operationContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.AxiomTag.unionIntro.proof

private def setCoreIdentityCertificate : setCoreContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula

theorem unionIntroduction_replays_in_prime :
    (primeContract.checker (operationToCandidate.{u, v}.mapKind ())).check
      (operationToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (operationToCandidate.{u, v}.mapCertificate () unionCertificate) = true := by
  calc
    _ = (operationContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula
          unionCertificate :=
      operationToCandidate.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem unionIntroduction_accepted_by_base_checker :
    (baseCheckerLayer.toAuthorityContract.checker
      (operationToBaseChecker.mapKind ())).check
      (operationToBaseChecker.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula)
      (operationToBaseChecker.mapCertificate () unionCertificate) = true := by
  calc
    _ = (operationContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.unionIntroFormula
          unionCertificate :=
      operationToBaseChecker.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.Canary.unionIntro_replays

theorem operation_identity_meaning_in_prime :
    primeTheory.Meaning
      (operationToCandidate.{u, v}.mapKind ())
      (operationToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula) :=
  operationToCandidate.{u, v}.meaning_preserved () _
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_valid

theorem operation_identity_not_scope_in_prime :
    Not (primeTheory.Scope
      (operationToCandidate.{u, v}.mapKind ())
      (operationToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)) := by
  intro inScope
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_not_covered
      (operationToCandidate_conservative.{u, v}.scope_reflecting () _ inScope)

theorem operation_identity_meaning_in_base_checker :
    baseCheckerLayer.toTheoryFamily.Meaning
      (operationToBaseChecker.mapKind ())
      (operationToBaseChecker.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula) :=
  operationToBaseChecker.meaning_preserved () _
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_valid

theorem operation_identity_not_in_base_checker_scope :
    Not (baseCheckerLayer.toTheoryFamily.Scope
      (operationToBaseChecker.mapKind ())
      (operationToBaseChecker.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identityFormula)) := by
  intro inScope
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.identity_not_covered
      (operationToBaseChecker_conservative.scope_reflecting () _ inScope)

theorem operation_universalMembership_not_meaning_in_prime :
    Not (primeTheory.Meaning
      (operationToCandidate.{u, v}.mapKind ())
      (operationToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership)) := by
  intro meaningful
  exact
    Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority.universalMembership_not_valid
      (operationToCandidate_conservative.{u, v}.meaning_reflecting () _ meaningful)

theorem operation_route_has_no_sourceSound_image
    (formula : operationTheory.Claim ()) :
    Not (Exists fun sourceFormula : operationTheory.Claim () =>
      operationToBaseChecker.mapClaim () sourceFormula =
        Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBaseCheckerSetOperation.operationSourceSoundClaim
          formula) := by
  rintro ⟨sourceFormula, equality⟩
  cases equality

/-- The earlier finite-stage decision route survives both outer extensions. -/
theorem staged_properPart_replays_in_prime :
    (primeContract.checker (stagedToCandidate.{u, v}.mapKind ())).check
      (stagedToCandidate.{u, v}.mapClaim ()
        Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence)
      (stagedToCandidate.{u, v}.mapCertificate () ()) = true := by
  calc
    _ = (stagedContract.checker ()).check
          Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary.properPartSentence
          () :=
      stagedToCandidate.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

/-- The earlier external set-core route also remains exact in the new base checker. -/
theorem setCore_identity_accepted_by_base_checker :
    (baseCheckerLayer.toAuthorityContract.checker
      (setCoreToBaseChecker.mapKind ())).check
      (setCoreToBaseChecker.mapClaim ()
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
      (setCoreToBaseChecker.mapCertificate () setCoreIdentityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          setCoreIdentityCertificate :=
      setCoreToBaseChecker.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

end Canary

#print axioms stagedToCandidate_conservative
#print axioms setCoreToCandidate_conservative
#print axioms stagedToBaseChecker_conservative
#print axioms setCoreToBaseChecker_conservative
#print axioms operationToCandidate_conservative
#print axioms operationToBaseChecker_conservative
#print axioms staged_meaning_is_host_irrelevant
#print axioms staged_replay_is_host_irrelevant
#print axioms setCore_meaning_is_host_irrelevant
#print axioms setCore_replay_is_host_irrelevant
#print axioms operation_meaning_is_host_irrelevant
#print axioms operation_replay_is_host_irrelevant
#print axioms Canary.unionIntroduction_replays_in_prime
#print axioms Canary.unionIntroduction_accepted_by_base_checker
#print axioms Canary.operation_identity_meaning_in_prime
#print axioms Canary.operation_identity_not_scope_in_prime
#print axioms Canary.operation_identity_meaning_in_base_checker
#print axioms Canary.operation_identity_not_in_base_checker_scope
#print axioms Canary.operation_universalMembership_not_meaning_in_prime
#print axioms Canary.operation_route_has_no_sourceSound_image
#print axioms Canary.staged_properPart_replays_in_prime
#print axioms Canary.setCore_identity_accepted_by_base_checker

end Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKSetOperationGrounding
