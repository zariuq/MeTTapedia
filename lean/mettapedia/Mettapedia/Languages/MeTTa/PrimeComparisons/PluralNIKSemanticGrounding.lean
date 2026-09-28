import Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding
import Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore

/-!
# Shared semantic grounds for the plural candidate NIK waist

The full candidate authority waist and the base checker are distinct
hosts.  This module does not identify them.  Instead, it gives two guest
authorities exact conservative routes into both hosts:

* finite-stage Cantor semantics enters candidate's atomless node and the base checker's
  complete `modelSound` node; and
* the external Megalodon set-core semantics enters candidate's retained set-core
  node and the base checker's partial `modelSound` node.

For each guest, semantic host irrelevance and certificate replay follow from
the two conservative exact routes.  The hosts retain different statement and
certificate representations, and the set-core semantic gap remains visible
in both.  This is a proper set-core fragment rather than the full HOTG
foundation.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSemanticGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u v

private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory

private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

private abbrev setCoreWaistContract :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSetCoreWaist.contract

private abbrev dependentPiWaistContract :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKDependentPiWaist.contract.{u, v}

private abbrev booleanWaistContract :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBooleanIdentityWaist.contract.{u, v}

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKAtomlessBooleanWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKAtomlessBooleanWaist.contract.{u, v}

private abbrev stagedTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev stagedContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev baseCheckerLayer :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.layer

/-! ## The retained set-core route into the full candidate waist -/

/-- The external set-core authority enters the next retained candidate layer. -/
def setCoreToDependentPi : CertifiedTranslation
    setCoreContract dependentPiWaistContract :=
  CertifiedTranslation.comp
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSetCoreWaist.setCoreInclusion
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKDependentPiWaist.primeInclusion

theorem setCoreToDependentPi_conservative :
    setCoreToDependentPi.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSetCoreWaist.setCoreInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKDependentPiWaist.primeInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSetCoreWaist.setCoreInclusion_conservative
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKDependentPiWaist.primeInclusion_conservative

/-- Retain the same set-core authority through the Boolean-identity layer. -/
def setCoreToBoolean : CertifiedTranslation
    setCoreContract booleanWaistContract :=
  CertifiedTranslation.comp setCoreToDependentPi.{u, v}
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBooleanIdentityWaist.primeInclusion

theorem setCoreToBoolean_conservative :
    setCoreToBoolean.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    setCoreToDependentPi.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBooleanIdentityWaist.primeInclusion.toTheoryTranslation
    setCoreToDependentPi_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBooleanIdentityWaist.primeInclusion_conservative

/-- The exact set-core authority route into the current full candidate waist. -/
def setCoreToCandidate : CertifiedTranslation setCoreContract primeContract :=
  CertifiedTranslation.comp setCoreToBoolean.{u, v}
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKAtomlessBooleanWaist.priorInclusion

theorem setCoreToCandidate_conservative :
    setCoreToCandidate.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    setCoreToBoolean.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKAtomlessBooleanWaist.priorInclusion.toTheoryTranslation
    setCoreToBoolean_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKAtomlessBooleanWaist.priorInclusion_conservative

@[simp] theorem setCoreToCandidate_mapClaim
    (formula : setCoreTheory.Claim ()) :
    setCoreToCandidate.{u, v}.mapClaim () formula = formula :=
  rfl

/-! ## Both guests route into the extended base checker -/

/-- Retain the exact finite-stage route while extending the base checker with a
separate set-core lane. -/
def stagedToExtendedBaseChecker : CertifiedTranslation
    stagedContract baseCheckerLayer.toAuthorityContract :=
  CertifiedTranslation.comp
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.priorInclusion

theorem stagedToExtendedBaseChecker_conservative :
    stagedToExtendedBaseChecker.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.priorInclusion.toTheoryTranslation
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel_conservative
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.priorInclusion_conservative

/-- The set-core guest's exact route into the extended base checker. -/
def setCoreToExtendedBaseChecker : CertifiedTranslation
    setCoreContract baseCheckerLayer.toAuthorityContract :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.setCoreToBaseChecker

theorem setCoreToExtendedBaseChecker_conservative :
    setCoreToExtendedBaseChecker.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.setCoreToBaseChecker_conservative

/-! ## Host irrelevance for the two distinct semantic guests -/

/-- The staged atomless guest has the same meaning in the full candidate waist
and the extended base checker. -/
theorem staged_meaning_is_host_irrelevant (formula : stagedTheory.Claim ()) :
    primeTheory.Meaning
        (Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.mapKind ())
        (Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.mapClaim () formula) <->
      baseCheckerLayer.toTheoryFamily.Meaning
        (stagedToExtendedBaseChecker.mapKind ())
        (stagedToExtendedBaseChecker.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.toTheoryTranslation
    stagedToExtendedBaseChecker.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate_conservative.{u, v}
    stagedToExtendedBaseChecker_conservative
    () formula

/-- The two distinct hosts replay an incoming staged certificate identically. -/
theorem staged_replay_is_host_irrelevant (formula : stagedTheory.Claim ())
    (certificate : stagedContract.Certificate ()) :
    (primeContract.checker
        (Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.mapKind ())).check
        (Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.mapClaim () formula)
        (Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}.mapCertificate () certificate) =
      (baseCheckerLayer.toAuthorityContract.checker
        (stagedToExtendedBaseChecker.mapKind ())).check
        (stagedToExtendedBaseChecker.mapClaim () formula)
        (stagedToExtendedBaseChecker.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKGenerativeAtomlessGrounding.stagedToCandidate.{u, v}
    stagedToExtendedBaseChecker () formula certificate

/-- The independently stated set-core semantics is likewise invariant under
the choice between the full candidate waist and the base checker. -/
theorem setCore_meaning_is_host_irrelevant
    (formula : setCoreTheory.Claim ()) :
    primeTheory.Meaning
        (setCoreToCandidate.{u, v}.mapKind ())
        (setCoreToCandidate.{u, v}.mapClaim () formula) <->
      baseCheckerLayer.toTheoryFamily.Meaning
        (setCoreToExtendedBaseChecker.mapKind ())
        (setCoreToExtendedBaseChecker.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    setCoreToCandidate.{u, v}.toTheoryTranslation
    setCoreToExtendedBaseChecker.toTheoryTranslation
    setCoreToCandidate_conservative.{u, v}
    setCoreToExtendedBaseChecker_conservative
    () formula

/-- Set-core certificates also replay identically through the shared guest,
while their translated evidence remains host-specific. -/
theorem setCore_replay_is_host_irrelevant
    (formula : setCoreTheory.Claim ())
    (certificate : setCoreContract.Certificate ()) :
    (primeContract.checker (setCoreToCandidate.{u, v}.mapKind ())).check
        (setCoreToCandidate.{u, v}.mapClaim () formula)
        (setCoreToCandidate.{u, v}.mapCertificate () certificate) =
      (baseCheckerLayer.toAuthorityContract.checker
        (setCoreToExtendedBaseChecker.mapKind ())).check
        (setCoreToExtendedBaseChecker.mapClaim () formula)
        (setCoreToExtendedBaseChecker.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    setCoreToCandidate.{u, v} setCoreToExtendedBaseChecker () formula certificate

/-! ## Positive and negative controls -/

namespace Canary

private def identityCertificate : setCoreContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula

theorem setCore_identity_replays_in_prime :
    (primeContract.checker (setCoreToCandidate.{u, v}.mapKind ())).check
        (setCoreToCandidate.{u, v}.mapClaim ()
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (setCoreToCandidate.{u, v}.mapCertificate () identityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          identityCertificate :=
      setCoreToCandidate.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

theorem setCore_identity_accepted_by_base_checker :
    (baseCheckerLayer.toAuthorityContract.checker
        (setCoreToExtendedBaseChecker.mapKind ())).check
        (setCoreToExtendedBaseChecker.mapClaim ()
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (setCoreToExtendedBaseChecker.mapCertificate () identityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          identityCertificate :=
      setCoreToExtendedBaseChecker.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

/-- A valid but uncovered set-core formula remains meaningful in candidate. -/
theorem quantifiedIdentity_meaning_in_prime :
    primeTheory.Meaning
      (setCoreToCandidate.{u, v}.mapKind ())
      (setCoreToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity) :=
  setCoreToCandidate.{u, v}.meaning_preserved () _
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity_valid

/-- Conservativity prevents the larger candidate host from inventing native
scope for that semantically valid formula. -/
theorem quantifiedIdentity_not_scope_in_prime :
    Not (primeTheory.Scope
      (setCoreToCandidate.{u, v}.mapKind ())
      (setCoreToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity)) := by
  intro inScope
  exact
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity_not_covered
      (setCoreToCandidate_conservative.{u, v}.scope_reflecting () _ inScope)

/-- The base checker retains the same semantic gap rather than defining truth by
its selected native certificates. -/
theorem quantifiedIdentity_meaning_in_base_checker :
    baseCheckerLayer.toTheoryFamily.Meaning
      (setCoreToExtendedBaseChecker.mapKind ())
      (setCoreToExtendedBaseChecker.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity) :=
  setCoreToExtendedBaseChecker.meaning_preserved () _
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity_valid

theorem quantifiedIdentity_not_in_base_checker_scope :
    Not (baseCheckerLayer.toTheoryFamily.Scope
      (setCoreToExtendedBaseChecker.mapKind ())
      (setCoreToExtendedBaseChecker.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity)) := by
  intro inScope
  exact
    Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.quantifiedIdentity_not_covered
      (setCoreToExtendedBaseChecker_conservative.scope_reflecting () _ inScope)

/-- The concrete false membership formula remains false in candidate. -/
theorem universalMembership_not_meaning_in_prime :
    Not (primeTheory.Meaning
      (setCoreToCandidate.{u, v}.mapKind ())
      (setCoreToCandidate.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership)) := by
  intro meaningful
  exact
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership_not_valid
      (setCoreToCandidate_conservative.{u, v}.meaning_reflecting () _ meaningful)

/-- A source-soundness contract cannot be manufactured by the set-core
model-soundness route. -/
theorem setCore_route_has_no_sourceSound_image
    (formula : setCoreTheory.Claim ()) :
    Not (Exists fun sourceFormula : setCoreTheory.Claim () =>
      setCoreToExtendedBaseChecker.mapClaim () sourceFormula =
        Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKBaseCheckerSetCore.setCoreSourceSoundClaim
          formula) := by
  rintro ⟨sourceFormula, equality⟩
  cases equality

end Canary

#print axioms setCoreToDependentPi
#print axioms setCoreToDependentPi_conservative
#print axioms setCoreToBoolean
#print axioms setCoreToBoolean_conservative
#print axioms setCoreToCandidate
#print axioms setCoreToCandidate_conservative
#print axioms stagedToExtendedBaseChecker
#print axioms stagedToExtendedBaseChecker_conservative
#print axioms setCoreToExtendedBaseChecker
#print axioms setCoreToExtendedBaseChecker_conservative
#print axioms staged_meaning_is_host_irrelevant
#print axioms staged_replay_is_host_irrelevant
#print axioms setCore_meaning_is_host_irrelevant
#print axioms setCore_replay_is_host_irrelevant
#print axioms Canary.setCore_identity_replays_in_prime
#print axioms Canary.setCore_identity_accepted_by_base_checker
#print axioms Canary.quantifiedIdentity_meaning_in_prime
#print axioms Canary.quantifiedIdentity_not_scope_in_prime
#print axioms Canary.quantifiedIdentity_meaning_in_base_checker
#print axioms Canary.quantifiedIdentity_not_in_base_checker_scope
#print axioms Canary.universalMembership_not_meaning_in_prime
#print axioms Canary.setCore_route_has_no_sourceSound_image

end Mettapedia.Languages.MeTTa.PrimeComparisons.PluralNIKSemanticGrounding
