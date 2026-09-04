import Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding
import Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas

/-!
# Shared semantic grounds for the plural Prime NIK waist

The full Prime authority waist and the lower bootstrap atlas are distinct
hosts.  This module does not identify them.  Instead, it gives two guest
authorities exact conservative routes into both hosts:

* finite-stage Cantor semantics enters Prime's atomless node and the atlas's
  complete `modelSound` node; and
* the external Megalodon set-core semantics enters Prime's retained set-core
  node and the atlas's partial `modelSound` node.

For each guest, semantic host irrelevance and certificate replay follow from
the two conservative exact routes.  The hosts retain different statement and
certificate representations, and the set-core semantic gap remains visible
in both.  This is a proper set-core fragment rather than the full HOTG
foundation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u v

private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory

private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

private abbrev setCoreWaistContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.contract

private abbrev dependentPiWaistContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.contract.{u, v}

private abbrev booleanWaistContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.contract.{u, v}

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.contract.{u, v}

private abbrev stagedTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev stagedContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev atlasLayer :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.layer

/-! ## The retained set-core route into the full Prime waist -/

/-- The external set-core authority enters the next retained Prime layer. -/
def setCoreToDependentPi : AuthorityTranslation
    setCoreContract dependentPiWaistContract :=
  AuthorityTranslation.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.setCoreInclusion
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion

theorem setCoreToDependentPi_conservative :
    setCoreToDependentPi.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.setCoreInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.setCoreInclusion_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.primeInclusion_conservative

/-- Retain the same set-core authority through the Boolean-identity layer. -/
def setCoreToBoolean : AuthorityTranslation
    setCoreContract booleanWaistContract :=
  AuthorityTranslation.comp setCoreToDependentPi.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion

theorem setCoreToBoolean_conservative :
    setCoreToBoolean.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    setCoreToDependentPi.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion.toTheoryTranslation
    setCoreToDependentPi_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.primeInclusion_conservative

/-- The exact set-core authority route into the current full Prime waist. -/
def setCoreToPrime : AuthorityTranslation setCoreContract primeContract :=
  AuthorityTranslation.comp setCoreToBoolean.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion

theorem setCoreToPrime_conservative :
    setCoreToPrime.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    setCoreToBoolean.{u, v}.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion.toTheoryTranslation
    setCoreToBoolean_conservative.{u, v}
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.priorInclusion_conservative

@[simp] theorem setCoreToPrime_mapClaim
    (formula : setCoreTheory.Claim ()) :
    setCoreToPrime.{u, v}.mapClaim () formula = formula :=
  rfl

/-! ## Both guests route into the extended lower atlas -/

/-- Retain the exact finite-stage route while extending the atlas with a
separate set-core lane. -/
def stagedToExtendedAtlas : AuthorityTranslation
    stagedContract atlasLayer.toAuthorityContract :=
  AuthorityTranslation.comp
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.priorInclusion

theorem stagedToExtendedAtlas_conservative :
    stagedToExtendedAtlas.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.priorInclusion.toTheoryTranslation
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.priorInclusion_conservative

/-- The set-core guest's exact route into the extended atlas. -/
def setCoreToExtendedAtlas : AuthorityTranslation
    setCoreContract atlasLayer.toAuthorityContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.setCoreToAtlas

theorem setCoreToExtendedAtlas_conservative :
    setCoreToExtendedAtlas.toTheoryTranslation.Conservative :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.setCoreToAtlas_conservative

/-! ## Host irrelevance for the two distinct semantic guests -/

/-- The staged atomless guest has the same meaning in the full Prime waist
and the extended lower atlas. -/
theorem staged_meaning_is_host_irrelevant (formula : stagedTheory.Claim ()) :
    primeTheory.Meaning
        (Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.mapKind ())
        (Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.mapClaim () formula) <->
      atlasLayer.toTheoryFamily.Meaning
        (stagedToExtendedAtlas.mapKind ())
        (stagedToExtendedAtlas.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.toTheoryTranslation
    stagedToExtendedAtlas.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime_conservative.{u, v}
    stagedToExtendedAtlas_conservative
    () formula

/-- The two distinct hosts replay an incoming staged certificate identically. -/
theorem staged_replay_is_host_irrelevant (formula : stagedTheory.Claim ())
    (certificate : stagedContract.Certificate ()) :
    (primeContract.checker
        (Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.mapKind ())).check
        (Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.mapClaim () formula)
        (Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}.mapCertificate () certificate) =
      (atlasLayer.toAuthorityContract.checker
        (stagedToExtendedAtlas.mapKind ())).check
        (stagedToExtendedAtlas.mapClaim () formula)
        (stagedToExtendedAtlas.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding.stagedToPrime.{u, v}
    stagedToExtendedAtlas () formula certificate

/-- The independently stated set-core semantics is likewise invariant under
the choice between the full Prime waist and the lower atlas. -/
theorem setCore_meaning_is_host_irrelevant
    (formula : setCoreTheory.Claim ()) :
    primeTheory.Meaning
        (setCoreToPrime.{u, v}.mapKind ())
        (setCoreToPrime.{u, v}.mapClaim () formula) <->
      atlasLayer.toTheoryFamily.Meaning
        (setCoreToExtendedAtlas.mapKind ())
        (setCoreToExtendedAtlas.mapClaim () formula) :=
  HostIrrelevance.meaning_iff
    setCoreToPrime.{u, v}.toTheoryTranslation
    setCoreToExtendedAtlas.toTheoryTranslation
    setCoreToPrime_conservative.{u, v}
    setCoreToExtendedAtlas_conservative
    () formula

/-- Set-core certificates also replay identically through the shared guest,
while their translated evidence remains host-specific. -/
theorem setCore_replay_is_host_irrelevant
    (formula : setCoreTheory.Claim ())
    (certificate : setCoreContract.Certificate ()) :
    (primeContract.checker (setCoreToPrime.{u, v}.mapKind ())).check
        (setCoreToPrime.{u, v}.mapClaim () formula)
        (setCoreToPrime.{u, v}.mapCertificate () certificate) =
      (atlasLayer.toAuthorityContract.checker
        (setCoreToExtendedAtlas.mapKind ())).check
        (setCoreToExtendedAtlas.mapClaim () formula)
        (setCoreToExtendedAtlas.mapCertificate () certificate) :=
  HostIrrelevance.check_eq
    setCoreToPrime.{u, v} setCoreToExtendedAtlas () formula certificate

/-! ## Positive and negative controls -/

namespace Canary

private def identityCertificate : setCoreContract.Certificate () :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula

theorem setCore_identity_replays_in_prime :
    (primeContract.checker (setCoreToPrime.{u, v}.mapKind ())).check
        (setCoreToPrime.{u, v}.mapClaim ()
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (setCoreToPrime.{u, v}.mapCertificate () identityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          identityCertificate :=
      setCoreToPrime.{u, v}.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

theorem setCore_identity_replays_in_atlas :
    (atlasLayer.toAuthorityContract.checker
        (setCoreToExtendedAtlas.mapKind ())).check
        (setCoreToExtendedAtlas.mapClaim ()
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (setCoreToExtendedAtlas.mapCertificate () identityCertificate) = true := by
  calc
    _ = (setCoreContract.checker ()).check
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
          identityCertificate :=
      setCoreToExtendedAtlas.check_commutes () _ _
    _ = true :=
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

/-- A valid but uncovered set-core formula remains meaningful in Prime. -/
theorem quantifiedIdentity_meaning_in_prime :
    primeTheory.Meaning
      (setCoreToPrime.{u, v}.mapKind ())
      (setCoreToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity) :=
  setCoreToPrime.{u, v}.meaning_preserved () _
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity_valid

/-- Conservativity prevents the larger Prime host from inventing native
scope for that semantically valid formula. -/
theorem quantifiedIdentity_not_scope_in_prime :
    Not (primeTheory.Scope
      (setCoreToPrime.{u, v}.mapKind ())
      (setCoreToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity)) := by
  intro inScope
  exact
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity_not_covered
      (setCoreToPrime_conservative.{u, v}.scope_reflecting () _ inScope)

/-- The atlas retains the same semantic gap rather than defining truth by
its selected native certificates. -/
theorem quantifiedIdentity_meaning_in_atlas :
    atlasLayer.toTheoryFamily.Meaning
      (setCoreToExtendedAtlas.mapKind ())
      (setCoreToExtendedAtlas.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity) :=
  setCoreToExtendedAtlas.meaning_preserved () _
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity_valid

theorem quantifiedIdentity_not_scope_in_atlas :
    Not (atlasLayer.toTheoryFamily.Scope
      (setCoreToExtendedAtlas.mapKind ())
      (setCoreToExtendedAtlas.mapClaim ()
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity)) := by
  intro inScope
  exact
    Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.quantifiedIdentity_not_covered
      (setCoreToExtendedAtlas_conservative.scope_reflecting () _ inScope)

/-- The concrete false membership formula remains false in Prime. -/
theorem universalMembership_not_meaning_in_prime :
    Not (primeTheory.Meaning
      (setCoreToPrime.{u, v}.mapKind ())
      (setCoreToPrime.{u, v}.mapClaim ()
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership)) := by
  intro meaningful
  exact
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership_not_valid
      (setCoreToPrime_conservative.{u, v}.meaning_reflecting () _ meaningful)

/-- A source-soundness contract cannot be manufactured by the set-core
model-soundness route. -/
theorem setCore_route_has_no_sourceSound_image
    (formula : setCoreTheory.Claim ()) :
    Not (Exists fun sourceFormula : setCoreTheory.Claim () =>
      setCoreToExtendedAtlas.mapClaim () sourceFormula =
        Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGroundAtlas.setCoreSourceSoundClaim
          formula) := by
  rintro ⟨sourceFormula, equality⟩
  cases equality

end Canary

#print axioms setCoreToDependentPi
#print axioms setCoreToDependentPi_conservative
#print axioms setCoreToBoolean
#print axioms setCoreToBoolean_conservative
#print axioms setCoreToPrime
#print axioms setCoreToPrime_conservative
#print axioms stagedToExtendedAtlas
#print axioms stagedToExtendedAtlas_conservative
#print axioms setCoreToExtendedAtlas
#print axioms setCoreToExtendedAtlas_conservative
#print axioms staged_meaning_is_host_irrelevant
#print axioms staged_replay_is_host_irrelevant
#print axioms setCore_meaning_is_host_irrelevant
#print axioms setCore_replay_is_host_irrelevant
#print axioms Canary.setCore_identity_replays_in_prime
#print axioms Canary.setCore_identity_replays_in_atlas
#print axioms Canary.quantifiedIdentity_meaning_in_prime
#print axioms Canary.quantifiedIdentity_not_scope_in_prime
#print axioms Canary.quantifiedIdentity_meaning_in_atlas
#print axioms Canary.quantifiedIdentity_not_scope_in_atlas
#print axioms Canary.universalMembership_not_meaning_in_prime
#print axioms Canary.setCore_route_has_no_sourceSound_image

end Mettapedia.Languages.MeTTa.PrimePluralNIKSemanticGrounding
