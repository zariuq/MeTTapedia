import Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority
import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist

/-!
# An infinite-primary Boolean peer in the plural Prime NIK waist

The established Prime waist already keeps structural DTT, semantic
implication, selected Megalodon/HOTG fragments, and one dependent-Pi
computation as distinct native authorities.  This module conservatively adds
the arity-indexed Boolean-identity authority:

* its executable scope is finite truth-table validity;
* its independent meaning is validity in the infinite atomless algebra of
  Cantor clopens;
* Stone representation proves the adequacy edge between them.

The new node is a semantic peer and a decidable equational ground.  It is not
identified with the Prime host, the executable shield, or the full
first-order theory of atomless Boolean algebras.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist

open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision.Canary
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.Canary
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment

universe u v

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.contract.{u, v}

private abbrev booleanTheory :=
  Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.theory

private abbrev booleanContract :=
  Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.contract

/-- The established Prime waist or an arity-indexed Boolean identity. -/
abbrev Kind := Sum
  Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.Kind Nat

/-- The retained structural DTT authority tag. -/
def structuralDTTKind : Kind :=
  .inl
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.structuralDTTKind

/-- The retained selected dependent-Pi computation tag. -/
def selectedDependentPiKind : Kind :=
  .inl
    Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.selectedDependentPiKind

/-- The Boolean identity authority at a fixed finite variable arity. -/
def booleanIdentityKind (arity : Nat) : Kind := .inr arity

/-- Conservative coexistence of the prior Prime waist and the Boolean
identity authority. -/
def theory :=
  Coproduct.theory primeTheory.{u, v} booleanTheory

/-- The outer tag selects the prior Prime authority or finite truth-table
replay. -/
def contract :=
  Coproduct.contract primeTheory.{u, v} booleanTheory primeContract.{u, v}
    booleanContract

/-- The established Prime waist enters without reinterpretation. -/
def primeInclusion :=
  Coproduct.leftInclusion primeTheory.{u, v} booleanTheory primeContract.{u, v}
    booleanContract

/-- The infinite-primary Boolean authority enters without changing its
finite scope or external meaning. -/
def booleanInclusion :=
  Coproduct.rightInclusion primeTheory.{u, v} booleanTheory primeContract.{u, v}
    booleanContract

theorem primeInclusion_conservative :
    primeInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative primeTheory.{u, v} booleanTheory
    primeContract.{u, v} booleanContract

theorem booleanInclusion_conservative :
    booleanInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.rightInclusion_conservative primeTheory.{u, v} booleanTheory
    primeContract.{u, v} booleanContract

private theorem booleanIdentity_conservative :
    (TheoryTranslation.identity booleanTheory).Conservative where
  scope_reflecting := by
    intro kind candidate inScope
    exact inScope
  meaning_reflecting := by
    intro kind candidate meaningful
    exact meaningful

/-! ## Exact semantic host irrelevance -/

/-- Entering the larger Prime host changes no Boolean proof scope. -/
theorem boolean_scope_is_host_irrelevant (arity : Nat)
    (equation : booleanTheory.Claim arity) :
    booleanTheory.Scope arity equation <->
      theory.{u, v}.Scope (booleanIdentityKind arity) equation :=
  HostIrrelevance.scope_iff
    (TheoryTranslation.identity booleanTheory)
    booleanInclusion.{u, v}.toTheoryTranslation
    booleanIdentity_conservative
    booleanInclusion_conservative.{u, v}
    arity equation

/-- Entering the larger Prime host changes no validity statement about the
infinite atomless Cantor algebra. -/
theorem boolean_meaning_is_host_irrelevant (arity : Nat)
    (equation : booleanTheory.Claim arity) :
    booleanTheory.Meaning arity equation <->
      theory.{u, v}.Meaning (booleanIdentityKind arity) equation :=
  HostIrrelevance.meaning_iff
    (TheoryTranslation.identity booleanTheory)
    booleanInclusion.{u, v}.toTheoryTranslation
    booleanIdentity_conservative
    booleanInclusion_conservative.{u, v}
    arity equation

/-! ## Retention and discriminating controls -/

/-- The selected dependent computation still replays at its retained tag. -/
theorem dependentPi_beta_replays :
    (contract.{u, v}.checker selectedDependentPiKind).check
      NIKProfile.canonicalCandidate NIKProfile.canonicalCertificate = true :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist.dependentPi_beta_replays.{u, v}

/-- A valid Boolean identity replays through the new Prime tag. -/
theorem boolean_distributive_replays :
    (contract.{u, v}.checker (booleanIdentityKind 2)).check
      distributiveIdentity (fullTruthTable (Var := TwoVar)) = true :=
  distributive_replays

/-- Accepted finite replay has infinite-primary meaning inside Prime. -/
theorem boolean_distributive_has_infinitePrimaryMeaning :
    theory.{u, v}.Meaning (booleanIdentityKind 2)
      distributiveIdentity :=
  (boolean_meaning_is_host_irrelevant.{u, v} 2
    distributiveIdentity).mp distributive_has_infinitePrimaryMeaning

/-- The external semantic carrier remains genuinely gunky and infinite. -/
theorem boolean_semanticCarrier_is_gunky_and_infinite :
    Mettapedia.Foundations.Gunk.IsGunky CantorAlgebra /\
      Infinite CantorAlgebra :=
  semanticCarrier_is_gunky_and_infinite

/-- A false identity remains semantically false after entering Prime. -/
theorem falseIdentity_not_meaning :
    ¬ theory.{u, v}.Meaning (booleanIdentityKind 2)
      falseIdentity := by
  intro meaningful
  exact falseIdentity_not_infinitePrimaryMeaning
      ((boolean_meaning_is_host_irrelevant.{u, v} 2
        falseIdentity).mpr meaningful)

/-- No replacement certificate makes the false identity pass inside Prime. -/
theorem boolean_falseIdentity_rejected
    (certificate : booleanContract.Certificate 2) :
    (contract.{u, v}.checker (booleanIdentityKind 2)).check
      falseIdentity certificate = false :=
  falseIdentity_rejected certificate

/-- An incomplete certificate remains rejected after entering Prime. -/
theorem boolean_incomplete_distributive_certificate_rejected :
    (contract.{u, v}.checker (booleanIdentityKind 2)).check
      distributiveIdentity [separatingAssignment] = false :=
  incomplete_distributive_certificate_rejected

#print axioms primeInclusion_conservative
#print axioms booleanInclusion_conservative
#print axioms boolean_scope_is_host_irrelevant
#print axioms boolean_meaning_is_host_irrelevant
#print axioms dependentPi_beta_replays
#print axioms boolean_distributive_replays
#print axioms boolean_distributive_has_infinitePrimaryMeaning
#print axioms boolean_semanticCarrier_is_gunky_and_infinite
#print axioms falseIdentity_not_meaning
#print axioms boolean_falseIdentity_rejected
#print axioms boolean_incomplete_distributive_certificate_rejected

end Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist
