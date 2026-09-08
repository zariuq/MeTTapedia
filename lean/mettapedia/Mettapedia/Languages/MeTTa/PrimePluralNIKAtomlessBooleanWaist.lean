import Mettapedia.GSLT.LanguageDef.AtomlessBooleanEquationalEmbedding
import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist

/-!
# Atomless first-order semantics in the plural Prime NIK waist

The plural Prime waist retains the equational Boolean authority and adds the
strictly richer closed first-order atomless authority as a separate node.
Their meanings are related by a conservative universal-closure translation,
but their certificate disciplines are not collapsed: explicit truth-table
replay is certificate-sensitive, while the decidable first-order kernel erases
boundary evidence after qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanEquationalEmbedding
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision.Canary
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment

universe u v

private abbrev priorTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.theory.{u, v}

private abbrev priorContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.contract.{u, v}

private abbrev atomlessTheory :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.theory

private abbrev atomlessContract :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.contract

/-- The established Prime/Boolean waist or the richer atomless first-order
authority. -/
abbrev Kind := Sum
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.Kind Unit

def structuralDTTKind : Kind :=
  .inl
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.structuralDTTKind

def selectedDependentPiKind : Kind :=
  .inl
    Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.selectedDependentPiKind

def booleanIdentityKind (arity : Nat) : Kind :=
  .inl
    (Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.booleanIdentityKind
      arity)

def atomlessBooleanKind : Kind := .inr ()

def theory := Coproduct.theory priorTheory.{u, v} atomlessTheory

def contract :=
  Coproduct.contract priorTheory.{u, v} atomlessTheory priorContract.{u, v}
    atomlessContract

def priorInclusion :=
  Coproduct.leftInclusion priorTheory.{u, v} atomlessTheory priorContract.{u, v}
    atomlessContract

def atomlessInclusion :=
  Coproduct.rightInclusion priorTheory.{u, v} atomlessTheory priorContract.{u, v}
    atomlessContract

theorem priorInclusion_conservative :
    priorInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative priorTheory.{u, v} atomlessTheory
    priorContract.{u, v} atomlessContract

theorem atomlessInclusion_conservative :
    atomlessInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.rightInclusion_conservative priorTheory.{u, v} atomlessTheory
    priorContract.{u, v} atomlessContract

private theorem atomlessIdentity_conservative :
    (TheoryTranslation.identity atomlessTheory).Conservative where
  scope_reflecting := by
    intro kind formula inScope
    exact inScope
  meaning_reflecting := by
    intro kind formula meaningful
    exact meaningful

/-! ## Exact host irrelevance -/

theorem atomless_scope_is_host_irrelevant (formula : atomlessTheory.Claim ()) :
    atomlessTheory.Scope () formula <->
      theory.{u, v}.Scope atomlessBooleanKind formula :=
  HostIrrelevance.scope_iff
    (TheoryTranslation.identity atomlessTheory)
    atomlessInclusion.{u, v}.toTheoryTranslation
    atomlessIdentity_conservative atomlessInclusion_conservative.{u, v}
    () formula

theorem atomless_meaning_is_host_irrelevant
    (formula : atomlessTheory.Claim ()) :
    atomlessTheory.Meaning () formula <->
      theory.{u, v}.Meaning atomlessBooleanKind formula :=
  HostIrrelevance.meaning_iff
    (TheoryTranslation.identity atomlessTheory)
    atomlessInclusion.{u, v}.toTheoryTranslation
    atomlessIdentity_conservative atomlessInclusion_conservative.{u, v}
    () formula

/-! ## Retention and non-collapse controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem dependentPi_beta_replays :
    (contract.{u, v}.checker selectedDependentPiKind).check
      NIKProfile.canonicalCandidate NIKProfile.canonicalCertificate = true :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.dependentPi_beta_replays.{u, v}

theorem boolean_distributive_replays :
    (contract.{u, v}.checker (booleanIdentityKind 2)).check
      distributiveIdentity (fullTruthTable (Var := Fin 2)) = true :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.boolean_distributive_replays.{u, v}

theorem properPart_replays :
    (contract.{u, v}.checker atomlessBooleanKind).check
      properPartSentence () = true :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.Canary.properPart_replays

theorem properPart_has_infinitePrimaryMeaning :
    theory.{u, v}.Meaning atomlessBooleanKind properPartSentence :=
  (atomless_meaning_is_host_irrelevant.{u, v} properPartSentence).mp
    Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.Canary.properPart_has_coldMeaning

theorem noProperPart_rejected :
    (contract.{u, v}.checker atomlessBooleanKind).check
      Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.Canary.noProperPartSentence
      () = false :=
  Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority.Canary.noProperPart_rejected

/-- The richer node observes atomlessness even though the retained equational
node cannot. -/
theorem finiteBasis_disagrees_with_atomless_node :
    theory.{u, v}.Meaning atomlessBooleanKind properPartSentence /\
      ¬ Satisfies properPartSentence (emptyValuation (B := Bool)) :=
  ⟨properPart_has_infinitePrimaryMeaning.{u, v},
    properPartSentence_fails_in_bool⟩

/-- The semantic embedding exists and is conservative. -/
theorem equational_semantic_embedding_is_conservative :
    theoryTranslation.Conservative :=
  theoryTranslation_conservative

/-- The two proof disciplines remain observably different and therefore allow
no exact evidence-erasing authority translation. -/
theorem equational_authority_does_not_collapse_into_direct_decision :
    ¬ Nonempty (CertifiedTranslation
      Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority.contract
      atomlessContract) :=
  no_exact_authorityTranslation

end Canary

#print axioms priorInclusion_conservative
#print axioms atomlessInclusion_conservative
#print axioms atomless_scope_is_host_irrelevant
#print axioms atomless_meaning_is_host_irrelevant
#print axioms Canary.dependentPi_beta_replays
#print axioms Canary.boolean_distributive_replays
#print axioms Canary.properPart_replays
#print axioms Canary.properPart_has_infinitePrimaryMeaning
#print axioms Canary.noProperPart_rejected
#print axioms Canary.finiteBasis_disagrees_with_atomless_node
#print axioms Canary.equational_semantic_embedding_is_conservative
#print axioms Canary.equational_authority_does_not_collapse_into_direct_decision

end Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist
