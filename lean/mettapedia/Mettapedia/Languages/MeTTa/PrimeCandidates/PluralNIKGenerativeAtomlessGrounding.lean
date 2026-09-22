import Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding
import Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist

/-!
# Finite-stage Cantor grounding in the plural candidate NIK waist

The Cantor-clopen atomless authority has two equivalent semantic
presentations:

* ordinary quantification over the ambient clopen algebra; and
* unbounded quantification over finite prefix-stage codes.

This module composes their exact authority translation with the established
atomless inclusion into candidate.  It also relates the same staged meaning to the
base checker's `modelSound` lane.  The resulting vertical keeps
three boundaries explicit: finite generation presents the semantic carrier,
the atomless decision authority checks the selected first-order fragment, and
candidate retains that authority as one node among several.

The negative controls are essential.  This route lands only at candidate's
atomless node, and its semantic decision certificate does not authorize a
`sourceSound` claim.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKGenerativeAtomlessGrounding

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderNIKAuthority
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.Ultrainfinite.GenerativeCantorAtomlessness

universe u v

private abbrev finiteStageTheory :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedTheory

private abbrev finiteStageContract :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.stagedContract

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.contract.{u, v}

private abbrev primeAtomlessKind :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.atomlessBooleanKind

/-! ## Exact authority route into candidate -/

/-- Compose finite-stage semantic grounding with the retained atomless candidate
authority. -/
def stagedToCandidate : CertifiedTranslation finiteStageContract primeContract :=
  CertifiedTranslation.comp stagedToCold
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.atomlessInclusion

@[simp] theorem stagedToCandidate_mapKind :
    stagedToCandidate.{u, v}.mapKind () = primeAtomlessKind :=
  rfl

@[simp] theorem stagedToCandidate_mapClaim (formula : Formula 0) :
    stagedToCandidate.{u, v}.mapClaim () formula = formula :=
  rfl

theorem stagedToCandidate_conservative :
    stagedToCandidate.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    stagedToCold.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.atomlessInclusion.toTheoryTranslation
    stagedToCold_conservative
    Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.atomlessInclusion_conservative

/-- Native certificate replay commutes through the complete staged-to-candidate
route. -/
theorem stagedToCandidate_check_commutes (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (primeContract.checker primeAtomlessKind).check formula
        (stagedToCandidate.{u, v}.mapCertificate () certificate) =
      (finiteStageContract.checker ()).check formula certificate :=
  stagedToCandidate.{u, v}.check_commutes () formula certificate

/-- candidate's atomless meaning is exactly the finite-stage meaning on routed
claims. -/
theorem primeMeaning_iff_stagedMeaning (formula : Formula 0) :
    primeTheory.{u, v}.Meaning primeAtomlessKind formula <->
      finiteStageTheory.Meaning () formula :=
  TheoryTranslation.meaning_iff_of_conservative
    stagedToCandidate.{u, v}.toTheoryTranslation
    stagedToCandidate_conservative.{u, v} () formula

/-! ## Relation to the base checker -/

/-- The base checker's selected `modelSound` meaning is the same independently
stated staged meaning for this atomless fragment. -/
theorem baseCheckerModelMeaning_iff_stagedMeaning (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKBaseChecker.Meaning
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula) <->
      finiteStageTheory.Meaning () formula := by
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.baseCheckerModelMeaning_iff_stagedMeaning
      formula

/-- Base-checker acceptance is qualified by the staged semantics, rather than being
used to define it. -/
theorem baseCheckerModelAccepts_iff_stagedMeaning (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKBaseChecker.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula)
        .semanticDecision = true <->
      finiteStageTheory.Meaning () formula := by
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.baseCheckerModelAccepts_iff_stagedMeaning
      formula

/-- The selected candidate node and the base checker model lane agree exactly because
both have been qualified against the same staged semantic presentation. -/
theorem primeMeaning_iff_baseCheckerModelMeaning (formula : Formula 0) :
    primeTheory.{u, v}.Meaning primeAtomlessKind formula <->
      Mettapedia.GSLT.LanguageDef.NIKBaseChecker.Meaning
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula) :=
  HostIrrelevance.meaning_iff
    stagedToCandidate.{u, v}.toTheoryTranslation
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel.toTheoryTranslation
    stagedToCandidate_conservative.{u, v}
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel_conservative
    () formula

/-- The two hosts also replay identically after receiving their distinct
translated certificate representations. -/
theorem primeCheck_eq_baseCheckerCheck (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (primeContract.{u, v}.checker primeAtomlessKind).check formula
        (stagedToCandidate.{u, v}.mapCertificate () certificate) =
      Mettapedia.GSLT.LanguageDef.NIKBaseChecker.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          formula)
        .semanticDecision := by
  calc
    _ =
        ((Mettapedia.GSLT.LanguageDef.NIKBaseChecker.layer.toAuthorityContract.checker
          ()).check
          (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
            formula)
          .semanticDecision) := by
      simpa using HostIrrelevance.check_eq
        stagedToCandidate.{u, v}
        Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel
        () formula certificate
    _ = _ := rfl

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_replays_at_finite_stage :
    (finiteStageContract.checker ()).check properPartSentence () = true :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_replays

theorem properPart_replays_in_prime :
    (primeContract.{u, v}.checker primeAtomlessKind).check
      properPartSentence () = true :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.Canary.properPart_replays.{u, v}

theorem properPart_accepted_by_base_checker :
    Mettapedia.GSLT.LanguageDef.NIKBaseChecker.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.modelClaim
          properPartSentence)
        .semanticDecision = true :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.Canary.properPart_accepted_by_base_checker

/-- Atomlessness has a concrete finite-stage witness even though no fixed
finite stage is itself atomless. -/
theorem properPart_retains_finite_stage_witness :
    exists code : FiniteClopenCode,
      code.decode ≠ (⊥ : CantorAlgebra) /\
        code.decode ≠ (⊤ : CantorAlgebra) :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_has_finite_code

/-- The staged route is disjoint from every authority already retained in the
prior candidate waist. -/
theorem staged_route_does_not_land_in_prior
    (kind : Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBooleanIdentityWaist.Kind) :
    not (stagedToCandidate.{u, v}.mapKind () = Sum.inl kind) := by
  change not (Sum.inr () = Sum.inl kind)
  simp

/-- In particular, the composite cannot silently relabel an extensional
atomless claim as a structural DTT claim. -/
theorem staged_route_does_not_land_at_structuralDTT :
    not (stagedToCandidate.{u, v}.mapKind () =
      Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.structuralDTTKind) := by
  exact staged_route_does_not_land_in_prior.{u, v}
      Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBooleanIdentityWaist.structuralDTTKind

/-- The same separation holds for the selected dependent-Pi authority. -/
theorem staged_route_does_not_land_at_selectedDependentPi :
    not (stagedToCandidate.{u, v}.mapKind () =
      Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKAtomlessBooleanWaist.selectedDependentPiKind) := by
  exact staged_route_does_not_land_in_prior.{u, v}
      Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKBooleanIdentityWaist.selectedDependentPiKind

/-- Model evidence does not acquire source-calculus soundness merely by
appearing in the base checker. -/
theorem staged_model_evidence_does_not_authorize_sourceSound
    (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKBaseChecker.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKBaseChecker.sourceSoundClaim
          formula)
        .semanticDecision = false :=
  rfl

/-- The rejection reflects a stronger syntactic fact: source-soundness claims
are outside the image of the staged authority route. -/
theorem staged_route_has_no_sourceSound_image (formula : Formula 0) :
    Not (exists stagedFormula : Formula 0,
      Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToBaseCheckerModel.mapClaim
          () stagedFormula =
        Mettapedia.GSLT.LanguageDef.NIKBaseChecker.sourceSoundClaim
          formula) :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.Canary.sourceSound_not_in_image
    formula

end Canary

#print axioms stagedToCandidate
#print axioms stagedToCandidate_conservative
#print axioms stagedToCandidate_check_commutes
#print axioms primeMeaning_iff_stagedMeaning
#print axioms baseCheckerModelMeaning_iff_stagedMeaning
#print axioms baseCheckerModelAccepts_iff_stagedMeaning
#print axioms primeMeaning_iff_baseCheckerModelMeaning
#print axioms primeCheck_eq_baseCheckerCheck
#print axioms Canary.properPart_replays_at_finite_stage
#print axioms Canary.properPart_replays_in_prime
#print axioms Canary.properPart_accepted_by_base_checker
#print axioms Canary.properPart_retains_finite_stage_witness
#print axioms Canary.staged_route_does_not_land_in_prior
#print axioms Canary.staged_route_does_not_land_at_structuralDTT
#print axioms Canary.staged_route_does_not_land_at_selectedDependentPi
#print axioms Canary.staged_model_evidence_does_not_authorize_sourceSound
#print axioms Canary.staged_route_has_no_sourceSound_image

end Mettapedia.Languages.MeTTa.PrimeCandidates.PluralNIKGenerativeAtomlessGrounding
