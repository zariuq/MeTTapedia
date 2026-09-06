import Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding
import Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist

/-!
# Finite-stage Cantor grounding in the plural Prime NIK waist

The Cantor-clopen atomless authority has two equivalent semantic
presentations:

* ordinary quantification over the ambient clopen algebra; and
* unbounded quantification over finite prefix-stage codes.

This module composes their exact authority translation with the established
atomless inclusion into Prime.  It also relates the same staged meaning to the
plural bootstrap atlas's `modelSound` lane.  The resulting vertical keeps
three boundaries explicit: finite generation presents the semantic carrier,
the atomless decision authority checks the selected first-order fragment, and
Prime retains that authority as one node among several.

The negative controls are essential.  This route lands only at Prime's
atomless node, and its semantic decision certificate does not authorize a
`sourceSound` claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding

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
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.theory.{u, v}

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.contract.{u, v}

private abbrev primeAtomlessKind :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.atomlessBooleanKind

/-! ## Exact authority route into Prime -/

/-- Compose finite-stage semantic grounding with the retained atomless Prime
authority. -/
def stagedToPrime : CertifiedTranslation finiteStageContract primeContract :=
  CertifiedTranslation.comp stagedToCold
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.atomlessInclusion

@[simp] theorem stagedToPrime_mapKind :
    stagedToPrime.{u, v}.mapKind () = primeAtomlessKind :=
  rfl

@[simp] theorem stagedToPrime_mapClaim (formula : Formula 0) :
    stagedToPrime.{u, v}.mapClaim () formula = formula :=
  rfl

theorem stagedToPrime_conservative :
    stagedToPrime.{u, v}.toTheoryTranslation.Conservative :=
  TheoryTranslation.Conservative.comp
    stagedToCold.toTheoryTranslation
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.atomlessInclusion.toTheoryTranslation
    stagedToCold_conservative
    Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.atomlessInclusion_conservative

/-- Native certificate replay commutes through the complete staged-to-Prime
route. -/
theorem stagedToPrime_check_commutes (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (primeContract.checker primeAtomlessKind).check formula
        (stagedToPrime.{u, v}.mapCertificate () certificate) =
      (finiteStageContract.checker ()).check formula certificate :=
  stagedToPrime.{u, v}.check_commutes () formula certificate

/-- Prime's atomless meaning is exactly the finite-stage meaning on routed
claims. -/
theorem primeMeaning_iff_stagedMeaning (formula : Formula 0) :
    primeTheory.{u, v}.Meaning primeAtomlessKind formula <->
      finiteStageTheory.Meaning () formula :=
  TheoryTranslation.meaning_iff_of_conservative
    stagedToPrime.{u, v}.toTheoryTranslation
    stagedToPrime_conservative.{u, v} () formula

/-! ## Relation to the plural bootstrap atlas -/

/-- The atlas's selected `modelSound` meaning is the same independently
stated staged meaning for this atomless fragment. -/
theorem atlasModelMeaning_iff_stagedMeaning (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Meaning
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula) <->
      finiteStageTheory.Meaning () formula := by
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.atlasModelMeaning_iff_stagedMeaning
      formula

/-- Atlas acceptance is qualified by the staged semantics, rather than being
used to define it. -/
theorem atlasModelAccepts_iff_stagedMeaning (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula)
        .semanticDecision = true <->
      finiteStageTheory.Meaning () formula := by
  exact
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.atlasModelAccepts_iff_stagedMeaning
      formula

/-- The selected Prime node and the atlas model lane agree exactly because
both have been qualified against the same staged semantic presentation. -/
theorem primeMeaning_iff_atlasModelMeaning (formula : Formula 0) :
    primeTheory.{u, v}.Meaning primeAtomlessKind formula <->
      Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.Meaning
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula) :=
  HostIrrelevance.meaning_iff
    stagedToPrime.{u, v}.toTheoryTranslation
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel.toTheoryTranslation
    stagedToPrime_conservative.{u, v}
    Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel_conservative
    () formula

/-- The two hosts also replay identically after receiving their distinct
translated certificate representations. -/
theorem primeAtlas_check_eq (formula : Formula 0)
    (certificate : finiteStageContract.Certificate ()) :
    (primeContract.{u, v}.checker primeAtomlessKind).check formula
        (stagedToPrime.{u, v}.mapCertificate () certificate) =
      Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          formula)
        .semanticDecision := by
  calc
    _ =
        ((Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.layer.toAuthorityContract.checker
          ()).check
          (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
            formula)
          .semanticDecision) := by
      simpa using HostIrrelevance.check_eq
        stagedToPrime.{u, v}
        Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel
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
  Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.Canary.properPart_replays.{u, v}

theorem properPart_replays_in_atlas :
    Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.modelClaim
          properPartSentence)
        .semanticDecision = true :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.Canary.properPart_replays_in_atlas

/-- Atomlessness has a concrete finite-stage witness even though no fixed
finite stage is itself atomless. -/
theorem properPart_retains_finite_stage_witness :
    exists code : FiniteClopenCode,
      code.decode ≠ (⊥ : CantorAlgebra) /\
        code.decode ≠ (⊤ : CantorAlgebra) :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorSemanticGrounding.Canary.properPart_has_finite_code

/-- The staged route is disjoint from every authority already retained in the
prior Prime waist. -/
theorem staged_route_does_not_land_in_prior
    (kind : Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.Kind) :
    not (stagedToPrime.{u, v}.mapKind () = Sum.inl kind) := by
  change not (Sum.inr () = Sum.inl kind)
  simp

/-- In particular, the composite cannot silently relabel an extensional
atomless claim as a structural DTT claim. -/
theorem staged_route_does_not_land_at_structuralDTT :
    not (stagedToPrime.{u, v}.mapKind () =
      Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.structuralDTTKind) := by
  simpa [Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.structuralDTTKind]
    using staged_route_does_not_land_in_prior.{u, v}
      Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.structuralDTTKind

/-- The same separation holds for the selected dependent-Pi authority. -/
theorem staged_route_does_not_land_at_selectedDependentPi :
    not (stagedToPrime.{u, v}.mapKind () =
      Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.selectedDependentPiKind) := by
  simpa [Mettapedia.Languages.MeTTa.PrimePluralNIKAtomlessBooleanWaist.selectedDependentPiKind]
    using staged_route_does_not_land_in_prior.{u, v}
      Mettapedia.Languages.MeTTa.PrimePluralNIKBooleanIdentityWaist.selectedDependentPiKind

/-- Model evidence does not acquire source-calculus soundness merely by
appearing in the lower atlas. -/
theorem staged_model_evidence_does_not_authorize_sourceSound
    (formula : Formula 0) :
    Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.checker.check
        (Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.sourceSoundClaim
          formula)
        .semanticDecision = false :=
  rfl

/-- The rejection reflects a stronger syntactic fact: source-soundness claims
are outside the image of the staged authority route. -/
theorem staged_route_has_no_sourceSound_image (formula : Formula 0) :
    Not (exists stagedFormula : Formula 0,
      Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.stagedToAtlasModel.mapClaim
          () stagedFormula =
        Mettapedia.GSLT.LanguageDef.NIKPluralBootstrapGroundAtlas.sourceSoundClaim
          formula) :=
  Mettapedia.GSLT.LanguageDef.GenerativeCantorBootstrapGrounding.Canary.sourceSound_not_in_image
    formula

end Canary

#print axioms stagedToPrime
#print axioms stagedToPrime_conservative
#print axioms stagedToPrime_check_commutes
#print axioms primeMeaning_iff_stagedMeaning
#print axioms atlasModelMeaning_iff_stagedMeaning
#print axioms atlasModelAccepts_iff_stagedMeaning
#print axioms primeMeaning_iff_atlasModelMeaning
#print axioms primeAtlas_check_eq
#print axioms Canary.properPart_replays_at_finite_stage
#print axioms Canary.properPart_replays_in_prime
#print axioms Canary.properPart_replays_in_atlas
#print axioms Canary.properPart_retains_finite_stage_witness
#print axioms Canary.staged_route_does_not_land_in_prior
#print axioms Canary.staged_route_does_not_land_at_structuralDTT
#print axioms Canary.staged_route_does_not_land_at_selectedDependentPi
#print axioms Canary.staged_model_evidence_does_not_authorize_sourceSound
#print axioms Canary.staged_route_has_no_sourceSound_image

end Mettapedia.Languages.MeTTa.PrimePluralNIKGenerativeAtomlessGrounding
