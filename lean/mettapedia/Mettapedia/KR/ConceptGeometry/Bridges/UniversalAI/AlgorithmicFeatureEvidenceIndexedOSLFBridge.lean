import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowthBridge
import Mettapedia.OSLF.Framework.IndexedModalFunctor

/-!
# Indexed OSLF semantics for growing algorithmic-feature evidence

A finite evidence stage induces an operational GSLT whose terms are feature
indices and whose one-step reductions are the implications supported at that
stage.  Adding observations can refute a provisional implication, so these
operational theories are contravariant in the observed source set.  They form
a forward diagram over `OrderDual (Set SourceIndex)`.

Applying indexed OSLF to this diagram produces the corresponding family of
lax modal predicate theories.  The strict-growth control proves that the lax
qualification is necessary: the growth map preserves every later-supported
implication, but it need not cover all implications present at the earlier
stage and therefore need not commute with diamonds exactly.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth

universe u v

namespace FiniteFeatureExperiment

variable {SourceIndex : Type u} {FeatureIndex : Type v}
variable [Fintype SourceIndex] [Fintype FeatureIndex]

/-- Observation stages ordered oppositely, matching the antitone implication
relation. -/
abbrev ImplicationStage (SourceIndex : Type u) :=
  OrderDual (Set SourceIndex)

/-- The operational theory of implications supported by one observation
stage.  Equality is the only term equation; implication is the rewrite
relation. -/
abbrev implicationGSLTAt
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) : GSLT where
  Term := FeatureIndex
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := E.ImplicationAt observed
  rewrites_resp_left := by
    intro premise premise' consequent premiseEq implication
    subst premise'
    exact ⟨consequent, implication, rfl⟩
  rewrites_resp_right := by
    intro premise consequent consequent' implication consequentEq
    subst consequent'
    exact implication

@[simp]
theorem implicationGSLTAt_step_iff
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : Set SourceIndex) (premise consequent : FeatureIndex) :
    (E.implicationGSLTAt observed).Step premise consequent ↔
      E.ImplicationAt observed premise consequent :=
  Iff.rfl

/-- Observation growth gives a forward operational map in the reverse
direction: every implication surviving at the later stage was already valid
at the earlier stage. -/
def implicationGrowthTranslation
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later) :
    OperationalTranslation
      (E.implicationGSLTAt later) (E.implicationGSLTAt earlier) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun implication => E.implicationAt_anti growth implication

@[simp]
theorem implicationGrowthTranslation_mapTerm
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    {earlier later : Set SourceIndex} (growth : earlier ⊆ later)
    (feature : FeatureIndex) :
    (E.implicationGrowthTranslation growth).mapTerm feature = feature :=
  rfl

/-- The implication theories form a forward operational diagram after
reversing the observation-set order. -/
def implicationDiagram
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex) :
    IndexedOperational.Diagram (ImplicationStage SourceIndex) where
  obj observed := ⟨E.implicationGSLTAt (show Set SourceIndex from observed)⟩
  map {earlier later} growth :=
    E.implicationGrowthTranslation
      (show (show Set SourceIndex from later) ⊆
        (show Set SourceIndex from earlier) from CategoryTheory.leOfHom growth)
  map_id observed := by
    apply OperationalTranslation.ext
    rfl
  map_comp first second := by
    apply OperationalTranslation.ext
    rfl

@[simp]
theorem implicationDiagram_obj_theory
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (observed : ImplicationStage SourceIndex) :
    (E.implicationDiagram.obj observed).theory =
      E.implicationGSLTAt (show Set SourceIndex from observed) :=
  rfl

/-- Pointwise OSLF semantics for the growing implication diagram.  Since OSLF
is contravariant, its index is the opposite of the already dualized
observation order. -/
def implicationIndexedOSLF
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex) :
    CategoryTheory.Functor (ImplicationStage SourceIndex)ᵒᵖ
      ForwardModalPredicateTheory :=
  forwardIndexedOSLF E.implicationDiagram

end FiniteFeatureExperiment

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceIndexedOSLF

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth

/-! ## Strict-growth exactness boundary -/

/-- The operational map induced by the strict-growth control. -/
def growthCanaryTranslation :
    OperationalTranslation
      (growthCanaryExperiment.implicationGSLTAt laterObserved)
      (growthCanaryExperiment.implicationGSLTAt earlyObserved) :=
  growthCanaryExperiment.implicationGrowthTranslation
    earlyObserved_subset_laterObserved

/-- Positive control: the growth map preserves every implication supported at
the later stage. -/
theorem growthCanary_translation_preserves_steps
    {premise consequent : Bool}
    (step : (growthCanaryExperiment.implicationGSLTAt laterObserved).Step
      premise consequent) :
    (growthCanaryExperiment.implicationGSLTAt earlyObserved).Step
      (growthCanaryTranslation.mapTerm premise)
      (growthCanaryTranslation.mapTerm consequent) :=
  growthCanaryTranslation.mapStep step

/-- The same growth map is not locally covered: the provisional early edge
`false → true` has no later-stage lift after the checked counterexample is
added. -/
theorem growthCanary_translation_not_covered :
    ¬ Nonempty (StepCover
      (growthCanaryExperiment.implicationGSLTAt laterObserved)
      (growthCanaryExperiment.implicationGSLTAt earlyObserved)
      growthCanaryTranslation.mapTerm) := by
  rintro ⟨cover⟩
  have earlyStep :
      (growthCanaryExperiment.implicationGSLTAt earlyObserved).Step
        (growthCanaryTranslation.mapTerm false) true := by
    exact growthCanary_early_false_implies_true
  obtain ⟨sourceTarget, laterStep, targetEq⟩ := cover.liftStep earlyStep
  have sourceTargetEq : sourceTarget = true := by
    simpa [growthCanaryTranslation] using targetEq
  subst sourceTarget
  exact growthCanary_later_not_false_implies_true laterStep

/-- Consequently, modal diamond pullback along strict evidence growth cannot
commute exactly for every predicate. -/
theorem growthCanary_diamond_not_exact :
    ¬ ∀ predicate : Set Bool,
      Set.preimage growthCanaryTranslation.mapTerm
          (gsltDiamond
            (growthCanaryExperiment.implicationGSLTAt earlyObserved)
            predicate) =
        gsltDiamond
          (growthCanaryExperiment.implicationGSLTAt laterObserved)
          (Set.preimage growthCanaryTranslation.mapTerm predicate) := by
  intro commutes
  exact growthCanary_translation_not_covered
    ((Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.OperationalTranslation.diamondCommutation_iff_covered
      growthCanaryTranslation).mp commutes)

/-- The one-sided diamond law remains valid despite failure of exactness. -/
theorem growthCanary_diamond_lax (predicate : Set Bool) :
    gsltDiamond
        (growthCanaryExperiment.implicationGSLTAt laterObserved)
        (Set.preimage growthCanaryTranslation.mapTerm predicate) ≤
      Set.preimage growthCanaryTranslation.mapTerm
        (gsltDiamond
          (growthCanaryExperiment.implicationGSLTAt earlyObserved)
          predicate) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.preimage_diamond_le
    growthCanaryTranslation predicate

/-- The dual one-sided box law also remains valid. -/
theorem growthCanary_box_lax (predicate : Set Bool) :
    Set.preimage growthCanaryTranslation.mapTerm
        (gsltBox
          (growthCanaryExperiment.implicationGSLTAt earlyObserved)
          predicate) ≤
      gsltBox
        (growthCanaryExperiment.implicationGSLTAt laterObserved)
        (Set.preimage growthCanaryTranslation.mapTerm predicate) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.preimage_box_le
    growthCanaryTranslation predicate

section AxiomAudit

#print axioms FiniteFeatureExperiment.implicationGrowthTranslation
#print axioms FiniteFeatureExperiment.implicationDiagram
#print axioms FiniteFeatureExperiment.implicationIndexedOSLF
#print axioms growthCanary_translation_preserves_steps
#print axioms growthCanary_translation_not_covered
#print axioms growthCanary_diamond_not_exact
#print axioms growthCanary_diamond_lax
#print axioms growthCanary_box_lax

end AxiomAudit

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceIndexedOSLF
