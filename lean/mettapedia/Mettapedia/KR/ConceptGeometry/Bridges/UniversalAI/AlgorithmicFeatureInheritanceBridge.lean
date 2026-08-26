import Mettapedia.KR.ConceptGeometry.IntensionalInheritance
import Mettapedia.Logic.WorldModel.FeatureContainment

/-!
# Algorithmic features as crisp dual inheritance

Arthur Franz's algorithmic-containment programme interprets a property by a
compressive generator and implication by feature containment.  PLN's crisp
inheritance substrate interprets a concept by an extent and an intent.  This
file gives the exact bridge between those two semantic objects.

For one conditional algorithm `U`, the canonical concept of a feature program
`f` has

* extent: the sources for which `f` is a strict executable feature;
* intent: the feature programs strictly implied by `f`.

Under this interpretation, strict feature implication is equivalent to
extensional inheritance, intensional inheritance, and full dual inheritance.
This is a semantic identification, not a claim that Franz's algorithmic
complexity or WILLIAM's learned scores are PLN evidence values.

The bridge is deliberately strict.  Franz's 2026 family-level argument has
logarithmic description overhead; `FeatureImplicationWithBudget` records that
slack separately.  The negative control below proves that a one-bit budgeted
implication need not inhabit this exact inheritance relation.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureInheritance

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.FeatureContainment

/-- The dual concept canonically induced by a strict algorithmic feature. -/
def featureConcept (U : ConditionalAlgorithm) (feature : BinString) :
    DualConcept BinString BinString where
  extent := {source | StrictFeatureOf U feature source}
  intent := {consequent | StrictFeatureImplication U feature consequent}

/-- Interpret feature programs by their strict instance sets and their strict
consequence theories. -/
def featureInterpretation (U : ConditionalAlgorithm) :
    Interpretation BinString BinString BinString where
  meaning := featureConcept U

@[simp]
theorem mem_featureConcept_extent_iff
    (U : ConditionalAlgorithm) (feature source : BinString) :
    source ∈ (featureConcept U feature).extent ↔
      StrictFeatureOf U feature source :=
  Iff.rfl

@[simp]
theorem mem_featureConcept_intent_iff
    (U : ConditionalAlgorithm) (feature consequent : BinString) :
    consequent ∈ (featureConcept U feature).intent ↔
      StrictFeatureImplication U feature consequent :=
  Iff.rfl

/-- Extensional inclusion of strict feature instances is exactly strict
feature implication. -/
theorem extensionalInherits_iff_strictFeatureImplication
    (U : ConditionalAlgorithm) (premise consequent : BinString) :
    (featureInterpretation U).ExtensionalInherits premise consequent ↔
      StrictFeatureImplication U premise consequent := by
  constructor
  · intro inherits certificate source realizesPremise
    exact inherits ⟨certificate, realizesPremise⟩
  · intro implication source featureOfPremise
    obtain ⟨certificate, realizesPremise⟩ := featureOfPremise
    exact implication certificate source realizesPremise

/-- The consequence-theory intent is contravariant, so its inclusion is also
exactly strict feature implication. -/
theorem intensionalInherits_iff_strictFeatureImplication
    (U : ConditionalAlgorithm) (premise consequent : BinString) :
    (featureInterpretation U).IntensionalInherits premise consequent ↔
      StrictFeatureImplication U premise consequent := by
  constructor
  · intro inherits
    exact inherits (strictFeatureImplication_refl U consequent)
  · intro implication after impliedAfter
    exact strictFeatureImplication_trans implication impliedAfter

/-- Main bridge: strict algorithmic containment is exactly full crisp dual
inheritance under the canonical feature interpretation. -/
theorem inherits_iff_strictFeatureImplication
    (U : ConditionalAlgorithm) (premise consequent : BinString) :
    (featureInterpretation U).Inherits premise consequent ↔
      StrictFeatureImplication U premise consequent := by
  rw [Interpretation.inherits_iff,
    extensionalInherits_iff_strictFeatureImplication,
    intensionalInherits_iff_strictFeatureImplication, and_self]

/-- Positive control: every strict feature inherits itself in the canonical
interpretation, including the witnessed finite compression feature. -/
theorem finiteCompressionFeature_inherits_itself :
    (featureInterpretation finiteCompressionAlgorithm).Inherits
      finiteCompressionStep.featureProgram
      finiteCompressionStep.featureProgram := by
  exact (inherits_iff_strictFeatureImplication _ _ _).2
    (strictFeatureImplication_refl _ _)

/-- A witnessed strict instance is present in the extent of its feature
concept; inheritance is not being proved over an empty example. -/
theorem finiteCompressionSource_mem_featureExtent :
    fourTrue ∈
      (featureConcept finiteCompressionAlgorithm
        finiteCompressionStep.featureProgram).extent :=
  finiteCompressionStep_strictFeature

/-- Negative control: bare image inclusion does not yield algorithmic
inheritance because it can lose the strict compression condition. -/
theorem imageInclusion_does_not_imply_algorithmicInheritance :
    ImageIncluded imageCompressionAlgorithm [false] fourTrue ∧
      ¬ (featureInterpretation imageCompressionAlgorithm).Inherits
        [false] fourTrue := by
  refine ⟨shortImage_included_in_longImage, ?_⟩
  rw [inherits_iff_strictFeatureImplication]
  exact imageInclusion_does_not_imply_strictFeatureImplication.2.2

/-- Negative control: even a witnessed one-bit-slack implication does not
collapse to exact crisp inheritance. -/
theorem budgetedImplication_does_not_imply_algorithmicInheritance :
    WitnessedFeatureImplicationWithBudget imageCompressionAlgorithm
      (fun _ => 1) [false] fourTrue fourTrue ∧
      ¬ (featureInterpretation imageCompressionAlgorithm).Inherits
        [false] fourTrue := by
  refine ⟨shortImpliesLong_with_oneBitBudget, ?_⟩
  rw [inherits_iff_strictFeatureImplication]
  exact budgetedImplication_does_not_imply_strictFeatureImplication.2

#print axioms extensionalInherits_iff_strictFeatureImplication
#print axioms intensionalInherits_iff_strictFeatureImplication
#print axioms inherits_iff_strictFeatureImplication
#print axioms finiteCompressionFeature_inherits_itself
#print axioms finiteCompressionSource_mem_featureExtent
#print axioms imageInclusion_does_not_imply_algorithmicInheritance
#print axioms budgetedImplication_does_not_imply_algorithmicInheritance

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureInheritance
