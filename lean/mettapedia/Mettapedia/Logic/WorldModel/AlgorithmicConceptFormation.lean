import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConceptFormationBridge

/-!
# A strict finite hierarchy of algorithmic concepts

The canonical concept-formation bridge already proves that strict algorithmic
feature implication is exactly formal-concept order.  This module contributes
a nondegenerate finite control: two distinct features form a *strict* concept
hierarchy because the consequent feature compresses one additional source.

The control establishes all three required facts:

* every instance of the premise is an instance of the consequent;
* the consequent has a witnessed instance absent from the premise; and
* the resulting formal-concept order is strict, not merely reflexive.

The general closure, order-equivalence, and additive-slack boundary remain in
the imported concept-formation and inheritance bridges.
-/

namespace Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureInheritance
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConceptFormation
open Mettapedia.Logic.WorldModel.Algorithmic

/-! ## A strict finite hierarchy -/

/-- A second four-bit source used to witness proper extent inclusion. -/
def fourFalse : BinString := [false, false, false, false]

/-- A finite table with two distinct one-bit features.  Both compress
`fourTrue`, while only `[true]` also compresses `fourFalse`. -/
def conceptCanaryAlgorithm : ConditionalAlgorithm :=
  fun program condition =>
    if program = [false] ∧ condition = [] then Part.some fourTrue
    else if program = [true] ∧ condition = [] then Part.some fourTrue
    else if program = [true] ∧ condition = [false] then Part.some fourFalse
    else if program = [] ∧ condition = fourTrue then Part.some []
    else if program = [] ∧ condition = fourFalse then Part.some [false]
    else Part.none

/-- The more specific feature strictly compresses the shared source. -/
theorem conceptCanary_false_featureOf_fourTrue :
    StrictFeatureOf conceptCanaryAlgorithm [false] fourTrue := by
  refine ⟨{ descriptiveProgram := [], residual := [] }, ?_⟩
  exact ⟨by simp [conceptCanaryAlgorithm],
    by simp [conceptCanaryAlgorithm], by simp [fourTrue]⟩

/-- The more general feature also strictly compresses the shared source. -/
theorem conceptCanary_true_featureOf_fourTrue :
    StrictFeatureOf conceptCanaryAlgorithm [true] fourTrue := by
  refine ⟨{ descriptiveProgram := [], residual := [] }, ?_⟩
  exact ⟨by simp [conceptCanaryAlgorithm],
    by simp [conceptCanaryAlgorithm], by simp [fourTrue]⟩

theorem conceptCanary_false_implies_true :
    StrictFeatureImplication conceptCanaryAlgorithm [false] [true] := by
  intro certificate source realizesFalse
  rcases realizesFalse with ⟨_extracts, reconstructs, _compresses⟩
  have residualEmpty : certificate.residual = [] := by
    by_cases residualEmpty : certificate.residual = []
    · exact residualEmpty
    · simp [conceptCanaryAlgorithm, residualEmpty] at reconstructs
  have sourceEq : source = fourTrue := by
    rw [residualEmpty] at reconstructs
    simpa [conceptCanaryAlgorithm] using reconstructs
  subst source
  refine ⟨{ descriptiveProgram := [], residual := [] }, ?_⟩
  exact ⟨by simp [conceptCanaryAlgorithm],
    by simp [conceptCanaryAlgorithm], by simp [fourTrue]⟩

/-- The consequent feature has a second witnessed strict instance. -/
theorem conceptCanary_true_featureOf_fourFalse :
    StrictFeatureOf conceptCanaryAlgorithm [true] fourFalse := by
  refine ⟨{ descriptiveProgram := [], residual := [false] }, ?_⟩
  exact ⟨by simp [conceptCanaryAlgorithm, fourFalse, fourTrue],
    by simp [conceptCanaryAlgorithm, fourFalse],
    by simp [fourFalse]⟩

/-- The premise feature cannot reconstruct the second source. -/
theorem conceptCanary_false_not_featureOf_fourFalse :
    ¬ StrictFeatureOf conceptCanaryAlgorithm [false] fourFalse := by
  rintro ⟨certificate, _extracts, reconstructs, _compresses⟩
  by_cases residualEmpty : certificate.residual = []
  · rw [residualEmpty] at reconstructs
    simp [conceptCanaryAlgorithm, fourFalse] at reconstructs
    exact (by decide : fourFalse ≠ fourTrue) reconstructs
  · simp [conceptCanaryAlgorithm, residualEmpty] at reconstructs

/-- The witnessed additional source refutes the reverse implication. -/
theorem conceptCanary_true_not_implies_false :
    ¬ StrictFeatureImplication conceptCanaryAlgorithm [true] [false] := by
  intro implication
  obtain ⟨certificate, realizesTrue⟩ := conceptCanary_true_featureOf_fourFalse
  exact conceptCanary_false_not_featureOf_fourFalse
    (implication certificate fourFalse realizesTrue)

/-- Positive control: distinct executable features stand in full dual
inheritance in the intended direction. -/
theorem conceptCanary_distinct_features_inherit :
    (featureInterpretation conceptCanaryAlgorithm).Inherits
      [false] [true] :=
  (inherits_iff_strictFeatureImplication
    conceptCanaryAlgorithm [false] [true]).2 conceptCanary_false_implies_true

/-- The second source witnesses that the consequent extent properly contains
the premise extent. -/
theorem conceptCanary_proper_extent_witness :
    fourFalse ∈ (featureConcept conceptCanaryAlgorithm [true]).extent ∧
      fourFalse ∉ (featureConcept conceptCanaryAlgorithm [false]).extent := by
  exact ⟨conceptCanary_true_featureOf_fourFalse,
    conceptCanary_false_not_featureOf_fourFalse⟩

/-- The canonical formal concepts therefore form a strict order. -/
theorem conceptCanary_strict_formalConcept_order :
    featureFormalConcept conceptCanaryAlgorithm [false] <
      featureFormalConcept conceptCanaryAlgorithm [true] := by
  apply lt_of_le_of_ne
  · exact (featureFormalConcept_le_iff_strictFeatureImplication
      conceptCanaryAlgorithm [false] [true]).2 conceptCanary_false_implies_true
  · intro conceptsEqual
    apply conceptCanary_true_not_implies_false
    apply (featureFormalConcept_le_iff_strictFeatureImplication
      conceptCanaryAlgorithm [true] [false]).1
    rw [conceptsEqual]

section AxiomAudit

#print axioms conceptCanary_false_implies_true
#print axioms conceptCanary_false_featureOf_fourTrue
#print axioms conceptCanary_true_featureOf_fourTrue
#print axioms conceptCanary_true_featureOf_fourFalse
#print axioms conceptCanary_false_not_featureOf_fourFalse
#print axioms conceptCanary_true_not_implies_false
#print axioms conceptCanary_distinct_features_inherit
#print axioms conceptCanary_proper_extent_witness
#print axioms conceptCanary_strict_formalConcept_order

end AxiomAudit

end Mettapedia.Logic.WorldModel.AlgorithmicConceptFormationExamples
