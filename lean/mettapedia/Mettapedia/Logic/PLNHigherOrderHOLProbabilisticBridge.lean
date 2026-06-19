import Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
import Mettapedia.Logic.HOL.Probabilistic.Flattening

/-!
# Probabilistic Higher-Order HOL Predicate Bridge

This file connects the theoremic predicate bridge to the existing ProbHOL /
Kyburg flattening layer. The crisp bridge says when a pointed Henkin model
validates predicate inheritance or equivalence. This layer asks for the
flattened higher-order probability of those HOL predicate sentences over a
hierarchical model-space state.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.HOL.Probabilistic.ModelSpace
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Flattened hierarchical strength of the HOL predicate-inheritance sentence
`∀x, p x -> q x`. -/
noncomputable def hierarchicalPredicateImplicationStrength
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ≥0∞ :=
  hierarchicalProbQueryStrength H
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)

/-- Flattened hierarchical strength of the HOL predicate-equivalence sentence.
This is the probabilistic sibling of crisp predicate similarity: it measures the
Kyburg-flattened probability that the two predicates mutually inherit. -/
noncomputable def hierarchicalPredicateSimilarityStrength
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ≥0∞ :=
  hierarchicalProbQueryStrength H
    (predicateIffFormula (Base := Base) (Const := Const) σ p q)

/-- Flattened hierarchical strength of universal predicate truth `∀x, p x`. -/
noncomputable def hierarchicalPredicateForAllStrength
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ≥0∞ :=
  hierarchicalProbQueryStrength H
    (predicateForAllFormula (Base := Base) (Const := Const) σ p)

/-- Flattened hierarchical strength of existential predicate truth `∃x, p x`. -/
noncomputable def hierarchicalPredicateExistsStrength
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ≥0∞ :=
  hierarchicalProbQueryStrength H
    (predicateExistsFormula (Base := Base) (Const := Const) σ p)

/-- The predicate-implication strength is definitionally the ProbHOL/Kyburg
flattened sentence probability of the HOL implication formula. -/
theorem hierarchicalPredicateImplicationStrength_eq_sentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    hierarchicalPredicateImplicationStrength H σ p q =
      hierarchicalSentenceProb H
        (predicateImpFormula (Base := Base) (Const := Const) σ p q) := by
  simp [hierarchicalPredicateImplicationStrength,
    hierarchicalProbQueryStrength_eq_sentenceProb]

/-- The predicate-similarity strength is the flattened sentence probability of
the HOL equivalence formula. -/
theorem hierarchicalPredicateSimilarityStrength_eq_sentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    hierarchicalPredicateSimilarityStrength H σ p q =
      hierarchicalSentenceProb H
        (predicateIffFormula (Base := Base) (Const := Const) σ p q) := by
  simp [hierarchicalPredicateSimilarityStrength,
    hierarchicalProbQueryStrength_eq_sentenceProb]

/-- Pointwise predicate inheritance over the indexed model space transports
universal predicate probability monotonically. -/
theorem hierarchicalPredicateForAllStrength_mono_of_pointwiseInherits
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      ∀ i : H.baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          (H.baseSpace.model i) σ).Inherits p q) :
    hierarchicalPredicateForAllStrength H σ p ≤
      hierarchicalPredicateForAllStrength H σ q := by
  unfold hierarchicalPredicateForAllStrength
  exact
    hierarchicalProbQueryStrength_mono_of_pointwiseImplies
      (H := H)
      (φ := predicateForAllFormula (Base := Base) (Const := Const) σ p)
      (ψ := predicateForAllFormula (Base := Base) (Const := Const) σ q)
      (by
        intro i hAll
        exact
          predicateForAll_mono_of_inherits
            (Base := Base) (Const := Const)
            (H.baseSpace.model i) σ p q (hInh i) hAll)

/-- Pointwise predicate inheritance over the indexed model space transports
existential predicate probability monotonically. -/
theorem hierarchicalPredicateExistsStrength_mono_of_pointwiseInherits
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      ∀ i : H.baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          (H.baseSpace.model i) σ).Inherits p q) :
    hierarchicalPredicateExistsStrength H σ p ≤
      hierarchicalPredicateExistsStrength H σ q := by
  unfold hierarchicalPredicateExistsStrength
  exact
    hierarchicalProbQueryStrength_mono_of_pointwiseImplies
      (H := H)
      (φ := predicateExistsFormula (Base := Base) (Const := Const) σ p)
      (ψ := predicateExistsFormula (Base := Base) (Const := Const) σ q)
      (by
        intro i hExists
        exact
          predicateExists_mono_of_inherits
            (Base := Base) (Const := Const)
            (H.baseSpace.model i) σ p q (hInh i) hExists)

/-- Predicate-equivalence formulas are pointwise symmetric over any indexed
model space. -/
theorem pointwiseIff_predicateIffFormula_comm
    (S : ModelSpace.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    S.PointwiseIff
      (predicateIffFormula (Base := Base) (Const := Const) σ p q)
      (predicateIffFormula (Base := Base) (Const := Const) σ q p) := by
  intro i
  constructor
  · intro hpq
    have hMutual :
        predicateMutualInheritsAt (Base := Base) (Const := Const)
          (S.model i) σ p q :=
      (predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) (S.model i) σ p q).2 hpq
    exact
      (predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) (S.model i) σ q p).1
        ((predicateInterpretation (Base := Base) (Const := Const)
          (S.model i) σ).mutualInherits_symm hMutual)
  · intro hqp
    have hMutual :
        predicateMutualInheritsAt (Base := Base) (Const := Const)
          (S.model i) σ q p :=
      (predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) (S.model i) σ q p).2 hqp
    exact
      (predicateMutualInheritsAt_iff_models_predicateIffFormula
        (Base := Base) (Const := Const) (S.model i) σ p q).1
        ((predicateInterpretation (Base := Base) (Const := Const)
          (S.model i) σ).mutualInherits_symm hMutual)

/-- The probabilistic predicate-similarity readout is symmetric because it is
the flattened probability of a symmetric HOL predicate-equivalence formula. -/
theorem hierarchicalPredicateSimilarityStrength_comm
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    hierarchicalPredicateSimilarityStrength H σ p q =
      hierarchicalPredicateSimilarityStrength H σ q p := by
  unfold hierarchicalPredicateSimilarityStrength
  exact
    hierarchicalProbQueryStrength_eq_of_pointwiseIff
      (H := H)
      (pointwiseIff_predicateIffFormula_comm
        (Base := Base) (Const := Const) H.baseSpace σ p q)

/-- If every indexed model validates mutual predicate inheritance, then the
Kyburg-flattened predicate-similarity strength is maximal. -/
theorem hierarchicalPredicateSimilarityStrength_eq_one_of_pointwiseMutualInherits
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hMutual :
      ∀ i : H.baseSpace.Idx,
        predicateMutualInheritsAt (Base := Base) (Const := Const)
          (H.baseSpace.model i) σ p q) :
    hierarchicalPredicateSimilarityStrength H σ p q = 1 := by
  unfold hierarchicalPredicateSimilarityStrength
  have hTop :
      H.baseSpace.PointwiseIff
        (.top : ClosedFormula Const)
        (predicateIffFormula (Base := Base) (Const := Const) σ p q) := by
    intro i
    constructor
    · intro _hTop
      exact
        (predicateMutualInheritsAt_iff_models_predicateIffFormula
          (Base := Base) (Const := Const) (H.baseSpace.model i) σ p q).1
          (hMutual i)
    · intro _hIff
      exact HenkinModel.models_top (H.baseSpace.model i)
  rw [← hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := H) hTop]
  exact
    hierarchicalProbQueryStrength_eq_sentenceProb
      (H := H) (.top : ClosedFormula Const) |>.trans
      (hierarchicalSentenceProb_top_eq_one (H := H))

/-- If no indexed model validates mutual predicate inheritance, then the
Kyburg-flattened predicate-similarity strength is zero. -/
theorem hierarchicalPredicateSimilarityStrength_eq_zero_of_pointwiseNotMutualInherits
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hNotMutual :
      ∀ i : H.baseSpace.Idx,
        ¬ predicateMutualInheritsAt (Base := Base) (Const := Const)
          (H.baseSpace.model i) σ p q) :
    hierarchicalPredicateSimilarityStrength H σ p q = 0 := by
  unfold hierarchicalPredicateSimilarityStrength
  have hBot :
      H.baseSpace.PointwiseIff
        (predicateIffFormula (Base := Base) (Const := Const) σ p q)
        (.bot : ClosedFormula Const) := by
    intro i
    constructor
    · intro hIff
      exact
        (hNotMutual i)
          ((predicateMutualInheritsAt_iff_models_predicateIffFormula
            (Base := Base) (Const := Const) (H.baseSpace.model i) σ p q).2 hIff)
    · intro hBotModel
      exact False.elim
        (HenkinModel.models_bot (H.baseSpace.model i) hBotModel)
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := H) hBot]
  exact
    hierarchicalProbQueryStrength_eq_sentenceProb
      (H := H) (.bot : ClosedFormula Const) |>.trans
      (hierarchicalSentenceProb_bot_eq_zero (H := H))

end Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge
