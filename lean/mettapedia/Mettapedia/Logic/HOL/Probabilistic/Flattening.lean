import Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
import Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening

/-!
# Flattening for Hierarchical Probabilistic HOL

This module lifts the semantic `ProbHOL` layer from indexed model spaces to
hierarchical uncertainty over measures on those spaces.

The main theorem shape is Kyburg-style flattening: probabilities of HOL
sentences under a higher-order state are computed by flattening the hierarchy to
its predictive marginal. This follows the higher-order probability line
formalized elsewhere in the repository and documented by:

- Henry E. Kyburg, *Higher Order Probabilities*
- Haim Gaifman, *A Theory of Higher Order Probabilities* (1986)
- David Atkinson and Jeanne Peijnenburg,
  *A Consistent Set of Infinite-Order Probabilities* (2013)
- Michèle Giry, *A categorical approach to probability theory* (1982)
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.HOL.Probabilistic.ModelSpace
open MeasureTheory
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Semantic probability of a closed HOL sentence under a hierarchical
probabilistic state. -/
noncomputable def hierarchicalSentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) : ℝ≥0∞ :=
  sentenceProb H.baseSpace H.flattenedModelMeasure φ

theorem hierarchicalSentenceProb_eq_flat_sentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    hierarchicalSentenceProb H φ =
      sentenceProb H.baseSpace H.flattenedModelMeasure φ := by
  rfl

theorem hierarchicalSentenceProb_eq_integral_componentSentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    hierarchicalSentenceProb H φ =
      ∫⁻ θ, H.componentSentenceProb θ φ ∂H.pd.mixingMeasure := by
  unfold hierarchicalSentenceProb HierarchicalState.componentSentenceProb
  rw [sentenceProb, HierarchicalState.flattenedModelMeasure]
  simpa [sentenceProb] using
    Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten_apply H.pd
      (H.baseSpace.sentenceEvent φ)
      (H.baseSpace.measurable_sentenceEvent φ)

theorem hierarchicalSentenceProb_top_eq_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    :
    hierarchicalSentenceProb H (.top : ClosedFormula Const) = 1 := by
  simpa [hierarchicalSentenceProb, HierarchicalState.flattenedModelMeasure] using
    sentenceProb_top_eq_one
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      (hμ := by
        unfold HierarchicalState.flattenedModelMeasure
        infer_instance)

theorem hierarchicalSentenceProb_bot_eq_zero
    (H : HierarchicalState.{u, v, w, x} Base Const) :
    hierarchicalSentenceProb H (.bot : ClosedFormula Const) = 0 := by
  simpa [hierarchicalSentenceProb] using
    sentenceProb_bot_eq_zero
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)

theorem hierarchicalSentenceProb_mono_of_pointwiseImplies
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (himp : H.baseSpace.PointwiseImplies φ ψ) :
    hierarchicalSentenceProb H φ ≤ hierarchicalSentenceProb H ψ := by
  simpa [hierarchicalSentenceProb] using
    sentenceProb_mono_of_pointwiseImplies
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      himp

theorem hierarchicalSentenceProb_eq_of_pointwiseIff
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hiff : H.baseSpace.PointwiseIff φ ψ) :
    hierarchicalSentenceProb H φ = hierarchicalSentenceProb H ψ := by
  simpa [hierarchicalSentenceProb] using
    sentenceProb_eq_of_pointwiseIff
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      hiff

theorem hierarchicalSentenceProb_eq_of_pointwiseEq
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (heq : ∀ i : H.baseSpace.Idx,
      holSatisfies (H.baseSpace.model i) φ = holSatisfies (H.baseSpace.model i) ψ) :
    hierarchicalSentenceProb H φ = hierarchicalSentenceProb H ψ := by
  simpa [hierarchicalSentenceProb] using
    sentenceProb_eq_of_pointwiseEq
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      heq

/-- Hierarchical probability of a negated HOL sentence is the complement of
the flattened sentence probability. -/
theorem hierarchicalSentenceProb_not_eq_one_sub
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    hierarchicalSentenceProb H (.not φ) =
      1 - hierarchicalSentenceProb H φ := by
  simpa [hierarchicalSentenceProb] using
    sentenceProb_not_eq_one_sub
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      (hμ := by
        unfold HierarchicalState.flattenedModelMeasure
        infer_instance)
      φ

theorem flattenedModelMeasure_ofConstantMeasure_eq
    (S : ModelSpace Base Const)
    (μIdx : MeasureTheory.Measure S.Idx)
    [MeasureTheory.IsProbabilityMeasure μIdx] :
    (HierarchicalState.ofConstantMeasure S μIdx).flattenedModelMeasure = μIdx := by
  unfold HierarchicalState.flattenedModelMeasure HierarchicalState.ofConstantMeasure
  rw [Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten]
  rw [MeasureTheory.Measure.const_comp]
  simp

theorem hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb
    (S : ModelSpace Base Const)
    (μIdx : MeasureTheory.Measure S.Idx)
    [MeasureTheory.IsProbabilityMeasure μIdx]
    (φ : ClosedFormula Const) :
    hierarchicalSentenceProb (HierarchicalState.ofConstantMeasure S μIdx) φ =
      sentenceProb S μIdx φ := by
  rw [hierarchicalSentenceProb, flattenedModelMeasure_ofConstantMeasure_eq]
  rfl

theorem hierarchicalSentenceProb_ofDeterministic_eq_sentenceProb
    {Θ : Type x} [MeasurableSpace Θ]
    (S : ModelSpace Base Const)
    (f : Θ → S.Idx)
    (hf : Measurable f)
    (μ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (φ : ClosedFormula Const) :
    hierarchicalSentenceProb (HierarchicalState.ofDeterministic S f hf μ) φ =
      sentenceProb S (μ.map f) φ := by
  exact congrArg (fun m => sentenceProb S m φ)
    (Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution.flatten_deterministic
      (f := f) (μ := μ) hf)

end Mettapedia.Logic.HOL.Probabilistic
