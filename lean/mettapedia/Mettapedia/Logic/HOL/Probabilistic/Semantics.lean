import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mettapedia.Logic.HOL.Probabilistic.ModelSpace

/-!
# Infinitary Semantic Probabilities of HOL Sentences

This module defines the canonical infinitary-first `ProbHOL` semantics:
probabilities of closed HOL formulas over measurable index spaces of pointed
Henkin models.

The abstraction is intentionally semantic and static. It should remain distinct
from the dynamic belief-process layer inspired by Garrabrant, Benson-Tilsen,
Critch, Soares, and Taylor, *Logical Induction*, arXiv:1609.03543v5 (2020).
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL.Probabilistic.ModelSpace
open Mettapedia.Logic.HOL.WorldModel
open MeasureTheory
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Semantic probability of a closed HOL sentence over an indexed measurable
family of pointed Henkin models. -/
noncomputable def sentenceProb
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (φ : ClosedFormula Const) : ℝ≥0∞ :=
  μ (S.sentenceEvent φ)

theorem sentenceProb_top_eq_one
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ) :
    sentenceProb S μ (.top : ClosedFormula Const) = 1 := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμ
  have hEvent : S.sentenceEvent (.top : ClosedFormula Const) = Set.univ := by
    ext i
    simp [ModelSpace.sentenceEvent, holSatisfies, HenkinModel.models_top]
  simp [sentenceProb, hEvent]

theorem sentenceProb_bot_eq_zero
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) :
    sentenceProb S μ (.bot : ClosedFormula Const) = 0 := by
  have hEvent : S.sentenceEvent (.bot : ClosedFormula Const) = ∅ := by
    ext i
    simp [ModelSpace.sentenceEvent, holSatisfies, HenkinModel.models_bot]
  simp [sentenceProb, hEvent]

theorem sentenceProb_le_one
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    (φ : ClosedFormula Const) :
    sentenceProb S μ φ ≤ 1 := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμ
  have := measure_mono (μ := μ) (Set.subset_univ (S.sentenceEvent φ))
  simpa [sentenceProb] using this

theorem sentenceProb_mono_of_pointwiseImplies
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    {φ ψ : ClosedFormula Const}
    (himp : S.PointwiseImplies φ ψ) :
    sentenceProb S μ φ ≤ sentenceProb S μ ψ := by
  exact measure_mono (μ := μ) (S.sentenceEvent_subset_of_pointwiseImplies himp)

theorem sentenceProb_eq_of_pointwiseIff
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    {φ ψ : ClosedFormula Const}
    (hiff : S.PointwiseIff φ ψ) :
    sentenceProb S μ φ = sentenceProb S μ ψ := by
  rw [sentenceProb, sentenceProb, S.sentenceEvent_eq_of_pointwiseIff hiff]

theorem sentenceProb_eq_of_pointwiseEq
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    {φ ψ : ClosedFormula Const}
    (heq : ∀ i : S.Idx, holSatisfies (S.model i) φ = holSatisfies (S.model i) ψ) :
    sentenceProb S μ φ = sentenceProb S μ ψ := by
  rw [sentenceProb, sentenceProb, S.sentenceEvent_eq_of_pointwiseEq heq]

end Mettapedia.Logic.HOL.Probabilistic
