import Mettapedia.Logic.HOL.Probabilistic.Flattening
import Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# Hierarchical ProbHOL Strength Bridge

This module is the PLN-facing readout of the core hierarchical `ProbHOL`
flattening layer.  The Logic layer provides sentence probabilities; this bridge
packages those probabilities as WM/PLN binary evidence and query strength.
-/

namespace Mettapedia.PLN.Bridges.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- WM-style evidence induced by a hierarchical sentence probability. -/
noncomputable def hierarchicalProbEvidence
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) : BinaryEvidence :=
  ⟨hierarchicalSentenceProb H φ, 1 - hierarchicalSentenceProb H φ⟩

/-- WM-style strength induced by a hierarchical sentence probability. -/
noncomputable def hierarchicalProbQueryStrength
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (hierarchicalProbEvidence H φ)

theorem hierarchicalProbEvidence_total_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    (hierarchicalProbEvidence H φ).total = 1 := by
  unfold hierarchicalProbEvidence BinaryEvidence.total
  have hle :
      hierarchicalSentenceProb H φ ≤ 1 := by
    simpa [hierarchicalSentenceProb, HierarchicalState.flattenedModelMeasure] using
      sentenceProb_le_one
        (S := H.baseSpace)
        (μ := H.flattenedModelMeasure)
        (hμ := by
          unfold HierarchicalState.flattenedModelMeasure
          infer_instance)
        (φ := φ)
  simpa using add_tsub_cancel_of_le hle

theorem hierarchicalProbQueryStrength_eq_sentenceProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    hierarchicalProbQueryStrength H φ = hierarchicalSentenceProb H φ := by
  unfold hierarchicalProbQueryStrength
  let p := hierarchicalSentenceProb H φ
  have hp : p ≤ 1 := by
    dsimp [p, hierarchicalSentenceProb]
    exact
      sentenceProb_le_one
        (S := H.baseSpace)
        (μ := H.flattenedModelMeasure)
        (hμ := by
          unfold HierarchicalState.flattenedModelMeasure
          infer_instance)
        (φ := φ)
  simpa [hierarchicalProbEvidence, p] using
    (BinaryEvidence.toStrength_of_scaled (s := p) (t := 1) hp one_ne_zero ENNReal.one_ne_top)

theorem hierarchicalProbQueryStrength_mono_of_pointwiseImplies
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (himp : H.baseSpace.PointwiseImplies φ ψ) :
    hierarchicalProbQueryStrength H φ ≤ hierarchicalProbQueryStrength H ψ := by
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalProbQueryStrength_eq_sentenceProb]
  exact hierarchicalSentenceProb_mono_of_pointwiseImplies (H := H) himp

theorem hierarchicalProbQueryStrength_eq_of_pointwiseIff
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hiff : H.baseSpace.PointwiseIff φ ψ) :
    hierarchicalProbQueryStrength H φ = hierarchicalProbQueryStrength H ψ := by
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalProbQueryStrength_eq_sentenceProb]
  exact hierarchicalSentenceProb_eq_of_pointwiseIff (H := H) hiff

end Mettapedia.PLN.Bridges.HOL.Probabilistic
