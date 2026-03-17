import Mettapedia.Logic.HOL.Probabilistic.Semantics
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel

/-!
# Thin WM-Facing Bridge for Probabilistic HOL Semantics

This module turns semantic `ProbHOL` sentence probabilities into the same
`BinaryEvidence`/strength views used elsewhere in the PLN world-model interface.

The bridge is intentionally thin:

- semantic truth remains in `HOL/Semantics/Henkin.lean`,
- probabilistic truth remains in `HOL/Probabilistic/Semantics.lean`,
- and dynamic belief processes remain in `HOL/LogicalInduction/`.

This separation is important for future Logical Induction work in the sense of
Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor, *Logical Induction*,
arXiv:1609.03543v5 (2020).
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open MeasureTheory
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- BinaryEvidence view of semantic sentence probability: positive mass and the
complementary negative mass. -/
noncomputable def probEvidence
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (φ : ClosedFormula Const) : BinaryEvidence :=
  ⟨sentenceProb S μ φ, 1 - sentenceProb S μ φ⟩

/-- WM-style strength view of semantic sentence probability. -/
noncomputable def probQueryStrength
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (φ : ClosedFormula Const) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (probEvidence S μ φ)

theorem probEvidence_total_one
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    (φ : ClosedFormula Const) :
    (probEvidence S μ φ).total = 1 := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμ
  unfold probEvidence BinaryEvidence.total
  simpa using add_tsub_cancel_of_le (sentenceProb_le_one S μ hμ φ)

theorem probQueryStrength_eq_sentenceProb
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    (φ : ClosedFormula Const) :
    probQueryStrength S μ φ = sentenceProb S μ φ := by
  unfold probQueryStrength
  let p := sentenceProb S μ φ
  have hp : p ≤ 1 := sentenceProb_le_one S μ hμ φ
  simpa [probEvidence, p] using
    (BinaryEvidence.toStrength_of_scaled (s := p) (t := 1) hp one_ne_zero ENNReal.one_ne_top)

theorem probQueryStrength_mono_of_pointwiseImplies
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    {φ ψ : ClosedFormula Const}
    (himp : S.PointwiseImplies φ ψ) :
    probQueryStrength S μ φ ≤ probQueryStrength S μ ψ := by
  rw [probQueryStrength_eq_sentenceProb S μ hμ, probQueryStrength_eq_sentenceProb S μ hμ]
  exact sentenceProb_mono_of_pointwiseImplies S μ himp

theorem probQueryStrength_eq_of_pointwiseIff
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx) (hμ : MeasureTheory.IsProbabilityMeasure μ)
    {φ ψ : ClosedFormula Const}
    (hiff : S.PointwiseIff φ ψ) :
    probQueryStrength S μ φ = probQueryStrength S μ ψ := by
  rw [probQueryStrength_eq_sentenceProb S μ hμ, probQueryStrength_eq_sentenceProb S μ hμ]
  exact sentenceProb_eq_of_pointwiseIff S μ hiff

end Mettapedia.Logic.HOL.Probabilistic
