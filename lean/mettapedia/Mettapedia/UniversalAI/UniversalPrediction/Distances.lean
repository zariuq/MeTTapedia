import Mettapedia.UniversalAI.UniversalPrediction.PrefixMeasure
import Mettapedia.UniversalAI.UniversalPrediction.Entropy

/-!
# Binary Prediction Distances (Hutter 2005, Chapter 3)

This file connects the analytic binary entropy inequalities from
`Mettapedia.UniversalAI.UniversalPrediction.Entropy` to the `PrefixMeasure` interface.

In particular, it defines (for a prefix `x`) the next-bit probability
`Pμ(true | x)` and the associated instantaneous distances

* squared distance `s`
* relative entropy `d`

and proves the pointwise inequality `s ≤ d` under the mild hypothesis that
`Pξ(true | x) ∈ (0,1)`.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical

namespace Distances

open Entropy

/-- ENNReal conditional probability of the next bit, derived from a prefix measure. -/
def condENN (μ : PrefixMeasure) (x : BinString) (b : Bool) : ENNReal :=
  conditionalENN μ.toSemimeasure [b] x

/-- Real-valued conditional probability of the next bit. -/
def condProb (μ : PrefixMeasure) (x : BinString) (b : Bool) : ℝ :=
  (condENN μ x b).toReal

/-- `Pμ(true | x)` as a real number. -/
def pTrue (μ : PrefixMeasure) (x : BinString) : ℝ :=
  condProb μ x true

lemma condENN_le_one (μ : PrefixMeasure) (x : BinString) (b : Bool) : condENN μ x b ≤ 1 := by
  unfold condENN
  -- `μ(xb) ≤ μ(x)` implies `μ(xb)/μ(x) ≤ 1`.
  unfold conditionalENN
  have hb0 : μ.toSemimeasure x ≠ 0 ∨ (1 : ENNReal) ≠ (⊤ : ENNReal) := Or.inr (by simp)
  have hbt : μ.toSemimeasure x ≠ (⊤ : ENNReal) ∨ (1 : ENNReal) ≠ 0 := Or.inr (by simp)
  have hmono : μ.toSemimeasure (x ++ [b]) ≤ μ.toSemimeasure x := by
    simpa using (μ.toSemimeasure.mono x b)
  have : μ.toSemimeasure (x ++ [b]) ≤ (1 : ENNReal) * μ.toSemimeasure x := by
    simpa [one_mul] using hmono
  exact (ENNReal.div_le_iff_le_mul hb0 hbt).2 this

lemma pTrue_mem_Icc (μ : PrefixMeasure) (x : BinString) : pTrue μ x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · unfold pTrue condProb
    exact ENNReal.toReal_nonneg
  · unfold pTrue condProb
    have hle : condENN μ x true ≤ 1 := condENN_le_one (μ := μ) (x := x) (b := true)
    have hto : (condENN μ x true).toReal ≤ (1 : ENNReal).toReal :=
      ENNReal.toReal_mono (hb := by simp) hle
    simpa using hto

/-- Instantaneous squared distance between `μ(·|x)` and `ξ(·|x)` in the binary setting. -/
def s (μ ξ : PrefixMeasure) (x : BinString) : ℝ :=
  sqDistBinary (pTrue μ x) (pTrue ξ x)

/-- Instantaneous (binary) relative entropy between `μ(·|x)` and `ξ(·|x)`.

Note: this is meaningful under hypotheses ensuring `pTrue ξ x ∈ (0,1)` (or under domination
assumptions that rule out the problematic boundary cases). -/
def d (μ ξ : PrefixMeasure) (x : BinString) : ℝ :=
  klBinary (pTrue μ x) (pTrue ξ x)

theorem s_le_d_of_pTrue_mem_Ioo (μ ξ : PrefixMeasure) (x : BinString)
    (hξ : pTrue ξ x ∈ Set.Ioo (0 : ℝ) 1) : s μ ξ x ≤ d μ ξ x := by
  unfold s d
  have hμ : pTrue μ x ∈ Set.Icc (0 : ℝ) 1 := pTrue_mem_Icc (μ := μ) (x := x)
  exact sqDistBinary_le_klBinary_Icc_left (y := pTrue μ x) (z := pTrue ξ x) hμ hξ

end Distances

end Mettapedia.UniversalAI.UniversalPrediction

