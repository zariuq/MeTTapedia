import Mettapedia.Computability.HutterComputabilityENNReal
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.HutterEnumeration
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Computability of Countable Mixtures (Finite Alphabet)

This file factors out a reusable lemma used across the “Hook B” developments:

*if `x ↦ (w i * μᵢ x).toReal` is uniformly lower semicomputable and the pointwise weighted sum is
finite, then the `xiPrefixMeasure` mixture is a lower-semicomputable prefix measure.*

This isolates the boilerplate around `tsum`/`ENNReal.toReal` so individual models only need to
prove lower-semicomputability for the component terms.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

open Mettapedia.Computability.Hutter

variable {α : Type*} [Fintype α] [Primcodable α]

namespace Computability

/-- A countable (`ℕ`-indexed) mixture of prefix measures is lower semicomputable provided the
weighted term map is uniformly lower semicomputable and the pointwise sum is finite.

This is the standard computability “glue” needed to turn Hook‑B hyperprior mixtures into valid
competitors for Solomonoff/V3 bounds. -/
theorem lsc_xiPrefixMeasure_nat (ν : ℕ → PrefixMeasure α) (w : ℕ → ENNReal) (hw : (∑' n, w n) = 1)
    (hf_ne_top : ∀ n x, w n * ν n x ≠ ⊤)
    (hsum : ∀ x, Summable (fun n : ℕ => (w n * ν n x).toReal))
    (hLSC : LowerSemicomputable (fun p : ℕ × Word α => (w p.1 * ν p.1 p.2).toReal)) :
    LowerSemicomputablePrefixMeasure (α := α) (xiPrefixMeasure (ν := ν) (w := w) (hw := hw)) := by
  -- First, show the `ENNReal`-valued `tsum` is lower semicomputable after applying `toReal`.
  have hLSC_sum :
      LowerSemicomputable (fun x : Word α => (∑' n : ℕ, w n * ν n x).toReal) :=
    LowerSemicomputable.tsum_toReal_of_nonneg
      (f := fun n x => w n * ν n x)
      (hf_ne_top := by
        intro n x
        simpa using hf_ne_top n x)
      (hsum := by
        intro x
        simpa using hsum x)
      (hLSC := hLSC)
  -- Rewrite the mixture's `toReal` as the same `tsum`.
  have hEq : ∀ x : Word α,
      (xiPrefixMeasure (ν := ν) (w := w) (hw := hw) x).toReal = (∑' n : ℕ, w n * ν n x).toReal := by
    intro x
    simp [xiPrefixMeasure, PrefixMeasure.toSemimeasure, xiFun]
  -- Finish by pointwise equality.
  refine LowerSemicomputable.congr (f := fun x : Word α => (∑' n : ℕ, w n * ν n x).toReal)
    (g := fun x : Word α => (xiPrefixMeasure (ν := ν) (w := w) (hw := hw) x).toReal)
    hLSC_sum (fun x => (hEq x).symm)

end Computability

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

