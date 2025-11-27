import Mettapedia.MeasureTheory.FromSymmetry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-
# Examples of symmetric measures

Concrete instances illustrating how classical measures fit the
Knuth–Skilling symmetry framework.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory
open Mettapedia.MeasureTheory

namespace Mettapedia.Examples

/-! ## Example 1: Lebesgue measure on `[0,1]` -/

/-- Lebesgue measure restricted to `[0,1]` viewed as an unnormalized valuation (axiomatic). -/
axiom lebesgueValuation01 :
    UnnormalizedValuation (Set (Set.Icc (0 : ℝ) 1))

/-- Cox structure for the Lebesgue valuation on `[0,1]` (axiomatic placeholder). -/
axiom lebesgueCox01 :
    UnnormalizedCox (Set (Set.Icc (0 : ℝ) 1)) lebesgueValuation01

axiom lebesgueValuation01_univ :
    lebesgueValuation01.val Set.univ = (1 : ℝ≥0∞)

axiom lebesgueValuation01_half :
    lebesgueValuation01.val {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ≤ 1 / 2} =
      (1 / 2 : ℝ≥0∞)

/-! ## Example 2: Discrete uniform measure on a finite set -/

/-- Uniform valuation assigning mass `1/n` to each point of `Fin n` (axiomatic). -/
axiom uniformValuation (n : ℕ) : UnnormalizedValuation (Set (Fin n))

axiom uniformValuation_count (n k : ℕ) (hk : k ≤ n) :
    (uniformValuation n).val {i : Fin n | i.val < k} = (k : ℝ≥0∞) / n

/-! ## Example 3: Gaussian measure (sketch) -/

/-- Gaussian valuation on `ℝ` (sketch; treated axiomatically here). -/
axiom gaussianValuation : UnnormalizedValuation (Set ℝ)

/-- Cox structure witnessing Gaussian additivity (axiomatic placeholder). -/
axiom gaussianCox : UnnormalizedCox (Set ℝ) gaussianValuation

end Mettapedia.Examples
