import Mettapedia.MeasureTheory.FromSymmetry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Examples of symmetric measures

Concrete instances illustrating how classical measures fit the
Knuth–Skilling symmetry framework.

## Note on approach

Rather than using global axioms (which are "cheats"), we use section
variables that make assumptions explicit. To actually construct these
instances from Mathlib's Lebesgue/Gaussian measures would require
substantial additional infrastructure.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory
open Mettapedia.MeasureTheory

namespace Mettapedia.Examples

/-! ## Example 1: Lebesgue measure on `[0,1]`

Assuming we have a valuation representing Lebesgue measure on [0,1],
we can derive various properties.

### Assumptions:
- `lebesgueValuation01`: Lebesgue measure restricted to `[0,1]` as an unnormalized valuation
- `lebesgueCox01`: Cox structure for the Lebesgue valuation
- `lebesgueValuation01_univ`: The whole interval has measure 1
- `lebesgueValuation01_half`: The left half [0, 1/2] has measure 1/2
-/

section LebesgueExample

variable (lebesgueValuation01 : UnnormalizedValuation (Set (Set.Icc (0 : ℝ) 1)))
variable (lebesgueCox01 : UnnormalizedCox (Set (Set.Icc (0 : ℝ) 1)) lebesgueValuation01)
variable (lebesgueValuation01_univ : lebesgueValuation01.val Set.univ = (1 : ℝ≥0∞))
variable (lebesgueValuation01_half :
    lebesgueValuation01.val {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ≤ 1 / 2} = (1 / 2 : ℝ≥0∞))

/-- Under the Cox structure, the combination function is addition. -/
theorem lebesgue_combine_is_add :
    ∀ x y, lebesgueCox01.combine_fn x y = x + y :=
  unnormalized_combine_is_add lebesgueValuation01 lebesgueCox01

end LebesgueExample

/-! ## Example 2: Discrete uniform measure on a finite set

### Assumptions:
- `uniformValuation`: Uniform valuation assigning mass `1/n` to each point of `Fin n`
- `uniformValuation_count`: The count property for uniform measure
-/

section UniformExample

variable (uniformValuation : (n : ℕ) → UnnormalizedValuation (Set (Fin n)))
variable (uniformValuation_count : ∀ n k : ℕ, k ≤ n →
    (uniformValuation n).val {i : Fin n | i.val < k} = (k : ℝ≥0∞) / n)

/-- The uniform valuation of the empty set is 0 (from the structure). -/
theorem uniform_empty (n : ℕ) : (uniformValuation n).val ∅ = 0 :=
  (uniformValuation n).val_bot

end UniformExample

/-! ## Example 3: Gaussian measure (sketch)

### Assumptions:
- `gaussianValuation`: Gaussian valuation on `ℝ`
- `gaussianCox`: Cox structure witnessing Gaussian additivity
-/

section GaussianExample

variable (gaussianValuation : UnnormalizedValuation (Set ℝ))
variable (gaussianCox : UnnormalizedCox (Set ℝ) gaussianValuation)

/-- Under the Cox structure, Gaussian combination is addition. -/
theorem gaussian_combine_is_add :
    ∀ x y, gaussianCox.combine_fn x y = x + y :=
  unnormalized_combine_is_add gaussianValuation gaussianCox

end GaussianExample

end Mettapedia.Examples
