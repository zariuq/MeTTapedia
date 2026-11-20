import Mettapedia.ProbabilityTheory.ImpreciseProbability.AnytimeConditional
import Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError

/-!
# Executable local Fréchet bounds for a conditional

The three inputs per branch are its carrier mass and the two marginal
masses inside it. A branch intersection is bounded without a product
assumption. The same query readout can then be tightened by the solver.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.BranchFrechet

open FiniteEventMass FiniteConditionalConstraints AnytimeConditional
open IntervalError

structure Marginals where
  carrier : ℚ
  left : ℚ
  right : ℚ
  left_nonneg : 0 ≤ left
  right_nonneg : 0 ≤ right
  left_fits : left ≤ carrier
  right_fits : right ≤ carrier

def Marginals.lower (r : Marginals) : ℚ := max 0 (r.left + r.right - r.carrier)
def Marginals.upper (r : Marginals) : ℚ := min r.left r.right

def bounds (pos neg : Marginals) : Answer :=
  let support := pos.left + neg.left
  if 0 < support then some ((pos.lower + neg.lower) / support, (pos.upper + neg.upper) / support)
  else none

variable {Ω : Type*} [Fintype Ω]

structure Matches (r : Marginals) (model : Distribution Ω) (left branch right : Event Ω) : Prop where
  carrier : mass model.weight branch = (r.carrier : ℝ)
  left : mass model.weight (fun w => left w && branch w) = (r.left : ℝ)
  right : mass model.weight (fun w => branch w && right w) = (r.right : ℝ)

theorem Matches.joint_bounds (r : Marginals) (model : Distribution Ω) (left branch right : Event Ω)
    (reads : Matches r model left branch right) :
    mass model.weight (fun w => left w && branch w && right w) ∈
      Set.Icc (r.lower : ℝ) (r.upper : ℝ) := by
  have identified := branch_frechet model.weight model.nonneg left branch right
  rw [reads.left, reads.right, reads.carrier] at identified
  simpa only [Marginals.lower, Marginals.upper, Rat.cast_max, Rat.cast_min, Rat.cast_sub,
    Rat.cast_add, Rat.cast_zero, Set.mem_Icc] using identified

theorem bounds_sound (model : Distribution Ω) (evidence split query : Event Ω)
    (pos neg : Marginals) (hi : Matches pos model evidence split query)
    (lo : Matches neg model evidence (fun w => !split w) query)
    (possible : 0 < mass model.weight evidence) :
    conditionalValue model query evidence ∈ range (bounds pos neg) := by
  have splitSupport := partition model.weight evidence split
  rw [hi.left, lo.left] at splitSupport
  have positiveSum : 0 < pos.left + neg.left := by
    exact_mod_cast (splitSupport ▸ possible)
  have splitJoint := partition model.weight (fun w => query w && evidence w) split
  have positive := hi.joint_bounds
  have negative := lo.joint_bounds
  simp only [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc] at positive negative splitJoint
  rw [bounds, if_pos positiveSum, range, conditionalValue, splitSupport]
  simp only [Rat.cast_div, Rat.cast_add, Set.mem_Icc, Bool.and_comm]
  have d : 0 ≤ (pos.left : ℝ) + neg.left := (show 0 < (pos.left : ℝ) + neg.left by
    exact_mod_cast positiveSum).le
  constructor
  · apply div_le_div_of_nonneg_right _ d
    linarith only [positive.1, negative.1, splitJoint]
  · apply div_le_div_of_nonneg_right _ d
    linarith only [positive.2, negative.2, splitJoint]

/-- Any point forecast can carry a guarantee measured over the full
enclosure. Its error depends on the farther endpoint. -/
theorem estimate_error {lo hi : ℚ} {actual point : ℝ}
    (within : actual ∈ range (some (lo, hi))) :
    |actual - point| ≤ intervalErrorRadius (lo : ℝ) (hi : ℝ) point :=
  error_le_intervalErrorRadius within

end Mettapedia.ProbabilityTheory.ImpreciseProbability.BranchFrechet
