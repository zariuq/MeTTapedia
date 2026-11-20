import Mettapedia.ProbabilityTheory.ImpreciseProbability.FiniteConditionalConstraints
import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError

/-!
# Approximate screening as simultaneous conditional constraints

A certified absolute-error radius on a reference row gives a clipped
conditional constraint. Mixtures of two such rows follow the law of
total probability. A stratum with zero mass contributes zero, so the
proof uses conditional probabilities only at the outer query.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.ScreeningBand

open FiniteConditionalConstraints FiniteEventMass
open Mettapedia.ProbabilityTheory.StochasticInference (UnitProbability)

variable {Ω : Type*}

def around (event condition : Event Ω) (center : UnitProbability)
    (radius : ℚ) (nonnegative : 0 ≤ radius) : Constraint Ω where
  event := event
  condition := condition
  lower := max 0 (center.val - radius)
  upper := min 1 (center.val + radius)
  nonneg := le_max_left _ _
  bounded := min_le_left _ _
  ordered := (max_le center.nonneg (by linarith)).trans
    (le_min center.le_one (by linarith))

variable [Fintype Ω]

theorem around_iff (model : Distribution Ω) (event condition : Event Ω) (center : UnitProbability)
    (radius : ℚ) (nonnegative : 0 ≤ radius) (possible : 0 < mass model.weight condition) :
    (around event condition center radius nonnegative).Holds model.weight ↔
      |conditionalValue model event condition - (center.val : ℝ)| ≤ (radius : ℝ) := by
  rw [Constraint.holds_iff_conditional _ model possible, abs_le]
  have unit := conditionalValue_mem_unit model event condition possible
  simp only [around, Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
    Rat.cast_one, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨_, l⟩, _, u⟩
    constructor <;> linarith
  · rintro ⟨l, u⟩
    exact ⟨⟨unit.1, by linarith⟩, unit.2, by linarith⟩

private def blend {R : Type*} [Ring R] (weight yes no : R) : R :=
  weight * yes + (1 - weight) * no

def mixRows (branchWeight : UnitProbability) (positive negative : Constraint Ω) : ℚ × ℚ :=
  (blend branchWeight.val positive.lower negative.lower, blend branchWeight.val positive.upper negative.upper)

private theorem mixRows_real (model : Distribution Ω) (event context split : Event Ω)
    (possible : 0 < mass model.weight context) (p : ℝ) (weight : conditionalValue model split context = p)
    (positive negative : Constraint Ω)
    (posEvent : positive.event = event) (negEvent : negative.event = event)
    (posCond : positive.condition = fun w => context w && split w)
    (negCond : negative.condition = fun w => context w && !split w)
    (posHeld : positive.Holds model.weight) (negHeld : negative.Holds model.weight) :
    conditionalValue model event context ∈
      Set.Icc (blend p (positive.lower : ℝ) negative.lower)
        (blend p (positive.upper : ℝ) negative.upper) := by
  have contextParts := partition model.weight context split
  have jointParts := partition model.weight (fun w => event w && context w) split
  have massPos : p * mass model.weight context =
      mass model.weight (fun w => context w && split w) := by
    rw [conditionalValue, div_eq_iff possible.ne'] at weight
    simpa only [Bool.and_comm] using weight.symm
  have massNeg : (1 - p) * mass model.weight context =
      mass model.weight (fun w => context w && !split w) := by
    rw [sub_mul, one_mul, massPos]
    linarith only [contextParts]
  simp only [Constraint.Holds, posCond, negCond, posEvent, negEvent,
    ← Bool.and_assoc] at posHeld negHeld
  unfold conditionalValue
  simp only [blend, Set.mem_Icc]
  constructor
  · apply (le_div_iff₀ possible).mpr
    rw [add_mul, mul_right_comm p, mul_right_comm (1 - p), massPos, massNeg]
    linarith only [posHeld.1, negHeld.1, jointParts]
  · apply (div_le_iff₀ possible).mpr
    rw [add_mul, mul_right_comm p, mul_right_comm (1 - p), massPos, massNeg]
    linarith only [posHeld.2, negHeld.2, jointParts]

theorem mixRows_sound (model : Distribution Ω) (event context split : Event Ω)
    (possible : 0 < mass model.weight context) (branchWeight : UnitProbability)
    (weight : conditionalValue model split context = (branchWeight.val : ℝ))
    (positive negative : Constraint Ω)
    (posEvent : positive.event = event) (negEvent : negative.event = event)
    (posCond : positive.condition = fun w => context w && split w)
    (negCond : negative.condition = fun w => context w && !split w)
    (posHeld : positive.Holds model.weight) (negHeld : negative.Holds model.weight) :
    conditionalValue model event context ∈
      Set.Icc (((mixRows branchWeight positive negative).1 : ℚ) : ℝ)
        (((mixRows branchWeight positive negative).2 : ℚ) : ℝ) := by
  simpa only [mixRows, blend, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] using
    mixRows_real model event context split possible _ weight positive negative
      posEvent negEvent posCond negCond posHeld negHeld

def mixRowIntervals (weight positive negative : Constraint Ω) : ℚ × ℚ :=
  (min (blend weight.lower positive.lower negative.lower) (blend weight.upper positive.lower negative.lower),
    max (blend weight.lower positive.upper negative.upper) (blend weight.upper positive.upper negative.upper))

private theorem blend_extrema {left x right : ℝ} (lo : left ≤ x) (hi : x ≤ right) (yes no : ℝ) :
    blend x yes no ∈ Set.Icc (min (blend left yes no) (blend right yes no))
      (max (blend left yes no) (blend right yes no)) := by
  by_cases order : no ≤ yes
  · have a := mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr order)
    have b := mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr order)
    exact ⟨(min_le_left _ _).trans (by unfold blend; nlinarith only [a]),
      (show blend x yes no ≤ blend right yes no by unfold blend; nlinarith only [b]).trans (le_max_right _ _)⟩
  · have gap : 0 ≤ no - yes := sub_nonneg.mpr (le_of_lt (lt_of_not_ge order))
    have a := mul_nonneg (sub_nonneg.mpr lo) gap
    have b := mul_nonneg (sub_nonneg.mpr hi) gap
    exact ⟨(min_le_right _ _).trans (by unfold blend; nlinarith only [b]),
      (show blend x yes no ≤ blend left yes no by unfold blend; nlinarith only [a]).trans (le_max_left _ _)⟩

/-- The branch probability may itself be imprecise. The same branch mass
is used in both terms of the mixture. -/
theorem mixRowIntervals_sound (model : Distribution Ω) (event context split : Event Ω)
    (possible : 0 < mass model.weight context) (weight positive negative : Constraint Ω)
    (weightEvent : weight.event = split) (weightCond : weight.condition = context)
    (posEvent : positive.event = event) (negEvent : negative.event = event)
    (posCond : positive.condition = fun w => context w && split w)
    (negCond : negative.condition = fun w => context w && !split w)
    (weightHeld : weight.Holds model.weight)
    (posHeld : positive.Holds model.weight) (negHeld : negative.Holds model.weight) :
    conditionalValue model event context ∈
      Set.Icc (((mixRowIntervals weight positive negative).1 : ℚ) : ℝ)
        (((mixRowIntervals weight positive negative).2 : ℚ) : ℝ) := by
  have support : 0 < mass model.weight weight.condition := by simpa only [weightCond] using possible
  have branch := (Constraint.holds_iff_conditional weight model support).mp weightHeld
  rw [weightEvent, weightCond] at branch
  have target := mixRows_real model event context split possible _ rfl positive negative
    posEvent negEvent posCond negCond posHeld negHeld
  have lo := (blend_extrema branch.1 branch.2 (positive.lower : ℝ) negative.lower).1
  have hi := (blend_extrema branch.1 branch.2 (positive.upper : ℝ) negative.upper).2
  simpa only [mixRowIntervals, blend, Rat.cast_min, Rat.cast_max, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_one, Set.mem_Icc] using ⟨lo.trans target.1, target.2.trans hi⟩

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ScreeningBand
