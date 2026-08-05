import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ArbitraryGraphEnergy

/-!
# Sequential predictive context

Ororbia, Mali, Kifer, and Giles, *Lifelong Neural Predictive Coding:
Learning Cumulatively Online without Forgetting* (2019), combine local
predictive-coding state dynamics with context memory and competitive task
routing.  The source PDF has SHA-256
`e193d1f465e7021c8fcd21908de67c9ec5d9bc72d21cc74a21a9e449b7186505`.
This file recovers four source-level mechanisms and states their load-bearing
boundaries.

For the scalar two-residual instance of source Equations (1)--(5) and
(10)--(16), the feedback perturbation is exactly the negative state gradient
when the feedback and forward weights agree.  The energy change is an exact
quadratic, yielding a sharp open descent-rate condition.  A sign-reversed
feedback fixture raises the energy.

The context-memory rule from source Equation (4) is analyzed independently.
With no innovation, the printed minus sign contracts a context toward the
previous-context mean when its rate lies in `(0, 1)`; genuine repulsion uses
the opposite sign.  This algebraic distinction is independent of the
source's empirical task-separation results.

For source Equation (9), dot-product competition among unit keys is exactly
nearest-key competition.  A one-dimensional counterexample shows that
normalization is essential.  Finally, the running error moments from source
Equations (6)--(8) preserve nonnegative variance and expose their precise
exponential-tracking semantics.

The arbitrary-graph weight update is already recovered, more generally, by
`ArbitraryGraphEnergy.weightGradientStep_eq_source_update`; it is not
duplicated here.  No theorem below claims the source's benchmark accuracy,
automatic task discovery, or resistance to catastrophic forgetting.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SequentialPredictiveContext

open scoped InnerProductSpace

noncomputable section

/-! ## Scalar predictive-coding energy -/

/-- Residual between a sensory value and a one-edge prediction. -/
def lowerError
    (sensory weight state : ℝ) : ℝ :=
  sensory - weight * state

/-- Residual between a state and its top-down prediction. -/
def upperError
    (state prediction : ℝ) : ℝ :=
  state - prediction

/-- Scalar two-residual instance of the source's total discrepancy. -/
def totalDiscrepancy
    (sensory weight prediction state : ℝ) : ℝ :=
  (lowerError sensory weight state ^ 2 +
      upperError state prediction ^ 2) / 2

/-- Exact negative derivative of `totalDiscrepancy` with respect to state. -/
def negativeStateGradient
    (sensory weight prediction state : ℝ) : ℝ :=
  weight * lowerError sensory weight state -
    upperError state prediction

/-- Source-shaped local perturbation with an independently supplied feedback
weight. -/
def feedbackPerturbation
    (sensory weight prediction feedback state : ℝ) : ℝ :=
  feedback * lowerError sensory weight state -
    upperError state prediction

/-- One identity-activation state update. -/
def stateStep
    (rate sensory weight prediction feedback state : ℝ) : ℝ :=
  state +
    rate * feedbackPerturbation sensory weight prediction feedback state

/-- Exact quadratic response of the scalar discrepancy to a state
perturbation. -/
theorem totalDiscrepancy_perturb_exact
    (sensory weight prediction state delta : ℝ) :
    totalDiscrepancy sensory weight prediction (state + delta) =
      totalDiscrepancy sensory weight prediction state -
        delta * negativeStateGradient sensory weight prediction state +
          delta ^ 2 / 2 * (weight ^ 2 + 1) := by
  simp [totalDiscrepancy, lowerError, upperError, negativeStateGradient]
  ring

/-- Symmetric feedback recovers the exact negative state gradient. -/
theorem symmetricFeedback_exact
    (sensory weight prediction state : ℝ) :
    feedbackPerturbation sensory weight prediction weight state =
      negativeStateGradient sensory weight prediction state := by
  rfl

/-- Exact energy law for one symmetric-feedback state update. -/
theorem symmetricFeedback_step_energy_exact
    (rate sensory weight prediction state : ℝ) :
    totalDiscrepancy sensory weight prediction
        (stateStep rate sensory weight prediction weight state) =
      totalDiscrepancy sensory weight prediction state -
        rate *
          (1 - rate * (weight ^ 2 + 1) / 2) *
          negativeStateGradient sensory weight prediction state ^ 2 := by
  rw [stateStep, symmetricFeedback_exact,
    totalDiscrepancy_perturb_exact]
  ring

/-- Symmetric feedback strictly decreases discrepancy whenever the step rate
lies inside the exact quadratic stability interval and the local gradient is
nonzero. -/
theorem symmetricFeedback_step_strict_descent
    (rate sensory weight prediction state : ℝ)
    (ratePositive : 0 < rate)
    (rateBelowBoundary : rate * (weight ^ 2 + 1) < 2)
    (liveGradient :
      negativeStateGradient sensory weight prediction state ≠ 0) :
    totalDiscrepancy sensory weight prediction
        (stateStep rate sensory weight prediction weight state) <
      totalDiscrepancy sensory weight prediction state := by
  rw [symmetricFeedback_step_energy_exact]
  have factorPositive :
      0 < 1 - rate * (weight ^ 2 + 1) / 2 := by
    linarith
  have squarePositive :
      0 < negativeStateGradient sensory weight prediction state ^ 2 :=
    sq_pos_of_ne_zero liveGradient
  have productPositive :
      0 <
        rate *
          (1 - rate * (weight ^ 2 + 1) / 2) *
          negativeStateGradient sensory weight prediction state ^ 2 :=
    mul_pos (mul_pos ratePositive factorPositive) squarePositive
  linarith

/-- Reversing the feedback weight can turn the same positive-rate local rule
into a strict energy increase. -/
theorem antiFeedback_raises_energy :
    totalDiscrepancy 1 1 0
        (stateStep 1 1 1 0 (-1) 0) >
      totalDiscrepancy 1 1 0 0 := by
  norm_num [stateStep, feedbackPerturbation, totalDiscrepancy,
    lowerError, upperError]

/-! ## Context-memory sign boundary -/

section Context

variable {Context : Type*}
  [NormedAddCommGroup Context] [NormedSpace ℝ Context]

/-- Source Equation (4): innovation followed by the printed signed
mean-context term. -/
def contextUpdate
    (innovationRate driftRate : ℝ)
    (context perturbation anchor : Context) : Context :=
  context + innovationRate • perturbation -
    driftRate • (context - anchor)

/-- A genuinely repulsive alternative, differing only in the sign of the
mean-context term. -/
def repulsiveContextUpdate
    (driftRate : ℝ) (context anchor : Context) : Context :=
  context + driftRate • (context - anchor)

/-- Exact affine displacement of the printed context update. -/
theorem contextUpdate_displacement
    (innovationRate driftRate : ℝ)
    (context perturbation anchor : Context) :
    contextUpdate innovationRate driftRate context perturbation anchor -
        anchor =
      (1 - driftRate) • (context - anchor) +
        innovationRate • perturbation := by
  simp [contextUpdate]
  module

/-- With no innovation and a rate in `[0, 1]`, the printed rule scales
distance to the anchor by `1 - driftRate`. -/
theorem contextUpdate_zeroInnovation_norm
    (innovationRate driftRate : ℝ)
    (context anchor : Context)
    (driftAtMostOne : driftRate ≤ 1) :
    ‖contextUpdate innovationRate driftRate context 0 anchor - anchor‖ =
      (1 - driftRate) * ‖context - anchor‖ := by
  rw [contextUpdate_displacement]
  simp [norm_smul, abs_of_nonneg (sub_nonneg.mpr driftAtMostOne)]

/-- Thus the source's printed minus sign is strictly contractive toward the
anchor when the context is distinct and the rate lies in `(0, 1)`. -/
theorem contextUpdate_zeroInnovation_strict_contraction
    (innovationRate driftRate : ℝ)
    (context anchor : Context)
    (driftPositive : 0 < driftRate)
    (driftBelowOne : driftRate < 1)
    (contextNeAnchor : context ≠ anchor) :
    ‖contextUpdate innovationRate driftRate context 0 anchor - anchor‖ <
      ‖context - anchor‖ := by
  rw [contextUpdate_zeroInnovation_norm innovationRate driftRate context anchor
    (le_of_lt driftBelowOne)]
  have displacementPositive : 0 < ‖context - anchor‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr contextNeAnchor)
  nlinarith

/-- Innovation and drift contributions have a direct norm budget. -/
theorem contextUpdate_norm_le
    (innovationRate driftRate : ℝ)
    (context perturbation anchor : Context) :
    ‖contextUpdate innovationRate driftRate context perturbation anchor -
        anchor‖ ≤
      |1 - driftRate| * ‖context - anchor‖ +
        |innovationRate| * ‖perturbation‖ := by
  rw [contextUpdate_displacement]
  simpa only [norm_smul, Real.norm_eq_abs] using
    norm_add_le
      ((1 - driftRate) • (context - anchor))
      (innovationRate • perturbation)

/-- Exact displacement of the sign-reversed, genuinely repulsive rule. -/
theorem repulsiveContextUpdate_displacement
    (driftRate : ℝ) (context anchor : Context) :
    repulsiveContextUpdate driftRate context anchor - anchor =
      (1 + driftRate) • (context - anchor) := by
  simp [repulsiveContextUpdate]
  module

/-- Positive sign-reversed drift strictly expands a nonzero displacement. -/
theorem repulsiveContextUpdate_strict_expansion
    (driftRate : ℝ) (context anchor : Context)
    (driftPositive : 0 < driftRate)
    (contextNeAnchor : context ≠ anchor) :
    ‖context - anchor‖ <
      ‖repulsiveContextUpdate driftRate context anchor - anchor‖ := by
  rw [repulsiveContextUpdate_displacement, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + driftRate)]
  have displacementPositive : 0 < ‖context - anchor‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr contextNeAnchor)
  nlinarith

end Context

/-- Executable scalar witness of the context-sign distinction. -/
theorem printed_minus_contracts_but_plus_expands :
    contextUpdate 0 (1 / 2 : ℝ) 1 0 0 = (1 / 2 : ℝ) ∧
      repulsiveContextUpdate (1 / 2 : ℝ) 1 0 = (3 / 2 : ℝ) := by
  norm_num [contextUpdate, repulsiveContextUpdate]

/-! ## Competitive task routing -/

section Routing

variable {Key : Type*}
  [NormedAddCommGroup Key] [InnerProductSpace ℝ Key]

/-- Among unit query and key vectors, maximum dot product and minimum squared
Euclidean distance induce exactly the same two-key ordering. -/
theorem unit_dot_order_iff_distance_order
    (query first second : Key)
    (queryUnit : ‖query‖ = 1)
    (firstUnit : ‖first‖ = 1)
    (secondUnit : ‖second‖ = 1) :
    @inner ℝ Key _ query first ≥ @inner ℝ Key _ query second ↔
      ‖query - first‖ ^ 2 ≤ ‖query - second‖ ^ 2 := by
  have firstDistance :
      ‖query - first‖ ^ 2 =
        2 - 2 * @inner ℝ Key _ query first := by
    rw [norm_sub_sq_real, queryUnit, firstUnit]
    ring
  have secondDistance :
      ‖query - second‖ ^ 2 =
        2 - 2 * @inner ℝ Key _ query second := by
    rw [norm_sub_sq_real, queryUnit, secondUnit]
    ring
  rw [firstDistance, secondDistance]
  constructor <;> intro ordering <;> linarith

end Routing

/-- Without key normalization, a larger dot product can select the more
distant key. -/
theorem without_normalization_dot_order_can_reverse_distance_order :
    @inner ℝ ℝ _ (1 : ℝ) 2 > @inner ℝ ℝ _ 1 1 ∧
      ‖(1 : ℝ) - 2‖ ^ 2 > ‖(1 : ℝ) - 1‖ ^ 2 := by
  norm_num [Real.norm_eq_abs]

/-! ## Running label-error moments -/

/-- Exponentially tracked first and second central-deviation statistics from
source Equations (6)--(8). -/
structure ErrorMoments where
  mean : ℝ
  variance : ℝ

/-- One source-shaped moment update.  The variance uses the previous mean,
as in the source equation. -/
def observe
    (rate observation : ℝ) (previous : ErrorMoments) : ErrorMoments where
  mean :=
    previous.mean + rate * (observation - previous.mean)
  variance :=
    (1 - rate) * previous.variance +
      rate * (observation - previous.mean) ^ 2

/-- The running mean is an exact convex-combination expression. -/
theorem observe_mean
    (rate observation : ℝ) (previous : ErrorMoments) :
    (observe rate observation previous).mean =
      (1 - rate) * previous.mean + rate * observation := by
  simp [observe]
  ring

/-- A rate in `[0, 1]` preserves nonnegative tracked variance. -/
theorem observe_variance_nonnegative
    (rate observation : ℝ) (previous : ErrorMoments)
    (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (varianceNonnegative : 0 ≤ previous.variance) :
    0 ≤ (observe rate observation previous).variance := by
  simp only [observe]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr rateAtMostOne) varianceNonnegative)
    (mul_nonneg rateNonnegative (sq_nonneg _))

/-- Initial state for the running detector. -/
def zeroMoments : ErrorMoments where
  mean := 0
  variance := 0

/-- Source-shaped threshold predicate using the previous running moments. -/
def shiftSignal
    (multiplier : ℝ) (previous : ErrorMoments) (updatedMean : ℝ) : Prop :=
  previous.mean + multiplier * Real.sqrt previous.variance < updatedMean

/-- From the zero state, any positive-rate positive observation crosses the
old zero-variance threshold, independently of its multiplier. -/
theorem initial_positive_observation_signals
    (rate observation multiplier : ℝ)
    (ratePositive : 0 < rate)
    (observationPositive : 0 < observation) :
    shiftSignal multiplier zeroMoments
      (observe rate observation zeroMoments).mean := by
  simp [shiftSignal, zeroMoments, observe]
  exact mul_pos ratePositive observationPositive

/-- At rate one and from the zero state, the source variance update stores
the squared observation rather than the variance of a one-sample population.
This distinguishes exponential deviation tracking from a Welford update. -/
theorem observe_rate_one_zero_variance_eq_sq
    (observation : ℝ) :
    (observe 1 observation zeroMoments).variance = observation ^ 2 := by
  simp [observe, zeroMoments]

/-- The distinction above is nondegenerate for every nonzero observation. -/
theorem observe_rate_one_zero_variance_positive
    (observation : ℝ) (observationNonzero : observation ≠ 0) :
    0 < (observe 1 observation zeroMoments).variance := by
  rw [observe_rate_one_zero_variance_eq_sq]
  exact sq_pos_of_ne_zero observationNonzero

#print axioms totalDiscrepancy_perturb_exact
#print axioms symmetricFeedback_step_strict_descent
#print axioms antiFeedback_raises_energy
#print axioms contextUpdate_zeroInnovation_strict_contraction
#print axioms repulsiveContextUpdate_strict_expansion
#print axioms unit_dot_order_iff_distance_order
#print axioms without_normalization_dot_order_can_reverse_distance_order
#print axioms observe_variance_nonnegative
#print axioms observe_rate_one_zero_variance_positive

end

end SequentialPredictiveContext

end Mettapedia.MachineLearning.ContinualLearning
