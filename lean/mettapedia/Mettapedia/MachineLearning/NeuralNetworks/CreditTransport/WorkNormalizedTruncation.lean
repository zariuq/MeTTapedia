import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedCreditReadout
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FiniteSettlingGradientGap

/-!
# Work-normalized certificates for truncated credit

A finite solver direction is useful only when its certified error is small
relative to the direction actually observed. This module derives that
observable alignment gate, composes it with the Hilbert finite-settling bound,
and separates per-round task progress from fixed and per-sweep work.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace WorkNormalizedTruncation

open scoped InnerProductSpace
open DirectionalTaskDescent
open AmortizedInitialization
open AmortizedCreditReadout
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

variable {Credit : Type*}
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-! ## Observable alignment -/

/-- If the exact credit lies in a certified ball around the finite credit,
the finite direction's own norm gives a directly observable alignment lower
bound. -/
theorem finiteCredit_inner_lower_from_self
    (exact finite : Credit) (error : ℝ)
    (herror : ‖finite - exact‖ ≤ error) :
    ‖finite‖ * (‖finite‖ - error) ≤ ⟪exact, finite⟫_ℝ := by
  have hdecompose : exact = finite + (exact - finite) := by
    abel
  rw [hdecompose, inner_add_left, real_inner_self_eq_norm_sq]
  have hcauchy :
      -(‖exact - finite‖ * ‖finite‖) ≤ ⟪exact - finite, finite⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm (exact - finite) finite)
  have hsymm : ‖exact - finite‖ = ‖finite - exact‖ := by
    rw [show exact - finite = -(finite - exact) by abel, norm_neg]
  have hscaled :
      ‖exact - finite‖ * ‖finite‖ ≤ error * ‖finite‖ := by
    rw [hsymm]
    exact mul_le_mul_of_nonneg_right herror (norm_nonneg finite)
  nlinarith

/-- Error strictly below the observed finite-credit norm certifies positive
alignment with the unknown exact credit. -/
theorem finiteCredit_positiveAlignment
    (exact finite : Credit) (error : ℝ)
    (herror : ‖finite - exact‖ ≤ error)
    (hrelative : error < ‖finite‖) :
    0 < ⟪exact, finite⟫_ℝ := by
  have herrorNonneg : 0 ≤ error :=
    le_trans (norm_nonneg (finite - exact)) herror
  have hfinitePositive : 0 < ‖finite‖ :=
    lt_of_le_of_lt herrorNonneg hrelative
  have hlower := finiteCredit_inner_lower_from_self exact finite error herror
  have hmargin : 0 < ‖finite‖ * (‖finite‖ - error) :=
    mul_pos hfinitePositive (sub_pos.mpr hrelative)
  exact lt_of_lt_of_le hmargin hlower

/-- The observable alignment lower bound plugs directly into the existing
directional curvature certificate. -/
theorem finiteCredit_strictTaskDescent
    {loss : Credit → ℝ} {parameter exact finite : Credit}
    {error curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter exact finite curvature)
    (herror : ‖finite - exact‖ ≤ error)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 < ‖finite‖ * (‖finite‖ - error)) :
    loss (parameter - step • finite) < loss parameter := by
  have halignment := finiteCredit_inner_lower_from_self exact finite error herror
  exact directionalTask_strict_descent certificate hstep
    (lt_of_lt_of_le htrust halignment)

/-! ## Composition with finite predictive settling -/

variable {Latent : Type*}
  [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]

/-- The existing finite-settling gradient-gap theorem yields an observable
positive-alignment certificate whenever its complete error budget is smaller
than the finite credit norm. The equilibrium mismatch remains explicit. -/
theorem hilbertFiniteSettling_positiveAlignment
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (gradientReadout : Latent → Credit) (exactCredit : Credit)
    (hK : 0 ≤ K)
    (hreadout : HilbertGradientReadoutLipschitzAt gradientReadout target K)
    (sweeps : ℕ)
    (hrelative :
      K * hilbertSettlingContraction mu L rate ^ sweeps *
            ‖initial - target‖ +
          hilbertEquilibriumGradientMismatch gradientReadout target exactCredit <
        ‖gradientReadout
          ((hilbertSettlingStep model rate)^[sweeps] initial)‖) :
    0 < ⟪exactCredit,
      gradientReadout ((hilbertSettlingStep model rate)^[sweeps] initial)⟫_ℝ := by
  let finite :=
    gradientReadout ((hilbertSettlingStep model rate)^[sweeps] initial)
  let error :=
    K * hilbertSettlingContraction mu L rate ^ sweeps * ‖initial - target‖ +
      hilbertEquilibriumGradientMismatch gradientReadout target exactCredit
  have hgap : ‖finite - exactCredit‖ ≤ error := by
    simpa [finite, error] using
      hilbertFiniteSettlingGradientGap_le model hL hrate hcoefficient
        target initial htarget gradientReadout exactCredit hK hreadout sweeps
  exact finiteCredit_positiveAlignment exactCredit finite error hgap
    (by simpa [finite, error] using hrelative)

/-! ## Residual-certified credit with equilibrium mismatch -/

variable {State : Type*} [NormedAddCommGroup State]

omit [InnerProductSpace ℝ Credit] in
/-- An observable solver residual controls raw-credit error up to the separate
equilibrium mismatch between the solved local readout and exact task credit. -/
theorem creditError_le_residual_plus_equilibriumMismatch
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (exactCredit : Credit)
    (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K) :
    ‖readout state - exactCredit‖ ≤
      K * (‖state - solver state‖ / (1 - certificate.factor)) +
        ‖readout target - exactCredit‖ := by
  calc
    ‖readout state - exactCredit‖ ≤
        ‖readout state - readout target‖ +
          ‖readout target - exactCredit‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (readout state - readout target)
          (readout target - exactCredit)
    _ ≤ K * (‖state - solver state‖ / (1 - certificate.factor)) +
          ‖readout target - exactCredit‖ :=
      (by
        simpa [add_comm] using
          add_le_add_right
            (creditReadout_distance_le_residual_div certificate target state
              htarget readout K hK hreadout)
            ‖readout target - exactCredit‖)

/-- The complete residual-plus-mismatch budget yields an observable positive
alignment gate for the current raw credit. -/
theorem residualCertifiedCredit_positiveAlignment
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (exactCredit : Credit)
    (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K)
    (hrelative :
      K * (‖state - solver state‖ / (1 - certificate.factor)) +
          ‖readout target - exactCredit‖ < ‖readout state‖) :
    0 < ⟪exactCredit, readout state⟫_ℝ := by
  let error :=
    K * (‖state - solver state‖ / (1 - certificate.factor)) +
      ‖readout target - exactCredit‖
  have herror : ‖readout state - exactCredit‖ ≤ error := by
    simpa [error] using creditError_le_residual_plus_equilibriumMismatch
      certificate target state htarget readout exactCredit K hK hreadout
  exact finiteCredit_positiveAlignment exactCredit (readout state) error herror
    (by simpa [error] using hrelative)

/-! ## Per-round progress and work -/

/-- Lower bound on the task decrease supplied by a directional quadratic
upper model. It may be negative when the step is outside the trust region. -/
noncomputable def directionalDecreaseLower
    (step alignment curvature : ℝ) : ℝ :=
  step * alignment - step ^ 2 * curvature / 2

theorem directionalTask_decrease_lower
    {loss : Credit → ℝ} {parameter exact finite : Credit}
    {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter exact finite curvature)
    (hstep : 0 ≤ step) :
    directionalDecreaseLower step ⟪exact, finite⟫_ℝ curvature ≤
      loss parameter - loss (parameter - step • finite) := by
  have hupper := certificate step hstep
  unfold directionalDecreaseLower
  linarith

/-- A uniform per-round decrease lower bound telescopes over any finite run. -/
theorem loss_after_rounds_le
    (loss : ℕ → ℝ) (margin : ℝ)
    (hround : ∀ round, loss (round + 1) ≤ loss round - margin)
    (rounds : ℕ) :
    loss rounds ≤ loss 0 - (rounds : ℝ) * margin := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      calc
        loss (Nat.succ rounds) = loss (rounds + 1) := by rfl
        _ ≤ loss rounds - margin := hround rounds
        _ ≤ (loss 0 - (rounds : ℝ) * margin) - margin :=
          sub_le_sub_right ih margin
        _ = loss 0 - (Nat.succ rounds : ℝ) * margin := by
          push_cast
          ring

/-- Fixed overhead plus per-sweep work for one update. -/
def settlingWork (fixedCost sweepCost depth : ℕ) : ℕ :=
  fixedCost + sweepCost * depth

/-- Number of complete updates affordable under a discrete work budget. -/
def roundsWithin (budget fixedCost sweepCost depth : ℕ) : ℕ :=
  budget / settlingWork fixedCost sweepCost depth

/-- Cumulative lower bound obtained from a uniform per-round margin. -/
noncomputable def cumulativeDecreaseLower (rounds : ℕ) (margin : ℝ) : ℝ :=
  (rounds : ℝ) * margin

/-- Exact threshold for when more cheap rounds have the stronger cumulative
guarantee. This theorem compares guarantees, not realized verifier yield. -/
theorem cumulativeDecreaseLower_gt_iff
    (cheapRounds fullRounds : ℕ) (cheapMargin fullMargin : ℝ)
    (hcheapRounds : 0 < cheapRounds) :
    cumulativeDecreaseLower fullRounds fullMargin <
        cumulativeDecreaseLower cheapRounds cheapMargin ↔
      (fullRounds : ℝ) * fullMargin / (cheapRounds : ℝ) < cheapMargin := by
  have hpositive : 0 < (cheapRounds : ℝ) := by exact_mod_cast hcheapRounds
  rw [div_lt_iff₀ hpositive]
  simp only [cumulativeDecreaseLower]
  ring_nf

/-! ## Positive and negative executable boundaries -/

/-- With negligible fixed overhead, eight one-sweep rounds at margin one beat
two four-sweep rounds at margin three under the same work budget. -/
theorem lowOverhead_truncation_has_stronger_guarantee :
    roundsWithin 8 0 1 1 = 8 ∧
      roundsWithin 8 0 1 4 = 2 ∧
      cumulativeDecreaseLower (roundsWithin 8 0 1 4) 3 <
        cumulativeDecreaseLower (roundsWithin 8 0 1 1) 1 := by
  norm_num [roundsWithin, settlingWork, cumulativeDecreaseLower]

/-- Large fixed overhead can erase the extra-round advantage: both depths fit
twice, so the stronger full-round margin wins. -/
theorem fixedOverhead_can_reverse_throughput_order :
    roundsWithin 204 100 1 1 = 2 ∧
      roundsWithin 204 100 1 2 = 2 ∧
      cumulativeDecreaseLower (roundsWithin 204 100 1 1) 1 <
        cumulativeDecreaseLower (roundsWithin 204 100 1 2) 3 := by
  norm_num [roundsWithin, settlingWork, cumulativeDecreaseLower]

/-- An error radius larger than the finite direction can contain a direction
opposite to the exact credit, so the observable gate is substantive. -/
theorem insufficient_settling_can_reverse_alignment :
    ‖(-1 : ℝ) - 1‖ ≤ 2 ∧
      ¬ (2 : ℝ) < ‖(-1 : ℝ)‖ ∧
      ⟪(1 : ℝ), (-1 : ℝ)⟫_ℝ < 0 := by
  norm_num [Real.norm_eq_abs]

noncomputable def doublingSolver (state : ℝ) : ℝ := 2 * state

/-- Substituting an expansive factor into the contraction residual formula
produces a false bound; the strict factor-below-one premise cannot be dropped. -/
theorem expansive_factor_invalidates_residual_bound :
    ¬ (|(1 : ℝ) - 0| ≤
      |(1 : ℝ) - doublingSolver 1| / (1 - 2)) := by
  norm_num [doublingSolver]

#print axioms finiteCredit_inner_lower_from_self
#print axioms finiteCredit_positiveAlignment
#print axioms finiteCredit_strictTaskDescent
#print axioms hilbertFiniteSettling_positiveAlignment
#print axioms creditError_le_residual_plus_equilibriumMismatch
#print axioms residualCertifiedCredit_positiveAlignment
#print axioms directionalTask_decrease_lower
#print axioms loss_after_rounds_le
#print axioms cumulativeDecreaseLower_gt_iff
#print axioms lowOverhead_truncation_has_stronger_guarantee
#print axioms fixedOverhead_can_reverse_throughput_order
#print axioms insufficient_settling_can_reverse_alignment
#print axioms expansive_factor_invalidates_residual_bound

end WorkNormalizedTruncation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
