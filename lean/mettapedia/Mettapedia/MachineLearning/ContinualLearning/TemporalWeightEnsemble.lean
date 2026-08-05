import Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory

/-!
# Temporal weight ensembles

Soutif-Cormerais, Carta, and van de Weijer,
*Improving Online Continual Learning Performance and Stability with Temporal
Ensembles* (CoLLAs 2023, arXiv:2306.16817), Equations (5)--(6), maintain one
evaluation model by taking an exponential moving average of the chronological
training checkpoints.

This file proves the exact finite algebra behind that construction:

* the recursive EMA equals its geometrically discounted checkpoint sum;
* decay zero keeps the latest checkpoint and decay one keeps the initial one;
* a convex interpolation preserves every norm ball containing both inputs;
* real-linear readouts commute with the entire temporal ensemble;
* checkpoint order matters away from the endpoint decays;
* nonlinear readouts need not turn a weight EMA into a prediction ensemble.

The source reports empirical accuracy and stability improvements.  None of
those empirical claims follow merely from these identities.  In particular,
the linear-readout theorem is an exact scope condition, not an approximation
theorem for a nonlinear neural network.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TemporalWeightEnsemble

noncomputable section

open StochasticSemanticMemory

variable {State Output : Type*}

section Run

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Chronological EMA of a finite checkpoint stream. -/
def emaRun (decay : ℝ) :
    List State → State → State
  | [], initial => initial
  | checkpoint :: checkpoints, initial =>
      emaRun decay checkpoints (emaUpdate decay initial checkpoint)

@[simp]
theorem emaRun_nil (decay : ℝ) (initial : State) :
    emaRun decay [] initial = initial := rfl

@[simp]
theorem emaRun_cons
    (decay : ℝ) (checkpoint : State)
    (checkpoints : List State) (initial : State) :
    emaRun decay (checkpoint :: checkpoints) initial =
      emaRun decay checkpoints
        (emaUpdate decay initial checkpoint) := rfl

/-- Processing concatenated streams is sequential composition. -/
theorem emaRun_append
    (decay : ℝ) (first second : List State) (initial : State) :
    emaRun decay (first ++ second) initial =
      emaRun decay second (emaRun decay first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons checkpoint checkpoints ih =>
      simp only [List.cons_append, emaRun_cons]
      exact ih (emaUpdate decay initial checkpoint)

/-- Geometrically discounted checkpoint contribution in chronological order.
Older checkpoints receive more powers of `decay`. -/
def discountedCheckpointSum (decay : ℝ) : List State → State
  | [] => 0
  | checkpoint :: checkpoints =>
      ((1 - decay) * decay ^ checkpoints.length) • checkpoint +
        discountedCheckpointSum decay checkpoints

/-- Equation (6), including the exact contribution of the initial ensemble
state. -/
theorem emaRun_eq_discountedCheckpointSum
    (decay : ℝ) (checkpoints : List State) (initial : State) :
    emaRun decay checkpoints initial =
      decay ^ checkpoints.length • initial +
        discountedCheckpointSum decay checkpoints := by
  induction checkpoints generalizing initial with
  | nil =>
      simp [emaRun, discountedCheckpointSum]
  | cons checkpoint checkpoints ih =>
      rw [emaRun_cons, ih]
      simp only [discountedCheckpointSum, List.length_cons, pow_succ]
      unfold emaUpdate
      module

/-- At zero decay, any nonempty chronological stream returns its latest
checkpoint exactly. -/
theorem zeroDecay_keeps_latest
    (earlier : List State) (latest initial : State) :
    emaRun 0 (earlier ++ [latest]) initial = latest := by
  rw [emaRun_append]
  simp [emaRun, emaUpdate]

/-- At unit decay, every checkpoint is ignored. -/
theorem unitDecay_keeps_initial
    (checkpoints : List State) (initial : State) :
    emaRun 1 checkpoints initial = initial := by
  induction checkpoints generalizing initial with
  | nil => rfl
  | cons checkpoint checkpoints ih =>
      rw [emaRun_cons]
      simpa [emaUpdate] using ih initial

/-- One EMA displacement relative to an arbitrary reference. -/
theorem emaUpdate_sub_reference
    (decay : ℝ) (memory checkpoint reference : State) :
    emaUpdate decay memory checkpoint - reference =
      decay • (memory - reference) +
        (1 - decay) • (checkpoint - reference) := by
  unfold emaUpdate
  module

/-- Exact convex-weight upper bound for one EMA displacement. -/
theorem emaUpdate_norm_sub_reference_le_weighted
    (decay : ℝ) (memory checkpoint reference : State)
    (decay_nonnegative : 0 ≤ decay)
    (decay_le_one : decay ≤ 1) :
    ‖emaUpdate decay memory checkpoint - reference‖ ≤
      decay * ‖memory - reference‖ +
        (1 - decay) * ‖checkpoint - reference‖ := by
  rw [emaUpdate_sub_reference]
  calc
    ‖decay • (memory - reference) +
        (1 - decay) • (checkpoint - reference)‖
        ≤ ‖decay • (memory - reference)‖ +
            ‖(1 - decay) • (checkpoint - reference)‖ :=
      norm_add_le _ _
    _ = decay * ‖memory - reference‖ +
        (1 - decay) * ‖checkpoint - reference‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg decay_nonnegative,
        abs_of_nonneg (sub_nonneg.mpr decay_le_one)]

/-- A convex EMA preserves a closed norm ball containing both inputs. -/
theorem emaUpdate_norm_sub_le
    (decay radius : ℝ) (memory checkpoint reference : State)
    (decay_nonnegative : 0 ≤ decay)
    (decay_le_one : decay ≤ 1)
    (memory_in_ball : ‖memory - reference‖ ≤ radius)
    (checkpoint_in_ball : ‖checkpoint - reference‖ ≤ radius) :
    ‖emaUpdate decay memory checkpoint - reference‖ ≤ radius := by
  rw [emaUpdate_sub_reference]
  calc
    ‖decay • (memory - reference) +
        (1 - decay) • (checkpoint - reference)‖
        ≤ ‖decay • (memory - reference)‖ +
            ‖(1 - decay) • (checkpoint - reference)‖ :=
      norm_add_le _ _
    _ = decay * ‖memory - reference‖ +
        (1 - decay) * ‖checkpoint - reference‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg decay_nonnegative,
        abs_of_nonneg (sub_nonneg.mpr decay_le_one)]
    _ ≤ decay * radius + (1 - decay) * radius := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left memory_in_ball decay_nonnegative)
        (mul_le_mul_of_nonneg_left checkpoint_in_ball
          (sub_nonneg.mpr decay_le_one))
    _ = radius := by ring

/-- Geometrically discounted upper bound contributed by checkpoint
displacements from a fixed reference. -/
def discountedCheckpointDeviation
    (decay : ℝ) (reference : State) : List State → ℝ
  | [] => 0
  | checkpoint :: checkpoints =>
      (1 - decay) * decay ^ checkpoints.length *
          ‖checkpoint - reference‖ +
        discountedCheckpointDeviation decay reference checkpoints

/-- The complete temporal ensemble obeys an explicit geometrically weighted
deviation budget.  Unlike the common-ball corollary below, this retains the
individual displacement of every checkpoint. -/
theorem emaRun_norm_sub_le_discounted
    (decay : ℝ) (checkpoints : List State)
    (initial reference : State)
    (decay_nonnegative : 0 ≤ decay)
    (decay_le_one : decay ≤ 1) :
    ‖emaRun decay checkpoints initial - reference‖ ≤
      decay ^ checkpoints.length * ‖initial - reference‖ +
        discountedCheckpointDeviation decay reference checkpoints := by
  induction checkpoints generalizing initial with
  | nil =>
      simp [emaRun, discountedCheckpointDeviation]
  | cons checkpoint checkpoints ih =>
      rw [emaRun_cons]
      calc
        ‖emaRun decay checkpoints
              (emaUpdate decay initial checkpoint) - reference‖
            ≤ decay ^ checkpoints.length *
                ‖emaUpdate decay initial checkpoint - reference‖ +
              discountedCheckpointDeviation decay reference checkpoints :=
          ih (emaUpdate decay initial checkpoint)
        _ ≤ decay ^ checkpoints.length *
                (decay * ‖initial - reference‖ +
                  (1 - decay) * ‖checkpoint - reference‖) +
              discountedCheckpointDeviation decay reference checkpoints := by
          gcongr
          exact emaUpdate_norm_sub_reference_le_weighted
            decay initial checkpoint reference decay_nonnegative decay_le_one
        _ = decay ^ (checkpoint :: checkpoints).length *
                ‖initial - reference‖ +
              discountedCheckpointDeviation decay reference
                (checkpoint :: checkpoints) := by
          simp only [List.length_cons, discountedCheckpointDeviation, pow_succ]
          ring

/-- A complete temporal ensemble remains in a norm ball when its initial state
and every checkpoint lie in that ball. -/
theorem emaRun_norm_sub_le
    (decay radius : ℝ) (checkpoints : List State)
    (initial reference : State)
    (decay_nonnegative : 0 ≤ decay)
    (decay_le_one : decay ≤ 1)
    (initial_in_ball : ‖initial - reference‖ ≤ radius)
    (checkpoints_in_ball :
      ∀ checkpoint ∈ checkpoints,
        ‖checkpoint - reference‖ ≤ radius) :
    ‖emaRun decay checkpoints initial - reference‖ ≤ radius := by
  induction checkpoints generalizing initial with
  | nil =>
      simpa [emaRun] using initial_in_ball
  | cons checkpoint checkpoints ih =>
      rw [emaRun_cons]
      apply ih (emaUpdate decay initial checkpoint)
      · exact emaUpdate_norm_sub_le decay radius initial checkpoint reference
          decay_nonnegative decay_le_one initial_in_ball
          (checkpoints_in_ball checkpoint (by simp))
      · intro later later_mem
        exact checkpoints_in_ball later (by simp [later_mem])

end Run

section LinearReadout

variable [NormedAddCommGroup State] [NormedSpace ℝ State]
variable [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- A real-linear prediction map commutes with one weight EMA exactly. -/
theorem LinearMap.map_emaUpdate
    (readout : State →ₗ[ℝ] Output)
    (decay : ℝ) (memory checkpoint : State) :
    readout (emaUpdate decay memory checkpoint) =
      emaUpdate decay (readout memory) (readout checkpoint) := by
  simp [emaUpdate]

/-- A real-linear prediction map commutes with the full chronological temporal
ensemble. -/
theorem LinearMap.map_emaRun
    (readout : State →ₗ[ℝ] Output)
    (decay : ℝ) (checkpoints : List State) (initial : State) :
    readout (emaRun decay checkpoints initial) =
      emaRun decay (checkpoints.map readout) (readout initial) := by
  induction checkpoints generalizing initial with
  | nil => rfl
  | cons checkpoint checkpoints ih =>
      rw [emaRun_cons, List.map_cons, emaRun_cons,
        ← LinearMap.map_emaUpdate readout]
      exact ih (emaUpdate decay initial checkpoint)

end LinearReadout

/-! ## Executable boundaries -/

/-- At decay one-half, initial zero and checkpoints two then four yield
five-halves. -/
theorem chronological_half_decay :
    emaRun (1 / 2 : ℝ) [(2 : ℝ), 4] 0 = (5 / 2 : ℝ) := by
  norm_num [emaRun, emaUpdate]

/-- Reversing the same checkpoints yields two, so EMA is not an unordered
model soup. -/
theorem reversed_half_decay :
    emaRun (1 / 2 : ℝ) [(4 : ℝ), 2] 0 = 2 := by
  norm_num [emaRun, emaUpdate]

theorem temporal_checkpoint_order_matters :
    emaRun (1 / 2 : ℝ) [(2 : ℝ), 4] 0 ≠
      emaRun (1 / 2 : ℝ) [(4 : ℝ), 2] 0 := by
  rw [chronological_half_decay, reversed_half_decay]
  norm_num

/-- The upper-bound premise `decay ≤ 1` is load-bearing: above one, the
putative checkpoint coefficient is negative and cannot bound a norm. -/
theorem decay_above_one_breaks_weighted_bound :
    ¬ (‖emaUpdate (2 : ℝ) (0 : ℝ) (1 : ℝ) - 0‖ ≤
      2 * ‖(0 : ℝ) - 0‖ + (1 - 2) * ‖(1 : ℝ) - 0‖) := by
  norm_num [emaUpdate]

/-- A nonlinear scalar readout exposing the weight/prediction ensemble
boundary. -/
def squareReadout (weight : ℝ) : ℝ :=
  weight ^ 2

/-- Averaging weights and averaging predictions disagree for a nonlinear
readout, even for a two-point symmetric fixture. -/
theorem nonlinear_weight_ema_ne_prediction_ema :
    squareReadout (emaUpdate (1 / 2 : ℝ) (-1) 1) ≠
      emaUpdate (1 / 2 : ℝ) (squareReadout (-1)) (squareReadout 1) := by
  norm_num [squareReadout, emaUpdate]

end

end TemporalWeightEnsemble

end Mettapedia.MachineLearning.ContinualLearning

#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.emaRun_eq_discountedCheckpointSum
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.emaRun_norm_sub_le_discounted
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.emaRun_norm_sub_le
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.LinearMap.map_emaRun
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.temporal_checkpoint_order_matters
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.decay_above_one_breaks_weighted_bound
#print axioms Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble.nonlinear_weight_ema_ne_prediction_ema
