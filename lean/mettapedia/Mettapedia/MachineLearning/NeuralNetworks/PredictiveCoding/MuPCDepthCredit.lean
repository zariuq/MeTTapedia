import Mathlib.Analysis.SpecificLimits.Normed
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ErrorStateReparameterization
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BackpropExactness

/-!
# Depth credit and what μPC scaling can cancel

This file formalizes the depth-credit pathology discussed by Innocenti,
Achour, and Buckley, *μPC: Scaling Predictive Coding to 100+ Layer
Networks*, arXiv:2505.13124v2 (revised 2025-11-28).  The source archive
retrieved on 2026-07-15 had SHA-256
`b696832a37635998e1b1ef490ede0cf565514cfc4c9f93c55712bdfde00d7fb0`.

The paper's Table 1 gives hidden residual-block multipliers proportional to
`(width * depth)^{-1/2}`.  Its discussion records the optimiser-dependent
Depth-μP Adam learning-rate factor `sqrt (width * depth)`, but also states
that μPC did not use that factor because it made the tested networks
untrainable.  Neither choice changes the inference rate itself.

We do not reprove the sealed ePC/backprop or `(P-1)²` theorems.  Instead we
compose them.  At distance `depth - layer` from the output, first-arrival PC
has effective scalar preconditioner `λ^(depth-layer)`.  Heterogeneous rates
accumulate as a suffix product.  Equalizing every suffix, including the empty
output suffix, forces every inference rate to one.  Finally, the prescribed
Depth-μP learning-rate factor exactly cancels its own hidden multiplier but
leaves the inference attenuation unchanged; any polynomial compensation is
asymptotically dominated by a strictly contractive geometric signal.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Topology

/-! ## M1: uniform-rate first-arrival depth credit -/

/-- Effective scalar preconditioner at one layer under a uniform inference
rate.  Its exponent is the layer's distance from the output. -/
noncomputable def uniformDepthCreditPreconditioner
    (inferenceRate : ℝ) (depth layer : ℕ) : ℝ :=
  inferenceRate ^ (depth - layer)

/-- The local update produced when the unit-rate ePC output error propagates
to `layer` through the sealed sPC wavefront recurrence. -/
noncomputable def spcFirstArrivalParameterUpdate
    (inferenceRate predictionJacobian lossGradient : ℝ)
    (depth layer : ℕ) : ℝ :=
  pcLocalParameterUpdate predictionJacobian
    (spcWavefrontSignal inferenceRate
      (epcOneStepError 1 lossGradient) (depth - layer))

/-- Composition crown for M1: the sealed first-arrival law and sealed ePC
one-step theorem give the effective preconditioner
`P_layer = λ^(depth-layer)` without redefining either component. -/
theorem spcFirstArrivalParameterUpdate_eq_depthCreditBackprop
    (inferenceRate predictionJacobian lossGradient : ℝ)
    (depth layer : ℕ) :
    spcFirstArrivalParameterUpdate inferenceRate predictionJacobian
        lossGradient depth layer =
      uniformDepthCreditPreconditioner inferenceRate depth layer *
        (predictionJacobian * lossGradient) := by
  calc
    spcFirstArrivalParameterUpdate inferenceRate predictionJacobian
        lossGradient depth layer =
        pcLocalParameterUpdate predictionJacobian
          (epcOneStepError
            (uniformDepthCreditPreconditioner inferenceRate depth layer)
            lossGradient) := by
      rw [spcFirstArrivalParameterUpdate,
        spcWavefrontSignal_closedForm]
      simp [uniformDepthCreditPreconditioner, epcOneStepError]
    _ = uniformDepthCreditPreconditioner inferenceRate depth layer *
          (predictionJacobian * lossGradient) :=
      epcOneStepParameterUpdate_eq_rescaledBackprop _ _ _

/-- Pricing crown for M1: the sealed quadratic link theorem turns the depth
credit into the exact retained-loss factor `(1-λ^(depth-layer))²`. -/
theorem chainLinkLoss_after_uniformDepthCredit_exact
    (inferenceRate sourceActivation downstreamGain target weight : ℝ)
    (depth layer : ℕ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate
          (uniformDepthCreditPreconditioner inferenceRate depth layer)
          sourceActivation downstreamGain target weight) =
      (1 - inferenceRate ^ (depth - layer)) ^ 2 *
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  rw [chainLinkLoss_preconditionedUpdate_exact _ sourceActivation
    downstreamGain target weight heffective]
  unfold uniformDepthCreditPreconditioner
  congr 1
  ring

/-- Positive fixture: a half-rate depth-four chain has sharply different
credit at the input, middle, and output layers. -/
theorem halfRate_depthFour_depthCredit :
    uniformDepthCreditPreconditioner (1 / 2) 4 0 = 1 / 16 ∧
      uniformDepthCreditPreconditioner (1 / 2) 4 2 = 1 / 4 ∧
      uniformDepthCreditPreconditioner (1 / 2) 4 4 = 1 := by
  norm_num [uniformDepthCreditPreconditioner]

/-- Concrete loss price at the middle of the same chain. -/
theorem halfRate_depthFour_middle_retains_nineSixteenths
    (sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate
          (uniformDepthCreditPreconditioner (1 / 2) 4 2)
          sourceActivation downstreamGain target weight) =
      (9 / 16) *
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  rw [chainLinkLoss_after_uniformDepthCredit_exact
    (1 / 2) sourceActivation downstreamGain target weight 4 2 heffective]
  norm_num

/-- Negative boundary: unit inference rate removes the depth imbalance and
reduces every first-arrival update to the backprop product. -/
theorem unitRate_uniformDepthCredit_is_backprop
    (predictionJacobian lossGradient : ℝ) (depth layer : ℕ) :
    spcFirstArrivalParameterUpdate 1 predictionJacobian lossGradient depth layer =
      predictionJacobian * lossGradient := by
  rw [spcFirstArrivalParameterUpdate_eq_depthCreditBackprop]
  simp [uniformDepthCreditPreconditioner]

/-! ## M2: heterogeneous inference rates and the equalization no-go -/

/-- Accumulate `distance` successive inference rates, beginning immediately
after `layer`. -/
noncomputable def accumulatedInferenceRateFrom
    (inferenceRate : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | layer, distance + 1 =>
      inferenceRate (layer + 1) *
        accumulatedInferenceRateFrom inferenceRate (layer + 1) distance

/-- The recursive accumulator is the literal product over the consecutive
rates strictly after `layer`. -/
theorem accumulatedInferenceRateFrom_eq_prod_Ioc
    (inferenceRate : ℕ → ℝ) (layer distance : ℕ) :
    accumulatedInferenceRateFrom inferenceRate layer distance =
      ∏ j ∈ Finset.Ioc layer (layer + distance), inferenceRate j := by
  induction distance generalizing layer with
  | zero => simp [accumulatedInferenceRateFrom]
  | succ distance ih =>
      rw [accumulatedInferenceRateFrom, ih]
      rw [← Finset.insert_Ioc_succ_left_eq_Ioc
        (show layer < layer + (distance + 1) by omega)]
      rw [Finset.prod_insert (by simp)]
      simp only [Order.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

/-- Per-layer suffix product `∏_{j>layer} λ_j`, truncated at `depth`. -/
noncomputable def heterogeneousDepthCredit
    (inferenceRate : ℕ → ℝ) (depth layer : ℕ) : ℝ :=
  accumulatedInferenceRateFrom inferenceRate layer (depth - layer)

/-- Explicit suffix-product form requested by the depth-credit analysis. -/
theorem heterogeneousDepthCredit_eq_prod_Ioc
    (inferenceRate : ℕ → ℝ) (depth layer : ℕ)
    (hlayer : layer ≤ depth) :
    heterogeneousDepthCredit inferenceRate depth layer =
      ∏ j ∈ Finset.Ioc layer depth, inferenceRate j := by
  rw [heterogeneousDepthCredit, accumulatedInferenceRateFrom_eq_prod_Ioc,
    Nat.add_sub_of_le hlayer]

@[simp] theorem heterogeneousDepthCredit_at_output
    (inferenceRate : ℕ → ℝ) (depth : ℕ) :
    heterogeneousDepthCredit inferenceRate depth depth = 1 := by
  simp [heterogeneousDepthCredit, accumulatedInferenceRateFrom]

theorem heterogeneousDepthCredit_step
    (inferenceRate : ℕ → ℝ) (depth layer : ℕ)
    (hlayer : layer < depth) :
    heterogeneousDepthCredit inferenceRate depth layer =
      inferenceRate (layer + 1) *
        heterogeneousDepthCredit inferenceRate depth (layer + 1) := by
  unfold heterogeneousDepthCredit
  rw [show depth - layer = (depth - (layer + 1)) + 1 by omega]
  rfl

theorem accumulatedInferenceRateFrom_const
    (inferenceRate : ℝ) (layer distance : ℕ) :
    accumulatedInferenceRateFrom (fun _ ↦ inferenceRate) layer distance =
      inferenceRate ^ distance := by
  induction distance generalizing layer with
  | zero => simp [accumulatedInferenceRateFrom]
  | succ distance ih =>
      rw [accumulatedInferenceRateFrom, ih, pow_succ']

/-- The heterogeneous definition specializes exactly to M1's uniform
`λ^(depth-layer)` law. -/
theorem heterogeneousDepthCredit_const_eq_uniform
    (inferenceRate : ℝ) (depth layer : ℕ) :
    heterogeneousDepthCredit (fun _ ↦ inferenceRate) depth layer =
      uniformDepthCreditPreconditioner inferenceRate depth layer := by
  simp [heterogeneousDepthCredit, uniformDepthCreditPreconditioner,
    accumulatedInferenceRateFrom_const]

/-- A rate schedule equalizes depth credit when every layer through the
output has one common effective preconditioner. -/
def InferenceRatesEqualizeDepthCredit
    (inferenceRate : ℕ → ℝ) (depth : ℕ) : Prop :=
  ∃ common, ∀ layer, layer ≤ depth →
    heterogeneousDepthCredit inferenceRate depth layer = common

private theorem accumulatedInferenceRateFrom_eq_one_of_rates_one
    (inferenceRate : ℕ → ℝ) (layer distance : ℕ)
    (hrates : ∀ j, layer < j → j ≤ layer + distance →
      inferenceRate j = 1) :
    accumulatedInferenceRateFrom inferenceRate layer distance = 1 := by
  induction distance generalizing layer with
  | zero => simp [accumulatedInferenceRateFrom]
  | succ distance ih =>
      rw [accumulatedInferenceRateFrom,
        hrates (layer + 1) (by omega) (by omega)]
      simp only [one_mul]
      apply ih
      intro j hjLower hjUpper
      apply hrates j (by omega) (by omega)

/-- Exact M2 classification: because the output suffix is empty and equals
one, equalizing every layer forces every used inference rate to one.  The
converse also holds. -/
theorem inferenceRatesEqualizeDepthCredit_iff_all_unit
    (inferenceRate : ℕ → ℝ) (depth : ℕ) :
    InferenceRatesEqualizeDepthCredit inferenceRate depth ↔
      ∀ j, 0 < j → j ≤ depth → inferenceRate j = 1 := by
  constructor
  · rintro ⟨common, hequal⟩
    have hcommon : common = 1 := by
      simpa using (hequal depth le_rfl).symm
    intro j hjPositive hjDepth
    let layer := j - 1
    have hlayerSucc : layer + 1 = j := by
      dsimp [layer]
      omega
    have hlayerDepth : layer < depth := by
      dsimp [layer]
      omega
    have hstep := heterogeneousDepthCredit_step
      inferenceRate depth layer hlayerDepth
    rw [hequal layer (by omega), hequal (layer + 1) (by omega),
      hcommon, hlayerSucc] at hstep
    linarith
  · intro hunit
    refine ⟨1, ?_⟩
    intro layer hlayer
    unfold heterogeneousDepthCredit
    apply accumulatedInferenceRateFrom_eq_one_of_rates_one
    intro j hjLower hjUpper
    apply hunit j (by omega)
    rw [Nat.add_sub_of_le hlayer] at hjUpper
    exact hjUpper

/-- M2 no-go crown, phrased constructively: an equalizing schedule has unit
credit everywhere and every inference multiplier used by the chain is one. -/
theorem inferenceRateEqualization_forces_unitBackpropBoundary
    (inferenceRate : ℕ → ℝ) (depth : ℕ)
    (hequal : InferenceRatesEqualizeDepthCredit inferenceRate depth) :
    (∀ j, 0 < j → j ≤ depth → inferenceRate j = 1) ∧
      (∀ layer, layer ≤ depth →
        heterogeneousDepthCredit inferenceRate depth layer = 1) := by
  have hunit :=
    (inferenceRatesEqualizeDepthCredit_iff_all_unit inferenceRate depth).1 hequal
  refine ⟨hunit, ?_⟩
  intro layer hlayer
  obtain ⟨common, hevery⟩ := hequal
  have hcommon : common = 1 := by
    simpa using (hevery depth le_rfl).symm
  simpa [hcommon] using hevery layer hlayer

/-- Positive fixture: the unit schedule really does equalize every depth. -/
theorem unitInferenceRates_equalizeDepthCredit (depth : ℕ) :
    InferenceRatesEqualizeDepthCredit (fun _ ↦ 1) depth := by
  rw [inferenceRatesEqualizeDepthCredit_iff_all_unit]
  simp

/-- Negative fixture: one nonunit rate already destroys equalization. -/
theorem halfFirstInferenceRate_does_not_equalize :
    ¬ InferenceRatesEqualizeDepthCredit
      (fun j ↦ if j = 1 then (1 / 2 : ℝ) else 1) 3 := by
  rw [inferenceRatesEqualizeDepthCredit_iff_all_unit]
  push Not
  exact ⟨1, by norm_num, by norm_num, by norm_num⟩

/-! ## M3: the exact Depth-μP exponent boundary -/

/-- Table-1 hidden-block multiplier `(width * depth)^{-1/2}`. -/
noncomputable def depthMuPHiddenMultiplier (width depth : ℕ) : ℝ :=
  1 / Real.sqrt ((width : ℝ) * depth)

/-- Optimiser-dependent Adam learning-rate factor `sqrt(width * depth)`
prescribed by Depth-μP.  The μPC experiments explicitly omitted it. -/
noncomputable def depthMuPAdamLearningRateScale (width depth : ℕ) : ℝ :=
  Real.sqrt ((width : ℝ) * depth)

/-- The prescribed Adam factor cancels its paired hidden multiplier exactly. -/
theorem depthMuPAdamScale_mul_hiddenMultiplier
    (width depth : ℕ) (hwidth : 0 < width) (hdepth : 0 < depth) :
    depthMuPAdamLearningRateScale width depth *
        depthMuPHiddenMultiplier width depth = 1 := by
  have hpositive : 0 < Real.sqrt ((width : ℝ) * depth) := by
    apply Real.sqrt_pos.2
    positivity
  unfold depthMuPAdamLearningRateScale depthMuPHiddenMultiplier
  field_simp

/-- Exact exponent comparison: even if the paper's omitted Adam factor is
restored, it cancels only the Depth-μP multiplier and leaves the independent
PC inference attenuation `λ^distance` unchanged. -/
theorem depthMuPScaling_leaves_depthCredit_unchanged
    (width depth distance : ℕ) (inferenceRate : ℝ)
    (hwidth : 0 < width) (hdepth : 0 < depth) :
    depthMuPAdamLearningRateScale width depth *
        depthMuPHiddenMultiplier width depth *
          inferenceRate ^ distance =
      inferenceRate ^ distance := by
  rw [depthMuPAdamScale_mul_hiddenMultiplier width depth hwidth hdepth]
  simp

/-- Any exact scalar learning-rate cancellation of nonzero depth credit must
use the reciprocal geometric factor. -/
theorem learningRate_cancels_depthCredit_iff_geometricReciprocal
    (learningRate inferenceRate : ℝ) (distance : ℕ)
    (hrate : inferenceRate ≠ 0) :
    learningRate * inferenceRate ^ distance = 1 ↔
      learningRate = (inferenceRate ^ distance)⁻¹ := by
  exact mul_eq_one_iff_eq_inv₀ (pow_ne_zero distance hrate)

/-- A degree-`degree` polynomial learning-rate compensation. -/
noncomputable def polynomialDepthCompensation
    (coefficient : ℝ) (degree distance : ℕ) : ℝ :=
  coefficient * (distance : ℝ) ^ degree

/-- Every fixed polynomial compensation is dominated by a genuinely
contractive geometric PC signal. -/
theorem polynomialCompensatedDepthCredit_tendsto_zero
    (coefficient inferenceRate : ℝ) (degree : ℕ)
    (hrate : |inferenceRate| < 1) :
    Tendsto (fun distance : ℕ ↦
      polynomialDepthCompensation coefficient degree distance *
        inferenceRate ^ distance) atTop (nhds 0) := by
  have hbase :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one degree hrate
  simpa [polynomialDepthCompensation, mul_assoc] using
    hbase.const_mul coefficient

/-- Consequently polynomial scaling eventually fails exact cancellation. -/
theorem polynomialCompensation_eventually_not_exact
    (coefficient inferenceRate : ℝ) (degree : ℕ)
    (hrate : |inferenceRate| < 1) :
    ∀ᶠ distance : ℕ in atTop,
      polynomialDepthCompensation coefficient degree distance *
          inferenceRate ^ distance ≠ 1 := by
  have htendsto := polynomialCompensatedDepthCredit_tendsto_zero
    coefficient inferenceRate degree hrate
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp htendsto) (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop threshold] with distance hdistance
  intro hone
  have hnear := hthreshold distance hdistance
  rw [hone] at hnear
  norm_num [Real.dist_eq] at hnear

/-- M3 crown: Depth-μP cancels its own square-root parameterization factor,
not first-arrival PC attenuation; exact cancellation requires a geometric
reciprocal, while every polynomial alternative eventually fails. -/
theorem muPCDepthScaling_cannot_cancel_contractingDepthCredit
    (width depth : ℕ) (inferenceRate : ℝ)
    (hwidth : 0 < width) (hdepth : 0 < depth)
    (hrateNonzero : inferenceRate ≠ 0) (hrateContractive : |inferenceRate| < 1) :
    depthMuPAdamLearningRateScale width depth *
        depthMuPHiddenMultiplier width depth = 1 ∧
      (∀ distance,
        depthMuPAdamLearningRateScale width depth *
            depthMuPHiddenMultiplier width depth *
              inferenceRate ^ distance = inferenceRate ^ distance) ∧
      (∀ learningRate distance,
        learningRate * inferenceRate ^ distance = 1 ↔
          learningRate = (inferenceRate ^ distance)⁻¹) ∧
      (∀ coefficient degree,
        ∀ᶠ distance : ℕ in atTop,
          polynomialDepthCompensation coefficient degree distance *
              inferenceRate ^ distance ≠ 1) := by
  refine ⟨depthMuPAdamScale_mul_hiddenMultiplier
      width depth hwidth hdepth, ?_, ?_, ?_⟩
  · intro distance
    exact depthMuPScaling_leaves_depthCredit_unchanged
      width depth distance inferenceRate hwidth hdepth
  · intro learningRate distance
    exact learningRate_cancels_depthCredit_iff_geometricReciprocal
      learningRate inferenceRate distance hrateNonzero
  · intro coefficient degree
    exact polynomialCompensation_eventually_not_exact
      coefficient inferenceRate degree hrateContractive

/-! ## M4: how far equilibrium moves from the forward pass -/

/-- Cumulative resistance of the first `node` links.  Precision is the
inverse resistance, so this is `Σ_{j<node} 1/precision_j`. -/
noncomputable def precisionResistancePrefix
    (precision : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | node + 1 =>
      precisionResistancePrefix precision node + (precision node)⁻¹

theorem precisionResistancePrefix_nonneg
    (precision : ℕ → ℝ) (node : ℕ)
    (hprecision : ∀ j, j < node → 0 < precision j) :
    0 ≤ precisionResistancePrefix precision node := by
  induction node with
  | zero => simp [precisionResistancePrefix]
  | succ node ih =>
      rw [precisionResistancePrefix]
      exact add_nonneg (ih (fun j hj ↦ hprecision j (by omega)))
        (inv_nonneg.mpr (le_of_lt (hprecision node (by omega))))

theorem precisionResistancePrefix_pos
    (precision : ℕ → ℝ) (node : ℕ) (hnode : 0 < node)
    (hprecision : ∀ j, j < node → 0 < precision j) :
    0 < precisionResistancePrefix precision node := by
  cases node with
  | zero => omega
  | succ node =>
      rw [precisionResistancePrefix]
      exact add_pos_of_nonneg_of_pos
        (precisionResistancePrefix_nonneg precision node
          (fun j hj ↦ hprecision j (by omega)))
        (inv_pos.mpr (hprecision node (by omega)))

theorem precisionResistancePrefix_mono
    (precision : ℕ → ℝ) (first last : ℕ)
    (hfirstLast : first ≤ last)
    (hprecision : ∀ j, j < last → 0 < precision j) :
    precisionResistancePrefix precision first ≤
      precisionResistancePrefix precision last := by
  induction last with
  | zero =>
      have : first = 0 := by omega
      subst first
      exact le_rfl
  | succ last ih =>
      by_cases hfirst : first = last + 1
      · subst first
        exact le_rfl
      · have hfirstLast' : first ≤ last := by omega
        calc
          precisionResistancePrefix precision first ≤
              precisionResistancePrefix precision last :=
            ih hfirstLast' (fun j hj ↦ hprecision j (by omega))
          _ ≤ precisionResistancePrefix precision (last + 1) := by
            rw [precisionResistancePrefix]
            exact le_add_of_nonneg_right
              (inv_nonneg.mpr (le_of_lt (hprecision last (by omega))))

/-- Unit-gain chain with arbitrary positive edge precisions. -/
noncomputable def precisionWeightedUnitLinks
    (depth : ℕ) (precision : ℕ → ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j) :
    Fin depth → PCLink :=
  fun edge ↦
    { gain := 1
      precision := precision edge.val
      precision_pos := hprecision edge.val edge.isLt }

/-- Exact endpoint-conditioned equilibrium: displacement is proportional to
cumulative inverse precision. -/
noncomputable def precisionWeightedEquilibriumState
    (depth : ℕ) (precision : ℕ → ℝ) (input target : ℝ) :
    PCState depth :=
  fun node ↦
    input +
      precisionResistancePrefix precision node.val /
        precisionResistancePrefix precision depth * (target - input)

/-- The feedforward state of a unit-gain chain is constant at the input. -/
noncomputable def unitGainForwardState (depth : ℕ) (input : ℝ) :
    PCState depth :=
  fun _ ↦ input

theorem precisionWeightedEquilibriumState_residual
    (depth : ℕ) (precision : ℕ → ℝ) (input target : ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j)
    (edge : Fin depth) :
    pcResidual (precisionWeightedUnitLinks depth precision hprecision)
        (precisionWeightedEquilibriumState depth precision input target) edge =
      (precision edge.val)⁻¹ /
        precisionResistancePrefix precision depth * (target - input) := by
  simp only [pcResidual, precisionWeightedUnitLinks,
    precisionWeightedEquilibriumState]
  rw [show edge.succ.val = edge.val + 1 by rfl,
    precisionResistancePrefix,
    show edge.castSucc.val = edge.val by rfl]
  ring

theorem precisionWeightedResidualForce_eq
    (depth : ℕ) (precision : ℕ → ℝ) (input target : ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j)
    (edge : Fin depth) :
    (precisionWeightedUnitLinks depth precision hprecision edge).precision *
        pcResidual (precisionWeightedUnitLinks depth precision hprecision)
          (precisionWeightedEquilibriumState depth precision input target) edge =
      (target - input) / precisionResistancePrefix precision depth := by
  rw [precisionWeightedEquilibriumState_residual]
  simp only [precisionWeightedUnitLinks]
  field_simp [ne_of_gt (hprecision edge.val edge.isLt)]

/-- The inverse-precision interpolation is the actual clamped PC
equilibrium, not merely a stationary guess. -/
theorem precisionWeightedEquilibriumState_is_equilibrium
    (depth : ℕ) (hdepth : 0 < depth)
    (precision : ℕ → ℝ) (input target : ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j) :
    pcEquilibrium (precisionWeightedUnitLinks depth precision hprecision)
      input target
      (precisionWeightedEquilibriumState depth precision input target) := by
  rw [pcEquilibrium_iff_normalEquations]
  constructor
  · constructor
    · simp [precisionWeightedEquilibriumState,
        precisionResistancePrefix]
    · have htotal : precisionResistancePrefix precision depth ≠ 0 :=
        ne_of_gt (precisionResistancePrefix_pos precision depth hdepth hprecision)
      simp [precisionWeightedEquilibriumState, htotal]
  · intro node
    unfold pcLocalNormalEquationAt
    by_cases hzero : node.val = 0
    · simp [hzero]
    by_cases hlast : node.val = depth
    · simp [hlast]
    simp [hzero, hlast, precisionWeightedUnitLinks]
    rw [precisionWeightedEquilibriumState_residual,
      precisionWeightedEquilibriumState_residual]
    have htotal : precisionResistancePrefix precision depth ≠ 0 :=
      ne_of_gt (precisionResistancePrefix_pos precision depth hdepth hprecision)
    field_simp [htotal, ne_of_gt (hprecision (node.val - 1) (by omega)),
      ne_of_gt (hprecision node.val (by omega))]

/-- Exact M4 displacement formula.  It exposes both the depth and precision
dependence through a cumulative-resistance ratio. -/
theorem precisionWeightedEquilibrium_sub_forward_exact
    (depth : ℕ) (precision : ℕ → ℝ) (input target : ℝ)
    (node : Fin (depth + 1)) :
    precisionWeightedEquilibriumState depth precision input target node -
        unitGainForwardState depth input node =
      precisionResistancePrefix precision node.val /
        precisionResistancePrefix precision depth * (target - input) := by
  simp [precisionWeightedEquilibriumState, unitGainForwardState]

/-- Norm form of the exact displacement. -/
theorem abs_precisionWeightedEquilibrium_sub_forward
    (depth : ℕ) (hdepth : 0 < depth)
    (precision : ℕ → ℝ) (input target : ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j)
    (node : Fin (depth + 1)) :
    |precisionWeightedEquilibriumState depth precision input target node -
        unitGainForwardState depth input node| =
      (precisionResistancePrefix precision node.val /
          precisionResistancePrefix precision depth) * |target - input| := by
  rw [precisionWeightedEquilibrium_sub_forward_exact, abs_mul]
  have hprefix : 0 ≤ precisionResistancePrefix precision node.val :=
    precisionResistancePrefix_nonneg precision node.val
      (fun j hj ↦ hprecision j (by omega))
  have htotal : 0 ≤ precisionResistancePrefix precision depth :=
    (precisionResistancePrefix_pos precision depth hdepth hprecision).le
  rw [abs_of_nonneg (div_nonneg hprefix htotal)]

/-- Every equilibrium displacement is bounded by the endpoint mismatch; a
small prefix/total resistance ratio gives the precise "barely moves" regime. -/
theorem abs_precisionWeightedEquilibrium_sub_forward_le_endpointMismatch
    (depth : ℕ) (hdepth : 0 < depth)
    (precision : ℕ → ℝ) (input target : ℝ)
    (hprecision : ∀ j, j < depth → 0 < precision j)
    (node : Fin (depth + 1)) :
    |precisionWeightedEquilibriumState depth precision input target node -
        unitGainForwardState depth input node| ≤ |target - input| := by
  rw [abs_precisionWeightedEquilibrium_sub_forward
    depth hdepth precision input target hprecision node]
  have hprefix : 0 ≤ precisionResistancePrefix precision node.val :=
    precisionResistancePrefix_nonneg precision node.val
      (fun j hj ↦ hprecision j (by omega))
  have htotalPos : 0 < precisionResistancePrefix precision depth :=
    precisionResistancePrefix_pos precision depth hdepth hprecision
  have hprefixTotal : precisionResistancePrefix precision node.val ≤
      precisionResistancePrefix precision depth :=
    precisionResistancePrefix_mono precision node.val depth
      (by omega) hprecision
  have hratio : precisionResistancePrefix precision node.val /
      precisionResistancePrefix precision depth ≤ 1 :=
    (div_le_one htotalPos).2 hprefixTotal
  exact mul_le_of_le_one_left (abs_nonneg _) hratio

theorem precisionResistancePrefix_const
    (precision : ℝ) (node : ℕ) :
    precisionResistancePrefix (fun _ ↦ precision) node =
      (node : ℝ) * precision⁻¹ := by
  induction node with
  | zero => simp [precisionResistancePrefix]
  | succ node ih =>
      rw [precisionResistancePrefix, ih]
      push_cast
      ring

/-- With uniform precision, common precision cancels from the equilibrium:
node `k` moves exactly the fraction `k/depth` of the endpoint mismatch. -/
theorem uniformPrecision_equilibrium_sub_forward_exact
    (depth : ℕ) (hdepth : 0 < depth) (precision : ℝ)
    (hprecision : 0 < precision) (input target : ℝ)
    (node : Fin (depth + 1)) :
    precisionWeightedEquilibriumState depth (fun _ ↦ precision)
          input target node -
        unitGainForwardState depth input node =
      (node.val : ℝ) / depth * (target - input) := by
  rw [precisionWeightedEquilibrium_sub_forward_exact,
    precisionResistancePrefix_const, precisionResistancePrefix_const]
  have hprecisionNe : precision ≠ 0 := ne_of_gt hprecision
  have hdepthNe : (depth : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdepth)
  field_simp

/-- Positive fixture: the sealed depth-two example moves halfway from input
to target, exactly `3/2`, so equilibrium is not the forward pass. -/
theorem depthTwo_uniformPrecision_moves_halfway :
    precisionWeightedEquilibriumState 2 (fun _ ↦ 1) 1 2 1 = 3 / 2 := by
  norm_num [precisionWeightedEquilibriumState, precisionResistancePrefix]

/-- Negative boundary: if the endpoint prediction is already correct, every
precision-weighted equilibrium state equals the forward state. -/
theorem precisionWeightedEquilibrium_eq_forward_of_target_eq_input
    (depth : ℕ) (precision : ℕ → ℝ) (input : ℝ) :
    precisionWeightedEquilibriumState depth precision input input =
      unitGainForwardState depth input := by
  funext node
  simp [precisionWeightedEquilibriumState, unitGainForwardState]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
