import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning

/-!
# Strict and non-strict saddles of equilibrated PC energy

The literature comparison is pinned to Innocenti, Achour, Singh, and Buckley,
*Only Strict Saddles in the Energy Landscape of Predictive Coding Networks?*,
arXiv:2408.11979v2 (revised 2024-11-08).  The source archive retrieved on
2026-07-15 had SHA-256
`1b2b311bf4587e7a3c37d55243864bf29df07d38150a1f02bb708c3bf88b8b0f`.

We first provide derivative-independent Hessian infrastructure through
symmetric second directional quotients, then verify the published strict
origin result in an exact scalar two-layer instance.  The same instance with a
covariance-degenerate but nontrivial dataset yields a counterexample to the
paper's unrestricted conjecture that every equilibrated-energy saddle is
strict: `(w₁,w₂) = (1,0)` is critical and has rising and falling cubic-order
approach curves, while every second directional curvature is zero.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Topology

/-! ## Hessian-facing definitions -/

/-- Symmetric second difference divided by the squared step.  For a twice
Fréchet-differentiable function its punctured limit is the Hessian quadratic
form in `direction`. -/
noncomputable def symmetricSecondDirectionalQuotient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (energy : V → ℝ) (point direction : V) (step : ℝ) : ℝ :=
  (energy (point + step • direction) - 2 * energy point +
      energy (point - step • direction)) / step ^ 2

/-- A certified second directional curvature, expressed without choosing
coordinates for a Hessian matrix. -/
def HasSecondDirectionalCurvatureAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (energy : V → ℝ) (point direction : V) (curvature : ℝ) : Prop :=
  Tendsto (symmetricSecondDirectionalQuotient energy point direction)
    (𝓝[≠] 0) (𝓝 curvature)

/-- Exact criticality in real coordinates. -/
def IsCriticalPoint
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (energy : V → ℝ) (point : V) : Prop :=
  HasFDerivAt energy (0 : V →L[ℝ] ℝ) point

/-- A strict-saddle certificate consists of exact criticality and one negative
second directional curvature. -/
def HasStrictSaddleCertificate
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (energy : V → ℝ) (point : V) : Prop :=
  IsCriticalPoint energy point ∧
    ∃ direction curvature,
      HasSecondDirectionalCurvatureAt energy point direction curvature ∧
        curvature < 0

/-- Two curves approaching the point through strictly lower and strictly
higher energy provide a direct local saddle witness. -/
def HasTwoSidedSaddleCurves
    {V : Type*} [TopologicalSpace V]
    (energy : V → ℝ) (point : V) (lower upper : ℝ → V) : Prop :=
  Tendsto lower (𝓝 0) (𝓝 point) ∧
    Tendsto upper (𝓝 0) (𝓝 point) ∧
    ∀ step, 0 < step → step < 1 →
      energy (lower step) < energy point ∧ energy point < energy (upper step)

/-! ## Exact two-layer scalar dataset -/

/-- Two examples have inputs `(1,1)` and targets `(1,-1)`.  For scalar weights
`(w₁,w₂)`, their exact equilibrated PC energy is the rescaled batch MSE below. -/
noncomputable def orthogonalDatasetEquilibratedEnergy
    (weights : ℝ × ℝ) : ℝ :=
  (1 + weights.1 ^ 2 * weights.2 ^ 2) /
    (2 * (1 + weights.2 ^ 2))

/-- Direct derivation from the two residuals and the predictive variance
`1 + w₂²`. -/
theorem orthogonalDatasetEquilibratedEnergy_eq_rescaledBatchMSE
    (weights : ℝ × ℝ) :
    orthogonalDatasetEquilibratedEnergy weights =
      (((1 - weights.2 * weights.1) ^ 2 +
          (-1 - weights.2 * weights.1) ^ 2) / 4) /
        (1 + weights.2 ^ 2) := by
  unfold orthogonalDatasetEquilibratedEnergy
  field_simp
  ring

noncomputable def orthogonalEnergyCubicFactor
    (weights : ℝ × ℝ) : ℝ :=
  weights.2 ^ 2 * (weights.1 ^ 2 - 1)

noncomputable def orthogonalEnergyPositiveScale
    (weights : ℝ × ℝ) : ℝ :=
  1 / (2 * (1 + weights.2 ^ 2))

/-- Separating the constant energy level exposes the cubic-order degeneracy at
`(1,0)`. -/
theorem orthogonalDatasetEquilibratedEnergy_eq_constant_add_cubicFactor
    (weights : ℝ × ℝ) :
    orthogonalDatasetEquilibratedEnergy weights =
      1 / 2 + orthogonalEnergyCubicFactor weights *
        orthogonalEnergyPositiveScale weights := by
  unfold orthogonalDatasetEquilibratedEnergy orthogonalEnergyCubicFactor
    orthogonalEnergyPositiveScale
  field_simp
  ring

theorem orthogonalEnergyCubicFactor_hasFDerivAt_zero
    (firstWeight : ℝ) :
    HasFDerivAt orthogonalEnergyCubicFactor
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) (firstWeight, 0) := by
  have hsnd :=
    (hasFDerivAt_snd (𝕜 := ℝ)
      (p := ((firstWeight, 0) : ℝ × ℝ))).pow 2
  have hfst :=
    ((hasFDerivAt_fst (𝕜 := ℝ)
      (p := ((firstWeight, 0) : ℝ × ℝ))).pow 2).sub_const 1
  have hproduct := hsnd.mul hfst
  unfold orthogonalEnergyCubicFactor
  apply hproduct.congr_fderiv
  norm_num

/-- Every point `(w₁,0)` is exactly critical for this zero input-target
covariance dataset. -/
theorem orthogonalDatasetEquilibratedEnergy_critical
    (firstWeight : ℝ) :
    IsCriticalPoint orthogonalDatasetEquilibratedEnergy (firstWeight, 0) := by
  have hscale : DifferentiableAt ℝ orthogonalEnergyPositiveScale
      (firstWeight, 0) := by
    unfold orthogonalEnergyPositiveScale
    fun_prop (disch := norm_num)
  have hproduct :=
    (orthogonalEnergyCubicFactor_hasFDerivAt_zero firstWeight).mul
      hscale.hasFDerivAt
  have hsum :=
    (hasFDerivAt_const (x := ((firstWeight, 0) : ℝ × ℝ))
      (c := (1 / 2 : ℝ))).add hproduct
  have hfunction : orthogonalDatasetEquilibratedEnergy = fun weights =>
      1 / 2 + orthogonalEnergyCubicFactor weights *
        orthogonalEnergyPositiveScale weights := by
    funext weights
    exact orthogonalDatasetEquilibratedEnergy_eq_constant_add_cubicFactor weights
  rw [IsCriticalPoint, hfunction]
  apply hsum.congr_fderiv
  norm_num [orthogonalEnergyCubicFactor]

/-- Algebraic difference from the critical energy level at `(1,0)`. -/
theorem orthogonalDatasetEquilibratedEnergy_sub_counterexamplePoint
    (firstWeight secondWeight : ℝ) :
    orthogonalDatasetEquilibratedEnergy (firstWeight, secondWeight) -
        orthogonalDatasetEquilibratedEnergy (1, 0) =
      secondWeight ^ 2 * (firstWeight ^ 2 - 1) /
        (2 * (1 + secondWeight ^ 2)) := by
  unfold orthogonalDatasetEquilibratedEnergy
  field_simp
  ring

/-! ## Published strict-origin special case -/

/-- At every critical point `(w₁,0)`, the output-weight direction has exact
curvature `w₁² - 1`.  This identifies both the published strict region and
its degenerate boundary. -/
theorem orthogonalDataset_outputDirection_curvature
    (firstWeight : ℝ) :
    HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
      (firstWeight, 0) (0, 1) (firstWeight ^ 2 - 1) := by
  let formula : ℝ → ℝ := fun step ↦
    (firstWeight ^ 2 - 1) / (1 + step ^ 2)
  have hcontinuous : ContinuousAt formula 0 := by
    dsimp [formula]
    fun_prop (disch := positivity)
  have hzero : formula 0 = firstWeight ^ 2 - 1 := by
    simp [formula]
  have htendsto : Tendsto formula (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds (firstWeight ^ 2 - 1)) := by
    simpa only [hzero] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  unfold HasSecondDirectionalCurvatureAt
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with step hstep
  have hne : step ≠ 0 := by simpa using hstep
  dsimp [formula]
  unfold symmetricSecondDirectionalQuotient
  rw [show step • ((0, 1) : ℝ × ℝ) = (step * 0, step * 1) by
    ext <;> simp]
  rw [show ((firstWeight, 0) : ℝ × ℝ) + (step * 0, step * 1) =
      (firstWeight, step) by ext <;> simp]
  rw [show ((firstWeight, 0) : ℝ × ℝ) - (step * 0, step * 1) =
      (firstWeight, -step) by ext <;> simp]
  unfold orthogonalDatasetEquilibratedEnergy
  field_simp
  ring

/-- The output-weight direction at the origin has curvature exactly `-1`. -/
theorem orthogonalDataset_origin_outputDirection_curvature :
    HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
      (0, 0) (0, 1) (-1) := by
  let formula : ℝ → ℝ := fun step => -1 / (1 + step ^ 2)
  have hcontinuous : ContinuousAt formula 0 := by
    dsimp [formula]
    fun_prop (disch := positivity)
  have hzero : formula 0 = -1 := by norm_num [formula]
  have htendsto : Tendsto formula (𝓝[≠] 0) (𝓝 (-1)) := by
    simpa only [hzero] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  unfold HasSecondDirectionalCurvatureAt
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with step hstep
  have hne : step ≠ 0 := by simpa using hstep
  dsimp [formula]
  unfold symmetricSecondDirectionalQuotient
  rw [show step • ((0, 1) : ℝ × ℝ) = (step * 0, step * 1) by
    ext <;> simp]
  rw [show ((0, 0) : ℝ × ℝ) + (step * 0, step * 1) =
      (step * 0, step * 1) by ext <;> simp]
  rw [show ((0, 0) : ℝ × ℝ) - (step * 0, step * 1) =
      (-step * 0, -step * 1) by ext <;> simp]
  unfold orthogonalDatasetEquilibratedEnergy
  field_simp
  ring

/-- Kernel-checked instance of the published result: the origin is critical and
has a strict negative-curvature direction. -/
theorem orthogonalDataset_origin_hasStrictSaddleCertificate :
    HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (0, 0) := by
  refine ⟨orthogonalDatasetEquilibratedEnergy_critical 0, (0, 1), -1,
    orthogonalDataset_origin_outputDirection_curvature, by norm_num⟩

/-- Strongest strictification statement for this critical line: every point
inside the covariance boundary `w₁² < 1` has a negative output-direction
curvature and is therefore strict. -/
theorem orthogonalDataset_innerStrip_hasStrictSaddleCertificate
    (firstWeight : ℝ) (hinner : firstWeight ^ 2 < 1) :
    HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy
      (firstWeight, 0) := by
  exact ⟨orthogonalDatasetEquilibratedEnergy_critical firstWeight,
    (0, 1), firstWeight ^ 2 - 1,
    orthogonalDataset_outputDirection_curvature firstWeight, by linarith⟩

/-! ## Counterexample to unrestricted universal strictness -/

/-- At `(1,0)`, every symmetric second directional quotient tends to zero. -/
theorem orthogonalDataset_counterexamplePoint_all_curvatures_zero
    (direction : ℝ × ℝ) :
    HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
      (1, 0) direction 0 := by
  let formula : ℝ → ℝ := fun step =>
    step ^ 2 * direction.1 ^ 2 * direction.2 ^ 2 /
      (1 + step ^ 2 * direction.2 ^ 2)
  have hcontinuous : ContinuousAt formula 0 := by
    dsimp [formula]
    fun_prop (disch := positivity)
  have hzero : formula 0 = 0 := by simp [formula]
  have htendsto : Tendsto formula (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hzero] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  unfold HasSecondDirectionalCurvatureAt
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with step hstep
  have hne : step ≠ 0 := by simpa using hstep
  rcases direction with ⟨firstDirection, secondDirection⟩
  dsimp [formula]
  unfold symmetricSecondDirectionalQuotient
  rw [show step • ((firstDirection, secondDirection) : ℝ × ℝ) =
      (step * firstDirection, step * secondDirection) by ext <;> simp]
  rw [show ((1, 0) : ℝ × ℝ) +
      (step * firstDirection, step * secondDirection) =
      (1 + step * firstDirection, step * secondDirection) by ext <;> simp]
  rw [show ((1, 0) : ℝ × ℝ) -
      (step * firstDirection, step * secondDirection) =
      (1 - step * firstDirection, -step * secondDirection) by ext <;> simp]
  unfold orthogonalDatasetEquilibratedEnergy
  field_simp
  ring

/-- Explicit cubic approach curves make the zero-curvature critical point a
genuine saddle rather than a local minimum or maximum. -/
theorem orthogonalDataset_counterexamplePoint_twoSidedSaddleCurves :
    HasTwoSidedSaddleCurves orthogonalDatasetEquilibratedEnergy (1, 0)
      (fun step => (1 - step, step))
      (fun step => (1 + step, step)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcontinuous : ContinuousAt (fun step : ℝ => (1 - step, step)) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  · have hcontinuous : ContinuousAt (fun step : ℝ => (1 + step, step)) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  · intro step hpositive hone
    constructor
    · rw [← sub_neg,
        orthogonalDatasetEquilibratedEnergy_sub_counterexamplePoint]
      have hfactor : (1 - step) ^ 2 - 1 < 0 := by nlinarith
      have hsquare : 0 < step ^ 2 := sq_pos_of_pos hpositive
      have hdenominator : 0 < 2 * (1 + step ^ 2) := by positivity
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg hsquare hfactor) hdenominator
    · rw [← sub_pos,
        orthogonalDatasetEquilibratedEnergy_sub_counterexamplePoint]
      have hfactor : 0 < (1 + step) ^ 2 - 1 := by nlinarith
      positivity

/-- The zero-curvature result rules out every strict-saddle certificate at the
counterexample point. -/
theorem orthogonalDataset_counterexamplePoint_not_strict :
    ¬ HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (1, 0) := by
  rintro ⟨_hcritical, direction, curvature, hcurvature, hnegative⟩
  have hzero := orthogonalDataset_counterexamplePoint_all_curvatures_zero direction
  have : curvature = 0 := tendsto_nhds_unique hcurvature hzero
  linarith

/-- Final counterexample package: an exact critical point, explicit local
descent/ascent curves, zero curvature in every direction, and therefore no
strict-saddle certificate. -/
theorem orthogonalDataset_universalStrictSaddleConjecture_counterexample :
    IsCriticalPoint orthogonalDatasetEquilibratedEnergy (1, 0) ∧
      HasTwoSidedSaddleCurves orthogonalDatasetEquilibratedEnergy (1, 0)
        (fun step => (1 - step, step))
        (fun step => (1 + step, step)) ∧
      (∀ direction,
        HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
          (1, 0) direction 0) ∧
      ¬ HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (1, 0) :=
  ⟨orthogonalDatasetEquilibratedEnergy_critical 1,
    orthogonalDataset_counterexamplePoint_twoSidedSaddleCurves,
    orthogonalDataset_counterexamplePoint_all_curvatures_zero,
    orthogonalDataset_counterexamplePoint_not_strict⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
