import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.TrustRegion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Arbitrary-depth strict origin by line restriction

This file treats a deep linear chain along exact one-dimensional restrictions.
For backpropagation, scaling every matrix in an arbitrary direction by `t`
scales the end-to-end prediction by `t ^ depth`.  Consequently every such
restricted loss is critical at the origin for depth at least two and has zero
second derivative there for depth at least three.

For predictive coding, all matrices except the last are fixed to zero and the
last matrix follows the rank-one line `t · (u ⊗ v)`, where `u` is the
normalized nonzero target and `v` is a unit hidden direction.  The latent
energy is minimized explicitly, without differentiating a minimum function.
Its exact value is `‖target‖² / (2 * (1 + t²))`, giving strictly negative
curvature at the origin at every chain depth at least two.

All spaces are real Hilbert spaces.  A list of continuous linear maps is the
coordinate-free form of a same-width matrix chain; no scalar-weight
specialization is used in the depth argument.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Filter Topology
open scoped InnerProductSpace
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Matrix-ray degree counting -/

/-- End-to-end continuous linear map of a same-width matrix chain.  The list
is ordered from input to output. -/
noncomputable def deepLinearComposite
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (V →L[ℝ] V) → V →L[ℝ] V
  | [] => ContinuousLinearMap.id ℝ V
  | weight :: weights => deepLinearComposite weights ∘L weight

/-- An arbitrary matrix direction restricted to the line through the origin. -/
noncomputable def deepLinearRayWeights
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (direction : List (V →L[ℝ] V)) : List (V →L[ℝ] V) :=
  direction.map fun weight => t • weight

/-- Degree counting for a matrix chain: along an arbitrary common ray, the
prediction is homogeneous of degree equal to the number of layers. -/
theorem deepLinearComposite_ray
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (direction : List (V →L[ℝ] V)) :
    deepLinearComposite (deepLinearRayWeights t direction) =
      t ^ direction.length • deepLinearComposite direction := by
  induction direction with
  | nil => simp [deepLinearComposite, deepLinearRayWeights]
  | cons weight weights ih =>
      ext input
      simp only [deepLinearRayWeights, List.map_cons, deepLinearComposite,
        ContinuousLinearMap.comp_apply, smul_apply]
      change deepLinearComposite (deepLinearRayWeights t weights)
          (t • weight input) =
        t ^ (weight :: weights).length • deepLinearComposite weights (weight input)
      rw [ih]
      simp [pow_succ, smul_smul, mul_comm]

/-- Half-squared BP loss along a depth-`L` matrix direction, after applying
the homogeneous matrix product to the input. -/
noncomputable def deepLinearBPRayLoss
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target directionalPrediction : V) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖target - t ^ depth • directionalPrediction‖ ^ 2

/-- The actual matrix-chain ray loss reduces to `deepLinearBPRayLoss`; this is
the bridge from matrix directions to the degree-counted scalar restriction. -/
theorem matrixChain_rayLoss_eq_deepLinearBPRayLoss
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (direction : List (V →L[ℝ] V)) (input target : V) (t : ℝ) :
    (1 / 2 : ℝ) *
        ‖target - deepLinearComposite (deepLinearRayWeights t direction) input‖ ^ 2 =
      deepLinearBPRayLoss direction.length target
        (deepLinearComposite direction input) t := by
  rw [deepLinearComposite_ray]
  rfl

/-- Exact polynomial expansion of every matrix-direction BP restriction. -/
theorem deepLinearBPRayLoss_expansion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target directionalPrediction : V) (t : ℝ) :
    deepLinearBPRayLoss depth target directionalPrediction t =
      (1 / 2 : ℝ) * ‖target‖ ^ 2 -
        t ^ depth * ⟪target, directionalPrediction⟫_ℝ +
        (1 / 2 : ℝ) * t ^ (2 * depth) * ‖directionalPrediction‖ ^ 2 := by
  rw [deepLinearBPRayLoss, norm_sub_sq_real, real_inner_smul_right, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  rw [show 2 * depth = depth * 2 by omega, pow_mul]
  ring

/-- On the last-layer-only line used for the predictive-coding comparison,
all earlier zero weights force the BP prediction to remain zero.  Thus the BP
loss is not merely flat to second order: it is exactly constant on the whole
line. -/
theorem deepLinearBPLastLayerLine_constant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target : V) (t : ℝ) :
    deepLinearBPRayLoss depth target 0 t = (1 / 2 : ℝ) * ‖target‖ ^ 2 := by
  simp [deepLinearBPRayLoss]

/-- At depth at least two, every matrix-direction BP restriction is critical
at the origin. -/
theorem deepLinearBPRayLoss_origin_critical
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target directionalPrediction : V) (hdepth : 2 ≤ depth) :
    HasDerivAt (deepLinearBPRayLoss depth target directionalPrediction) 0 0 := by
  rw [show deepLinearBPRayLoss depth target directionalPrediction =
      fun t : ℝ =>
        (1 / 2 : ℝ) * ‖target‖ ^ 2 -
          t ^ depth * ⟪target, directionalPrediction⟫_ℝ +
          (1 / 2 : ℝ) * t ^ (2 * depth) * ‖directionalPrediction‖ ^ 2 by
    funext t
    exact deepLinearBPRayLoss_expansion depth target directionalPrediction t]
  have hderiv :=
    ((hasDerivAt_const (x := (0 : ℝ))
          ((1 / 2 : ℝ) * ‖target‖ ^ 2)).sub
        ((hasDerivAt_pow depth 0).mul_const
          ⟪target, directionalPrediction⟫_ℝ)).add
      (((hasDerivAt_const (x := (0 : ℝ)) (1 / 2 : ℝ)).mul
          (hasDerivAt_pow (2 * depth) 0)).mul_const
        (‖directionalPrediction‖ ^ 2))
  have hfunctions :
      (fun t : ℝ =>
        (1 / 2 : ℝ) * ‖target‖ ^ 2 -
          t ^ depth * ⟪target, directionalPrediction⟫_ℝ +
          (1 / 2 : ℝ) * t ^ (2 * depth) * ‖directionalPrediction‖ ^ 2) =ᶠ[𝓝 0]
        (((fun _ : ℝ => (1 / 2 : ℝ) * ‖target‖ ^ 2) -
            (fun t : ℝ => t ^ depth * ⟪target, directionalPrediction⟫_ℝ)) +
          (fun t : ℝ =>
            (1 / 2 : ℝ) * t ^ (2 * depth) * ‖directionalPrediction‖ ^ 2)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hpointwise := hderiv.congr_of_eventuallyEq hfunctions
  simpa [zero_pow (by omega : depth - 1 ≠ 0),
    zero_pow (by omega : 2 * depth - 1 ≠ 0)] using hpointwise

/-- From depth three onward, every matrix-direction BP restriction is flat to
second order at the origin. -/
theorem deepLinearBPRayLoss_origin_secondDerivative_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target directionalPrediction : V) (hdepth : 3 ≤ depth) :
    iteratedDeriv 2 (deepLinearBPRayLoss depth target directionalPrediction) 0 = 0 := by
  rw [show deepLinearBPRayLoss depth target directionalPrediction =
      fun t : ℝ =>
        (1 / 2 : ℝ) * ‖target‖ ^ 2 -
          t ^ depth * ⟪target, directionalPrediction⟫_ℝ +
          (1 / 2 : ℝ) * t ^ (2 * depth) * ‖directionalPrediction‖ ^ 2 by
    funext t
    exact deepLinearBPRayLoss_expansion depth target directionalPrediction t]
  change iteratedDeriv 2
      (((fun _ : ℝ => (1 / 2 : ℝ) * ‖target‖ ^ 2) -
          (fun t : ℝ => t ^ depth * ⟪target, directionalPrediction⟫_ℝ)) +
        (fun t : ℝ =>
          ((1 / 2 : ℝ) * t ^ (2 * depth)) * ‖directionalPrediction‖ ^ 2)) 0 = 0
  have hleft : ContDiffAt ℝ 2
      ((fun _ : ℝ => (1 / 2 : ℝ) * ‖target‖ ^ 2) -
        (fun t : ℝ => t ^ depth * ⟪target, directionalPrediction⟫_ℝ)) 0 :=
    contDiffAt_const.sub (by fun_prop)
  rw [iteratedDeriv_add hleft (by fun_prop)]
  rw [iteratedDeriv_sub (by fun_prop) (by fun_prop)]
  rw [iteratedDeriv_const, iteratedDeriv_mul_const_field,
    iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate, iter_deriv_pow]
  norm_num
  have hpow₁ : (0 : ℝ) ^ (depth - 2) = 0 := by
    rw [zero_pow]
    omega
  have hpow₂ : (0 : ℝ) ^ (2 * depth - 2) = 0 := by
    rw [zero_pow]
    omega
  rw [hpow₁, hpow₂]
  ring

/-! ## Rank-one predictive-coding line -/

/-- The last latent on the exact rank-one PC line. -/
noncomputable def deepPCLineLastLatent
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (target : Output) (hiddenDirection : Hidden) (t : ℝ) : Hidden :=
  (t * ‖target‖ / (1 + t ^ 2)) • hiddenDirection

/-- Exact latent energy when every matrix except the final rank-one matrix is
zero.  `early` contains the first `depth - 2` latent vectors and `last` is
`z_(L-1)`. -/
noncomputable def deepPCLineLatentEnergy
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden) (t : ℝ)
    (early : Fin (depth - 2) → Hidden) (last : Hidden) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ‖early i‖ ^ 2 +
    (1 / 2 : ℝ) * ‖last‖ ^ 2 +
    (1 / 2 : ℝ) *
      ‖target -
        (t • InnerProductSpace.rankOne ℝ (NormedSpace.normalize target)
          hiddenDirection) last‖ ^ 2

/-- The selected equilibrated value is the latent energy at the explicit
candidate.  `deepPCLineLastLatent_is_globalMin` below proves that this
selection is genuinely minimizing. -/
noncomputable def deepPCLineEquilibratedEnergy
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden) (t : ℝ) : ℝ :=
  deepPCLineLatentEnergy depth target hiddenDirection t 0
    (deepPCLineLastLatent target hiddenDirection t)

/-- Scalar complete-the-square inequality used to certify the latent minimum. -/
theorem scalar_rankOne_completeSquare_lowerBound (t radius coordinate : ℝ) :
    radius ^ 2 / (1 + t ^ 2) ≤
      coordinate ^ 2 + (radius - t * coordinate) ^ 2 := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg ((1 + t ^ 2) * coordinate - t * radius)]

/-- Exact value of the rank-one line at its explicit latent minimizer. -/
theorem deepPCLineEquilibratedEnergy_exact
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden) (t : ℝ)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1) :
    deepPCLineEquilibratedEnergy depth target hiddenDirection t =
      ‖target‖ ^ 2 / (2 * (1 + t ^ 2)) := by
  have htargetNorm : ‖NormedSpace.normalize target‖ = 1 :=
    NormedSpace.norm_normalize htarget
  have htargetRecover : ‖target‖ • NormedSpace.normalize target = target :=
    NormedSpace.norm_smul_normalize target
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hrank :
      (t • InnerProductSpace.rankOne ℝ (NormedSpace.normalize target)
          hiddenDirection)
          ((t * ‖target‖ / (1 + t ^ 2)) • hiddenDirection) =
        (t ^ 2 * ‖target‖ / (1 + t ^ 2)) •
          NormedSpace.normalize target := by
    simp [InnerProductSpace.rankOne_apply, hhidden, smul_smul]
    ring_nf
  have hlastNorm :
      ‖(t * ‖target‖ / (1 + t ^ 2)) • hiddenDirection‖ ^ 2 =
        (t * ‖target‖ / (1 + t ^ 2)) ^ 2 := by
    rw [norm_smul, hhidden, mul_one, Real.norm_eq_abs, sq_abs]
  have hresidualNorm :
      ‖target -
          (t • InnerProductSpace.rankOne ℝ (NormedSpace.normalize target)
            hiddenDirection)
            ((t * ‖target‖ / (1 + t ^ 2)) • hiddenDirection)‖ ^ 2 =
        (‖target‖ - t ^ 2 * ‖target‖ / (1 + t ^ 2)) ^ 2 := by
    rw [hrank]
    calc
      ‖target -
          (t ^ 2 * ‖target‖ / (1 + t ^ 2)) •
            NormedSpace.normalize target‖ ^ 2 =
          ‖‖target‖ • NormedSpace.normalize target -
            (t ^ 2 * ‖target‖ / (1 + t ^ 2)) •
              NormedSpace.normalize target‖ ^ 2 := by rw [htargetRecover]
      _ = (‖target‖ - t ^ 2 * ‖target‖ / (1 + t ^ 2)) ^ 2 := by
        rw [← sub_smul, norm_smul, htargetNorm, mul_one,
          Real.norm_eq_abs, sq_abs]
  unfold deepPCLineEquilibratedEnergy deepPCLineLatentEnergy
    deepPCLineLastLatent
  simp only [Finset.sum_const_zero, Pi.zero_apply, norm_zero, ne_eq, zero_pow,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, zero_add]
  rw [hlastNorm, hresidualNorm]
  field_simp
  ring_nf

/-- The explicit final latent is a global minimizer of the exact line energy;
all earlier latents minimize independently at zero. -/
theorem deepPCLineLastLatent_is_globalMin
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden) (t : ℝ)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1)
    (early : Fin (depth - 2) → Hidden) (last : Hidden) :
    deepPCLineEquilibratedEnergy depth target hiddenDirection t ≤
      deepPCLineLatentEnergy depth target hiddenDirection t early last := by
  rw [deepPCLineEquilibratedEnergy_exact depth target hiddenDirection t
    htarget hhidden]
  have htargetNorm : ‖NormedSpace.normalize target‖ = 1 :=
    NormedSpace.norm_normalize htarget
  have htargetRecover : ‖target‖ • NormedSpace.normalize target = target :=
    NormedSpace.norm_smul_normalize target
  let coordinate : ℝ := ⟪hiddenDirection, last⟫_ℝ
  have habs : |coordinate| ≤ ‖last‖ := by
    simpa [coordinate, hhidden] using
      abs_real_inner_le_norm hiddenDirection last
  have hcoordinate : coordinate ^ 2 ≤ ‖last‖ ^ 2 := by
    rw [sq_le_sq]
    simpa using habs
  have hscalar := scalar_rankOne_completeSquare_lowerBound
    t ‖target‖ coordinate
  have hearly : 0 ≤ ∑ i, ‖early i‖ ^ 2 := by positivity
  have hrank :
      (t • InnerProductSpace.rankOne ℝ (NormedSpace.normalize target)
        hiddenDirection) last =
        (t * coordinate) • NormedSpace.normalize target := by
    simp [InnerProductSpace.rankOne_apply, coordinate, smul_smul]
  have hresidualNorm :
      ‖target -
          (t • InnerProductSpace.rankOne ℝ (NormedSpace.normalize target)
            hiddenDirection) last‖ ^ 2 =
        (‖target‖ - t * coordinate) ^ 2 := by
    rw [hrank]
    calc
      ‖target - (t * coordinate) • NormedSpace.normalize target‖ ^ 2 =
          ‖‖target‖ • NormedSpace.normalize target -
            (t * coordinate) • NormedSpace.normalize target‖ ^ 2 := by
        rw [htargetRecover]
      _ = (‖target‖ - t * coordinate) ^ 2 := by
        rw [← sub_smul, norm_smul, htargetNorm, mul_one,
          Real.norm_eq_abs, sq_abs]
  unfold deepPCLineLatentEnergy
  rw [hresidualNorm]
  change ‖target‖ ^ 2 / (2 * (1 + t ^ 2)) ≤
    (1 / 2 : ℝ) * ∑ i, ‖early i‖ ^ 2 +
      (1 / 2 : ℝ) * ‖last‖ ^ 2 +
      (1 / 2 : ℝ) * (‖target‖ - t * coordinate) ^ 2
  have hhalf :
      ‖target‖ ^ 2 / (2 * (1 + t ^ 2)) =
        (1 / 2 : ℝ) * (‖target‖ ^ 2 / (1 + t ^ 2)) := by
    field_simp
  rw [hhalf]
  nlinarith

/-! ## Strict line curvature -/

/-- The exact equilibrated line is critical at the origin. -/
theorem deepPCLineEquilibratedEnergy_origin_critical
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1) :
    HasDerivAt (deepPCLineEquilibratedEnergy depth target hiddenDirection) 0 0 := by
  have heq : deepPCLineEquilibratedEnergy depth target hiddenDirection =
      fun t : ℝ => ‖target‖ ^ 2 / (2 * (1 + t ^ 2)) := by
    funext t
    exact deepPCLineEquilibratedEnergy_exact depth target hiddenDirection t
      htarget hhidden
  rw [heq]
  have hdenominatorRaw :=
    (hasDerivAt_const (x := (0 : ℝ)) (2 : ℝ)).mul
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
        (hasDerivAt_pow 2 0))
  have hdenominatorFunctions :
      (fun t : ℝ => 2 * (1 + t ^ 2)) =ᶠ[𝓝 0]
        ((fun _ : ℝ => 2) * ((fun _ : ℝ => 1) + fun t : ℝ => t ^ 2)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hdenominator :
      HasDerivAt (fun t : ℝ => 2 * (1 + t ^ 2)) 0 0 := by
    simpa using
      hdenominatorRaw.congr_of_eventuallyEq hdenominatorFunctions
  have hnumerator :
      HasDerivAt (fun _ : ℝ => ‖target‖ ^ 2) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) (‖target‖ ^ 2)
  simpa using hnumerator.fun_div hdenominator (by norm_num)

/-- Exact negative second directional curvature of the equilibrated rank-one
line at the origin. -/
theorem deepPCLineEquilibratedEnergy_origin_curvature
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (depth : ℕ) (target : Output) (hiddenDirection : Hidden)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1) :
    HasSecondDirectionalCurvatureAt
      (deepPCLineEquilibratedEnergy depth target hiddenDirection)
      0 1 (-‖target‖ ^ 2) := by
  have heq : deepPCLineEquilibratedEnergy depth target hiddenDirection =
      fun t : ℝ => ‖target‖ ^ 2 / (2 * (1 + t ^ 2)) := by
    funext t
    exact deepPCLineEquilibratedEnergy_exact depth target hiddenDirection t
      htarget hhidden
  rw [heq]
  let formula : ℝ → ℝ := fun step => -‖target‖ ^ 2 / (1 + step ^ 2)
  have hcontinuous : ContinuousAt formula 0 := by
    dsimp [formula]
    fun_prop (disch := positivity)
  have hzero : formula 0 = -‖target‖ ^ 2 := by
    simp [formula]
  have htendsto : Tendsto formula (𝓝[≠] 0) (𝓝 (-‖target‖ ^ 2)) := by
    simpa only [hzero] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  unfold HasSecondDirectionalCurvatureAt
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with step hstep
  have hne : step ≠ 0 := by simpa using hstep
  dsimp [formula]
  unfold symmetricSecondDirectionalQuotient
  simp only [smul_eq_mul, mul_one, zero_add, zero_sub]
  field_simp
  ring

/-- The exact rank-one PC restriction is a certified strict saddle for every
formal depth; in particular this covers every deep-linear chain of depth at
least two.  Earlier zero-weight layers contribute independent squared norms
and therefore do not alter the selected line energy. -/
theorem deepPCLineEquilibratedEnergy_hasStrictSaddleCertificate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target hiddenDirection : V)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1) :
    HasStrictSaddleCertificate
      (deepPCLineEquilibratedEnergy depth target hiddenDirection) 0 := by
  refine ⟨?_, 1, -‖target‖ ^ 2,
    deepPCLineEquilibratedEnergy_origin_curvature depth target hiddenDirection
      htarget hhidden, ?_⟩
  · simpa [IsCriticalPoint] using
      (deepPCLineEquilibratedEnergy_origin_critical depth target
        hiddenDirection htarget hhidden).hasFDerivAt
  · exact neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr htarget))

/-- Crown: for every declared depth at least two and every nonzero target, the
rank-one equilibrated PC restriction has a strict saddle certificate, whereas
every BP matrix-direction restriction is critical from depth two and flat to
second order from depth three. -/
theorem arbitraryDepth_lineRestriction_strictSaddle
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target hiddenDirection directionalPrediction : V)
    (hdepth : 3 ≤ depth) (htarget : target ≠ 0)
    (hhidden : ‖hiddenDirection‖ = 1) :
    HasStrictSaddleCertificate
        (deepPCLineEquilibratedEnergy depth target hiddenDirection) 0 ∧
      HasDerivAt (deepLinearBPRayLoss depth target directionalPrediction) 0 0 ∧
      iteratedDeriv 2
        (deepLinearBPRayLoss depth target directionalPrediction) 0 = 0 := by
  refine ⟨?_, deepLinearBPRayLoss_origin_critical depth target
    directionalPrediction (by omega),
    deepLinearBPRayLoss_origin_secondDerivative_zero depth target
      directionalPrediction hdepth⟩
  exact deepPCLineEquilibratedEnergy_hasStrictSaddleCertificate depth target
    hiddenDirection htarget hhidden

/-- Shared-line crown: the rank-one PC restriction has strict negative
curvature while the BP restriction induced by zero earlier weights is exactly
constant at every parameter value. -/
theorem rankOnePCLine_strict_BPconstant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target hiddenDirection : V)
    (htarget : target ≠ 0) (hhidden : ‖hiddenDirection‖ = 1) :
    HasStrictSaddleCertificate
        (deepPCLineEquilibratedEnergy depth target hiddenDirection) 0 ∧
      ∀ t : ℝ,
        deepLinearBPRayLoss depth target 0 t =
          (1 / 2 : ℝ) * ‖target‖ ^ 2 := by
  exact ⟨deepPCLineEquilibratedEnergy_hasStrictSaddleCertificate depth target
      hiddenDirection htarget hhidden,
    deepLinearBPLastLayerLine_constant depth target⟩

/-- Proof-bearing discharge of the formerly named deep-origin boundary.  The
metadata status and the arbitrary-depth comparison certificate are packaged
together so the status cannot be cited without the checked theorem. -/
theorem generalDeepLinearOriginBoundary_discharged
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (depth : ℕ) (target hiddenDirection directionalPrediction : V)
    (hdepth : 3 ≤ depth) (htarget : target ≠ 0)
    (hhidden : ‖hiddenDirection‖ = 1) :
    generalDeepLinearOriginBoundary.status = .resolvedByMatrixLineRestriction ∧
      HasStrictSaddleCertificate
          (deepPCLineEquilibratedEnergy depth target hiddenDirection) 0 ∧
        HasDerivAt (deepLinearBPRayLoss depth target directionalPrediction) 0 0 ∧
        iteratedDeriv 2
          (deepLinearBPRayLoss depth target directionalPrediction) 0 = 0 := by
  exact ⟨generalDeepLinearOriginBoundary_resolved,
    arbitraryDepth_lineRestriction_strictSaddle depth target hiddenDirection
      directionalPrediction hdepth htarget hhidden⟩

/-- Positive fixture: a unit scalar target and hidden direction have exact
energy `1/4` at unit line parameter. -/
theorem depthFour_lineRestriction_positiveExample :
    deepPCLineEquilibratedEnergy 4 (1 : ℝ) (1 : ℝ) 1 = 1 / 4 := by
  rw [deepPCLineEquilibratedEnergy_exact]
  · norm_num
  · norm_num
  · norm_num

/-- Negative boundary: a zero target cannot yield strict negative curvature. -/
theorem zeroTarget_lineRestriction_curvature_boundary
    {Hidden Output : Type*}
    [NormedAddCommGroup Hidden] [InnerProductSpace ℝ Hidden]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    (_depth : ℕ) (_hiddenDirection : Hidden) :
    -‖(0 : Output)‖ ^ 2 = 0 := by
  norm_num

#print axioms arbitraryDepth_lineRestriction_strictSaddle
#print axioms rankOnePCLine_strict_BPconstant
#print axioms generalDeepLinearOriginBoundary_discharged

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
