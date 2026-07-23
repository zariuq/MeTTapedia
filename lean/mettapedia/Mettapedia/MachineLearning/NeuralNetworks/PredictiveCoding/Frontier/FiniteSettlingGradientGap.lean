import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BacktrackingDescent
import Mathlib.Analysis.Convex.Strong

/-!
# Finite-settling predictive-coding gradient error

This file quantifies the error made when a predictive-coding adapter update is
formed after finitely many latent-settling sweeps.  The main theorem covers a
strongly-convex, smooth latent energy on a real Hilbert space.  Its contraction
factor is derived from the inference rate, strong-convexity constant, and
gradient-smoothness constant; the adapter-gradient readout may be any
Lipschitz function.  A scalar quadratic is retained afterward as an exact
positive/negative fixture.

The resulting bound separates finite-settling error from equilibrium mismatch.
It therefore does not silently identify a finite PC update with backpropagation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace

/-! ## Hilbert-space strong-convex/smooth model -/

/-- First-order representation of a differentiable `mu`-strongly convex,
`L`-smooth latent energy.  Strong convexity is stated by its supporting
quadratic inequality, while smoothness is the Lipschitz property of the same
gradient field.  These are the standard first-order characterizations used by
the gradient-settling proof. -/
structure StrongSmoothLatentEnergy
    (Latent : Type*) [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
    (mu L : ℝ) where
  energy : Latent → ℝ
  gradient : Latent → Latent
  strongConvexFirstOrder : ∀ x y,
    energy x + ⟪gradient x, y - x⟫_ℝ + mu / 2 * ‖y - x‖ ^ 2 ≤ energy y
  gradientLipschitz : ∀ x y,
    ‖gradient x - gradient y‖ ≤ L * ‖x - y‖

section HilbertSettling

variable {Latent Adapter : Type*}
  [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
  [NormedAddCommGroup Adapter]

/-- Strong convexity implies strong monotonicity of the represented gradient;
this is derived by adding the two first-order supporting inequalities. -/
theorem StrongSmoothLatentEnergy.gradient_strongMonotone
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (x y : Latent) :
    mu * ‖x - y‖ ^ 2 ≤
      ⟪model.gradient x - model.gradient y, x - y⟫_ℝ := by
  have hxy := model.strongConvexFirstOrder x y
  have hyx := model.strongConvexFirstOrder y x
  have hyxvec : y - x = -(x - y) := by abel
  rw [hyxvec, norm_neg, inner_neg_right] at hxy
  rw [inner_sub_left]
  nlinarith

/-- One gradient-settling sweep on the latent energy. -/
noncomputable def hilbertSettlingStep
    {mu L : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (rate : ℝ) (state : Latent) : Latent :=
  state - rate • model.gradient state

/-- Squared rate-derived contraction coefficient. -/
noncomputable def hilbertSettlingContractionSq
    (mu L rate : ℝ) : ℝ :=
  1 - 2 * rate * mu + rate ^ 2 * L ^ 2

/-- Rate-derived contraction factor for Hilbert-space gradient settling. -/
noncomputable def hilbertSettlingContraction
    (mu L rate : ℝ) : ℝ :=
  Real.sqrt (hilbertSettlingContractionSq mu L rate)

theorem hilbertSettlingContraction_nonneg (mu L rate : ℝ) :
    0 ≤ hilbertSettlingContraction mu L rate := by
  exact Real.sqrt_nonneg _

/-- The squared distance contraction follows from strong monotonicity and
gradient Lipschitzness. -/
theorem hilbertSettlingStep_sub_sq_le
    {mu L rate : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate) (x y : Latent) :
    ‖hilbertSettlingStep model rate x -
        hilbertSettlingStep model rate y‖ ^ 2 ≤
      hilbertSettlingContractionSq mu L rate * ‖x - y‖ ^ 2 := by
  let difference := x - y
  let gradientDifference := model.gradient x - model.gradient y
  have hstep :
      hilbertSettlingStep model rate x -
          hilbertSettlingStep model rate y =
        difference - rate • gradientDifference := by
    dsimp [hilbertSettlingStep, difference, gradientDifference]
    module
  have hmono :
      mu * ‖difference‖ ^ 2 ≤
        ⟪gradientDifference, difference⟫_ℝ := by
    exact model.gradient_strongMonotone x y
  have hlip : ‖gradientDifference‖ ≤ L * ‖difference‖ := by
    exact model.gradientLipschitz x y
  have hlipSq :
      ‖gradientDifference‖ ^ 2 ≤ (L * ‖difference‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).2 hlip
  rw [hstep, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hrate, mul_pow]
  rw [real_inner_comm gradientDifference difference]
  unfold hilbertSettlingContractionSq
  nlinarith [mul_nonneg hrate (sub_nonneg.mpr hmono)]

/-- Under the explicit stable-rate interval, the derived factor is below one.
The nonnegative-coefficient premise is the exact condition needed for the real
square root representation. -/
theorem hilbertSettlingContraction_lt_one
    (mu L rate : ℝ)
    (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate) :
    hilbertSettlingContraction mu L rate < 1 := by
  rw [hilbertSettlingContraction]
  apply (Real.sqrt_lt hcoefficient zero_le_one).2
  unfold hilbertSettlingContractionSq
  nlinarith [mul_pos hrate (sub_pos.mpr hstable)]

/-- Norm contraction for one Hilbert-space settle sweep. -/
theorem hilbertSettlingStep_contraction
    {mu L rate : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (x y : Latent) :
    ‖hilbertSettlingStep model rate x -
        hilbertSettlingStep model rate y‖ ≤
      hilbertSettlingContraction mu L rate * ‖x - y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (hilbertSettlingContraction_nonneg mu L rate)
      (norm_nonneg _))).1
  rw [mul_pow, show hilbertSettlingContraction mu L rate ^ 2 =
    hilbertSettlingContractionSq mu L rate by
      exact Real.sq_sqrt hcoefficient]
  exact hilbertSettlingStep_sub_sq_le model hL hrate x y

theorem hilbertSettlingStep_fixed_of_gradient_zero
    {mu L rate : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (target : Latent) (htarget : model.gradient target = 0) :
    hilbertSettlingStep model rate target = target := by
  simp [hilbertSettlingStep, htarget]

/-- Exact geometric norm bound after `sweeps` settle iterations. -/
theorem hilbertSettling_iterate_distance_le
    {mu L rate : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (sweeps : ℕ) :
    ‖(hilbertSettlingStep model rate)^[sweeps] initial - target‖ ≤
      hilbertSettlingContraction mu L rate ^ sweeps * ‖initial - target‖ := by
  induction sweeps with
  | zero => simp
  | succ sweeps ih =>
      rw [Function.iterate_succ_apply']
      have hfixed := hilbertSettlingStep_fixed_of_gradient_zero
        model target (rate := rate) htarget
      calc
        ‖hilbertSettlingStep model rate
              ((hilbertSettlingStep model rate)^[sweeps] initial) - target‖ =
            ‖hilbertSettlingStep model rate
                ((hilbertSettlingStep model rate)^[sweeps] initial) -
              hilbertSettlingStep model rate target‖ := by rw [hfixed]
        _ ≤ hilbertSettlingContraction mu L rate *
              ‖(hilbertSettlingStep model rate)^[sweeps] initial - target‖ :=
          hilbertSettlingStep_contraction model hL hrate hcoefficient _ _
        _ ≤ hilbertSettlingContraction mu L rate *
              (hilbertSettlingContraction mu L rate ^ sweeps *
                ‖initial - target‖) := by
          exact mul_le_mul_of_nonneg_left ih
            (hilbertSettlingContraction_nonneg mu L rate)
        _ = hilbertSettlingContraction mu L rate ^ (sweeps + 1) *
              ‖initial - target‖ := by ring

/-- `K`-Lipschitz adapter-gradient readout about the latent equilibrium. -/
def HilbertGradientReadoutLipschitzAt
    (gradientReadout : Latent → Adapter) (target : Latent) (K : ℝ) : Prop :=
  ∀ state,
    ‖gradientReadout state - gradientReadout target‖ ≤ K * ‖state - target‖

/-- Equilibrium PC-to-BP mismatch in adapter-gradient norm. -/
noncomputable def hilbertEquilibriumGradientMismatch
    (gradientReadout : Latent → Adapter) (target : Latent)
    (bpGradient : Adapter) : ℝ :=
  ‖gradientReadout target - bpGradient‖

/-- Requested finite-settling PC-to-BP gradient gap in Hilbert latent space. -/
theorem hilbertFiniteSettlingGradientGap_le
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (gradientReadout : Latent → Adapter) (bpGradient : Adapter)
    (hK : 0 ≤ K)
    (hreadout : HilbertGradientReadoutLipschitzAt gradientReadout target K)
    (sweeps : ℕ) :
    ‖gradientReadout
          ((hilbertSettlingStep model rate)^[sweeps] initial) - bpGradient‖ ≤
      K * hilbertSettlingContraction mu L rate ^ sweeps * ‖initial - target‖ +
        hilbertEquilibriumGradientMismatch gradientReadout target bpGradient := by
  let settled := (hilbertSettlingStep model rate)^[sweeps] initial
  have hdistance := hilbertSettling_iterate_distance_le model hL hrate
    hcoefficient target initial htarget sweeps
  calc
    ‖gradientReadout settled - bpGradient‖ ≤
        ‖gradientReadout settled - gradientReadout target‖ +
          ‖gradientReadout target - bpGradient‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (gradientReadout settled - gradientReadout target)
          (gradientReadout target - bpGradient)
    _ ≤ K * ‖settled - target‖ +
          ‖gradientReadout target - bpGradient‖ := by
      gcongr
      exact hreadout settled
    _ ≤ K * (hilbertSettlingContraction mu L rate ^ sweeps *
          ‖initial - target‖) +
          ‖gradientReadout target - bpGradient‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hdistance hK]
    _ = K * hilbertSettlingContraction mu L rate ^ sweeps *
          ‖initial - target‖ +
          hilbertEquilibriumGradientMismatch gradientReadout target bpGradient := by
      unfold hilbertEquilibriumGradientMismatch
      ring

/-- Existing equilibrium exactness removes the irreducible mismatch term. -/
theorem hilbertFiniteSettlingGradientGap_zeroMismatch
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 ≤ rate)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (gradientReadout : Latent → Adapter) (bpGradient : Adapter)
    (hK : 0 ≤ K)
    (hreadout : HilbertGradientReadoutLipschitzAt gradientReadout target K)
    (hequilibriumExact : gradientReadout target = bpGradient)
    (sweeps : ℕ) :
    ‖gradientReadout
          ((hilbertSettlingStep model rate)^[sweeps] initial) - bpGradient‖ ≤
      K * hilbertSettlingContraction mu L rate ^ sweeps * ‖initial - target‖ := by
  have h := hilbertFiniteSettlingGradientGap_le model hL hrate hcoefficient
    target initial htarget gradientReadout bpGradient hK hreadout sweeps
  simpa [hilbertEquilibriumGradientMismatch, hequilibriumExact] using h

/-- Geometric term in the Hilbert-space gradient-gap bound. -/
noncomputable def hilbertFiniteSettlingRemainder
    (mu L rate K : ℝ) (initial target : Latent) (sweeps : ℕ) : ℝ :=
  K * hilbertSettlingContraction mu L rate ^ sweeps * ‖initial - target‖

omit [InnerProductSpace ℝ Latent] in
theorem hilbertFiniteSettling_exists_tolerance
    (mu L rate K tolerance : ℝ) (initial target : Latent)
    (hK : 0 ≤ K) (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (htolerance : 0 < tolerance) :
    ∃ sweeps : ℕ,
      hilbertFiniteSettlingRemainder mu L rate K initial target sweeps <
        tolerance := by
  let q := hilbertSettlingContraction mu L rate
  let scale := K * ‖initial - target‖
  by_cases hscaleZero : scale = 0
  · refine ⟨0, ?_⟩
    simp [hilbertFiniteSettlingRemainder, scale, hscaleZero, htolerance]
  · have hscale : 0 < scale :=
      lt_of_le_of_ne (mul_nonneg hK (norm_nonneg _)) (Ne.symm hscaleZero)
    have hq : q < 1 := hilbertSettlingContraction_lt_one mu L rate hrate
      hstable hcoefficient
    obtain ⟨sweeps, hsweeps⟩ :=
      exists_pow_lt_of_lt_one (div_pos htolerance hscale) hq
    refine ⟨sweeps, ?_⟩
    have hmul : q ^ sweeps * scale < tolerance :=
      (lt_div_iff₀ hscale).mp hsweeps
    dsimp [hilbertFiniteSettlingRemainder, q, scale] at hmul ⊢
    nlinarith

/-- Least settle depth satisfying a requested Hilbert gradient tolerance. -/
noncomputable def minimumHilbertSettlingDepth
    (mu L rate K tolerance : ℝ) (initial target : Latent)
    (hK : 0 ≤ K) (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (htolerance : 0 < tolerance) : ℕ :=
  Nat.find (hilbertFiniteSettling_exists_tolerance mu L rate K tolerance
    initial target hK hrate hstable hcoefficient htolerance)

omit [InnerProductSpace ℝ Latent] in
theorem minimumHilbertSettlingDepth_sufficient
    (mu L rate K tolerance : ℝ) (initial target : Latent)
    (hK : 0 ≤ K) (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (htolerance : 0 < tolerance) :
    hilbertFiniteSettlingRemainder mu L rate K initial target
        (minimumHilbertSettlingDepth mu L rate K tolerance initial target
          hK hrate hstable hcoefficient htolerance) < tolerance := by
  exact Nat.find_spec (hilbertFiniteSettling_exists_tolerance mu L rate K
    tolerance initial target hK hrate hstable hcoefficient htolerance)

/-- Under equilibrium exactness, the least depth selected from the geometric
remainder is sufficient for the requested *actual* PC-to-BP gradient
tolerance.  This is the operational zero-mismatch reading of
`minimumHilbertSettlingDepth`. -/
theorem minimumHilbertSettlingDepth_zeroMismatch_gap_lt
    {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L)
    (hL : 0 ≤ L) (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (target initial : Latent) (htarget : model.gradient target = 0)
    (gradientReadout : Latent → Adapter) (bpGradient : Adapter)
    (hK : 0 ≤ K)
    (hreadout : HilbertGradientReadoutLipschitzAt gradientReadout target K)
    (hequilibriumExact : gradientReadout target = bpGradient)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    let depth := minimumHilbertSettlingDepth mu L rate K tolerance
      initial target hK hrate hstable hcoefficient htolerance
    ‖gradientReadout
        ((hilbertSettlingStep model rate)^[depth] initial) - bpGradient‖ <
      tolerance := by
  dsimp only
  let depth := minimumHilbertSettlingDepth mu L rate K tolerance
    initial target hK hrate hstable hcoefficient htolerance
  have hgap := hilbertFiniteSettlingGradientGap_zeroMismatch
    model hL (le_of_lt hrate) hcoefficient target initial htarget
      gradientReadout bpGradient hK hreadout hequilibriumExact depth
  have hremainder := minimumHilbertSettlingDepth_sufficient
    mu L rate K tolerance initial target hK hrate hstable hcoefficient
      htolerance
  change ‖gradientReadout
      ((hilbertSettlingStep model rate)^[depth] initial) - bpGradient‖ <
    tolerance
  exact lt_of_le_of_lt hgap (by
    simpa [depth, hilbertFiniteSettlingRemainder] using hremainder)

omit [InnerProductSpace ℝ Latent] in
theorem below_minimumHilbertSettlingDepth_insufficient
    (mu L rate K tolerance : ℝ) (initial target : Latent)
    (hK : 0 ≤ K) (hrate : 0 < rate)
    (hstable : rate * L ^ 2 < 2 * mu)
    (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
    (htolerance : 0 < tolerance) (sweeps : ℕ)
    (hshort : sweeps < minimumHilbertSettlingDepth mu L rate K tolerance
      initial target hK hrate hstable hcoefficient htolerance) :
    ¬ hilbertFiniteSettlingRemainder mu L rate K initial target sweeps <
      tolerance := by
  exact Nat.find_min (hilbertFiniteSettling_exists_tolerance mu L rate K
    tolerance initial target hK hrate hstable hcoefficient htolerance) hshort

end HilbertSettling

/-! ## Rate-derived scalar settling -/

/-- Contraction factor of scalar gradient descent on a quadratic latent energy. -/
noncomputable def settlingContraction (rate curvature : ℝ) : ℝ :=
  |1 - rate * curvature|

/-- One inference sweep about the quadratic equilibrium `target`. -/
noncomputable def quadraticSettlingStep
    (rate curvature target state : ℝ) : ℝ :=
  target + (1 - rate * curvature) * (state - target)

theorem settlingContraction_lt_one
    (rate curvature : ℝ)
    (hpositive : 0 < rate * curvature)
    (hbelow : rate * curvature < 2) :
    settlingContraction rate curvature < 1 := by
  rw [settlingContraction, abs_lt]
  constructor <;> linarith

theorem settlingContraction_nonneg (rate curvature : ℝ) :
    0 ≤ settlingContraction rate curvature := by
  exact abs_nonneg _

theorem quadraticSettlingStep_iterate_exact
    (rate curvature target initial : ℝ) (sweeps : ℕ) :
    (quadraticSettlingStep rate curvature target)^[sweeps] initial =
      target + (1 - rate * curvature) ^ sweeps * (initial - target) := by
  induction sweeps with
  | zero => simp
  | succ sweeps ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      unfold quadraticSettlingStep
      ring

theorem quadraticSettlingStep_residual_exact
    (rate curvature target initial : ℝ) (sweeps : ℕ) :
    |(quadraticSettlingStep rate curvature target)^[sweeps] initial - target| =
      settlingContraction rate curvature ^ sweeps * |initial - target| := by
  rw [quadraticSettlingStep_iterate_exact]
  calc
    |target + (1 - rate * curvature) ^ sweeps * (initial - target) - target| =
        |(1 - rate * curvature) ^ sweeps * (initial - target)| := by ring_nf
    _ = settlingContraction rate curvature ^ sweeps * |initial - target| := by
      rw [abs_mul, abs_pow]
      rfl

/-! ## Gradient-gap decomposition -/

/-- A scalar adapter-gradient readout is `K`-Lipschitz about the settled
equilibrium.  Only the equilibrium-to-current comparison needed by the finite
settling theorem is required. -/
def GradientReadoutLipschitzAt
    (gradientReadout : ℝ → ℝ) (target K : ℝ) : Prop :=
  ∀ state,
    |gradientReadout state - gradientReadout target| ≤ K * |state - target|

/-- Difference between the PC gradient at exact equilibrium and the reference
backpropagation gradient. -/
noncomputable def equilibriumGradientMismatch
    (gradientReadout : ℝ → ℝ) (target bpGradient : ℝ) : ℝ :=
  |gradientReadout target - bpGradient|

/-- Finite-settling PC-to-BP gradient gap.  The first term vanishes
geometrically; the second is the irreducible equilibrium mismatch. -/
theorem finiteSettlingGradientGap_le
    (rate curvature target initial K bpGradient : ℝ)
    (gradientReadout : ℝ → ℝ) (sweeps : ℕ)
    (hLipschitz : GradientReadoutLipschitzAt gradientReadout target K) :
    |gradientReadout
          ((quadraticSettlingStep rate curvature target)^[sweeps] initial) -
        bpGradient| ≤
      K * settlingContraction rate curvature ^ sweeps * |initial - target| +
        equilibriumGradientMismatch gradientReadout target bpGradient := by
  let settled :=
    (quadraticSettlingStep rate curvature target)^[sweeps] initial
  calc
    |gradientReadout settled - bpGradient| ≤
        |gradientReadout settled - gradientReadout target| +
          |gradientReadout target - bpGradient| := by
      simpa [sub_eq_add_neg, add_assoc] using
        (abs_add_le
          (gradientReadout settled - gradientReadout target)
          (gradientReadout target - bpGradient))
    _ ≤ K * |settled - target| +
          |gradientReadout target - bpGradient| := by
      gcongr
      exact hLipschitz settled
    _ = K * settlingContraction rate curvature ^ sweeps * |initial - target| +
          equilibriumGradientMismatch gradientReadout target bpGradient := by
      rw [quadraticSettlingStep_residual_exact]
      simp only [equilibriumGradientMismatch]
      ring

/-- Under exact equilibrium agreement, the mismatch term disappears. -/
theorem finiteSettlingGradientGap_zeroMismatch
    (rate curvature target initial K bpGradient : ℝ)
    (gradientReadout : ℝ → ℝ) (sweeps : ℕ)
    (hLipschitz : GradientReadoutLipschitzAt gradientReadout target K)
    (hequilibrium : gradientReadout target = bpGradient) :
    |gradientReadout
          ((quadraticSettlingStep rate curvature target)^[sweeps] initial) -
        bpGradient| ≤
      K * settlingContraction rate curvature ^ sweeps * |initial - target| := by
  have h := finiteSettlingGradientGap_le rate curvature target initial K
    bpGradient gradientReadout sweeps hLipschitz
  simpa [equilibriumGradientMismatch, hequilibrium] using h

/-! ## Finite tolerance and the least sufficient settling depth -/

/-- The geometric portion of the gradient-gap bound. -/
noncomputable def finiteSettlingRemainder
    (rate curvature initial target K : ℝ) (sweeps : ℕ) : ℝ :=
  K * settlingContraction rate curvature ^ sweeps * |initial - target|

theorem finiteSettling_exists_tolerance
    (rate curvature initial target K tolerance : ℝ)
    (hK : 0 ≤ K)
    (hpositive : 0 < rate * curvature)
    (hbelow : rate * curvature < 2)
    (htolerance : 0 < tolerance) :
    ∃ sweeps : ℕ,
      finiteSettlingRemainder rate curvature initial target K sweeps < tolerance := by
  by_cases hzero : K * |initial - target| = 0
  · refine ⟨0, ?_⟩
    simp [finiteSettlingRemainder, hzero, htolerance]
  · have hscale : 0 < K * |initial - target| :=
      lt_of_le_of_ne (mul_nonneg hK (abs_nonneg _)) (Ne.symm hzero)
    have hq := settlingContraction_lt_one rate curvature hpositive hbelow
    obtain ⟨sweeps, hsweeps⟩ :=
      exists_pow_lt_of_lt_one (div_pos htolerance hscale) hq
    refine ⟨sweeps, ?_⟩
    rw [finiteSettlingRemainder]
    have hmul : settlingContraction rate curvature ^ sweeps *
        (K * |initial - target|) < tolerance :=
      (lt_div_iff₀ hscale).mp hsweeps
    nlinarith

/-- Least number of sweeps whose geometric gradient error is below the
declared tolerance. -/
noncomputable def minimumSettlingDepth
    (rate curvature initial target K tolerance : ℝ)
    (hK : 0 ≤ K)
    (hpositive : 0 < rate * curvature)
    (hbelow : rate * curvature < 2)
    (htolerance : 0 < tolerance) : ℕ :=
  Nat.find (finiteSettling_exists_tolerance rate curvature initial target K
    tolerance hK hpositive hbelow htolerance)

theorem minimumSettlingDepth_sufficient
    (rate curvature initial target K tolerance : ℝ)
    (hK : 0 ≤ K)
    (hpositive : 0 < rate * curvature)
    (hbelow : rate * curvature < 2)
    (htolerance : 0 < tolerance) :
    finiteSettlingRemainder rate curvature initial target K
        (minimumSettlingDepth rate curvature initial target K tolerance
          hK hpositive hbelow htolerance) < tolerance := by
  exact Nat.find_spec (finiteSettling_exists_tolerance rate curvature initial target K
    tolerance hK hpositive hbelow htolerance)

theorem below_minimumSettlingDepth_insufficient
    (rate curvature initial target K tolerance : ℝ)
    (hK : 0 ≤ K)
    (hpositive : 0 < rate * curvature)
    (hbelow : rate * curvature < 2)
    (htolerance : 0 < tolerance)
    (sweeps : ℕ)
    (hshort : sweeps < minimumSettlingDepth rate curvature initial target K tolerance
      hK hpositive hbelow htolerance) :
    ¬ finiteSettlingRemainder rate curvature initial target K sweeps < tolerance := by
  exact Nat.find_min
    (finiteSettling_exists_tolerance rate curvature initial target K tolerance
      hK hpositive hbelow htolerance) hshort

/-! ## Positive and negative fixtures -/

theorem unitQuadratic_halfRate_contracts_positive_example :
    settlingContraction (1 / 2) 1 = 1 / 2 := by
  norm_num [settlingContraction]

/-- A rate beyond the stable interval makes the same quadratic latent solver
expansive, so no geometric finite-settling conclusion is available. -/
theorem unitQuadratic_rateThree_expands_negative_example (sweeps : ℕ) :
    |(quadraticSettlingStep 3 1 0)^[sweeps] 1 - 0| = (2 : ℝ) ^ sweeps := by
  rw [quadraticSettlingStep_residual_exact]
  norm_num [settlingContraction]

theorem unitQuadratic_rateThree_never_reaches_halfTolerance (sweeps : ℕ) :
    ¬ |(quadraticSettlingStep 3 1 0)^[sweeps] 1 - 0| < 1 / 2 := by
  rw [unitQuadratic_rateThree_expands_negative_example]
  have hone : (1 : ℝ) ≤ 2 ^ sweeps := one_le_pow₀ (by norm_num)
  norm_num at hone ⊢
  linarith

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
