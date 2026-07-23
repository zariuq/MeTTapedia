import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate

/-!
# Online tracking regret for adapter updates

This file first proves a Hilbert-space dynamic-regret theorem for general
convex smooth adapter losses and nonexpansive projected updates.  The theorem
separates moving-optimum path length from an additive per-round approximate-
gradient certificate, which is where finite PC settling enters.  It then
specializes to a scalar unit-curvature quadratic for exact fixtures.

The regret bound separates three quantities: initial error, movement of the
roundwise optima, and the additive per-round approximation cost.  Thus PC can
match exact BP only when its finite-settling costs vanish (or are otherwise
offset); more inference sweeps have no benefit after exactness is reached.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

open Finset
open scoped InnerProductSpace

/-! ## General convex-smooth projected online adaptation -/

section GeneralProjectedOnline

variable {Adapter : Type*} [NormedAddCommGroup Adapter]
  [InnerProductSpace ℝ Adapter]

/-- A differentiable convex adapter loss with a `beta`-Lipschitz gradient.
The first-order inequality is the standard differentiable characterization
of convexity; smoothness is stated separately rather than conflated with it. -/
structure ConvexSmoothAdapterLoss
    (Adapter : Type*) [NormedAddCommGroup Adapter]
    [InnerProductSpace ℝ Adapter] (beta : ℝ) where
  loss : Adapter → ℝ
  gradient : Adapter → Adapter
  beta_nonneg : 0 ≤ beta
  convexFirstOrder : ∀ parameter comparator,
    loss parameter - loss comparator ≤
      ⟪gradient parameter, parameter - comparator⟫_ℝ
  gradientLipschitz : ∀ x y,
    ‖gradient x - gradient y‖ ≤ beta * ‖x - y‖

/-- A projection used by constrained BP.  It is nonexpansive, fixes every
feasible point, and maps every proposal back into the feasible adapter set. -/
structure OnlineProjection
    (Adapter : Type*) [NormedAddCommGroup Adapter]
    (feasible : Adapter → Prop) where
  project : Adapter → Adapter
  nonexpansive : ∀ x y,
    ‖project x - project y‖ ≤ ‖x - y‖
  fixes : ∀ x, feasible x → project x = x
  mapsToFeasible : ∀ x, feasible (project x)

/-- One constrained online step using an exact or approximate gradient
direction. -/
noncomputable def projectedOnlineStep
    {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
    (rate : ℝ) (parameter direction : Adapter) : Adapter :=
  projection.project (parameter - rate • direction)

/-- A per-round approximate direction certificate.  Its first field controls
the step norm; its second converts gradient mismatch into an additive loss
penalty `epsilon`, without pretending the approximate direction is exact BP. -/
structure ApproximateDirectionCertificate
    (gradient direction displacement : Adapter)
    (bound epsilon : ℝ) : Prop where
  directionBound : ‖direction‖ ≤ bound
  firstOrderGap :
    ⟪gradient, displacement⟫_ℝ ≤
      ⟪direction, displacement⟫_ℝ + epsilon

/-- An exact BP direction has zero approximation cost.  Consequently a PC
direction that has reached the exact BP gradient enters the online theorem
with precisely the BP certificate, rather than merely with a small error. -/
theorem exactDirection_zeroApproximationCertificate
    (gradient displacement : Adapter) (bound : ℝ)
    (hbound : ‖gradient‖ ≤ bound) :
    ApproximateDirectionCertificate gradient gradient displacement bound 0 := by
  exact ⟨hbound, by simp⟩

/-- A norm error certificate implies the additive first-order certificate on
a domain of diameter `diameter`.  This is the bridge from a finite PC gradient
gap to online regret. -/
theorem approximateDirectionCertificate_of_norm_gap
    (gradient direction displacement : Adapter)
    (bound gradientError diameter : ℝ)
    (hbound : ‖direction‖ ≤ bound)
    (herror : ‖gradient - direction‖ ≤ gradientError)
    (hdiameter : ‖displacement‖ ≤ diameter)
    (herror0 : 0 ≤ gradientError) :
    ApproximateDirectionCertificate gradient direction displacement
      bound (gradientError * diameter) := by
  constructor
  · exact hbound
  · calc
      ⟪gradient, displacement⟫_ℝ =
          ⟪direction, displacement⟫_ℝ +
            ⟪gradient - direction, displacement⟫_ℝ := by
        rw [← inner_add_left]
        congr 1
        abel
      _ ≤ ⟪direction, displacement⟫_ℝ +
            ‖gradient - direction‖ * ‖displacement‖ :=
        add_le_add_right (real_inner_le_norm _ _) _
      _ ≤ ⟪direction, displacement⟫_ℝ +
            gradientError * diameter := by
        exact add_le_add_right
          (mul_le_mul herror hdiameter (norm_nonneg _) herror0) _

/-- One projected approximate-gradient step obeys the usual BP potential
decrease plus the explicit approximation penalty. -/
theorem projectedOnlineStep_oneRoundRegret
    {beta : ℝ} (model : ConvexSmoothAdapterLoss Adapter beta)
    {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
    (rate bound epsilon : ℝ) (parameter comparator direction : Adapter)
    (hrate : 0 < rate) (hbound0 : 0 ≤ bound)
    (hcomparator : feasible comparator)
    (happrox : ApproximateDirectionCertificate
      (model.gradient parameter) direction (parameter - comparator)
      bound epsilon) :
    model.loss parameter - model.loss comparator ≤
      (‖parameter - comparator‖ ^ 2 -
          ‖projectedOnlineStep projection rate parameter direction -
            comparator‖ ^ 2) / (2 * rate) +
        rate * bound ^ 2 / 2 + epsilon := by
  let raw := parameter - rate • direction
  let next := projectedOnlineStep projection rate parameter direction
  have hproject : ‖next - comparator‖ ≤ ‖raw - comparator‖ := by
    calc
      ‖next - comparator‖ =
          ‖projection.project raw - projection.project comparator‖ := by
        rw [projection.fixes comparator hcomparator]
        rfl
      _ ≤ ‖raw - comparator‖ := projection.nonexpansive _ _
  have hprojectSq : ‖next - comparator‖ ^ 2 ≤
      ‖raw - comparator‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hproject
  have hraw : raw - comparator =
      (parameter - comparator) - rate • direction := by
    dsimp [raw]
    abel
  have hexpansion : ‖raw - comparator‖ ^ 2 =
      ‖parameter - comparator‖ ^ 2 -
        2 * rate * ⟪direction, parameter - comparator⟫_ℝ +
        rate ^ 2 * ‖direction‖ ^ 2 := by
    rw [hraw, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hrate]
    rw [real_inner_comm (parameter - comparator) direction]
    ring
  have hdirectionSq : ‖direction‖ ^ 2 ≤ bound ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hbound0).2 happrox.directionBound
  have hscaledDirection : rate ^ 2 * ‖direction‖ ^ 2 ≤
      rate ^ 2 * bound ^ 2 :=
    mul_le_mul_of_nonneg_left hdirectionSq (sq_nonneg rate)
  have hpotential :
      2 * rate * ⟪direction, parameter - comparator⟫_ℝ ≤
        ‖parameter - comparator‖ ^ 2 - ‖next - comparator‖ ^ 2 +
          rate ^ 2 * bound ^ 2 := by
    rw [hexpansion] at hprojectSq
    linarith
  have hdirection :
      ⟪direction, parameter - comparator⟫_ℝ ≤
        (‖parameter - comparator‖ ^ 2 - ‖next - comparator‖ ^ 2) /
            (2 * rate) + rate * bound ^ 2 / 2 := by
    rw [show
      (‖parameter - comparator‖ ^ 2 - ‖next - comparator‖ ^ 2) /
            (2 * rate) + rate * bound ^ 2 / 2 =
        (‖parameter - comparator‖ ^ 2 - ‖next - comparator‖ ^ 2 +
            rate ^ 2 * bound ^ 2) / (2 * rate) by
      field_simp]
    apply (le_div_iff₀ (by positivity : 0 < 2 * rate)).2
    nlinarith [hpotential]
  calc
    model.loss parameter - model.loss comparator ≤
        ⟪model.gradient parameter, parameter - comparator⟫_ℝ :=
      model.convexFirstOrder parameter comparator
    _ ≤ ⟪direction, parameter - comparator⟫_ℝ + epsilon :=
      happrox.firstOrderGap
    _ ≤ (‖parameter - comparator‖ ^ 2 - ‖next - comparator‖ ^ 2) /
          (2 * rate) + rate * bound ^ 2 / 2 + epsilon := by
      linarith
    _ = (‖parameter - comparator‖ ^ 2 -
          ‖projectedOnlineStep projection rate parameter direction -
            comparator‖ ^ 2) / (2 * rate) +
        rate * bound ^ 2 / 2 + epsilon := rfl

omit [InnerProductSpace ℝ Adapter] in
/- Changing the roundwise comparator costs at most diameter times path
length in the squared-distance potential. -/
theorem movingComparator_sq_gap_le
    (state current next : Adapter) (diameter : ℝ)
    (hcurrent : ‖state - current‖ ≤ diameter)
    (hnext : ‖state - next‖ ≤ diameter) :
    ‖state - next‖ ^ 2 - ‖state - current‖ ^ 2 ≤
      2 * diameter * ‖next - current‖ := by
  have hdifference : ‖state - next‖ - ‖state - current‖ ≤
      ‖next - current‖ := by
    calc
      ‖state - next‖ - ‖state - current‖ ≤
          ‖(state - next) - (state - current)‖ :=
        norm_sub_norm_le _ _
      _ = ‖next - current‖ := by
        rw [show (state - next) - (state - current) =
          -(next - current) by abel, norm_neg]
  have hsum : ‖state - next‖ + ‖state - current‖ ≤
      2 * diameter := by linarith
  have hsumNonnegative :
      0 ≤ ‖state - next‖ + ‖state - current‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right hdifference
    hsumNonnegative
  have hsecond := mul_le_mul_of_nonneg_left hsum (norm_nonneg (next - current))
  calc
    ‖state - next‖ ^ 2 - ‖state - current‖ ^ 2 =
        (‖state - next‖ - ‖state - current‖) *
          (‖state - next‖ + ‖state - current‖) := by ring
    _ ≤ ‖next - current‖ *
          (‖state - next‖ + ‖state - current‖) := hfirst
    _ ≤ ‖next - current‖ * (2 * diameter) := hsecond
    _ = 2 * diameter * ‖next - current‖ := by ring

/-- Dynamic regret for a general sequence of adapter losses. -/
noncomputable def projectedDynamicRegret
    (loss : ℕ → Adapter → ℝ)
    (parameter comparator : ℕ → Adapter) (horizon : ℕ) : ℝ :=
  ∑ t ∈ range horizon,
    (loss t (parameter t) - loss t (comparator t))

/-- Path length of the roundwise comparator/optimum sequence. -/
noncomputable def adapterOptimumPathLength
    (comparator : ℕ → Adapter) (horizon : ℕ) : ℝ :=
  ∑ t ∈ range horizon, ‖comparator (t + 1) - comparator t‖

/-- Algebraic telescope used by the projected online crown. -/
theorem sum_online_tracking_of_oneStep
    (regret potential path epsilon : ℕ → ℝ)
    (rate diameter bound : ℝ) (horizon : ℕ)
    (hrate : 0 < rate)
    (hpotential : 0 ≤ potential horizon)
    (honeStep : ∀ t < horizon,
      regret t ≤
        (potential t - potential (t + 1)) / (2 * rate) +
          diameter / rate * path t + rate * bound ^ 2 / 2 + epsilon t) :
    (∑ t ∈ range horizon, regret t) ≤
      potential 0 / (2 * rate) +
        diameter / rate * (∑ t ∈ range horizon, path t) +
        horizon * (rate * bound ^ 2 / 2) +
        ∑ t ∈ range horizon, epsilon t := by
  have hsum : (∑ t ∈ range horizon, regret t) ≤
      ∑ t ∈ range horizon,
        ((potential t - potential (t + 1)) / (2 * rate) +
          diameter / rate * path t + rate * bound ^ 2 / 2 + epsilon t) := by
    apply sum_le_sum
    intro t ht
    exact honeStep t (mem_range.mp ht)
  have htelescope :
      (∑ t ∈ range horizon,
        (potential t - potential (t + 1)) / (2 * rate)) =
      (potential 0 - potential horizon) / (2 * rate) := by
    rw [← sum_div, sum_range_sub']
  have hpath :
      (∑ t ∈ range horizon, diameter / rate * path t) =
        diameter / rate * (∑ t ∈ range horizon, path t) := by
    rw [mul_sum]
  have hconstant :
      (∑ _t ∈ range horizon, rate * bound ^ 2 / 2) =
        horizon * (rate * bound ^ 2 / 2) := by simp
  simp_rw [sum_add_distrib] at hsum
  rw [htelescope, hpath, hconstant] at hsum
  have hdrop :
      (potential 0 - potential horizon) / (2 * rate) ≤
        potential 0 / (2 * rate) := by
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- Dynamic-regret crown for constrained BP with an approximate direction at
each round.  For finite PC, instantiate `epsilon t` from the finite-settling
gradient gap; the total extra price is exactly additive `Σ epsilon t`. -/
theorem projectedOnlineDynamicRegret_le_path_add_approximation
    (beta : ℕ → ℝ)
    (model : ∀ t, ConvexSmoothAdapterLoss Adapter (beta t))
    {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
    (parameter comparator direction : ℕ → Adapter)
    (epsilon : ℕ → ℝ) (rate diameter bound : ℝ) (horizon : ℕ)
    (hrate : 0 < rate) (hbound0 : 0 ≤ bound)
    (hcomparator : ∀ t ≤ horizon, feasible (comparator t))
    (hupdate : ∀ t < horizon,
      parameter (t + 1) =
        projectedOnlineStep projection rate (parameter t) (direction t))
    (happrox : ∀ t < horizon,
      ApproximateDirectionCertificate
        ((model t).gradient (parameter t)) (direction t)
        (parameter t - comparator t) bound (epsilon t))
    (hdiameter : ∀ t < horizon,
      ‖parameter (t + 1) - comparator t‖ ≤ diameter ∧
      ‖parameter (t + 1) - comparator (t + 1)‖ ≤ diameter) :
    projectedDynamicRegret (fun t => (model t).loss)
        parameter comparator horizon ≤
      ‖parameter 0 - comparator 0‖ ^ 2 / (2 * rate) +
        diameter / rate * adapterOptimumPathLength comparator horizon +
        horizon * (rate * bound ^ 2 / 2) +
        ∑ t ∈ range horizon, epsilon t := by
  let potential : ℕ → ℝ := fun t =>
    ‖parameter t - comparator t‖ ^ 2
  let path : ℕ → ℝ := fun t =>
    ‖comparator (t + 1) - comparator t‖
  let regret : ℕ → ℝ := fun t =>
    (model t).loss (parameter t) - (model t).loss (comparator t)
  have honeRound : ∀ t < horizon,
      regret t ≤
        (potential t - ‖parameter (t + 1) - comparator t‖ ^ 2) /
            (2 * rate) + rate * bound ^ 2 / 2 + epsilon t := by
    intro t ht
    have h := projectedOnlineStep_oneRoundRegret
      (model t) projection rate bound (epsilon t)
      (parameter t) (comparator t) (direction t)
      hrate hbound0 (hcomparator t (Nat.le_of_lt ht)) (happrox t ht)
    rw [← hupdate t ht] at h
    exact h
  have honeStep : ∀ t < horizon,
      regret t ≤
        (potential t - potential (t + 1)) / (2 * rate) +
          diameter / rate * path t + rate * bound ^ 2 / 2 + epsilon t := by
    intro t ht
    have hdrift := movingComparator_sq_gap_le
      (parameter (t + 1)) (comparator t) (comparator (t + 1)) diameter
      (hdiameter t ht).1 (hdiameter t ht).2
    have hdriftScaled :
        (potential (t + 1) -
            ‖parameter (t + 1) - comparator t‖ ^ 2) / (2 * rate) ≤
          diameter / rate * path t := by
      dsimp [potential, path]
      apply (div_le_iff₀ (by positivity : 0 < 2 * rate)).2
      rw [show diameter / rate *
          ‖comparator (t + 1) - comparator t‖ * (2 * rate) =
        2 * diameter * ‖comparator (t + 1) - comparator t‖ by
          field_simp]
      exact hdrift
    have hround := honeRound t ht
    dsimp [potential] at hround ⊢
    dsimp [path]
    rw [show
      (‖parameter t - comparator t‖ ^ 2 -
          ‖parameter (t + 1) - comparator t‖ ^ 2) / (2 * rate) =
        (‖parameter t - comparator t‖ ^ 2 -
          ‖parameter (t + 1) - comparator (t + 1)‖ ^ 2) / (2 * rate) +
        (‖parameter (t + 1) - comparator (t + 1)‖ ^ 2 -
          ‖parameter (t + 1) - comparator t‖ ^ 2) / (2 * rate) by
            field_simp
            ring] at hround
    linarith
  have hsum := sum_online_tracking_of_oneStep regret potential path epsilon
    rate diameter bound horizon hrate (sq_nonneg _) honeStep
  simpa [projectedDynamicRegret, adapterOptimumPathLength,
    regret, potential, path] using hsum

/-- Norm-bounded finite-settling gradient errors compose directly with the
projected online theorem.  Instantiating `gradientError t` with the bound from
`hilbertFiniteSettlingGradientGap_zeroMismatch` gives the finite-PC tracking
bound, with explicit additive penalty
`∑ t, gradientError t * diameter`. -/
theorem projectedOnlineDynamicRegret_of_gradientGap
    (beta : ℕ → ℝ)
    (model : ∀ t, ConvexSmoothAdapterLoss Adapter (beta t))
    {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
    (parameter comparator direction : ℕ → Adapter)
    (gradientError : ℕ → ℝ) (rate diameter bound : ℝ) (horizon : ℕ)
    (hrate : 0 < rate) (hbound0 : 0 ≤ bound)
    (hcomparator : ∀ t ≤ horizon, feasible (comparator t))
    (hupdate : ∀ t < horizon,
      parameter (t + 1) =
        projectedOnlineStep projection rate (parameter t) (direction t))
    (hdirectionBound : ∀ t < horizon, ‖direction t‖ ≤ bound)
    (hgradientError0 : ∀ t < horizon, 0 ≤ gradientError t)
    (hgradientGap : ∀ t < horizon,
      ‖(model t).gradient (parameter t) - direction t‖ ≤ gradientError t)
    (hcurrentDiameter : ∀ t < horizon,
      ‖parameter t - comparator t‖ ≤ diameter)
    (hnextDiameter : ∀ t < horizon,
      ‖parameter (t + 1) - comparator t‖ ≤ diameter ∧
      ‖parameter (t + 1) - comparator (t + 1)‖ ≤ diameter) :
    projectedDynamicRegret (fun t => (model t).loss)
        parameter comparator horizon ≤
      ‖parameter 0 - comparator 0‖ ^ 2 / (2 * rate) +
        diameter / rate * adapterOptimumPathLength comparator horizon +
        horizon * (rate * bound ^ 2 / 2) +
        ∑ t ∈ range horizon, gradientError t * diameter := by
  apply projectedOnlineDynamicRegret_le_path_add_approximation
    beta model projection parameter comparator direction
      (fun t => gradientError t * diameter) rate diameter bound horizon
      hrate hbound0 hcomparator hupdate
  · intro t ht
    exact approximateDirectionCertificate_of_norm_gap
      ((model t).gradient (parameter t)) (direction t)
      (parameter t - comparator t) bound (gradientError t) diameter
      (hdirectionBound t ht) (hgradientGap t ht)
      (hcurrentDiameter t ht) (hgradientError0 t ht)
  · exact hnextDiameter

end GeneralProjectedOnline

/-! ## Scalar quadratic specialization -/

/-- Unit-curvature convex and smooth loss at a moving scalar optimum. -/
noncomputable def onlineQuadraticLoss (center parameter : ℝ) : ℝ :=
  (parameter - center) ^ 2 / 2

/-- Dynamic regret of a lineage that starts at `initial` and, after observing
round `t`, lands at `center t + error t`.  The first term is round zero; each
summand is the next-round loss of the previous update. -/
noncomputable def onlineQuadraticRegret
    (initial : ℝ) (center error : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  onlineQuadraticLoss (center 0) initial +
    ∑ t ∈ range horizon,
      onlineQuadraticLoss (center (t + 1)) (center t + error t)

/-- Squared path variation of the moving optima. -/
noncomputable def optimumPathEnergy
    (center : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  ∑ t ∈ range horizon, (center (t + 1) - center t) ^ 2

/-- Usual scalar path length of the moving optima. -/
noncomputable def optimumPathLength
    (center : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  ∑ t ∈ range horizon, |center (t + 1) - center t|

/-- Additive cost of projected or finite-settling update residuals. -/
noncomputable def approximationCost
    (error : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  ∑ t ∈ range horizon, error t ^ 2

theorem onlineQuadraticLoss_nonneg (center parameter : ℝ) :
    0 ≤ onlineQuadraticLoss center parameter := by
  unfold onlineQuadraticLoss
  positivity

/-- Exact unit-smooth expansion of the per-round convex quadratic loss. -/
theorem onlineQuadraticLoss_update_exact
    (center parameter update : ℝ) :
    onlineQuadraticLoss center (parameter + update) =
      onlineQuadraticLoss center parameter +
        (parameter - center) * update + update ^ 2 / 2 := by
  unfold onlineQuadraticLoss
  ring

/-- One-round tracking loss is bounded by path energy plus squared update
error. -/
theorem onlineQuadraticLoss_next_le_path_add_error
    (current next error : ℝ) :
    onlineQuadraticLoss next (current + error) ≤
      (next - current) ^ 2 + error ^ 2 := by
  unfold onlineQuadraticLoss
  nlinarith [sq_nonneg ((next - current) + error)]

/-- Dynamic-regret crown for arbitrary projected/approximate update errors. -/
theorem onlineQuadraticRegret_le_pathEnergy_add_approximationCost
    (initial : ℝ) (center error : ℕ → ℝ) (horizon : ℕ) :
    onlineQuadraticRegret initial center error horizon ≤
      onlineQuadraticLoss (center 0) initial +
        optimumPathEnergy center horizon + approximationCost error horizon := by
  unfold onlineQuadraticRegret optimumPathEnergy approximationCost
  have hsum :
      (∑ t ∈ range horizon,
        onlineQuadraticLoss (center (t + 1)) (center t + error t)) ≤
      ∑ t ∈ range horizon,
        ((center (t + 1) - center t) ^ 2 + error t ^ 2) := by
    apply sum_le_sum
    intro t _ht
    exact onlineQuadraticLoss_next_le_path_add_error
      (center t) (center (t + 1)) (error t)
  rw [sum_add_distrib] at hsum
  linarith

/-- Squared path variation is controlled by the square of the usual path
length `P_T`. -/
theorem optimumPathEnergy_le_pathLength_sq
    (center : ℕ → ℝ) (horizon : ℕ) :
    optimumPathEnergy center horizon ≤ optimumPathLength center horizon ^ 2 := by
  unfold optimumPathEnergy optimumPathLength
  calc
    (∑ t ∈ range horizon, (center (t + 1) - center t) ^ 2) =
        ∑ t ∈ range horizon, |center (t + 1) - center t| ^ 2 := by
      apply sum_congr rfl
      intro t _ht
      rw [sq_abs]
    _ ≤ (∑ t ∈ range horizon, |center (t + 1) - center t|) ^ 2 := by
      exact sum_sq_le_sq_sum_of_nonneg (fun _ _ => abs_nonneg _)

/-- Dynamic regret stated using the conventional moving-optimum path length. -/
theorem onlineQuadraticRegret_le_pathLength_sq_add_approximationCost
    (initial : ℝ) (center error : ℕ → ℝ) (horizon : ℕ) :
    onlineQuadraticRegret initial center error horizon ≤
      onlineQuadraticLoss (center 0) initial +
        optimumPathLength center horizon ^ 2 + approximationCost error horizon := by
  have hregret := onlineQuadraticRegret_le_pathEnergy_add_approximationCost
    initial center error horizon
  have hpath := optimumPathEnergy_le_pathLength_sq center horizon
  linarith

/-- If each squared update residual is certified by `epsilon t`, the total
PC/projection penalty is the additive sum `Σ epsilon t`. -/
theorem onlineQuadraticRegret_le_pathEnergy_add_errorCertificates
    (initial : ℝ) (center error epsilon : ℕ → ℝ) (horizon : ℕ)
    (herror : ∀ t < horizon, error t ^ 2 ≤ epsilon t) :
    onlineQuadraticRegret initial center error horizon ≤
      onlineQuadraticLoss (center 0) initial +
        optimumPathEnergy center horizon +
          ∑ t ∈ range horizon, epsilon t := by
  have hbase := onlineQuadraticRegret_le_pathEnergy_add_approximationCost
    initial center error horizon
  have hcost : approximationCost error horizon ≤
      ∑ t ∈ range horizon, epsilon t := by
    unfold approximationCost
    apply sum_le_sum
    intro t ht
    exact herror t (mem_range.mp ht)
  linarith

/-! ## Exact BP, approximate PC, and wasted settling -/

/-- Exact one-step BP in the unit quadratic model has zero update residual. -/
noncomputable def exactBPOnlineRegret
    (initial : ℝ) (center : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  onlineQuadraticRegret initial center (fun _ => 0) horizon

theorem exactBPOnlineRegret_le_pathEnergy
    (initial : ℝ) (center : ℕ → ℝ) (horizon : ℕ) :
    exactBPOnlineRegret initial center horizon ≤
      onlineQuadraticLoss (center 0) initial + optimumPathEnergy center horizon := by
  have h := onlineQuadraticRegret_le_pathEnergy_add_approximationCost
    initial center (fun _ => 0) horizon
  simpa [exactBPOnlineRegret, approximationCost] using h

theorem zeroApproximation_matches_exactBP
    (initial : ℝ) (center : ℕ → ℝ) (horizon : ℕ) :
    onlineQuadraticRegret initial center (fun _ => 0) horizon =
      exactBPOnlineRegret initial center horizon := rfl

/-- Abstract serial update work: one outer update plus `settlingSweeps` latent
sweeps per online round. -/
def onlineUpdateWork (horizon settlingSweeps : ℕ) : ℕ :=
  horizon * (settlingSweeps + 1)

theorem extraSettling_strictly_more_work
    (horizon settlingSweeps : ℕ)
    (hhorizon : 0 < horizon) (hsweeps : 0 < settlingSweeps) :
    onlineUpdateWork horizon 0 < onlineUpdateWork horizon settlingSweeps := by
  unfold onlineUpdateWork
  exact (Nat.mul_lt_mul_left hhorizon).2 (by omega)

/-- Once the PC update residual is zero, additional settling cannot improve
this regret, although it strictly increases serial work. -/
theorem zeroError_extraSettling_is_wasted
    (initial : ℝ) (center : ℕ → ℝ) (horizon settlingSweeps : ℕ)
    (hhorizon : 0 < horizon) (hsweeps : 0 < settlingSweeps) :
    onlineQuadraticRegret initial center (fun _ => 0) horizon =
        exactBPOnlineRegret initial center horizon ∧
      onlineUpdateWork horizon 0 < onlineUpdateWork horizon settlingSweeps :=
  ⟨rfl, extraSettling_strictly_more_work horizon settlingSweeps hhorizon hsweeps⟩

/-! ## Metric choice in the scalar quadratic model -/

/-- One preconditioned update toward the current scalar optimum. -/
noncomputable def preconditionedOnlineUpdate
    (preconditioner center parameter : ℝ) : ℝ :=
  parameter - preconditioner * (parameter - center)

theorem unitPreconditioner_reaches_currentOptimum
    (center parameter : ℝ) :
    preconditionedOnlineUpdate 1 center parameter = center := by
  unfold preconditionedOnlineUpdate
  ring

theorem unitPreconditioner_strictlyImproves_over_wrongMetric
    (preconditioner center parameter : ℝ)
    (hparameter : parameter ≠ center)
    (hmetric : preconditioner ≠ 1) :
    onlineQuadraticLoss center (preconditionedOnlineUpdate 1 center parameter) <
      onlineQuadraticLoss center
        (preconditionedOnlineUpdate preconditioner center parameter) := by
  rw [unitPreconditioner_reaches_currentOptimum]
  unfold onlineQuadraticLoss preconditionedOnlineUpdate
  have hproduct : (1 - preconditioner) * (parameter - center) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hmetric)) (sub_ne_zero.mpr hparameter)
  have hsquare : 0 < ((1 - preconditioner) * (parameter - center)) ^ 2 :=
    sq_pos_of_ne_zero hproduct
  nlinarith

/-! ## Stationary and abrupt-drift fixtures -/

theorem stationaryOptimum_zeroRegret_positive_example (horizon : ℕ) :
    exactBPOnlineRegret 0 (fun _ => 0) horizon = 0 := by
  simp [exactBPOnlineRegret, onlineQuadraticRegret, onlineQuadraticLoss]

noncomputable def abruptUnitDriftCenter (t : ℕ) : ℝ :=
  if t = 0 then 0 else 1

theorem abruptDrift_incurs_positive_regret_negative_example :
    exactBPOnlineRegret 0 abruptUnitDriftCenter 1 = 1 / 2 := by
  norm_num [exactBPOnlineRegret, onlineQuadraticRegret, onlineQuadraticLoss,
    abruptUnitDriftCenter]

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
