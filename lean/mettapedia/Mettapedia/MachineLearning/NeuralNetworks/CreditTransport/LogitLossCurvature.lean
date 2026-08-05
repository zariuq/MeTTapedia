import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CompositeTaskCurvature

/-!
# Curvature certificates for logit losses

This file derives directional quadratic upper models from exact scalar
second-derivative bounds and applies the result to binary cross-entropy with
logits.  The construction is phrased along a line so that the same theorem can
serve finite-dimensional categorical losses without choosing coordinates for
the surrounding neural parameter space.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace LogitLossCurvature

open Filter Set Topology
open scoped BigOperators InnerProductSpace
open DirectionalTaskDescent

noncomputable section

/-! ## A reusable one-dimensional descent lemma -/

/-- A pointwise upper bound on the second derivative along the nonnegative
half-line yields the usual quadratic upper model for every nonnegative step.
The proof uses two derivative fences, first for the slope and then for the
function itself. -/
theorem line_upper_of_second_derivative
    (line lineGradient lineCurvature : ℝ → ℝ) (curvature step : ℝ)
    (hline : ∀ t, HasDerivAt line (lineGradient t) t)
    (hgradient : ∀ t, HasDerivAt lineGradient (lineCurvature t) t)
    (hcurvature : ∀ t, 0 ≤ t → lineCurvature t ≤ curvature)
    (hstep : 0 ≤ step) :
    line step ≤ line 0 + step * lineGradient 0 + step ^ 2 * curvature / 2 := by
  have hslope : ∀ {t}, t ∈ Icc 0 step →
      lineGradient t ≤ lineGradient 0 + curvature * t := by
    intro t ht
    exact image_le_of_deriv_right_le_deriv_boundary
      (f := lineGradient) (f' := lineCurvature)
      (B := fun s => lineGradient 0 + curvature * s)
      (B' := fun _ => curvature)
      (hf := fun s _ => (hgradient s).continuousAt.continuousWithinAt)
      (hf' := fun s _ => (hgradient s).hasDerivWithinAt)
      (ha := by simp)
      (hB := by fun_prop)
      (hB' := fun s _ => by
        have h := (hasDerivAt_const s (lineGradient 0)).add
          ((hasDerivAt_id s).const_mul curvature)
        have heq :
            (fun u : ℝ => lineGradient 0 + curvature * u) =ᶠ[𝓝 s]
              ((fun _ : ℝ => lineGradient 0) +
                fun u : ℝ => curvature * id u) :=
          Eventually.of_forall fun _ => rfl
        exact ((h.congr_of_eventuallyEq heq).congr_deriv (by ring)).hasDerivWithinAt)
      (bound := fun s hs => hcurvature s hs.1) ht
  have hvalue : ∀ {t}, t ∈ Icc 0 step →
      line t ≤ line 0 + t * lineGradient 0 + t ^ 2 * curvature / 2 := by
    intro t ht
    exact image_le_of_deriv_right_le_deriv_boundary
      (f := line) (f' := lineGradient)
      (B := fun s => line 0 + s * lineGradient 0 + s ^ 2 * curvature / 2)
      (B' := fun s => lineGradient 0 + curvature * s)
      (hf := fun s _ => (hline s).continuousAt.continuousWithinAt)
      (hf' := fun s _ => (hline s).hasDerivWithinAt)
      (ha := by simp)
      (hB := by fun_prop)
      (hB' := fun s _ => by
        have h := ((hasDerivAt_const s (line 0)).add
          ((hasDerivAt_id s).mul_const (lineGradient 0))).add
          (((hasDerivAt_pow 2 s).mul_const curvature).div_const 2)
        have heq :
            (fun u : ℝ => line 0 + u * lineGradient 0 +
              u ^ 2 * curvature / 2) =ᶠ[𝓝 s]
              (((fun _ : ℝ => line 0) +
                fun u : ℝ => id u * lineGradient 0) +
                fun u : ℝ => id u ^ 2 * curvature / 2) :=
          Eventually.of_forall fun _ => rfl
        exact ((h.congr_of_eventuallyEq heq).congr_deriv (by ring)).hasDerivWithinAt)
      (bound := fun s hs => hslope ⟨hs.1, hs.2.le⟩) ht
  exact hvalue ⟨hstep, le_rfl⟩

/-! ## Binary cross-entropy with logits -/

/-- The exact real-valued binary cross-entropy-with-logits objective.  The
target is left real-valued so the theorem also covers soft binary targets. -/
def binaryCrossEntropyWithLogits (target logit : ℝ) : ℝ :=
  Real.log (1 + Real.exp logit) - target * logit

/-- Its derivative with respect to the logit. -/
def binaryCrossEntropyGradient (target logit : ℝ) : ℝ :=
  Real.sigmoid logit - target

theorem hasDerivAt_binaryCrossEntropyWithLogits (target logit : ℝ) :
    HasDerivAt (binaryCrossEntropyWithLogits target)
      (binaryCrossEntropyGradient target logit) logit := by
  have hpos : 1 + Real.exp logit ≠ 0 := by positivity
  have hsoftplus : HasDerivAt (fun z : ℝ => Real.log (1 + Real.exp z))
      (Real.sigmoid logit) logit := by
    have h := ((Real.hasDerivAt_exp logit).const_add 1).log hpos
    convert h using 1
    rw [Real.sigmoid_def]
    field_simp [Real.exp_ne_zero]
    rw [add_mul, one_mul, ← Real.exp_add]
    simp [add_comm]
  change HasDerivAt
    (fun z : ℝ => Real.log (1 + Real.exp z) - target * z)
    (Real.sigmoid logit - target) logit
  have h := hsoftplus.sub ((hasDerivAt_id logit).const_mul target)
  have heq : (fun z : ℝ => Real.log (1 + Real.exp z) - target * z) =ᶠ[𝓝 logit]
      ((fun z : ℝ => Real.log (1 + Real.exp z)) - fun z : ℝ => target * id z) :=
    Filter.Eventually.of_forall fun _ => rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

theorem hasDerivAt_binaryCrossEntropyGradient (target logit : ℝ) :
    HasDerivAt (binaryCrossEntropyGradient target)
      (Real.sigmoid logit * (1 - Real.sigmoid logit)) logit := by
  change HasDerivAt (fun z : ℝ => Real.sigmoid z - target)
    (Real.sigmoid logit * (1 - Real.sigmoid logit)) logit
  simpa only using
    (Real.hasDerivAt_sigmoid logit).sub_const target

theorem sigmoid_curvature_le_quarter (logit : ℝ) :
    Real.sigmoid logit * (1 - Real.sigmoid logit) ≤ (1 / 4 : ℝ) := by
  have hnonneg : 0 ≤ Real.sigmoid logit := Real.sigmoid_nonneg logit
  have hone : Real.sigmoid logit ≤ 1 := Real.sigmoid_le_one logit
  nlinarith [sq_nonneg (Real.sigmoid logit - (1 / 2 : ℝ))]

/-- Binary cross-entropy with logits has directional curvature at most
`direction² / 4` at every logit and for every real target. -/
theorem binaryCrossEntropyWithLogits_directional_upper
    (target logit direction : ℝ) :
    HasDirectionalTaskUpperModelAt
      (binaryCrossEntropyWithLogits target) logit
      (binaryCrossEntropyGradient target logit) direction
      (direction ^ 2 / 4) := by
  intro step hstep
  let line : ℝ → ℝ := fun t =>
    binaryCrossEntropyWithLogits target (logit - t * direction)
  let lineGradient : ℝ → ℝ := fun t =>
    -binaryCrossEntropyGradient target (logit - t * direction) * direction
  let lineCurvature : ℝ → ℝ := fun t =>
    (Real.sigmoid (logit - t * direction) *
      (1 - Real.sigmoid (logit - t * direction))) * direction ^ 2
  have hline : ∀ t, HasDerivAt line (lineGradient t) t := by
    intro t
    have hinner : HasDerivAt (fun s : ℝ => logit - s * direction)
        (-direction) t := by
      have h := (hasDerivAt_const t logit).sub
        ((hasDerivAt_id t).mul_const direction)
      have heq : (fun s : ℝ => logit - s * direction) =ᶠ[𝓝 t]
          ((fun _ : ℝ => logit) - fun s : ℝ => id s * direction) :=
        Filter.Eventually.of_forall fun _ => rfl
      exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
    change HasDerivAt
      (fun s : ℝ => binaryCrossEntropyWithLogits target (logit - s * direction))
      (-binaryCrossEntropyGradient target (logit - t * direction) * direction) t
    have h := (hasDerivAt_binaryCrossEntropyWithLogits target
      (logit - t * direction)).comp t hinner
    have heq :
        (fun s : ℝ => binaryCrossEntropyWithLogits target (logit - s * direction)) =ᶠ[𝓝 t]
          (binaryCrossEntropyWithLogits target ∘ fun s : ℝ => logit - s * direction) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have hgradient : ∀ t, HasDerivAt lineGradient (lineCurvature t) t := by
    intro t
    have hinner : HasDerivAt (fun s : ℝ => logit - s * direction)
        (-direction) t := by
      have h := (hasDerivAt_const t logit).sub
        ((hasDerivAt_id t).mul_const direction)
      have heq : (fun s : ℝ => logit - s * direction) =ᶠ[𝓝 t]
          ((fun _ : ℝ => logit) - fun s : ℝ => id s * direction) :=
        Filter.Eventually.of_forall fun _ => rfl
      exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
    have hcomp := (hasDerivAt_binaryCrossEntropyGradient target
      (logit - t * direction)).comp t hinner
    change HasDerivAt
      (fun s : ℝ => -binaryCrossEntropyGradient target
        (logit - s * direction) * direction)
      ((Real.sigmoid (logit - t * direction) *
        (1 - Real.sigmoid (logit - t * direction))) * direction ^ 2) t
    have h := hcomp.neg.mul_const direction
    have heq :
        (fun s : ℝ => -binaryCrossEntropyGradient target
          (logit - s * direction) * direction) =ᶠ[𝓝 t]
          (fun s => (-binaryCrossEntropyGradient target ∘
            fun u : ℝ => logit - u * direction) s * direction) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have hcurvature : ∀ t, 0 ≤ t → lineCurvature t ≤ direction ^ 2 / 4 := by
    intro t _
    dsimp [lineCurvature]
    have hsquare : 0 ≤ direction ^ 2 := sq_nonneg direction
    nlinarith [mul_le_mul_of_nonneg_right
      (sigmoid_curvature_le_quarter (logit - t * direction)) hsquare]
  have hupper := line_upper_of_second_derivative
    line lineGradient lineCurvature (direction ^ 2 / 4) step
    hline hgradient hcurvature hstep
  convert hupper using 1
  all_goals simp [line, lineGradient]
  all_goals ring

/-! ## Categorical cross-entropy with logits -/

variable {Class : Type*} [Fintype Class] [Nonempty Class]

/-- Finite-dimensional logit vectors use the ordinary Euclidean inner
product. -/
abbrev LogitVector (Class : Type*) [Fintype Class] := EuclideanSpace ℝ Class

/-- The normalizing exponential sum of a categorical logit vector. -/
def categoricalExpSum (logits : LogitVector Class) : ℝ :=
  ∑ i, Real.exp (logits i)

theorem categoricalExpSum_pos (logits : LogitVector Class) :
    0 < categoricalExpSum logits := by
  classical
  exact Finset.sum_pos (fun i _ => Real.exp_pos (logits i))
    Finset.univ_nonempty

/-- Exact real-valued categorical cross-entropy with a single target class. -/
def categoricalCrossEntropy (target : Class) (logits : LogitVector Class) : ℝ :=
  Real.log (categoricalExpSum logits) - logits target

/-- The softmax-minus-one-hot gradient of categorical cross-entropy. -/
noncomputable def categoricalCrossEntropyGradient
    [DecidableEq Class]
    (target : Class) (logits : LogitVector Class) : LogitVector Class :=
  WithLp.toLp 2 fun i =>
    Real.exp (logits i) / categoricalExpSum logits -
      if i = target then 1 else 0

/-- Exponential normalizer restricted to a line in logit space. -/
def categoricalExpSumAlong
    (logits direction : LogitVector Class) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (logits i - t * direction i)

/-- The unnormalized first directional moment along a logit-space line. -/
def categoricalFirstMomentAlong
    (logits direction : LogitVector Class) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (logits i - t * direction i) * direction i

/-- The unnormalized second directional moment along a logit-space line. -/
def categoricalSecondMomentAlong
    (logits direction : LogitVector Class) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (logits i - t * direction i) * direction i ^ 2

theorem categoricalExpSumAlong_pos
    (logits direction : LogitVector Class) (t : ℝ) :
    0 < categoricalExpSumAlong logits direction t := by
  classical
  exact Finset.sum_pos
    (fun i _ => Real.exp_pos (logits i - t * direction i))
    Finset.univ_nonempty

omit [Nonempty Class] in
theorem hasDerivAt_categoricalExpSumAlong
    (logits direction : LogitVector Class) (t : ℝ) :
    HasDerivAt (categoricalExpSumAlong logits direction)
      (-categoricalFirstMomentAlong logits direction t) t := by
  classical
  have h : HasDerivAt
      (fun s : ℝ => ∑ i, Real.exp (logits i - s * direction i))
      (∑ i, -(Real.exp (logits i - t * direction i) * direction i)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hinner : HasDerivAt (fun s : ℝ => logits i - s * direction i)
        (-direction i) t := by
      have hraw := (hasDerivAt_const t (logits i)).sub
        ((hasDerivAt_id t).mul_const (direction i))
      have heq : (fun s : ℝ => logits i - s * direction i) =ᶠ[𝓝 t]
          ((fun _ : ℝ => logits i) - fun s : ℝ => id s * direction i) :=
        Eventually.of_forall fun _ => rfl
      exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by ring)
    have hcomp :=
      (Real.hasDerivAt_exp (logits i - t * direction i)).comp t hinner
    have heq :
        (fun s : ℝ => Real.exp (logits i - s * direction i)) =ᶠ[𝓝 t]
          (Real.exp ∘ fun s : ℝ => logits i - s * direction i) :=
      Eventually.of_forall fun _ => rfl
    exact (hcomp.congr_of_eventuallyEq heq).congr_deriv (by ring)
  change HasDerivAt
    (fun s : ℝ => ∑ i, Real.exp (logits i - s * direction i))
    (-∑ i, Real.exp (logits i - t * direction i) * direction i) t
  simpa only [Finset.sum_neg_distrib] using h

omit [Nonempty Class] in
theorem hasDerivAt_categoricalFirstMomentAlong
    (logits direction : LogitVector Class) (t : ℝ) :
    HasDerivAt (categoricalFirstMomentAlong logits direction)
      (-categoricalSecondMomentAlong logits direction t) t := by
  classical
  have h : HasDerivAt
      (fun s : ℝ =>
        ∑ i, Real.exp (logits i - s * direction i) * direction i)
      (∑ i, -(Real.exp (logits i - t * direction i) * direction i ^ 2)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hexp : HasDerivAt
        (fun s : ℝ => Real.exp (logits i - s * direction i))
        (-Real.exp (logits i - t * direction i) * direction i) t := by
      have hinner : HasDerivAt (fun s : ℝ => logits i - s * direction i)
          (-direction i) t := by
        have hraw := (hasDerivAt_const t (logits i)).sub
          ((hasDerivAt_id t).mul_const (direction i))
        have heq : (fun s : ℝ => logits i - s * direction i) =ᶠ[𝓝 t]
            ((fun _ : ℝ => logits i) - fun s : ℝ => id s * direction i) :=
          Eventually.of_forall fun _ => rfl
        exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by ring)
      have hcomp :=
        (Real.hasDerivAt_exp (logits i - t * direction i)).comp t hinner
      have heq :
          (fun s : ℝ => Real.exp (logits i - s * direction i)) =ᶠ[𝓝 t]
            (Real.exp ∘ fun s : ℝ => logits i - s * direction i) :=
        Eventually.of_forall fun _ => rfl
      exact (hcomp.congr_of_eventuallyEq heq).congr_deriv (by ring)
    have hmul := hexp.mul_const (direction i)
    have heq :
        (fun s : ℝ => Real.exp (logits i - s * direction i) * direction i) =ᶠ[𝓝 t]
          (fun s : ℝ =>
            (fun u : ℝ => Real.exp (logits i - u * direction i)) s *
              direction i) :=
      Eventually.of_forall fun _ => rfl
    exact (hmul.congr_of_eventuallyEq heq).congr_deriv (by ring)
  change HasDerivAt
    (fun s : ℝ =>
      ∑ i, Real.exp (logits i - s * direction i) * direction i)
    (-∑ i, Real.exp (logits i - t * direction i) * direction i ^ 2) t
  simpa only [Finset.sum_neg_distrib] using h

/-- The directional Hessian of log-sum-exp is a softmax variance, bounded
above by the squared Euclidean length of the direction. -/
theorem categorical_directional_curvature_le
    (logits direction : LogitVector Class) (t : ℝ) :
    categoricalSecondMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t -
        (categoricalFirstMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t) ^ 2 ≤
      ∑ i, direction i ^ 2 := by
  classical
  let total := categoricalExpSumAlong logits direction t
  have htotal : 0 < total := categoricalExpSumAlong_pos logits direction t
  have hcomponent (i : Class) :
      Real.exp (logits i - t * direction i) / total ≤ 1 := by
    apply (div_le_one htotal).2
    exact Finset.single_le_sum
      (fun j _ => (Real.exp_pos (logits j - t * direction j)).le)
      (Finset.mem_univ i)
  have hweighted :
      ∑ i, (Real.exp (logits i - t * direction i) / total) *
          direction i ^ 2 ≤ ∑ i, direction i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (direction i), hcomponent i]
  calc
    categoricalSecondMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t -
        (categoricalFirstMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t) ^ 2
        ≤ categoricalSecondMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t :=
      sub_le_self _ (sq_nonneg _)
    _ = ∑ i, (Real.exp (logits i - t * direction i) / total) *
        direction i ^ 2 := by
      simp only [categoricalSecondMomentAlong, total, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, direction i ^ 2 := hweighted

/-- Categorical cross-entropy with logits has directional curvature at most
the squared Euclidean length of the chosen logit direction. -/
theorem categoricalCrossEntropy_directional_upper
    [DecidableEq Class]
    (target : Class) (logits direction : LogitVector Class) :
    HasDirectionalTaskUpperModelAt
      (categoricalCrossEntropy target) logits
      (categoricalCrossEntropyGradient target logits) direction
      (∑ i, direction i ^ 2) := by
  classical
  intro step hstep
  let line : ℝ → ℝ := fun t =>
    Real.log (categoricalExpSumAlong logits direction t) -
      (logits target - t * direction target)
  let lineGradient : ℝ → ℝ := fun t =>
    direction target -
      categoricalFirstMomentAlong logits direction t /
        categoricalExpSumAlong logits direction t
  let lineCurvature : ℝ → ℝ := fun t =>
    categoricalSecondMomentAlong logits direction t /
          categoricalExpSumAlong logits direction t -
      (categoricalFirstMomentAlong logits direction t /
        categoricalExpSumAlong logits direction t) ^ 2
  have hline : ∀ t, HasDerivAt line (lineGradient t) t := by
    intro t
    have hsum := hasDerivAt_categoricalExpSumAlong logits direction t
    have hsumNe := ne_of_gt (categoricalExpSumAlong_pos logits direction t)
    have htarget : HasDerivAt
        (fun s : ℝ => logits target - s * direction target)
        (-direction target) t := by
      have hraw := (hasDerivAt_const t (logits target)).sub
        ((hasDerivAt_id t).mul_const (direction target))
      have heq : (fun s : ℝ => logits target - s * direction target) =ᶠ[𝓝 t]
          ((fun _ : ℝ => logits target) -
            fun s : ℝ => id s * direction target) :=
        Eventually.of_forall fun _ => rfl
      exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by ring)
    dsimp only [line, lineGradient]
    have h := (hsum.log hsumNe).sub htarget
    have heq :
        (fun s : ℝ =>
          Real.log (categoricalExpSumAlong logits direction s) -
            (logits target - s * direction target)) =ᶠ[𝓝 t]
          ((Real.log ∘ categoricalExpSumAlong logits direction) -
            fun s : ℝ => logits target - s * direction target) :=
      Eventually.of_forall fun _ => rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by
      field_simp
      ring)
  have hgradient : ∀ t, HasDerivAt lineGradient (lineCurvature t) t := by
    intro t
    have hsum := hasDerivAt_categoricalExpSumAlong logits direction t
    have hmoment := hasDerivAt_categoricalFirstMomentAlong logits direction t
    have hsumNe := ne_of_gt (categoricalExpSumAlong_pos logits direction t)
    have hquotient := hmoment.div hsum hsumNe
    dsimp only [lineGradient, lineCurvature]
    have h := (hasDerivAt_const t (direction target)).sub hquotient
    have heq :
        (fun s : ℝ =>
          direction target -
            categoricalFirstMomentAlong logits direction s /
              categoricalExpSumAlong logits direction s) =ᶠ[𝓝 t]
          ((fun _ : ℝ => direction target) -
            fun s : ℝ =>
              categoricalFirstMomentAlong logits direction s /
                categoricalExpSumAlong logits direction s) :=
      Eventually.of_forall fun _ => rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by
      field_simp
      ring)
  have hcurvature : ∀ t, 0 ≤ t →
      lineCurvature t ≤ ∑ i, direction i ^ 2 := by
    intro t _
    exact categorical_directional_curvature_le logits direction t
  have hupper := line_upper_of_second_derivative
    line lineGradient lineCurvature (∑ i, direction i ^ 2) step
    hline hgradient hcurvature hstep
  have hinner :
      ⟪categoricalCrossEntropyGradient target logits, direction⟫_ℝ =
        categoricalFirstMomentAlong logits direction 0 /
            categoricalExpSumAlong logits direction 0 - direction target := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial,
      categoricalCrossEntropyGradient, PiLp.toLp_apply,
      categoricalFirstMomentAlong, categoricalExpSumAlong, zero_mul,
      sub_zero, categoricalExpSum]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have honeHot :
        ∑ i, direction i * (if i = target then 1 else 0) =
          direction target := by
      simp
    rw [honeHot]
    congr 1
    calc
      ∑ i, direction i *
          (Real.exp (logits i) / ∑ j, Real.exp (logits j)) =
          ∑ i, (Real.exp (logits i) * direction i) /
            ∑ j, Real.exp (logits j) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, Real.exp (logits i) * direction i) /
          ∑ j, Real.exp (logits j) :=
        (Finset.sum_div Finset.univ
          (fun i => Real.exp (logits i) * direction i)
          (∑ j, Real.exp (logits j))).symm
  rw [hinner]
  convert hupper using 1
  all_goals simp [line, lineGradient, categoricalCrossEntropy,
    categoricalExpSumAlong, categoricalFirstMomentAlong, categoricalExpSum,
    PiLp.sub_apply, PiLp.smul_apply]
  all_goals ring

/-! ## Positive and negative curvature fixtures -/

/-- A concrete two-class logit vector, used to exercise the categorical
certificate away from its abstract finite-index presentation. -/
noncomputable def twoClassLogits
    (falseLogit trueLogit : ℝ) : LogitVector Bool :=
  WithLp.toLp 2 fun i => if i then trueLogit else falseLogit

@[simp] theorem twoClassLogits_false (falseLogit trueLogit : ℝ) :
    twoClassLogits falseLogit trueLogit false = falseLogit := rfl

@[simp] theorem twoClassLogits_true (falseLogit trueLogit : ℝ) :
    twoClassLogits falseLogit trueLogit true = trueLogit := rfl

theorem categorical_two_class_positive :
    HasDirectionalTaskUpperModelAt
      (categoricalCrossEntropy false) (twoClassLogits 0 0)
      (categoricalCrossEntropyGradient false (twoClassLogits 0 0))
      (twoClassLogits (-1 / 2) (1 / 2)) (1 / 2) := by
  convert categoricalCrossEntropy_directional_upper false
    (twoClassLogits 0 0) (twoClassLogits (-1 / 2) (1 / 2)) using 1
  norm_num [twoClassLogits]

/-- Strict convexity at the balanced binary logit, in the precise numerical
form shared by the BCE and two-class categorical counterexamples below. -/
theorem log_two_sub_half_lt_log_one_add_exp_neg_one :
    Real.log 2 - 1 / 2 < Real.log (1 + Real.exp (-1)) := by
  let a : ℝ := Real.exp (-1 / 2)
  have haPos : 0 < a := Real.exp_pos _
  have haNe : a ≠ 1 := by
    intro ha
    have hexp : Real.exp (-1 / 2) = Real.exp 0 := by
      simp [a] at ha
    have := Real.exp_injective hexp
    norm_num at this
  have hsq : 0 < (a - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr haNe)
  have hexpNegOne : Real.exp (-1) = a ^ 2 := by
    rw [show (-1 : ℝ) = (-1 / 2) + (-1 / 2) by ring, Real.exp_add]
    simp only [a, pow_two]
  have hamgm : 2 * a < 1 + Real.exp (-1) := by
    rw [hexpNegOne]
    nlinarith
  have hlog := Real.log_lt_log (mul_pos (by norm_num) haPos) hamgm
  rw [Real.log_mul (by norm_num) (ne_of_gt haPos), Real.log_exp] at hlog
  convert hlog using 1
  all_goals ring

theorem binaryCrossEntropy_zero_target_positive :
    HasDirectionalTaskUpperModelAt
      (binaryCrossEntropyWithLogits 0) 0 (1 / 2) 2 1 := by
  convert binaryCrossEntropyWithLogits_directional_upper 0 0 2 using 1 <;>
    norm_num [binaryCrossEntropyGradient, Real.sigmoid_zero]

/-- The universal BCE curvature constant cannot be reduced below `1/4` at
the balanced logit: a zero-curvature model already fails for target zero. -/
theorem binaryCrossEntropy_zero_curvature_fails :
    ¬ HasDirectionalTaskUpperModelAt
      (binaryCrossEntropyWithLogits 0) 0 (1 / 2) 1 0 := by
  intro certificate
  have h := certificate 1 (by norm_num)
  simp [binaryCrossEntropyWithLogits, Real.exp_zero] at h
  linarith [log_two_sub_half_lt_log_one_add_exp_neg_one]

/-- The same zero-curvature failure occurs for the exact two-class
categorical loss along its nonzero balanced-gradient direction. -/
theorem categorical_two_class_zero_curvature_fails :
    ¬ HasDirectionalTaskUpperModelAt
      (categoricalCrossEntropy false) (twoClassLogits 0 0)
      (categoricalCrossEntropyGradient false (twoClassLogits 0 0))
      (twoClassLogits (-1 / 2) (1 / 2)) 0 := by
  intro certificate
  have h := certificate 1 (by norm_num)
  have hcurrent :
      categoricalCrossEntropy false (twoClassLogits 0 0) =
        Real.log 2 := by
    norm_num [categoricalCrossEntropy, categoricalExpSum, twoClassLogits,
      Real.exp_zero]
  have hinner :
      ⟪categoricalCrossEntropyGradient false (twoClassLogits 0 0),
          twoClassLogits (-1 / 2) (1 / 2)⟫_ℝ = 1 / 2 := by
    rw [PiLp.inner_apply]
    norm_num [categoricalCrossEntropyGradient, categoricalExpSum,
      twoClassLogits, RCLike.inner_apply, Real.exp_zero]
  have hfactor :
      Real.exp (1 / 2) + Real.exp (-1 / 2) =
        Real.exp (1 / 2) * (1 + Real.exp (-1)) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    norm_num
  have hnext :
      categoricalCrossEntropy false
          (twoClassLogits 0 0 -
            (1 : ℝ) • twoClassLogits (-1 / 2) (1 / 2)) =
        Real.log (1 + Real.exp (-1)) := by
    rw [categoricalCrossEntropy]
    have hsum :
        categoricalExpSum
            (twoClassLogits 0 0 -
              (1 : ℝ) • twoClassLogits (-1 / 2) (1 / 2)) =
          Real.exp (1 / 2) + Real.exp (-1 / 2) := by
      norm_num [categoricalExpSum, twoClassLogits, PiLp.sub_apply,
        PiLp.smul_apply]
      ring
    rw [hsum, hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity),
      Real.log_exp]
    norm_num [twoClassLogits, PiLp.sub_apply, PiLp.smul_apply]
  rw [hnext, hcurrent, hinner] at h
  norm_num at h
  linarith [log_two_sub_half_lt_log_one_add_exp_neg_one]

#print axioms line_upper_of_second_derivative
#print axioms hasDerivAt_binaryCrossEntropyWithLogits
#print axioms binaryCrossEntropyWithLogits_directional_upper
#print axioms categorical_directional_curvature_le
#print axioms categoricalCrossEntropy_directional_upper
#print axioms categorical_two_class_positive
#print axioms categorical_two_class_zero_curvature_fails
#print axioms binaryCrossEntropy_zero_target_positive
#print axioms binaryCrossEntropy_zero_curvature_fails

end

end LogitLossCurvature

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
