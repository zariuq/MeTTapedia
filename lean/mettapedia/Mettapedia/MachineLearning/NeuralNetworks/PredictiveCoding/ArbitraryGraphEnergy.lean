import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Energy geometry for predictive coding on arbitrary directed graphs

Salvatori, Pinchetti, Millidge, Song, Bao, Bogacz, and Lukasiewicz,
*Learning on Arbitrary Graph Topologies via Predictive Coding*,
arXiv:2201.13180v3, equations (1)--(6), define a residual energy on an
arbitrary directed graph and minimize it by local state and weight updates.
The source PDF has SHA-256
`f2caea59f3f4b7150f30d2f392610c5f732ef8b46e5d46d1b5ab151d3289df30`.

This file proves the graph calculus without assuming acyclicity.  The exact
coordinate derivative aggregates residuals over edges *leaving* the updated
state, because that state contributes to the predictions of their targets.
An asymmetric two-vertex fixture separates this derivative from the
transposed incoming-edge expression printed in equation (3).

For the identity activation the energy along any state coordinate is an exact
quadratic.  We derive its curvature, the exact energy change of a coordinate
step, and the sharp open descent-rate boundary.  The same analysis validates
the source's local weight update and its source/target orientation.

Clamped inference preserves every conditioned coordinate for every finite
run.  Initialization alone does not.  Finally, a double-well counterexample
shows that minimizing an energy need not select a unique conditional
expectation; that interpretation requires additional probabilistic semantics
and convergence or uniqueness hypotheses.

No theorem below claims convergence of the simultaneous nonlinear inference
loop, a probabilistic conditional expectation, or an empirical advantage for
cyclic graph topologies.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace ArbitraryGraphEnergy

open Finset

noncomputable section

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-! ## Source-shaped graph energy -/

/-- Prediction at `target`.  The first weight index is the source and the
second is the target, matching equation (1). -/
def prediction
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (target : Vertex) : ℝ :=
  ∑ source, weight source target * activation (state source)

/-- Local prediction residual `state - prediction`. -/
def residual
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (target : Vertex) : ℝ :=
  state target - prediction activation weight state target

/-- Half the sum of squared local residuals, equation (2). -/
def energy
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ target, residual activation weight state target ^ 2

/-- Add `delta` to one state coordinate. -/
def coordinatePerturb
    (state : Vertex → ℝ) (vertex : Vertex) (delta : ℝ) : Vertex → ℝ :=
  fun current => state current + if current = vertex then delta else 0

/-- First-order influence of a state coordinate on a target residual. -/
def residualInfluence
    (weight : Vertex → Vertex → ℝ) (activationSlope : ℝ)
    (vertex target : Vertex) : ℝ :=
  (if target = vertex then 1 else 0) -
    weight vertex target * activationSlope

/-- Exact energy derivative along one state coordinate when
`activationSlope` is the derivative of the activation at that coordinate. -/
def coordinateGradient
    (activation : ℝ → ℝ) (activationSlope : ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex) : ℝ :=
  ∑ target,
    residual activation weight state target *
      residualInfluence weight activationSlope vertex target

/-- Perturbing one state affects a target prediction only through the
corresponding source-to-target edge. -/
theorem prediction_coordinatePerturb_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex target : Vertex) (delta : ℝ) :
    prediction activation weight (coordinatePerturb state vertex delta) target =
      prediction activation weight state target +
        weight vertex target *
          (activation (state vertex + delta) - activation (state vertex)) := by
  classical
  unfold prediction coordinatePerturb
  have hsingle :
      weight vertex target *
          (activation (state vertex + delta) - activation (state vertex)) =
        ∑ source : Vertex,
          if source = vertex then
            weight source target *
              (activation (state source + delta) - activation (state source))
          else 0 := by
    simp
  rw [hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  by_cases hsource : source = vertex
  · subst source
    simp
    ring
  · simp [hsource]

/-- Exact residual response to a one-coordinate state perturbation. -/
theorem residual_coordinatePerturb_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex target : Vertex) (delta : ℝ) :
    residual activation weight (coordinatePerturb state vertex delta) target =
      residual activation weight state target +
        (if target = vertex then delta else 0) -
          weight vertex target *
            (activation (state vertex + delta) -
              activation (state vertex)) := by
  rw [residual, residual, prediction_coordinatePerturb_exact]
  simp only [coordinatePerturb]
  ring

/-- The derivative of a target residual along one state coordinate. -/
theorem residual_coordinatePerturb_hasDerivAt
    (activation : ℝ → ℝ) (activationSlope : ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex target : Vertex)
    (hactivation :
      HasDerivAt activation activationSlope (state vertex)) :
    HasDerivAt
      (fun delta =>
        residual activation weight
          (coordinatePerturb state vertex delta) target)
      (residualInfluence weight activationSlope vertex target) 0 := by
  have hshift :
      HasDerivAt (fun delta : ℝ => state vertex + delta) 1 0 :=
    (hasDerivAt_id' (𝕜 := ℝ) 0).const_add (state vertex)
  have hactivationAtShift :
      HasDerivAt activation activationSlope (state vertex + 0) := by
    simpa using hactivation
  have hactivationDifference :
      HasDerivAt
        (fun delta : ℝ =>
          activation (state vertex + delta) - activation (state vertex))
        activationSlope 0 := by
    simpa only [Function.comp_apply, mul_one] using
      (hactivationAtShift.comp 0 hshift).sub_const
        (activation (state vertex))
  have hcoordinate :
      HasDerivAt
        (fun delta : ℝ => if target = vertex then delta else 0)
        (if target = vertex then 1 else 0) 0 := by
    by_cases htarget : target = vertex
    · simpa only [htarget, if_true, id_eq] using
        (hasDerivAt_id' (𝕜 := ℝ) (0 : ℝ))
    · simpa only [htarget, if_false] using
        (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ))
  rw [show
      (fun delta =>
        residual activation weight
          (coordinatePerturb state vertex delta) target) =
        (fun delta =>
          residual activation weight state target +
            (if target = vertex then delta else 0) -
              weight vertex target *
                (activation (state vertex + delta) -
                  activation (state vertex))) by
    funext delta
    exact residual_coordinatePerturb_exact
      activation weight state vertex target delta]
  exact
    (hcoordinate.const_add (residual activation weight state target)).sub
      (hactivationDifference.const_mul (weight vertex target))

/-! The pointwise function-sum definitions below keep the finite derivative
calculus definitionally aligned with `HasDerivAt.sum`. -/

private def squaredResidualPath
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex target : Vertex) : ℝ → ℝ :=
  (fun delta =>
    residual activation weight (coordinatePerturb state vertex delta) target) ^ 2

private def squaredResidualPathSum
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex : Vertex) : ℝ → ℝ :=
  ∑ target : Vertex,
    squaredResidualPath activation weight state vertex target

private def coordinateEnergyPath
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex : Vertex) : ℝ → ℝ :=
  fun delta =>
    (1 / 2 : ℝ) *
      squaredResidualPathSum activation weight state vertex delta

private theorem coordinateEnergyPath_eq
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (vertex : Vertex) :
    coordinateEnergyPath activation weight state vertex =
      fun delta =>
        energy activation weight (coordinatePerturb state vertex delta) := by
  funext delta
  simp [coordinateEnergyPath, squaredResidualPathSum, squaredResidualPath,
    energy]

/-- Source equation (3), stated as a derivative theorem.  The aggregation is
over `weight vertex target`: edges leaving the updated vertex. -/
theorem energy_coordinatePerturb_hasDerivAt
    (activation : ℝ → ℝ) (activationSlope : ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex)
    (hactivation :
      HasDerivAt activation activationSlope (state vertex)) :
    HasDerivAt
      (fun delta =>
        energy activation weight (coordinatePerturb state vertex delta))
      (coordinateGradient
        activation activationSlope weight state vertex) 0 := by
  rw [← coordinateEnergyPath_eq]
  unfold coordinateEnergyPath
  have hsquared : ∀ target : Vertex,
      HasDerivAt
        (squaredResidualPath activation weight state vertex target)
        (2 * residual activation weight state target *
          residualInfluence weight activationSlope vertex target) 0 := by
    intro target
    unfold squaredResidualPath
    have hpower :=
      (residual_coordinatePerturb_hasDerivAt
        activation activationSlope weight state vertex target
        hactivation).pow 2
    have hzero :
        residual activation weight
            (coordinatePerturb state vertex 0) target =
          residual activation weight state target := by
      rw [residual_coordinatePerturb_exact]
      simp
    convert hpower using 1 <;> try rfl
    rw [hzero]
    norm_num
  have hsum :
      HasDerivAt
        (squaredResidualPathSum activation weight state vertex)
        (∑ target : Vertex,
          2 * residual activation weight state target *
            residualInfluence weight activationSlope vertex target) 0 := by
    unfold squaredResidualPathSum
    exact HasDerivAt.sum (u := (Finset.univ : Finset Vertex))
      (fun target _ => hsquared target)
  have hscaled := hsum.const_mul (1 / 2 : ℝ)
  have hderivative :
      (1 / 2 : ℝ) *
          (∑ target : Vertex,
            2 * residual activation weight state target *
              residualInfluence weight activationSlope vertex target) =
        coordinateGradient
          activation activationSlope weight state vertex := by
    unfold coordinateGradient
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring
  rw [hderivative] at hscaled
  exact hscaled

/-- The exact state gradient is the local residual minus the residuals of
targets reached by outgoing edges.  This is the orientation-sensitive form of
equation (3). -/
theorem coordinateGradient_eq_outgoing
    (activation : ℝ → ℝ) (activationSlope : ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex) :
    coordinateGradient activation activationSlope weight state vertex =
      residual activation weight state vertex -
        activationSlope *
          ∑ target,
            weight vertex target *
              residual activation weight state target := by
  unfold coordinateGradient residualInfluence
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [show
      (∑ target : Vertex,
        residual activation weight state target *
          (if target = vertex then 1 else 0)) =
        residual activation weight state vertex by
    classical
    simp]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  ring

/-! ## Exact identity-activation coordinate geometry -/

/-- Identity-activation residual. -/
def linearResidual
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (target : Vertex) : ℝ :=
  residual id weight state target

/-- Identity-activation energy. -/
def linearEnergy
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ) : ℝ :=
  energy id weight state

/-- Exact identity-activation coordinate gradient. -/
def linearCoordinateGradient
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex) : ℝ :=
  coordinateGradient id 1 weight state vertex

/-- Exact curvature of the identity-activation energy along one coordinate. -/
def linearCoordinateCurvature
    (weight : Vertex → Vertex → ℝ) (vertex : Vertex) : ℝ :=
  ∑ target, residualInfluence weight 1 vertex target ^ 2

/-- Identity activation makes every target residual affine in the coordinate
perturbation. -/
theorem linearResidual_coordinatePerturb_exact
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex target : Vertex) (delta : ℝ) :
    linearResidual weight (coordinatePerturb state vertex delta) target =
      linearResidual weight state target +
        delta * residualInfluence weight 1 vertex target := by
  rw [linearResidual, linearResidual,
    residual_coordinatePerturb_exact]
  by_cases htarget : target = vertex
  · simp [residualInfluence, htarget]
    ring
  · simp [residualInfluence, htarget]
    ring

omit [DecidableEq Vertex] in
/-- Finite sum-of-squares expansion used by both state and weight
coordinates. -/
theorem sum_add_scaled_sq
    (base direction : Vertex → ℝ) (delta : ℝ) :
    (∑ target, (base target + delta * direction target) ^ 2) =
      (∑ target, base target ^ 2) +
        2 * delta * (∑ target, base target * direction target) +
          delta ^ 2 * (∑ target, direction target ^ 2) := by
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross :
      (∑ target, 2 * base target * (delta * direction target)) =
        2 * delta * (∑ target, base target * direction target) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring
  have hquadratic :
      (∑ target, (delta * direction target) ^ 2) =
        delta ^ 2 * (∑ target, direction target ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring
  rw [hcross, hquadratic]

/-- Exact quadratic expansion of the identity-activation energy along any
state coordinate. -/
theorem linearEnergy_coordinatePerturb_exact
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex) (delta : ℝ) :
    linearEnergy weight (coordinatePerturb state vertex delta) =
      linearEnergy weight state +
        delta * linearCoordinateGradient weight state vertex +
          (delta ^ 2 / 2) * linearCoordinateCurvature weight vertex := by
  unfold linearEnergy
  change
    (1 / 2 : ℝ) *
        (∑ target,
          linearResidual weight
            (coordinatePerturb state vertex delta) target ^ 2) =
      (1 / 2 : ℝ) *
          (∑ target, linearResidual weight state target ^ 2) +
        delta * linearCoordinateGradient weight state vertex +
          delta ^ 2 / 2 * linearCoordinateCurvature weight vertex
  simp_rw [linearResidual_coordinatePerturb_exact]
  rw [sum_add_scaled_sq]
  unfold linearResidual linearCoordinateGradient linearCoordinateCurvature
    coordinateGradient
  ring

/-- Coordinate curvature is nonnegative on every directed graph, including
graphs with cycles and self-loops. -/
theorem linearCoordinateCurvature_nonneg
    (weight : Vertex → Vertex → ℝ) (vertex : Vertex) :
    0 ≤ linearCoordinateCurvature weight vertex := by
  exact Finset.sum_nonneg fun target _ =>
    sq_nonneg (residualInfluence weight 1 vertex target)

/-- One explicit state-coordinate gradient step. -/
def linearCoordinateStep
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (state : Vertex → ℝ) (vertex : Vertex) : Vertex → ℝ :=
  coordinatePerturb state vertex
    (-rate * linearCoordinateGradient weight state vertex)

/-- Exact energy change of one state-coordinate gradient step. -/
theorem linearCoordinateStep_energy_exact
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (state : Vertex → ℝ) (vertex : Vertex) :
    linearEnergy weight (linearCoordinateStep weight rate state vertex) =
      linearEnergy weight state -
        (rate / 2) *
          (2 - rate * linearCoordinateCurvature weight vertex) *
          linearCoordinateGradient weight state vertex ^ 2 := by
  rw [linearCoordinateStep, linearEnergy_coordinatePerturb_exact]
  ring

/-- Closed descent-rate interval for a coordinate step. -/
theorem linearCoordinateStep_energy_le
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (state : Vertex → ℝ) (vertex : Vertex)
    (hrate : 0 ≤ rate)
    (hupper : rate * linearCoordinateCurvature weight vertex ≤ 2) :
    linearEnergy weight (linearCoordinateStep weight rate state vertex) ≤
      linearEnergy weight state := by
  rw [linearCoordinateStep_energy_exact]
  have hfactor :
      0 ≤ (rate / 2) *
        (2 - rate * linearCoordinateCurvature weight vertex) *
        linearCoordinateGradient weight state vertex ^ 2 := by
    positivity
  linarith

/-- Sharp open descent-rate condition away from a coordinate critical point. -/
theorem linearCoordinateStep_energy_lt
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (state : Vertex → ℝ) (vertex : Vertex)
    (hrate : 0 < rate)
    (hupper : rate * linearCoordinateCurvature weight vertex < 2)
    (hgradient : linearCoordinateGradient weight state vertex ≠ 0) :
    linearEnergy weight (linearCoordinateStep weight rate state vertex) <
      linearEnergy weight state := by
  rw [linearCoordinateStep_energy_exact]
  have hfactor :
      0 < (rate / 2) *
        (2 - rate * linearCoordinateCurvature weight vertex) *
        linearCoordinateGradient weight state vertex ^ 2 := by
    have hsq :
        0 < linearCoordinateGradient weight state vertex ^ 2 :=
      sq_pos_of_ne_zero hgradient
    positivity
  linarith

/-! ## Local weight-coordinate geometry -/

/-- Add `delta` to one directed source-to-target weight. -/
def weightPerturb
    (weight : Vertex → Vertex → ℝ) (source target : Vertex)
    (delta : ℝ) : Vertex → Vertex → ℝ :=
  fun currentSource currentTarget =>
    weight currentSource currentTarget +
      if currentSource = source ∧ currentTarget = target then delta else 0

/-- Perturbing one weight affects only its target prediction. -/
theorem prediction_weightPerturb_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (source target actualTarget : Vertex)
    (delta : ℝ) :
    prediction activation (weightPerturb weight source target delta)
        state actualTarget =
      prediction activation weight state actualTarget +
        if actualTarget = target then
          delta * activation (state source)
        else 0 := by
  classical
  unfold prediction weightPerturb
  by_cases htarget : actualTarget = target
  · subst actualTarget
    simp only [and_true, ↓reduceIte]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  · simp only [htarget, if_false]
    simp

/-- Exact residual response to one weight perturbation. -/
theorem residual_weightPerturb_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (source target actualTarget : Vertex)
    (delta : ℝ) :
    residual activation (weightPerturb weight source target delta)
        state actualTarget =
      residual activation weight state actualTarget +
        delta *
          (if actualTarget = target then
            -activation (state source)
          else 0) := by
  rw [residual, residual, prediction_weightPerturb_exact]
  by_cases htarget : actualTarget = target
  · simp [htarget]
    ring
  · simp [htarget]

/-- Exact derivative of the energy with respect to one directed weight. -/
def weightGradient
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (source target : Vertex) : ℝ :=
  -residual activation weight state target * activation (state source)

/-- Curvature of the energy along one directed weight. -/
def weightCurvature
    (activation : ℝ → ℝ) (state : Vertex → ℝ)
    (source : Vertex) : ℝ :=
  activation (state source) ^ 2

/-- Exact quadratic expansion along a directed weight coordinate. -/
theorem energy_weightPerturb_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (source target : Vertex) (delta : ℝ) :
    energy activation (weightPerturb weight source target delta) state =
      energy activation weight state +
        delta * weightGradient activation weight state source target +
          (delta ^ 2 / 2) *
            weightCurvature activation state source := by
  unfold energy
  simp_rw [residual_weightPerturb_exact]
  rw [sum_add_scaled_sq]
  unfold weightGradient weightCurvature
  have hlinear :
      (∑ actualTarget : Vertex,
        residual activation weight state actualTarget *
          (if actualTarget = target then
            -activation (state source)
          else 0)) =
        -residual activation weight state target *
          activation (state source) := by
    simp
  have hquadratic :
      (∑ actualTarget : Vertex,
        (if actualTarget = target then
          -activation (state source)
        else 0) ^ 2) =
        activation (state source) ^ 2 := by
    simp
  rw [hlinear, hquadratic]
  ring

/-- The source's positive local update is exactly a negative-gradient step. -/
def weightGradientStep
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (rate : ℝ) (state : Vertex → ℝ) (source target : Vertex) :
    Vertex → Vertex → ℝ :=
  weightPerturb weight source target
    (-rate * weightGradient activation weight state source target)

theorem weightGradientStep_eq_source_update
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (rate : ℝ) (state : Vertex → ℝ) (source target : Vertex) :
    weightGradientStep activation weight rate state source target =
      weightPerturb weight source target
        (rate * residual activation weight state target *
          activation (state source)) := by
  unfold weightGradientStep weightGradient
  congr 1
  ring

/-- Exact energy change of one local weight-gradient step. -/
theorem weightGradientStep_energy_exact
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (rate : ℝ) (state : Vertex → ℝ) (source target : Vertex) :
    energy activation
        (weightGradientStep activation weight rate state source target) state =
      energy activation weight state -
        (rate / 2) *
          (2 - rate * weightCurvature activation state source) *
          weightGradient activation weight state source target ^ 2 := by
  rw [weightGradientStep, energy_weightPerturb_exact]
  ring

/-! ## Conditioning versus initialization -/

/-- One simultaneous graph-inference step.  The derivative oracle is read at
the current state, while members of `clamped` are copied exactly. -/
def inferenceStep
    (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (clamped : Finset Vertex) (state : Vertex → ℝ) : Vertex → ℝ :=
  fun vertex =>
    if vertex ∈ clamped then state vertex
    else
      state vertex -
        rate *
          coordinateGradient activation
            (activationDerivative (state vertex)) weight state vertex

/-- A conditioned coordinate is unchanged by one inference step. -/
theorem inferenceStep_of_mem_clamped
    (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (clamped : Finset Vertex) (state : Vertex → ℝ)
    (vertex : Vertex) (hvertex : vertex ∈ clamped) :
    inferenceStep activation activationDerivative weight rate
      clamped state vertex = state vertex := by
  simp [inferenceStep, hvertex]

/-- Finite synchronous inference run. -/
def runInference
    (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (clamped : Finset Vertex) (initial : Vertex → ℝ) :
    ℕ → Vertex → ℝ
  | 0 => initial
  | steps + 1 =>
      inferenceStep activation activationDerivative weight rate clamped
        (runInference activation activationDerivative weight rate
          clamped initial steps)

/-- Query by conditioning preserves each supplied value for every finite
inference horizon. -/
theorem runInference_of_mem_clamped
    (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ) (rate : ℝ)
    (clamped : Finset Vertex) (initial : Vertex → ℝ)
    (steps : ℕ) (vertex : Vertex) (hvertex : vertex ∈ clamped) :
    runInference activation activationDerivative weight rate
      clamped initial steps vertex = initial vertex := by
  induction steps with
  | zero =>
      rfl
  | succ steps ih =>
      simpa [runInference, inferenceStep, hvertex] using ih

/-! ## Executable orientation, cyclicity, and scope boundaries -/

/-- A nonsymmetric two-vertex graph with one edge `0 -> 1` of weight two. -/
def oneWayWeight (source target : Fin 2) : ℝ :=
  if source = 0 ∧ target = 1 then 2 else 0

/-- State used to expose the transpose error: `(1, 0)`. -/
def oneWayState (vertex : Fin 2) : ℝ :=
  if vertex = 0 then 1 else 0

/-- The transposed incoming-edge expression that equation (3) would denote
under equation (1)'s source/target convention. -/
def incomingCoordinateExpression
    (activation : ℝ → ℝ) (activationSlope : ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (vertex : Vertex) : ℝ :=
  residual activation weight state vertex -
    activationSlope *
      ∑ source,
        weight source vertex * residual activation weight state source

/-- Exact differentiation and transposed aggregation disagree on an
asymmetric graph: the true derivative is five, while the incoming expression
is one. -/
theorem outgoing_not_incoming_orientation :
    coordinateGradient id 1 oneWayWeight oneWayState 0 = 5 ∧
      incomingCoordinateExpression id 1 oneWayWeight oneWayState 0 = 1 := by
  norm_num [coordinateGradient, incomingCoordinateExpression,
    residualInfluence, residual, prediction, oneWayWeight, oneWayState,
    Fin.sum_univ_two]

/-- A self-loop contributes both the direct state residual derivative and the
prediction derivative. -/
def halfSelfLoopWeight (_source _target : Fin 1) : ℝ :=
  1 / 2

def twoState (_vertex : Fin 1) : ℝ :=
  2

theorem selfLoop_counts_direct_and_prediction_terms :
    linearResidual halfSelfLoopWeight twoState 0 = 1 ∧
      linearCoordinateGradient halfSelfLoopWeight twoState 0 = 1 / 2 := by
  norm_num [linearResidual, linearCoordinateGradient, coordinateGradient,
    residualInfluence, residual, prediction, halfSelfLoopWeight, twoState,
    Fin.sum_univ_one]

/-- A genuine directed two-cycle. -/
def twoCycleWeight (source target : Fin 2) : ℝ :=
  if source = 0 ∧ target = 1 then 2
  else if source = 1 ∧ target = 0 then 3
  else 0

/-- The two-cycle admits no strict forward rank, but all preceding energy
identities still apply because they require no topological order. -/
theorem twoCycle_has_no_strict_forward_rank :
    ¬ ∃ rank : Fin 2 → ℕ, rank 0 < rank 1 ∧ rank 1 < rank 0 := by
  rintro ⟨rank, hforward, hbackward⟩
  omega

theorem twoCycle_prediction (state : Fin 2 → ℝ) :
    prediction id twoCycleWeight state 0 = 3 * state 1 ∧
      prediction id twoCycleWeight state 1 = 2 * state 0 := by
  norm_num [prediction, twoCycleWeight, Fin.sum_univ_two]

/-- On a one-vertex zero-weight graph, rate three crosses the sharp curvature
boundary and increases energy from `1/2` to `2`. -/
def zeroWeight (_source _target : Fin 1) : ℝ :=
  0

def unitState (_vertex : Fin 1) : ℝ :=
  1

theorem oversized_coordinate_rate_increases_energy :
    linearEnergy zeroWeight
        (linearCoordinateStep zeroWeight 3 unitState 0) = 2 ∧
      linearEnergy zeroWeight unitState = 1 / 2 := by
  norm_num [linearEnergy, linearCoordinateStep, coordinatePerturb,
    linearCoordinateGradient, coordinateGradient, residualInfluence,
    residual, prediction, zeroWeight, unitState, energy, Fin.sum_univ_one]

/-- With no clamp, the same initialized coordinate can move immediately.
Initialization is therefore not conditioning. -/
theorem query_by_initialization_does_not_preserve :
    inferenceStep id (fun _ => 1) oneWayWeight 1
      (∅ : Finset (Fin 2)) oneWayState 0 = -4 := by
  norm_num [inferenceStep, coordinateGradient, residualInfluence, residual,
    prediction, oneWayWeight, oneWayState, Fin.sum_univ_two]

/-- A simple nonconvex energy with two distinct zero-energy global
minimizers. -/
def doubleWellEnergy (state : ℝ) : ℝ :=
  (state ^ 2 - 1) ^ 2

/-- Energy minimization alone need not choose a unique value.  Calling the
result a conditional expectation therefore requires a probabilistic model and
additional identification hypotheses. -/
theorem doubleWell_has_two_distinct_global_minimizers :
    (∀ state, doubleWellEnergy 1 ≤ doubleWellEnergy state) ∧
      (∀ state, doubleWellEnergy (-1) ≤ doubleWellEnergy state) ∧
      (1 : ℝ) ≠ -1 := by
  constructor
  · intro state
    simp [doubleWellEnergy]
    positivity
  constructor
  · intro state
    simp [doubleWellEnergy]
    positivity
  · norm_num

#print axioms prediction_coordinatePerturb_exact
#print axioms energy_coordinatePerturb_hasDerivAt
#print axioms coordinateGradient_eq_outgoing
#print axioms linearEnergy_coordinatePerturb_exact
#print axioms linearCoordinateStep_energy_lt
#print axioms energy_weightPerturb_exact
#print axioms weightGradientStep_energy_exact
#print axioms runInference_of_mem_clamped
#print axioms outgoing_not_incoming_orientation
#print axioms doubleWell_has_two_distinct_global_minimizers

end

end ArbitraryGraphEnergy

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
