import Mathlib

/-!
# Rectifier-aware variance transport

He et al., *Delving Deep into Rectifiers* (arXiv:1502.01852), derive the
forward second-moment multiplier

`(1 / 2) * (1 + a^2) * fanIn * weightVariance`

for a PReLU slope `a` under their independence and symmetry assumptions.
This file isolates the exact algebra after those probabilistic assumptions
have supplied the scalar recurrence.  It proves finite-depth transport,
recovers the ReLU and linear endpoints, and exposes two sharp failure
boundaries: zero fan-in and applying the ReLU scale to a nonzero PReLU slope.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

/-- One layer's second-moment multiplier after the source paper's
independence and symmetry reduction. -/
def preluSecondMomentFactor
    (slope fanIn weightVariance : ℝ) : ℝ :=
  ((1 + slope ^ 2) / 2) * fanIn * weightVariance

/-- Transport a scalar second moment through one rectifier layer. -/
def rectifierVarianceStep
    (slope fanIn weightVariance current : ℝ) : ℝ :=
  preluSecondMomentFactor slope fanIn weightVariance * current

/-- Transport a scalar second moment through a finite sequence of already
reduced layer multipliers. -/
def runVarianceFactors : List ℝ → ℝ → ℝ
  | [], current => current
  | factor :: factors, current =>
      runVarianceFactors factors (factor * current)

/-- The exact depth law corresponding to the product in equations (9) and
(13) of the source paper. -/
theorem runVarianceFactors_eq_prod_mul
    (factors : List ℝ) (initial : ℝ) :
    runVarianceFactors factors initial = factors.prod * initial := by
  induction factors generalizing initial with
  | nil =>
      simp [runVarianceFactors]
  | cons factor factors induction =>
      rw [runVarianceFactors, induction]
      simp only [List.prod_cons]
      ring

/-- The PReLU scale prescribed by equation (15). -/
def hePReLUWeightVariance (slope fanIn : ℝ) : ℝ :=
  2 / ((1 + slope ^ 2) * fanIn)

theorem one_add_slope_sq_pos (slope : ℝ) :
    0 < 1 + slope ^ 2 := by
  nlinarith [sq_nonneg slope]

/-- At nonzero fan-in, the rectifier-aware initialization makes every
reduced layer multiplier exactly one. -/
theorem preluSecondMomentFactor_he
    (slope fanIn : ℝ) (fanIn_ne : fanIn ≠ 0) :
    preluSecondMomentFactor slope fanIn
      (hePReLUWeightVariance slope fanIn) = 1 := by
  have slopeFactor_ne : 1 + slope ^ 2 ≠ 0 :=
    ne_of_gt (one_add_slope_sq_pos slope)
  simp only [preluSecondMomentFactor, hePReLUWeightVariance]
  field_simp [slopeFactor_ne, fanIn_ne]

/-- ReLU is the zero-slope endpoint of the source recurrence. -/
theorem preluSecondMomentFactor_zero_slope
    (fanIn weightVariance : ℝ) :
    preluSecondMomentFactor 0 fanIn weightVariance =
      fanIn * weightVariance / 2 := by
  simp [preluSecondMomentFactor]
  ring

/-- Slope one recovers the linear second-moment multiplier. -/
theorem preluSecondMomentFactor_one_slope
    (fanIn weightVariance : ℝ) :
    preluSecondMomentFactor 1 fanIn weightVariance =
      fanIn * weightVariance := by
  simp [preluSecondMomentFactor]

/-- Equation (15) reduces to variance `2 / fanIn` for ReLU. -/
theorem hePReLUWeightVariance_zero_slope (fanIn : ℝ) :
    hePReLUWeightVariance 0 fanIn = 2 / fanIn := by
  simp [hePReLUWeightVariance]

/-- Equation (15) reduces to variance `1 / fanIn` in the linear case. -/
theorem hePReLUWeightVariance_one_slope (fanIn : ℝ) :
    hePReLUWeightVariance 1 fanIn = 1 / fanIn := by
  simp [hePReLUWeightVariance]
  ring

/-- A finite stack of correctly scaled nondegenerate layers preserves its
initial second moment exactly, at every depth. -/
theorem runVarianceFactors_he
    (slope initial : ℝ) (fanIns : List ℝ)
    (nonzero : ∀ fanIn ∈ fanIns, fanIn ≠ 0) :
    runVarianceFactors
      (fanIns.map fun fanIn =>
        preluSecondMomentFactor slope fanIn
          (hePReLUWeightVariance slope fanIn))
      initial =
      initial := by
  rw [runVarianceFactors_eq_prod_mul]
  have allOne :
      fanIns.map (fun fanIn =>
        preluSecondMomentFactor slope fanIn
          (hePReLUWeightVariance slope fanIn)) =
        fanIns.map (fun _ => (1 : ℝ)) := by
    apply List.map_congr_left
    intro fanIn fanIn_mem
    rw [preluSecondMomentFactor_he slope fanIn
      (nonzero fanIn fanIn_mem)]
  rw [allOne]
  simp

/-- Using the ReLU variance `2 / fanIn` with a nonzero PReLU slope leaves
the uncompensated multiplier `1 + slope^2`. -/
theorem preluFactor_with_relu_scale
    (slope fanIn : ℝ) (fanIn_ne : fanIn ≠ 0) :
    preluSecondMomentFactor slope fanIn (2 / fanIn) =
      1 + slope ^ 2 := by
  simp only [preluSecondMomentFactor]
  field_simp [fanIn_ne]

/-- Therefore the ReLU scale strictly amplifies second moments for every
nonzero PReLU slope. -/
theorem preluFactor_with_relu_scale_gt_one
    (slope fanIn : ℝ) (slope_ne : slope ≠ 0)
    (fanIn_ne : fanIn ≠ 0) :
    1 < preluSecondMomentFactor slope fanIn (2 / fanIn) := by
  rw [preluFactor_with_relu_scale slope fanIn fanIn_ne]
  nlinarith [sq_pos_of_ne_zero slope_ne]

/-- The source initialization condition is intentionally inapplicable at
zero fan-in: Lean's totalized division yields a zero, not unit, multiplier. -/
theorem zero_fanIn_does_not_preserve (slope : ℝ) :
    preluSecondMomentFactor slope 0
      (hePReLUWeightVariance slope 0) = 0 := by
  simp [preluSecondMomentFactor, hePReLUWeightVariance]

/-- Four linear-slope layers initialized with the ReLU scale multiply the
second moment by sixteen instead of preserving it. -/
theorem relu_scale_on_linear_slope_explodes :
    runVarianceFactors
      (List.replicate 4
        (preluSecondMomentFactor 1 2 (2 / 2)))
      1 = 16 := by
  rw [runVarianceFactors_eq_prod_mul]
  norm_num [preluSecondMomentFactor]

#print axioms runVarianceFactors_eq_prod_mul
#print axioms preluSecondMomentFactor_he
#print axioms runVarianceFactors_he
#print axioms preluFactor_with_relu_scale_gt_one
#print axioms zero_fanIn_does_not_preserve
#print axioms relu_scale_on_linear_slope_explodes

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
