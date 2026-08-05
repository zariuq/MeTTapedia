import Mathlib

/-!
# Reduced edge-of-stability feedback dynamics

Cohen et al., *Gradient Descent on Neural Networks Typically Occurs at the
Edge of Stability* (arXiv:2103.00065), recall that one scalar quadratic mode
with curvature `a` and learning rate `η` multiplies its error by `1 - η * a`.
The classical stability boundary is therefore `a = 2 / η`.

Damian, Nichani, and Lee, *Self-Stabilization: The Implicit Bias of Gradient
Descent at the Edge of Stability* (arXiv:2209.15594), derive a reduced
two-coordinate model near that boundary.  If `x` is displacement in the top
eigendirection and `y` is sharpness relative to `2 / η`, their equation (3),
with approximation signs removed to declare the reduced model itself, is

`x⁺ = -(1 + η y) x`,

`y⁺ = y + η (α - β x² / 2)`.

This file develops exact finite properties of that declared reduced map.  It
connects its first coordinate to the scalar quadratic multiplier, identifies
the exact feedback threshold `β x² = 2 α`, proves growth and contraction
regions, and exhibits the boundary two-cycle.  It also records a necessary
negative boundary: with no unstable-coordinate amplitude, the stabilizing
feedback vanishes and progressive sharpening continues arithmetically.

These results concern the reduced dynamics only.  They do not assert that an
arbitrary neural-network loss satisfies the Taylor, eigengap, or remainder
hypotheses used to derive the approximation in the source paper.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace EdgeOfStabilityFeedback

noncomputable section

/-- Displacement in the unstable eigendirection and sharpness offset from
`2 / learningRate`. -/
@[ext]
structure ReducedState where
  unstable : ℝ
  sharpnessOffset : ℝ

/-- The exact map obtained by declaring the source paper's reduced equation
(3) as a discrete dynamical system. -/
def step
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) : ReducedState :=
  { unstable :=
      -(1 + learningRate * state.sharpnessOffset) * state.unstable
    sharpnessOffset :=
      state.sharpnessOffset +
        learningRate *
          (progressiveForce -
            stabilizationForce * state.unstable ^ 2 / 2) }

@[simp] theorem step_unstable
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) :
    (step learningRate progressiveForce stabilizationForce state).unstable =
      -(1 + learningRate * state.sharpnessOffset) * state.unstable := rfl

@[simp] theorem step_sharpnessOffset
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) :
    (step learningRate progressiveForce stabilizationForce state).sharpnessOffset =
      state.sharpnessOffset +
        learningRate *
          (progressiveForce -
            stabilizationForce * state.unstable ^ 2 / 2) := rfl

/-- Curvature represented by a sharpness offset in the reduced chart. -/
def effectiveSharpness
    (learningRate : ℝ) (state : ReducedState) : ℝ :=
  2 / learningRate + state.sharpnessOffset

/-- The unstable-coordinate update is exactly the scalar quadratic multiplier
at the effective sharpness. -/
theorem step_unstable_eq_quadratic_multiplier
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) (learningRate_ne : learningRate ≠ 0) :
    (step learningRate progressiveForce stabilizationForce state).unstable =
      (1 - learningRate * effectiveSharpness learningRate state) *
        state.unstable := by
  simp only [step_unstable, effectiveSharpness]
  field_simp [learningRate_ne]
  ring

/-- Positive offset is exactly the above-quadratic-threshold region. -/
theorem effectiveSharpness_above_edge_iff
    (learningRate : ℝ) (state : ReducedState) :
    2 / learningRate <
        effectiveSharpness learningRate state ↔
      0 < state.sharpnessOffset := by
  simp [effectiveSharpness]

/-- One-step displacement of the sharpness coordinate. -/
def sharpnessDrift
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) : ℝ :=
  (step learningRate progressiveForce stabilizationForce state).sharpnessOffset -
    state.sharpnessOffset

theorem sharpnessDrift_eq
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) :
    sharpnessDrift learningRate progressiveForce stabilizationForce state =
      learningRate *
        (progressiveForce -
          stabilizationForce * state.unstable ^ 2 / 2) := by
  simp [sharpnessDrift]

/-- Exact self-stabilizing side of the feedback threshold. -/
theorem sharpnessOffset_decreases_iff
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) (learningRate_pos : 0 < learningRate) :
    (step learningRate progressiveForce stabilizationForce state).sharpnessOffset <
        state.sharpnessOffset ↔
      2 * progressiveForce <
        stabilizationForce * state.unstable ^ 2 := by
  simp only [step_sharpnessOffset]
  constructor <;> intro hypothesis <;> nlinarith

/-- Exact progressive-sharpening side of the feedback threshold. -/
theorem sharpnessOffset_increases_iff
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) (learningRate_pos : 0 < learningRate) :
    state.sharpnessOffset <
        (step learningRate progressiveForce stabilizationForce state).sharpnessOffset ↔
      stabilizationForce * state.unstable ^ 2 <
        2 * progressiveForce := by
  simp only [step_sharpnessOffset]
  constructor <;> intro hypothesis <;> nlinarith

/-- Exact balance surface of the reduced negative-feedback loop. -/
theorem sharpnessOffset_preserved_iff
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) (learningRate_ne : learningRate ≠ 0) :
    (step learningRate progressiveForce stabilizationForce state).sharpnessOffset =
        state.sharpnessOffset ↔
      stabilizationForce * state.unstable ^ 2 =
        2 * progressiveForce := by
  simp only [step_sharpnessOffset]
  constructor
  · intro hypothesis
    have product_zero :
        learningRate *
          (progressiveForce -
            stabilizationForce * state.unstable ^ 2 / 2) = 0 := by
      linarith
    have force_zero : progressiveForce -
        stabilizationForce * state.unstable ^ 2 / 2 = 0 := by
      exact (mul_eq_zero.mp product_zero).resolve_left learningRate_ne
    nlinarith [force_zero]
  · intro hypothesis
    have force_zero : progressiveForce -
        stabilizationForce * state.unstable ^ 2 / 2 = 0 := by
      nlinarith
    rw [force_zero, mul_zero, add_zero]

/-- Exact absolute-amplitude multiplier for the unstable coordinate. -/
theorem abs_step_unstable
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState) :
    |(step learningRate progressiveForce stabilizationForce state).unstable| =
      |1 + learningRate * state.sharpnessOffset| *
        |state.unstable| := by
  simp only [step_unstable, abs_mul, abs_neg]

/-- Above the edge, a nonzero unstable component grows in absolute value. -/
theorem unstableAmplitude_grows_above_edge
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState)
    (learningRate_pos : 0 < learningRate)
    (aboveEdge : 0 < state.sharpnessOffset)
    (unstable_ne : state.unstable ≠ 0) :
    |state.unstable| <
      |(step learningRate progressiveForce stabilizationForce state).unstable| := by
  rw [abs_step_unstable]
  have factor_gt : 1 < 1 + learningRate * state.sharpnessOffset := by
    nlinarith
  rw [abs_of_pos (by linarith : 0 < 1 + learningRate * state.sharpnessOffset)]
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right factor_gt (abs_pos.mpr unstable_ne))

/-- Just below the edge, but still inside the scalar quadratic stability
interval, a nonzero unstable component contracts in absolute value. -/
theorem unstableAmplitude_contracts_below_edge
    (learningRate progressiveForce stabilizationForce : ℝ)
    (state : ReducedState)
    (lowerStable : -2 < learningRate * state.sharpnessOffset)
    (belowEdge : learningRate * state.sharpnessOffset < 0)
    (unstable_ne : state.unstable ≠ 0) :
    |(step learningRate progressiveForce stabilizationForce state).unstable| <
      |state.unstable| := by
  rw [abs_step_unstable]
  have factor_lt : |1 + learningRate * state.sharpnessOffset| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right factor_lt (abs_pos.mpr unstable_ne))

/-- On the balance surface at zero sharpness offset, one step flips the
unstable coordinate and preserves the offset. -/
theorem boundary_step
    (learningRate progressiveForce stabilizationForce unstable : ℝ)
    (balance :
      stabilizationForce * unstable ^ 2 = 2 * progressiveForce) :
    step learningRate progressiveForce stabilizationForce
        ⟨unstable, 0⟩ =
      ⟨-unstable, 0⟩ := by
  apply ReducedState.ext
  · simp [step]
  · simp only [step, zero_add, mul_zero, add_zero]
    have force_zero :
        progressiveForce - stabilizationForce * unstable ^ 2 / 2 = 0 := by
      nlinarith [balance]
    rw [force_zero, mul_zero]

/-- The reduced dynamics have an exact period-two orbit on the nonzero balance
surface, rather than a fixed point in the signed unstable coordinate. -/
theorem boundary_twoCycle
    (learningRate progressiveForce stabilizationForce unstable : ℝ)
    (balance :
      stabilizationForce * unstable ^ 2 = 2 * progressiveForce) :
    step learningRate progressiveForce stabilizationForce
        (step learningRate progressiveForce stabilizationForce
          ⟨unstable, 0⟩) =
      ⟨unstable, 0⟩ := by
  rw [boundary_step learningRate progressiveForce stabilizationForce
    unstable balance]
  have negBalance :
      stabilizationForce * (-unstable) ^ 2 =
        2 * progressiveForce := by
    nlinarith
  rw [boundary_step learningRate progressiveForce stabilizationForce
    (-unstable) negBalance]
  simp

/-- With zero unstable-coordinate amplitude, the stabilizing term is absent. -/
theorem step_zero_unstable
    (learningRate progressiveForce stabilizationForce offset : ℝ) :
    step learningRate progressiveForce stabilizationForce ⟨0, offset⟩ =
      ⟨0, offset + learningRate * progressiveForce⟩ := by
  apply ReducedState.ext <;> simp [step]

/-- The zero-amplitude boundary remains invariant and its sharpness offset
follows an exact arithmetic progression. -/
theorem iterate_zero_unstable
    (learningRate progressiveForce stabilizationForce offset : ℝ)
    (steps : ℕ) :
    Nat.iterate
        (step learningRate progressiveForce stabilizationForce)
        steps ⟨0, offset⟩ =
      ⟨0, offset + (steps : ℝ) * learningRate * progressiveForce⟩ := by
  induction steps with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis,
        step_zero_unstable]
      apply ReducedState.ext
      · simp
      · simp only [Nat.cast_add, Nat.cast_one]
        ring

/-! ## Concrete positive and negative fixtures -/

/-- A large unstable amplitude above the edge grows, while its feedback drives
the sharpness offset from `1` down to `-2` in one step. -/
theorem selfStabilizing_crossing :
    step 1 1 2 ⟨2, 1⟩ = ⟨-4, -2⟩ := by
  norm_num [step]

/-- A state just below the edge contracts in unstable amplitude while
progressive sharpening raises its offset. -/
theorem stableSide_contraction :
    step 1 1 2 ⟨1 / 2, -1 / 2⟩ =
      ⟨-1 / 4, 1 / 4⟩ := by
  norm_num [step]

/-- The balance amplitude gives the exact sign-flipping two-cycle. -/
theorem boundary_twoCycle_example :
    step 1 1 2 (step 1 1 2 ⟨1, 0⟩) = ⟨1, 0⟩ := by
  norm_num [step]

/-- Without an unstable-coordinate amplitude, positive progressive force
raises sharpness forever; the negative-feedback mechanism is not automatic. -/
theorem zeroAmplitude_progressiveSharpening (steps : ℕ) :
    (Nat.iterate (step 1 1 2) steps ⟨0, 0⟩).sharpnessOffset =
      steps := by
  rw [iterate_zero_unstable]
  simp

#print axioms step_unstable_eq_quadratic_multiplier
#print axioms effectiveSharpness_above_edge_iff
#print axioms sharpnessOffset_decreases_iff
#print axioms sharpnessOffset_increases_iff
#print axioms sharpnessOffset_preserved_iff
#print axioms unstableAmplitude_grows_above_edge
#print axioms unstableAmplitude_contracts_below_edge
#print axioms boundary_twoCycle
#print axioms iterate_zero_unstable
#print axioms selfStabilizing_crossing
#print axioms stableSide_contraction
#print axioms boundary_twoCycle_example
#print axioms zeroAmplitude_progressiveSharpening

end

end EdgeOfStabilityFeedback

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
