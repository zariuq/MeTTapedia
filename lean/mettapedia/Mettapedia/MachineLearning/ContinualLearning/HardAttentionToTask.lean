import Mathlib.Tactic

/-!
# Hard attention masks for continual learning

Serrà et al. (2018), *Overcoming Catastrophic Forgetting with Hard Attention
to the Task*, learn one attention coordinate per task and unit,

`attention = sigmoid (scale * embedding)`,

accumulate prior attention by elementwise maximum, and multiply a weight
gradient by

`1 - min previousOutputAttention previousInputAttention`.

This file formalizes those equations coordinatewise.  Cumulative attention is
monotone and idempotent.  Under the declared `[0,1]` range, the gradient gate
also lies in `[0,1]`; a connection whose two endpoints are fully attended is
exactly frozen, while a connection with an unused endpoint remains fully
plastic.  Arbitrarily many later optimizer steps therefore preserve every
fully attended scalar connection.  For soft masks, an exact finite-step drift
identity replaces the binary preservation claim.

The source's capacity regularizer is also isolated.  Its numerator is between
zero and the remaining-capacity denominator, so the normalized penalty lies
in `[0,1]` whenever capacity remains.  At complete capacity both numerator and
denominator vanish; this boundary is explicit rather than silently treated as
evidence of available plasticity.

Attention-range assumptions are load-bearing: executable fixtures show that
out-of-range cumulative attention can reverse or amplify a gradient.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace HardAttentionToTask

noncomputable section

/-- Logistic gate used by the source to learn an almost-binary unit mask. -/
def sigmoid (value : ℝ) : ℝ :=
  1 / (1 + Real.exp (-value))

/-- Equation (1): scaled task embedding followed by the logistic gate. -/
def attention (scale embedding : ℝ) : ℝ :=
  sigmoid (scale * embedding)

/-- At zero hardness every task embedding activates a unit by exactly one
half, as stated in the source's annealing discussion. -/
@[simp] theorem attention_zero_scale (embedding : ℝ) :
    attention 0 embedding = 1 / 2 := by
  norm_num [attention, sigmoid]

/-- A learned logistic attention is always strictly positive. -/
theorem attention_pos (scale embedding : ℝ) :
    0 < attention scale embedding := by
  unfold attention sigmoid
  positivity

/-- A learned logistic attention is always strictly below one. -/
theorem attention_lt_one (scale embedding : ℝ) :
    attention scale embedding < 1 := by
  unfold attention sigmoid
  have expPositive : 0 < Real.exp (-(scale * embedding)) :=
    Real.exp_pos _
  have denominatorGreater : 1 < 1 + Real.exp (-(scale * embedding)) := by
    linarith
  exact (div_lt_one (by positivity)).2 denominatorGreater

/-- Elementwise cumulative attention after one task. -/
def cumulativeAttention (current previous : ℝ) : ℝ :=
  max current previous

theorem current_le_cumulativeAttention (current previous : ℝ) :
    current ≤ cumulativeAttention current previous :=
  le_max_left _ _

theorem previous_le_cumulativeAttention (current previous : ℝ) :
    previous ≤ cumulativeAttention current previous :=
  le_max_right _ _

/-- Cumulative attention stays in the legal range when both inputs do. -/
theorem cumulativeAttention_mem_Icc
    {current previous : ℝ}
    (currentRange : current ∈ Set.Icc (0 : ℝ) 1)
    (previousRange : previous ∈ Set.Icc (0 : ℝ) 1) :
    cumulativeAttention current previous ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_trans currentRange.1 (current_le_cumulativeAttention _ _)
  · exact max_le currentRange.2 previousRange.2

/-- Reassimilating the same task mask is idempotent. -/
@[simp] theorem cumulativeAttention_self (value : ℝ) :
    cumulativeAttention value value = value :=
  max_self _

/-- Chronological accumulation of task masks by elementwise maximum. -/
def accumulateAttention : ℝ → List ℝ → ℝ
  | previous, [] => previous
  | previous, current :: rest =>
      accumulateAttention (cumulativeAttention current previous) rest

/-- No later task can reduce a previously accumulated attention value. -/
theorem initial_le_accumulateAttention
    (previous : ℝ) (tasks : List ℝ) :
    previous ≤ accumulateAttention previous tasks := by
  induction tasks generalizing previous with
  | nil =>
      rfl
  | cons current rest inductionHypothesis =>
      exact
        (previous_le_cumulativeAttention current previous).trans
          (inductionHypothesis (cumulativeAttention current previous))

/-- A fully occupied coordinate remains fully occupied when every later mask
is at most one. -/
theorem accumulateAttention_one
    (tasks : List ℝ)
    (bounded : ∀ value ∈ tasks, value ≤ 1) :
    accumulateAttention 1 tasks = 1 := by
  induction tasks with
  | nil =>
      rfl
  | cons current rest inductionHypothesis =>
      have currentBound : current ≤ 1 :=
        bounded current (by simp)
      have restBound : ∀ value ∈ rest, value ≤ 1 := by
        intro value member
        exact bounded value (by simp [member])
      simp only [accumulateAttention, cumulativeAttention]
      rw [max_eq_right currentBound]
      exact inductionHypothesis restBound

/-! ## Equation (2): backward gradient gating -/

/-- Reverse-minimum gate for one weight coordinate. -/
def gradientGate
    (previousOutputAttention previousInputAttention : ℝ) : ℝ :=
  1 - min previousOutputAttention previousInputAttention

/-- Gradient after conditioning by prior cumulative attention. -/
def gatedGradient
    (previousOutputAttention previousInputAttention gradient : ℝ) : ℝ :=
  gradientGate previousOutputAttention previousInputAttention * gradient

/-- Legal attention coordinates produce a gate between zero and one. -/
theorem gradientGate_mem_Icc
    {previousOutputAttention previousInputAttention : ℝ}
    (outputRange : previousOutputAttention ∈ Set.Icc (0 : ℝ) 1)
    (inputRange : previousInputAttention ∈ Set.Icc (0 : ℝ) 1) :
    gradientGate previousOutputAttention previousInputAttention ∈
      Set.Icc (0 : ℝ) 1 := by
  have minNonnegative :
      0 ≤ min previousOutputAttention previousInputAttention :=
    le_min outputRange.1 inputRange.1
  have minAtMostOne :
      min previousOutputAttention previousInputAttention ≤ 1 :=
    (min_le_left _ _).trans outputRange.2
  constructor <;> simp only [gradientGate] <;> linarith

/-- A connection between two fully attended units is exactly frozen. -/
@[simp] theorem gatedGradient_one_one (gradient : ℝ) :
    gatedGradient 1 1 gradient = 0 := by
  simp [gatedGradient, gradientGate]

/-- An unused output endpoint leaves the connection fully plastic. -/
theorem gatedGradient_zero_output
    {previousInputAttention gradient : ℝ}
    (inputNonnegative : 0 ≤ previousInputAttention) :
    gatedGradient 0 previousInputAttention gradient = gradient := by
  simp [gatedGradient, gradientGate, min_eq_left inputNonnegative]

/-- An unused input endpoint leaves the connection fully plastic. -/
theorem gatedGradient_zero_input
    {previousOutputAttention gradient : ℝ}
    (outputNonnegative : 0 ≤ previousOutputAttention) :
    gatedGradient previousOutputAttention 0 gradient = gradient := by
  simp [gatedGradient, gradientGate, min_eq_right outputNonnegative]

/-- One optimizer step using the HAT-conditioned gradient. -/
def applyGatedUpdate
    (previousOutputAttention previousInputAttention : ℝ)
    (weight rate gradient : ℝ) : ℝ :=
  weight - rate *
    gatedGradient
      previousOutputAttention previousInputAttention gradient

/-- Exact finite displacement of a softly protected connection. -/
theorem applyGatedUpdate_sub
    (previousOutputAttention previousInputAttention : ℝ)
    (weight rate gradient : ℝ) :
    applyGatedUpdate
          previousOutputAttention previousInputAttention
          weight rate gradient -
        weight =
      -rate *
        gradientGate previousOutputAttention previousInputAttention *
        gradient := by
  simp [applyGatedUpdate, gatedGradient]
  ring

/-- Soft masks give a quantitative drift identity, not exact freezing. -/
theorem abs_applyGatedUpdate_sub
    {previousOutputAttention previousInputAttention : ℝ}
    (outputRange : previousOutputAttention ∈ Set.Icc (0 : ℝ) 1)
    (inputRange : previousInputAttention ∈ Set.Icc (0 : ℝ) 1)
    (weight rate gradient : ℝ) :
    |applyGatedUpdate
          previousOutputAttention previousInputAttention
          weight rate gradient -
        weight| =
      |rate| *
        gradientGate previousOutputAttention previousInputAttention *
        |gradient| := by
  rw [applyGatedUpdate_sub, abs_mul, abs_mul, abs_neg]
  rw [abs_of_nonneg (gradientGate_mem_Icc outputRange inputRange).1]

structure OptimizerStep where
  rate : ℝ
  gradient : ℝ

def applyFullyProtectedStep
    (weight : ℝ) (step : OptimizerStep) : ℝ :=
  applyGatedUpdate 1 1 weight step.rate step.gradient

def runFullyProtectedSteps
    (weight : ℝ) (steps : List OptimizerStep) : ℝ :=
  steps.foldl applyFullyProtectedStep weight

/-- Any finite ordered optimizer trace preserves a connection whose two
endpoints are fully occupied by prior tasks. -/
theorem runFullyProtectedSteps_eq
    (weight : ℝ) (steps : List OptimizerStep) :
    runFullyProtectedSteps weight steps = weight := by
  induction steps generalizing weight with
  | nil =>
      rfl
  | cons step rest inductionHypothesis =>
      change
        runFullyProtectedSteps
            (applyFullyProtectedStep weight step) rest =
          weight
      rw [inductionHypothesis]
      simp [applyFullyProtectedStep, applyGatedUpdate]

/-! ## Equations (4)--(5): remaining-capacity regularization -/

/-- Unnormalized current-task attention allocated to capacity not already
claimed by prior tasks. -/
def capacityNumerator
    [Fintype UnitIndex]
    (current previous : UnitIndex → ℝ) : ℝ :=
  ∑ unit, current unit * (1 - previous unit)

/-- Total remaining attention capacity. -/
def remainingCapacity
    [Fintype UnitIndex]
    (previous : UnitIndex → ℝ) : ℝ :=
  ∑ unit, (1 - previous unit)

/-- Source capacity regularizer for one or several layers after flattening
their unit indices into a finite type. -/
def capacityPenalty
    [Fintype UnitIndex]
    (current previous : UnitIndex → ℝ) : ℝ :=
  capacityNumerator current previous / remainingCapacity previous

theorem capacityNumerator_nonnegative
    [Fintype UnitIndex]
    {current previous : UnitIndex → ℝ}
    (currentRange : ∀ unit, current unit ∈ Set.Icc (0 : ℝ) 1)
    (previousRange : ∀ unit, previous unit ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ capacityNumerator current previous := by
  apply Finset.sum_nonneg
  intro unit _
  exact mul_nonneg (currentRange unit).1 (by linarith [(previousRange unit).2])

theorem capacityNumerator_le_remainingCapacity
    [Fintype UnitIndex]
    {current previous : UnitIndex → ℝ}
    (currentRange : ∀ unit, current unit ∈ Set.Icc (0 : ℝ) 1)
    (previousRange : ∀ unit, previous unit ∈ Set.Icc (0 : ℝ) 1) :
    capacityNumerator current previous ≤ remainingCapacity previous := by
  apply Finset.sum_le_sum
  intro unit _
  have remainingNonnegative : 0 ≤ 1 - previous unit := by
    linarith [(previousRange unit).2]
  nlinarith [(currentRange unit).1, (currentRange unit).2]

/-- While some capacity remains, the normalized source regularizer lies in
`[0,1]`. -/
theorem capacityPenalty_mem_Icc
    [Fintype UnitIndex]
    {current previous : UnitIndex → ℝ}
    (currentRange : ∀ unit, current unit ∈ Set.Icc (0 : ℝ) 1)
    (previousRange : ∀ unit, previous unit ∈ Set.Icc (0 : ℝ) 1)
    (capacityPositive : 0 < remainingCapacity previous) :
    capacityPenalty current previous ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg
      (capacityNumerator_nonnegative currentRange previousRange)
      capacityPositive.le
  · exact (div_le_one capacityPositive).2
      (capacityNumerator_le_remainingCapacity currentRange previousRange)

/-- A previously fully occupied unit contributes zero to both the source
regularizer's numerator and its remaining-capacity denominator. -/
theorem occupied_unit_contribution_zero (current : ℝ) :
    current * (1 - (1 : ℝ)) = 0 ∧ 1 - (1 : ℝ) = 0 := by
  norm_num

/-- Complete prior occupancy exhausts capacity: both terms in the normalized
regularizer vanish. -/
theorem fullAttention_exhausts_capacity
    [Fintype UnitIndex]
    (current : UnitIndex → ℝ) :
    capacityNumerator current (fun _ => 1) = 0 ∧
      remainingCapacity (fun _ : UnitIndex => 1) = 0 := by
  simp [capacityNumerator, remainingCapacity]

/-! ## Executable range boundaries -/

/-- Attention above one reverses the nominal gradient. -/
theorem outOfRange_attention_reverses_gradient :
    gatedGradient 2 2 3 = -3 := by
  norm_num [gatedGradient, gradientGate]

/-- Negative attention amplifies the nominal gradient. -/
theorem negative_attention_amplifies_gradient :
    gatedGradient (-1) (-1) 3 = 6 := by
  norm_num [gatedGradient, gradientGate]

#print axioms attention_zero_scale
#print axioms cumulativeAttention_mem_Icc
#print axioms gradientGate_mem_Icc
#print axioms runFullyProtectedSteps_eq
#print axioms capacityPenalty_mem_Icc
#print axioms fullAttention_exhausts_capacity
#print axioms outOfRange_attention_reverses_gradient

end

end HardAttentionToTask

end Mettapedia.MachineLearning.ContinualLearning
