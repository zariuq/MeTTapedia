import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport

/-!
# Decoupled weight decay and adaptive preconditioning

Loshchilov and Hutter, *Decoupled Weight Decay Regularization*
(arXiv:1711.05101), separate parameter shrinkage from the preconditioned loss
gradient.  The primary PDF has SHA-256
`9d5af48931e773d6983d167e15c06ef594475b751c1f263827f5ed3c7a00d0d8`.

This file recovers source Propositions 1--3 coordinatewise and strengthens
their boundary statement.  Ordinary scalar preconditioning makes decoupled
decay equivalent to one scalar quadratic penalty.  A fixed diagonal
preconditioner instead requires a scale-adjusted coordinate penalty.  If two
coordinates have different preconditioner values, no single scalar penalty
can reproduce decoupled decay on every parameter and gradient.  If a
preconditioner changes over time at one coordinate, no single fixed
coordinatewise quadratic penalty can reproduce both steps.

These are exact update equalities.  They do not claim that either
regularization choice has better generalization, nor do they identify a raw
credit direction with the optimizer-transported parameter displacement.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DecoupledWeightDecay

noncomputable section

variable {Index : Type*}

/-- A diagonal-preconditioned loss-gradient step. -/
def adaptiveGradientStep
    (preconditioner : Index → ℝ)
    (learningRate : ℝ)
    (parameter gradient : Index → ℝ) : Index → ℝ :=
  fun index =>
    parameter index -
      learningRate * preconditioner index * gradient index

/-- Weight decay applied outside the diagonal preconditioner. -/
def decoupledWeightDecayStep
    (preconditioner : Index → ℝ)
    (learningRate decay : ℝ)
    (parameter gradient : Index → ℝ) : Index → ℝ :=
  fun index =>
    (1 - decay) * parameter index -
      learningRate * preconditioner index * gradient index

/-- A diagonal-preconditioned step after adding a coordinatewise quadratic
penalty gradient to the loss gradient. A scalar L2 penalty is the constant
case of `penalty`. -/
def coordinatePenaltyStep
    (preconditioner penalty : Index → ℝ)
    (learningRate : ℝ)
    (parameter gradient : Index → ℝ) : Index → ℝ :=
  fun index =>
    parameter index -
      learningRate * preconditioner index *
        (gradient index + penalty index * parameter index)

theorem decoupled_sub_adaptive_component
    (preconditioner : Index → ℝ)
    (learningRate decay : ℝ)
    (parameter gradient : Index → ℝ)
    (index : Index) :
    decoupledWeightDecayStep preconditioner learningRate decay
          parameter gradient index -
        adaptiveGradientStep preconditioner learningRate
          parameter gradient index =
      -decay * parameter index := by
  simp only [decoupledWeightDecayStep, adaptiveGradientStep]
  ring

theorem penalty_sub_adaptive_component
    (preconditioner penalty : Index → ℝ)
    (learningRate : ℝ)
    (parameter gradient : Index → ℝ)
    (index : Index) :
    coordinatePenaltyStep preconditioner penalty learningRate
          parameter gradient index -
        adaptiveGradientStep preconditioner learningRate
          parameter gradient index =
      -(learningRate * preconditioner index * penalty index) *
        parameter index := by
  simp only [coordinatePenaltyStep, adaptiveGradientStep]
  ring

/-- Exact discrepancy between coordinatewise quadratic regularization and
decoupled decay. -/
theorem penalty_sub_decoupled_component
    (preconditioner penalty : Index → ℝ)
    (learningRate decay : ℝ)
    (parameter gradient : Index → ℝ)
    (index : Index) :
    coordinatePenaltyStep preconditioner penalty learningRate
          parameter gradient index -
        decoupledWeightDecayStep preconditioner learningRate decay
          parameter gradient index =
      (decay -
          learningRate * preconditioner index * penalty index) *
        parameter index := by
  simp only [coordinatePenaltyStep, decoupledWeightDecayStep]
  ring

/-- A coordinate penalty exactly reproduces decoupled decay whenever its
preconditioned coefficient equals the declared decay at every coordinate. -/
theorem coordinatePenaltyStep_eq_decoupled
    {preconditioner penalty : Index → ℝ}
    {learningRate decay : ℝ}
    (coefficientMatch :
      ∀ index,
        learningRate * preconditioner index * penalty index = decay)
    (parameter gradient : Index → ℝ) :
    coordinatePenaltyStep preconditioner penalty learningRate
        parameter gradient =
      decoupledWeightDecayStep preconditioner learningRate decay
        parameter gradient := by
  funext index
  specialize coefficientMatch index
  simp only [coordinatePenaltyStep, decoupledWeightDecayStep]
  calc
    parameter index -
          learningRate * preconditioner index *
            (gradient index + penalty index * parameter index) =
        parameter index -
          learningRate * preconditioner index * gradient index -
          (learningRate * preconditioner index * penalty index) *
            parameter index := by ring
    _ = parameter index -
          learningRate * preconditioner index * gradient index -
          decay * parameter index := by rw [coefficientMatch]
    _ = (1 - decay) * parameter index -
          learningRate * preconditioner index * gradient index := by ring

/-! ## Source Propositions 1 and 3 -/

/-- Source Proposition 1: for unpreconditioned SGD, the scalar L2 coefficient
`decay / learningRate` reproduces per-step decay exactly. -/
theorem standardSGD_weightDecay_eq_scalarL2
    {learningRate decay : ℝ}
    (learningRateNeZero : learningRate ≠ 0)
    (parameter gradient : Index → ℝ) :
    coordinatePenaltyStep (fun _ => 1)
        (fun _ => decay / learningRate) learningRate
        parameter gradient =
      decoupledWeightDecayStep (fun _ => 1)
        learningRate decay parameter gradient := by
  apply coordinatePenaltyStep_eq_decoupled
  intro index
  field_simp [learningRateNeZero]

/-- Inverse coordinate scales are the fixed diagonal preconditioner used in
source Proposition 3. -/
def inverseScalePreconditioner
    (scale : Index → ℝ) : Index → ℝ :=
  fun index => 1 / scale index

/-- Source Proposition 3: with fixed diagonal inverse scale, the exact
equivalent quadratic penalty weights coordinate `i` by
`decay * scale i / learningRate`. -/
theorem fixedDiagonal_weightDecay_eq_scaleAdjustedPenalty
    {scale : Index → ℝ}
    {learningRate decay : ℝ}
    (learningRateNeZero : learningRate ≠ 0)
    (scaleNeZero : ∀ index, scale index ≠ 0)
    (parameter gradient : Index → ℝ) :
    coordinatePenaltyStep (inverseScalePreconditioner scale)
        (fun index => decay * scale index / learningRate)
        learningRate parameter gradient =
      decoupledWeightDecayStep (inverseScalePreconditioner scale)
        learningRate decay parameter gradient := by
  apply coordinatePenaltyStep_eq_decoupled
  intro index
  simp only [inverseScalePreconditioner]
  field_simp [learningRateNeZero, scaleNeZero index]

/-! ## Necessity and non-equivalence boundaries -/

/-- Equality on every parameter and gradient forces the coordinatewise
coefficient equation. Testing one basis parameter is sufficient. -/
theorem allInputs_equivalent_implies_coordinateMatch
    {preconditioner penalty : Index → ℝ}
    {learningRate decay : ℝ}
    (equivalent :
      ∀ parameter gradient : Index → ℝ,
        coordinatePenaltyStep preconditioner penalty learningRate
            parameter gradient =
          decoupledWeightDecayStep preconditioner learningRate decay
            parameter gradient)
    (index : Index) :
    learningRate * preconditioner index * penalty index = decay := by
  classical
  let probe : Index → ℝ :=
    fun candidate => if candidate = index then 1 else 0
  have atIndex :=
    congrFun (equivalent probe (fun _ => 0)) index
  simp [coordinatePenaltyStep, decoupledWeightDecayStep, probe] at atIndex
  linarith

/-- Source Proposition 2, in a finite-coordinate-free form: two unequal
diagonal preconditioner entries rule out one scalar L2 coefficient whenever
decay is nonzero. -/
theorem no_scalarPenalty_of_nonuniform_preconditioner
    {preconditioner : Index → ℝ}
    {learningRate decay : ℝ}
    (decayNeZero : decay ≠ 0)
    {left right : Index}
    (preconditionerNe :
      preconditioner left ≠ preconditioner right) :
    ¬ ∃ scalarPenalty : ℝ,
        ∀ parameter gradient : Index → ℝ,
          coordinatePenaltyStep preconditioner
              (fun _ => scalarPenalty) learningRate
              parameter gradient =
            decoupledWeightDecayStep preconditioner learningRate decay
              parameter gradient := by
  rintro ⟨scalarPenalty, equivalent⟩
  have leftMatch :=
    allInputs_equivalent_implies_coordinateMatch equivalent left
  have rightMatch :=
    allInputs_equivalent_implies_coordinateMatch equivalent right
  have factorNeZero : learningRate * scalarPenalty ≠ 0 := by
    intro factorZero
    apply decayNeZero
    calc
      decay = (learningRate * scalarPenalty) * preconditioner left := by
        nlinarith [leftMatch]
      _ = 0 := by rw [factorZero, zero_mul]
  apply preconditionerNe
  apply mul_left_cancel₀ factorNeZero
  calc
    (learningRate * scalarPenalty) * preconditioner left = decay := by
      nlinarith [leftMatch]
    _ = (learningRate * scalarPenalty) * preconditioner right := by
      nlinarith [rightMatch]

/-- The source fixed-preconditioner interpretation cannot be promoted to one
static quadratic regularizer when the same coordinate's preconditioner changes
between steps. -/
theorem no_fixedPenalty_matches_changed_preconditioner
    {first second : Index → ℝ}
    {learningRate decay : ℝ}
    (decayNeZero : decay ≠ 0)
    {index : Index}
    (changed : first index ≠ second index) :
    ¬ ∃ penalty : Index → ℝ,
        (∀ parameter gradient : Index → ℝ,
          coordinatePenaltyStep first penalty learningRate
              parameter gradient =
            decoupledWeightDecayStep first learningRate decay
              parameter gradient) ∧
        (∀ parameter gradient : Index → ℝ,
          coordinatePenaltyStep second penalty learningRate
              parameter gradient =
            decoupledWeightDecayStep second learningRate decay
              parameter gradient) := by
  rintro ⟨penalty, firstEquivalent, secondEquivalent⟩
  have firstMatch :=
    allInputs_equivalent_implies_coordinateMatch firstEquivalent index
  have secondMatch :=
    allInputs_equivalent_implies_coordinateMatch secondEquivalent index
  have factorNeZero : learningRate * penalty index ≠ 0 := by
    intro factorZero
    apply decayNeZero
    calc
      decay = (learningRate * penalty index) * first index := by
        nlinarith [firstMatch]
      _ = 0 := by rw [factorZero, zero_mul]
  apply changed
  apply mul_left_cancel₀ factorNeZero
  calc
    (learningRate * penalty index) * first index = decay := by
      nlinarith [firstMatch]
    _ = (learningRate * penalty index) * second index := by
      nlinarith [secondMatch]

/-! ## Executable two-coordinate fixture -/

def fixturePreconditioner : Fin 2 → ℝ := ![1, 2]
def fixtureParameter : Fin 2 → ℝ := ![1, 1]
def fixtureZeroGradient : Fin 2 → ℝ := ![0, 0]

/-- Decoupled decay shrinks both zero-gradient coordinates uniformly, while
one scalar L2 coefficient is distorted by the unequal preconditioner. -/
theorem scalarPenalty_distorts_nonuniform_coordinates :
    decoupledWeightDecayStep fixturePreconditioner 1 (1 / 4)
          fixtureParameter fixtureZeroGradient 0 = 3 / 4 ∧
      decoupledWeightDecayStep fixturePreconditioner 1 (1 / 4)
          fixtureParameter fixtureZeroGradient 1 = 3 / 4 ∧
      coordinatePenaltyStep fixturePreconditioner (fun _ => 1 / 4) 1
          fixtureParameter fixtureZeroGradient 0 = 3 / 4 ∧
      coordinatePenaltyStep fixturePreconditioner (fun _ => 1 / 4) 1
          fixtureParameter fixtureZeroGradient 1 = 1 / 2 := by
  norm_num [decoupledWeightDecayStep, coordinatePenaltyStep,
    fixturePreconditioner, fixtureParameter, fixtureZeroGradient]

end

end DecoupledWeightDecay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.standardSGD_weightDecay_eq_scalarL2
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.fixedDiagonal_weightDecay_eq_scaleAdjustedPenalty
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.allInputs_equivalent_implies_coordinateMatch
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.no_scalarPenalty_of_nonuniform_preconditioner
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.no_fixedPenalty_matches_changed_preconditioner
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay.scalarPenalty_distorts_nonuniform_coordinates
