import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.FastWeightMemory

/-!
# Recurrent fast-weight programmers

Irie, Schlag, Csordás, and Schmidhuber, *Going Beyond Linear Transformers
with Recurrent Fast Weight Programmers* (arXiv:2106.06295), add recurrence to
both sides of a fast-weight programmer.

* Source Equation (12) augments the forward fast-weight read with a second
  fast-weight matrix applied to an activated previous output.
* Source Equations (15)--(18) let the slow controller generate its next
  instruction from both the current input and the previous fast-network
  output.

This file gives a finite-dimensional transition semantics for both
constructions.  The two fast matrices use the source delta-rule update, and
the output theorem expands one recurrent step into its two old-memory reads
and two rank-one correction terms.  Zero recurrent memory and zero recurrent
write rate recover the feedforward fast-weight step.  Executable fixtures show
that the recurrent path is nontrivial: with the same current instruction and
forward state, changing only the previous output changes the result.

The activation is an explicit argument.  The source choices of softmax for
the fast recurrent query and tanh for the slow recurrent projection are
instances of this algebra.  No normalization, stability, capacity, or
empirical performance claim follows without separate hypotheses.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace RecurrentFastWeightProgrammer

noncomputable section

open FastWeightMemory

variable {Key Value : Type*} [Fintype Key] [Fintype Value]

/-- State of a recurrent fast-weight programmer: one input-facing fast
matrix, one output-recurrent fast matrix, and the previous output. -/
structure State (Key Value : Type*) where
  forwardMemory : Memory Value Key
  recurrentMemory : Memory Value Value
  output : Value → ℝ

/-- One controller-generated programming instruction.  Each fast matrix has
its own delta-rule value, key, and rate; the forward read has its own query. -/
structure Instruction (Key Value : Type*) where
  forwardKey : Key → ℝ
  forwardValue : Value → ℝ
  forwardRate : ℝ
  recurrentKey : Value → ℝ
  recurrentValue : Value → ℝ
  recurrentRate : ℝ
  query : Key → ℝ

/-- One recurrent fast-weight transition corresponding to the source's delta
updates followed by Equation (12). -/
def step
    (recurrentActivation : (Value → ℝ) → Value → ℝ)
    (state : State Key Value)
    (instruction : Instruction Key Value) :
    State Key Value :=
  let forwardMemory :=
    deltaWrite state.forwardMemory instruction.forwardRate
      instruction.forwardValue instruction.forwardKey
  let recurrentMemory :=
    deltaWrite state.recurrentMemory instruction.recurrentRate
      instruction.recurrentValue instruction.recurrentKey
  { forwardMemory := forwardMemory
    recurrentMemory := recurrentMemory
    output :=
      read forwardMemory instruction.query +
        read recurrentMemory (recurrentActivation state.output) }

/-- Exact one-step expansion: recurrence adds a second old-memory read and a
second delta correction to the ordinary forward fast-weight read. -/
theorem step_output_expansion
    (recurrentActivation : (Value → ℝ) → Value → ℝ)
    (state : State Key Value)
    (instruction : Instruction Key Value) :
    (step recurrentActivation state instruction).output =
      read state.forwardMemory instruction.query +
        (instruction.forwardRate *
            (instruction.forwardKey ⬝ᵥ instruction.query)) •
          (instruction.forwardValue -
            read state.forwardMemory instruction.forwardKey) +
        read state.recurrentMemory
          (recurrentActivation state.output) +
        (instruction.recurrentRate *
            (instruction.recurrentKey ⬝ᵥ
              recurrentActivation state.output)) •
          (instruction.recurrentValue -
            read state.recurrentMemory instruction.recurrentKey) := by
  change
    read
          (deltaWrite state.forwardMemory instruction.forwardRate
            instruction.forwardValue instruction.forwardKey)
          instruction.query +
        read
          (deltaWrite state.recurrentMemory instruction.recurrentRate
            instruction.recurrentValue instruction.recurrentKey)
          (recurrentActivation state.output) =
      _
  rw [read_deltaWrite, read_deltaWrite]
  abel

/-- With zero recurrent memory and zero recurrent write rate, the recurrent
programmer recovers the feedforward delta-rule fast-weight output exactly. -/
theorem step_output_eq_feedforward_of_zero_recurrent
    (recurrentActivation : (Value → ℝ) → Value → ℝ)
    (forwardMemory : Memory Value Key) (previousOutput : Value → ℝ)
    (instruction : Instruction Key Value)
    (recurrentRateZero : instruction.recurrentRate = 0) :
    (step recurrentActivation
        { forwardMemory := forwardMemory
          recurrentMemory := 0
          output := previousOutput }
        instruction).output =
      read
        (deltaWrite forwardMemory instruction.forwardRate
          instruction.forwardValue instruction.forwardKey)
        instruction.query := by
  rw [step_output_expansion, recurrentRateZero, read_deltaWrite]
  simp [FastWeightMemory.read]

/-! ## Recurrent slow-controller projection -/

variable {Input Feature : Type*} [Fintype Input]

/-- Shared algebraic core of source Equations (15)--(18), before the
coordinate-specific output nonlinearity: current-input projection plus
activated previous-output projection. -/
def recurrentControllerProjection
    (inputWeight : Matrix Feature Input ℝ)
    (recurrentWeight : Matrix Feature Value ℝ)
    (activation : (Value → ℝ) → Value → ℝ)
    (input : Input → ℝ) (previousOutput : Value → ℝ) :
    Feature → ℝ :=
  Matrix.mulVec inputWeight input +
    Matrix.mulVec recurrentWeight (activation previousOutput)

/-- Zero recurrent controller weights recover the feedforward slow
projection used by the nonrecurrent Delta Net. -/
theorem recurrentControllerProjection_zero_recurrent
    (inputWeight : Matrix Feature Input ℝ)
    (activation : (Value → ℝ) → Value → ℝ)
    (input : Input → ℝ) (previousOutput : Value → ℝ) :
    recurrentControllerProjection inputWeight 0 activation
        input previousOutput =
      Matrix.mulVec inputWeight input := by
  simp [recurrentControllerProjection]

/-! ## Executable nontriviality fixtures -/

abbrev Scalar := Fin 1

def identityActivation (value : Scalar → ℝ) : Scalar → ℝ :=
  value

def scalarInstruction : Instruction Scalar Scalar where
  forwardKey := scalarKey
  forwardValue := scalarValue 0
  forwardRate := 0
  recurrentKey := scalarKey
  recurrentValue := scalarValue 0
  recurrentRate := 0
  query := scalarValue 0

def scalarState (previous : ℝ) : State Scalar Scalar where
  forwardMemory := 0
  recurrentMemory := scalarMemory 2
  output := scalarValue previous

/-- Equation (12) is not a feedforward alias: the same matrices and current
instruction produce different outputs when only the prior output changes. -/
theorem recurrent_fast_path_changes_output :
    (step identityActivation (scalarState 3) scalarInstruction).output 0 = 6 ∧
      (step identityActivation (scalarState 0) scalarInstruction).output 0 = 0 ∧
      (step identityActivation (scalarState 3) scalarInstruction).output ≠
        (step identityActivation (scalarState 0) scalarInstruction).output := by
  constructor
  · norm_num [step, identityActivation, scalarState, scalarInstruction,
      FastWeightMemory.read, deltaWrite, scalarMemory, scalarValue, scalarKey,
      Matrix.mulVec, Matrix.vecMulVec, dotProduct]
  constructor
  · norm_num [step, identityActivation, scalarState, scalarInstruction,
      FastWeightMemory.read, deltaWrite, scalarMemory, scalarValue, scalarKey,
      Matrix.mulVec, Matrix.vecMulVec, dotProduct]
  · intro equality
    have atZero := congrFun equality 0
    norm_num [step, identityActivation, scalarState, scalarInstruction,
      FastWeightMemory.read, deltaWrite, scalarMemory, scalarValue, scalarKey,
      Matrix.mulVec, Matrix.vecMulVec, dotProduct] at atZero

def scalarInputWeight : Matrix Scalar Scalar ℝ := 0
def scalarRecurrentWeight : Matrix Scalar Scalar ℝ :=
  scalarMemory 2

/-- Equations (15)--(18) likewise add genuine controller state dependence:
identical current inputs need not generate identical preactivations. -/
theorem recurrent_controller_changes_instruction :
    recurrentControllerProjection scalarInputWeight scalarRecurrentWeight
          identityActivation (scalarValue 7) (scalarValue 3) 0 = 6 ∧
      recurrentControllerProjection scalarInputWeight scalarRecurrentWeight
          identityActivation (scalarValue 7) (scalarValue 0) 0 = 0 := by
  norm_num [recurrentControllerProjection, scalarInputWeight,
    scalarRecurrentWeight, identityActivation, scalarMemory, scalarValue,
    scalarKey, Matrix.mulVec, Matrix.vecMulVec, dotProduct]

#print axioms step_output_expansion
#print axioms step_output_eq_feedforward_of_zero_recurrent
#print axioms recurrentControllerProjection_zero_recurrent
#print axioms recurrent_fast_path_changes_output
#print axioms recurrent_controller_changes_instruction

end

end RecurrentFastWeightProgrammer

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
