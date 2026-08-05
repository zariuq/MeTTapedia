import Mathlib

/-!
# Coordinatewise learned optimizers

Andrychowicz et al., *Learning to learn by gradient descent by gradient
descent* (arXiv:1606.04474), Section 2.1, apply one recurrent optimizer cell
independently to every optimizee coordinate.  Cell parameters are shared, but
each coordinate carries a separate hidden state.  The source notes that this
makes the optimizer invariant to parameter ordering.

This file states that claim as exact finite semantics.  A shared coordinate
cell produces the same updated parameter and hidden-state field after any
coordinate reindexing, provided gradients, parameters, and hidden states are
reindexed together.  One coordinate's result also depends only on that
coordinate's gradient and state.

A two-coordinate fixture proves that the hidden-state qualification is
essential.  Reindexing parameters and gradients while leaving recurrent
states at their old positions can change the update, even though the cell
parameters remain shared.

No theorem here claims that a learned cell descends an objective, generalizes
to new optimizees, or outperforms a hand-designed optimizer.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CoordinatewiseLearnedOptimizer

/-- One optimizee coordinate and its private recurrent optimizer state. -/
structure CoordinateState (Parameter Hidden : Type*) where
  parameter : Parameter
  hidden : Hidden
deriving DecidableEq

/-- A bank of optimizee coordinates. -/
abbrev State (Index Parameter Hidden : Type*) :=
  Index → CoordinateState Parameter Hidden

/-- One shared recurrent optimizer cell.  It consumes the current gradient
coordinate and private hidden state, then emits a parameter increment and the
next private hidden state. -/
abbrev Cell (Gradient Hidden Delta : Type*) :=
  Gradient → Hidden → Delta × Hidden

variable {Index OtherIndex Parameter Gradient Hidden : Type*}

/-- Equation (1), applied independently at every coordinate with one shared
cell and separate recurrent states. -/
def step [Add Parameter]
    (cell : Cell Gradient Hidden Parameter)
    (gradient : Index → Gradient)
    (state : State Index Parameter Hidden) :
    State Index Parameter Hidden :=
  fun index =>
    let output := cell (gradient index) (state index).hidden
    { parameter := (state index).parameter + output.1
      hidden := output.2 }

/-- Reindex a coordinate field along an equivalence. -/
def reindex (equivalence : Index ≃ OtherIndex)
    (values : Index → Parameter) :
    OtherIndex → Parameter :=
  fun index => values (equivalence.symm index)

/-- The coordinatewise learned-optimizer step commutes exactly with any
simultaneous reindexing of gradients, parameters, and private hidden states. -/
theorem step_reindex [Add Parameter]
    (equivalence : Index ≃ OtherIndex)
    (cell : Cell Gradient Hidden Parameter)
    (gradient : Index → Gradient)
    (state : State Index Parameter Hidden) :
    reindex equivalence (step cell gradient state) =
      step cell (reindex equivalence gradient)
        (reindex equivalence state) := by
  rfl

/-- One coordinate's result is insensitive to every gradient and state entry
outside that coordinate. -/
theorem step_apply_eq_of_local_eq [Add Parameter]
    (cell : Cell Gradient Hidden Parameter)
    (leftGradient rightGradient : Index → Gradient)
    (leftState rightState : State Index Parameter Hidden)
    (index : Index)
    (gradientEqual : leftGradient index = rightGradient index)
    (stateEqual : leftState index = rightState index) :
    step cell leftGradient leftState index =
      step cell rightGradient rightState index := by
  simp [step, gradientEqual, stateEqual]

/-- Reindex only the optimizee parameters while leaving recurrent optimizer
states attached to their old positions.  This is deliberately not the source
architecture's simultaneous reindexing. -/
def reindexParametersOnly
    (equivalence : Index ≃ Index)
    (state : State Index Parameter Hidden) :
    State Index Parameter Hidden :=
  fun index =>
    { parameter := (state (equivalence.symm index)).parameter
      hidden := (state index).hidden }

/-! ## Executable positive and negative fixtures -/

abbrev TwoCoordinates := Fin 2

def swapCoordinates : TwoCoordinates ≃ TwoCoordinates :=
  Equiv.swap 0 1

def unitGradient : TwoCoordinates → Unit :=
  fun _ => ()

def hiddenIncrementCell : Cell Unit ℕ ℕ :=
  fun _gradient hidden => (hidden, hidden + 1)

def initialFixture : State TwoCoordinates ℕ ℕ
  | 0 => { parameter := 10, hidden := 1 }
  | 1 => { parameter := 20, hidden := 3 }

theorem simultaneous_reindex :
    reindex swapCoordinates
        (step hiddenIncrementCell unitGradient initialFixture) =
      step hiddenIncrementCell
        (reindex swapCoordinates unitGradient)
        (reindex swapCoordinates initialFixture) :=
  step_reindex swapCoordinates hiddenIncrementCell unitGradient initialFixture

/-- Parameter-only reindexing changes the update because each recurrent state
continues to emit the history associated with its old coordinate. -/
theorem parameters_only_reindex_breaks_equivariance :
    step hiddenIncrementCell (reindex swapCoordinates unitGradient)
        (reindexParametersOnly swapCoordinates initialFixture) ≠
      reindex swapCoordinates
        (step hiddenIncrementCell unitGradient initialFixture) := by
  intro equalStates
  have atZero := congrFun equalStates 0
  norm_num [step, reindex, reindexParametersOnly, swapCoordinates,
    hiddenIncrementCell, unitGradient, initialFixture] at atZero

#print axioms step_reindex
#print axioms step_apply_eq_of_local_eq
#print axioms simultaneous_reindex
#print axioms parameters_only_reindex_breaks_equivariance

end CoordinatewiseLearnedOptimizer

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
