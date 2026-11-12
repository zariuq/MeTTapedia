import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Partitions

/-!
# The stationary parity mechanism at perfect task success

The noiseless endpoint of Goertzel's three-unit mechanism is represented by
three Boolean input signs. Its six input/output coordinates are pairwise
independent, although each unit-history cut carries two bits of information.
The update is a bijection and preserves the uniform state law.

An independently evaluated binary-gate circuit realizes the same output
function. This is functional correctness at the output observation, not a
communication-calculus encoding or an atomicity/distribution theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Parity

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV

abbrev Bits := Bool × Bool × Bool

def transition (state : Bits) : Bits :=
  (Bool.xor state.2.1 state.2.2, Bool.xor state.1 state.2.2,
    Bool.xor (Bool.xor state.1 state.2.1) state.2.2)

def inverse (state : Bits) : Bits :=
  (Bool.xor state.1 state.2.2, Bool.xor state.2.1 state.2.2,
    Bool.xor (Bool.xor state.1 state.2.1) state.2.2)

theorem inverse_transition (state : Bits) : inverse (transition state) = state := by
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem transition_inverse (state : Bits) : transition (inverse state) = state := by
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

def sign (bit : Bool) : ℝ := if bit then -1 else 1

theorem sign_mechanism (state : Bits) :
    sign (transition state).1 = sign state.2.1 * sign state.2.2 ∧
    sign (transition state).2.1 = sign state.1 * sign state.2.2 ∧
    sign (transition state).2.2 = sign state.1 * sign state.2.1 * sign state.2.2 := by
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> norm_num [transition, sign]

def initial : Prob Bits :=
  ⟨fun _ => 1 / 8, (fun _ => by norm_num), by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

theorem stationary : Prob.coarsen initial transition = initial := by
  apply Subtype.ext
  funext state
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [Prob.coarsen_apply, pushforward_eq_sum_ite, Fintype.sum_prod_type,
      Fintype.sum_bool, initial, transition]

def coordinate (index : Fin 6) (state : Bits) : Bool :=
  ![state.1, state.2.1, state.2.2, (transition state).1,
    (transition state).2.1, (transition state).2.2] index

theorem single_uniform (index : Fin 6) (value : Bool) :
    pushforward initial.1 (coordinate index) value = 1 / 2 := by
  fin_cases index <;> cases value <;>
    norm_num [pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool,
      initial, coordinate, transition]

theorem pairs_uniform (first second : Fin 6) (different : first ≠ second) (left right : Bool) :
    law2 initial.1 (coordinate first) (coordinate second) (left, right) = 1 / 4 := by
  fin_cases first <;> fin_cases second
  all_goals try exact (different rfl).elim
  all_goals cases left <;> cases right <;>
    norm_num [law2, pushforward_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool,
      initial, coordinate, transition]

theorem pairs_independent (first second : Fin 6) (different : first ≠ second) (left right : Bool) :
    law2 initial.1 (coordinate first) (coordinate second) (left, right) =
      pushforward initial.1 (coordinate first) left * pushforward initial.1 (coordinate second) right := by
  rw [pairs_uniform first second different, single_uniform, single_uniform]
  norm_num

def historyA (state : Bits) : Bool × Bool := (state.1, (transition state).1)
def historyB (state : Bits) : Bool × Bool := (state.2.1, (transition state).2.1)
def historyC (state : Bits) : Bool × Bool := (state.2.2, (transition state).2.2)

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  have power := Real.log_pow (2 : ℝ) 2
  norm_num at power
  exact power

theorem information_cut_A :
    mutualInfo initial.1 historyA (fun state => (historyB state, historyC state)) = 2 * Real.log 2 := by
  norm_num [mutualInfo, klSum_eq_sum, law2, pushforward_eq_sum_ite,
    Fintype.sum_prod_type, Fintype.sum_bool, initial, historyA, historyB, historyC, transition]
  nlinarith [log_four]

theorem information_cut_B :
    mutualInfo initial.1 historyB (fun state => (historyA state, historyC state)) = 2 * Real.log 2 := by
  norm_num [mutualInfo, klSum_eq_sum, law2, pushforward_eq_sum_ite,
    Fintype.sum_prod_type, Fintype.sum_bool, initial, historyA, historyB, historyC, transition]
  nlinarith [log_four]

theorem information_cut_C :
    mutualInfo initial.1 historyC (fun state => (historyA state, historyB state)) = 2 * Real.log 2 := by
  norm_num [mutualInfo, klSum_eq_sum, law2, pushforward_eq_sum_ite,
    Fintype.sum_prod_type, Fintype.sum_bool, initial, historyA, historyB, historyC, transition]
  nlinarith [log_four]

inductive Gate where
  | input : Fin 3 → Gate
  | xor : Gate → Gate → Gate

def Gate.eval (state : Bits) : Gate → Bool
  | .input index => ![state.1, state.2.1, state.2.2] index
  | .xor left right => Bool.xor (left.eval state) (right.eval state)

def binaryCircuit : Fin 3 → Gate :=
  ![.xor (.input 1) (.input 2), .xor (.input 0) (.input 2),
    .xor (.input 0) (.xor (.input 1) (.input 2))]

def circuitOutput (state : Bits) : Bits :=
  ((binaryCircuit 0).eval state, (binaryCircuit 1).eval state, (binaryCircuit 2).eval state)

theorem binary_circuit_correct (state : Bits) : circuitOutput state = transition state := by
  rcases state with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem binary_circuit_law : Prob.coarsen initial circuitOutput = Prob.coarsen initial transition := by
  have outputs : circuitOutput = transition := funext binary_circuit_correct
  rw [outputs]

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Parity
