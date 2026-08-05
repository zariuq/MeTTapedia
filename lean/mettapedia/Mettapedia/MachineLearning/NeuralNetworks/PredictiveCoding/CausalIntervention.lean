import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ArbitraryGraphEnergy

/-!
# Error-clamped interventions on predictive-coding graphs

Salvatori, Pinchetti, M'Charrak, Millidge, and Lukasiewicz,
*Predictive Coding beyond Correlations*, arXiv:2306.15479v2, Proposition 3.1
and Appendix B, show that clamping an intervened value and setting its
prediction error to zero produces the same PC value-node dynamics as deleting
every incoming edge to that node.  The authenticated source artifact has
SHA-256
`b179477b75d0fc728fa6f13a40fb3633f86afba10a8f3ee8d6cc949d47965155`.

This file proves a stronger finite-graph statement.  No acyclicity,
probability distribution, equilibrium, or convergence assumption is needed
for the dynamical identity: zeroing the intervened residual erases exactly
the changed incoming-edge terms.  The two synchronous transition functions
are equal, so all finite trajectories agree from every initial state.

The result concerns deterministic PC update dynamics.  Identifying a finite
iterate or equilibrium with an interventional distribution still requires
the source's causal-sufficiency, probabilistic-model, convergence, and
uniqueness assumptions.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace CausalIntervention

open Finset

noncomputable section

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-! ## Graph surgery and the local PC force -/

/-- Delete every edge entering `intervention`, represented by zeroing its
source-to-target weight. -/
def removeIncomingEdges
    (weight : Vertex → Vertex → ℝ) (intervention : Vertex) :
    Vertex → Vertex → ℝ :=
  fun source target =>
    if target = intervention then 0 else weight source target

/-- Set only the intervened node's prediction residual to zero. -/
def interventionalResidual
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (intervention : Vertex) : Vertex → ℝ :=
  fun target =>
    if target = intervention then 0
    else ArbitraryGraphEnergy.residual activation weight state target

/-- The source's local value-node force before multiplication by its positive
inference rate. -/
def pcStateForce
    (activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ)
    (error state : Vertex → ℝ) (vertex : Vertex) : ℝ :=
  -error vertex +
    activationDerivative (state vertex) *
      ∑ target, error target * weight vertex target

omit [Fintype Vertex] in
theorem removeIncomingEdges_at_intervention
    (weight : Vertex → Vertex → ℝ) (intervention source : Vertex) :
    removeIncomingEdges weight intervention source intervention = 0 := by
  simp [removeIncomingEdges]

omit [Fintype Vertex] in
theorem removeIncomingEdges_of_ne
    (weight : Vertex → Vertex → ℝ) (intervention source target : Vertex)
    (htarget : target ≠ intervention) :
    removeIncomingEdges weight intervention source target =
      weight source target := by
  simp [removeIncomingEdges, htarget]

theorem interventionalResidual_at_intervention
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (intervention : Vertex) :
    interventionalResidual activation weight state intervention
      intervention = 0 := by
  simp [interventionalResidual]

theorem interventionalResidual_of_ne
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (intervention target : Vertex)
    (htarget : target ≠ intervention) :
    interventionalResidual activation weight state intervention target =
      ArbitraryGraphEnergy.residual activation weight state target := by
  simp [interventionalResidual, htarget]

/-- Mutilating incoming edges changes no residual except the residual owned by
the intervened target. -/
theorem mutilatedResidual_of_ne
    (activation : ℝ → ℝ) (weight : Vertex → Vertex → ℝ)
    (state : Vertex → ℝ) (intervention target : Vertex)
    (htarget : target ≠ intervention) :
    ArbitraryGraphEnergy.residual activation
        (removeIncomingEdges weight intervention) state target =
      ArbitraryGraphEnergy.residual activation weight state target := by
  simp [ArbitraryGraphEnergy.residual, ArbitraryGraphEnergy.prediction,
    removeIncomingEdges, htarget]

/-- Proposition 3.1 at the local-force level.  For every nonintervened value
node, zeroing the intervention residual on the original graph gives exactly
the force obtained after deleting all incoming intervention edges. -/
theorem errorClamp_force_eq_mutilated_force
    (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ) (state : Vertex → ℝ)
    (intervention vertex : Vertex) (hvertex : vertex ≠ intervention) :
    pcStateForce activationDerivative weight
        (interventionalResidual activation weight state intervention)
        state vertex =
      pcStateForce activationDerivative
        (removeIncomingEdges weight intervention)
        (ArbitraryGraphEnergy.residual activation
          (removeIncomingEdges weight intervention) state)
        state vertex := by
  have hlocal :
      interventionalResidual activation weight state intervention vertex =
        ArbitraryGraphEnergy.residual activation
          (removeIncomingEdges weight intervention) state vertex := by
    rw [interventionalResidual_of_ne
      activation weight state intervention vertex hvertex]
    symm
    exact mutilatedResidual_of_ne
      activation weight state intervention vertex hvertex
  simp only [pcStateForce]
  rw [hlocal]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro target _
  by_cases htarget : target = intervention
  · subst target
    simp [interventionalResidual, removeIncomingEdges]
  · rw [interventionalResidual_of_ne
      activation weight state intervention target htarget]
    rw [mutilatedResidual_of_ne
      activation weight state intervention target htarget]
    rw [removeIncomingEdges_of_ne
      weight intervention vertex target htarget]

/-! ## Equal transition maps and finite trajectories -/

/-- Runtime intervention on the original graph: clamp the value and zero its
error before every local update. -/
def errorClampedInterventionalStep
    (rate : ℝ) (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ)
    (intervention : Vertex) (value : ℝ)
    (state : Vertex → ℝ) : Vertex → ℝ :=
  fun vertex =>
    if vertex = intervention then value
    else state vertex +
      rate * pcStateForce activationDerivative weight
        (interventionalResidual activation weight state intervention)
        state vertex

/-- Conditional query on the mutilated graph: clamp the same value after
deleting every incoming edge to the intervention node. -/
def mutilatedConditionalStep
    (rate : ℝ) (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ)
    (intervention : Vertex) (value : ℝ)
    (state : Vertex → ℝ) : Vertex → ℝ :=
  fun vertex =>
    if vertex = intervention then value
    else state vertex +
      rate * pcStateForce activationDerivative
        (removeIncomingEdges weight intervention)
        (ArbitraryGraphEnergy.residual activation
          (removeIncomingEdges weight intervention) state)
        state vertex

/-- Strong form of the source proposition: the two synchronous transition
functions are equal on every finite graph and every state. -/
theorem errorClampedInterventionalStep_eq_mutilatedConditionalStep
    (rate : ℝ) (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ)
    (intervention : Vertex) (value : ℝ) :
    errorClampedInterventionalStep rate activation activationDerivative
        weight intervention value =
      mutilatedConditionalStep rate activation activationDerivative
        weight intervention value := by
  funext state vertex
  by_cases hvertex : vertex = intervention
  · simp [errorClampedInterventionalStep, mutilatedConditionalStep, hvertex]
  · simp only [errorClampedInterventionalStep, mutilatedConditionalStep,
      hvertex, if_false]
    rw [errorClamp_force_eq_mutilated_force
      activation activationDerivative weight state intervention vertex hvertex]

/-- Consequently every finite interventional trajectory agrees pointwise
with the conditional trajectory on the mutilated graph. -/
theorem errorClampedInterventional_iterate_eq_mutilatedConditional_iterate
    (rate : ℝ) (activation activationDerivative : ℝ → ℝ)
    (weight : Vertex → Vertex → ℝ)
    (intervention : Vertex) (value : ℝ)
    (steps : ℕ) (initial : Vertex → ℝ) :
    Nat.iterate
        (errorClampedInterventionalStep rate activation activationDerivative
          weight intervention value)
        steps initial =
      Nat.iterate
        (mutilatedConditionalStep rate activation activationDerivative
          weight intervention value)
        steps initial := by
  rw [errorClampedInterventionalStep_eq_mutilatedConditionalStep]

/-! ## Executable two-node boundaries -/

def twoNodeWeight : Fin 2 → Fin 2 → ℝ
  | 0, 1 => 1
  | _, _ => 0

def twoNodeState : Fin 2 → ℝ
  | 0 => 1
  | 1 => 2

/-- Positive fixture: zeroing the intervened residual reproduces the
mutilated-graph force on the parent node. -/
theorem twoNode_errorClamp_matches_mutilation :
    pcStateForce (fun _ ↦ 1) twoNodeWeight
        (interventionalResidual id twoNodeWeight twoNodeState 1)
        twoNodeState 0 = -1 ∧
      pcStateForce (fun _ ↦ 1)
        (removeIncomingEdges twoNodeWeight 1)
        (ArbitraryGraphEnergy.residual id
          (removeIncomingEdges twoNodeWeight 1) twoNodeState)
        twoNodeState 0 = -1 := by
  norm_num [pcStateForce, interventionalResidual, removeIncomingEdges,
    ArbitraryGraphEnergy.residual, ArbitraryGraphEnergy.prediction,
    twoNodeWeight, twoNodeState, Fin.sum_univ_two]

/-- Negative boundary: clamping only the intervention value while retaining
its nonzero residual is conditioning, not the source's interventional query;
the parent force then differs from graph mutilation. -/
theorem twoNode_valueClamp_without_errorClamp_not_intervention :
    pcStateForce (fun _ ↦ 1) twoNodeWeight
        (ArbitraryGraphEnergy.residual id twoNodeWeight twoNodeState)
        twoNodeState 0 = 0 ∧
      pcStateForce (fun _ ↦ 1)
        (removeIncomingEdges twoNodeWeight 1)
        (ArbitraryGraphEnergy.residual id
          (removeIncomingEdges twoNodeWeight 1) twoNodeState)
        twoNodeState 0 = -1 := by
  norm_num [pcStateForce, removeIncomingEdges,
    ArbitraryGraphEnergy.residual, ArbitraryGraphEnergy.prediction,
    twoNodeWeight, twoNodeState, Fin.sum_univ_two]

end

end CausalIntervention

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

#print axioms Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CausalIntervention.errorClamp_force_eq_mutilated_force
#print axioms Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CausalIntervention.errorClampedInterventionalStep_eq_mutilatedConditionalStep
#print axioms Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CausalIntervention.errorClampedInterventional_iterate_eq_mutilatedConditional_iterate
#print axioms Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CausalIntervention.twoNode_valueClamp_without_errorClamp_not_intervention
