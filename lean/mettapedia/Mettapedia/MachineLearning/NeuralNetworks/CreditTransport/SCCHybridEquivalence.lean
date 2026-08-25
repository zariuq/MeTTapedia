import Mettapedia.GSLT.Dynamics.KnotDecomposition
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CyclicEPCRefinement
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ShootingStructure

/-!
# SCC-local hybrid predictive-coding equivalence

The natural unit of cyclic refinement is a strongly connected component.  A
call-closed downset of the SCC condensation can be solved exactly in error
coordinates; cyclic components can then be refined locally against the exact
separator values.  Bekić gluing proves global equilibrium, while the existing
cycle-refinement bounds charge finite state, credit, and work error.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SCCHybridEquivalence

open Mettapedia.GSLT.Dynamics.KnotDecomposition
open CyclicEPCRefinement
open TruncatedNeumannResidual

/-! ## SCC condensation -/

variable {Head Answer : Type}

/-- Mutual reachability as a setoid. -/
def componentSetoid (system : CallSystem Head Answer) : Setoid Head where
  r := SameKnot system
  iseqv := sameKnot_equivalence system

/-- Vertices of the condensation graph are SCCs, not original heads. -/
def CondensationVertex (system : CallSystem Head Answer) :=
  Quotient (componentSetoid system)

def componentOf (system : CallSystem Head Answer) (head : Head) :
    CondensationVertex system :=
  Quotient.mk (componentSetoid system) head

theorem componentOf_eq_iff_sameKnot
    (system : CallSystem Head Answer) (left right : Head) :
    componentOf system left = componentOf system right ↔
      SameKnot system left right := by
  exact Quotient.eq

/-- The condensation has an edge when representatives in two *different*
components are related by a direct call. -/
def CondensationEdge (system : CallSystem Head Answer)
    (source target : CondensationVertex system) : Prop :=
  source ≠ target ∧
    ∃ sourceHead targetHead,
      componentOf system sourceHead = source ∧
      componentOf system targetHead = target ∧
      system.calls sourceHead targetHead

theorem condensationEdge_irreflexive
    (system : CallSystem Head Answer)
    (component : CondensationVertex system) :
    ¬ CondensationEdge system component component := by
  intro edge
  exact edge.1 rfl

/-- Every direct call is either internal to one SCC or induces a condensation
edge. -/
theorem call_internal_or_condensationEdge
    (system : CallSystem Head Answer) {source target : Head}
    (call : system.calls source target) :
    SameKnot system source target ∨
      CondensationEdge system (componentOf system source)
        (componentOf system target) := by
  by_cases internal : SameKnot system source target
  · exact Or.inl internal
  · refine Or.inr ⟨?_, source, target, rfl, rfl, call⟩
    exact fun equality => internal ((componentOf_eq_iff_sameKnot system source target).mp equality)

/-! ## Exact separator-consistent gluing -/

/-- The upper/local SCC solve must evaluate its equations against the exact
lower/DAG separator values. -/
def SeparatorConsistent
    (system : CallSystem Head Answer)
    (lower : Head → Prop) [DecidablePred lower]
    (dagSolution localSolution : Head → Answer) : Prop :=
  ∀ head, ¬ lower head →
    system.step (glue lower dagSolution localSolution) head =
      localSolution head

/-- A two-stratum hybrid solve.  `lower` may contain many SCCs, but must be a
call-closed downset of the condensation. -/
structure HybridErrorCoordinateSolve
    (system : CallSystem Head Answer)
    (lower : Head → Prop) [DecidablePred lower] where
  dagSolution : Head → Answer
  localSolution : Head → Answer
  lower_callClosed : CallClosed system lower
  dag_exact : ∀ head, lower head →
    system.step dagSolution head = dagSolution head
  separator_consistent :
    SeparatorConsistent system lower dagSolution localSolution

def HybridErrorCoordinateSolve.assembled
    {system : CallSystem Head Answer}
    {lower : Head → Prop} [DecidablePred lower]
    (solve : HybridErrorCoordinateSolve system lower) : Head → Answer :=
  glue lower solve.dagSolution solve.localSolution

/-- Exact DAG solving plus separator-consistent local SCC solves is a global
equilibrium. -/
theorem HybridErrorCoordinateSolve.assembled_solves
    {system : CallSystem Head Answer}
    {lower : Head → Prop} [DecidablePred lower]
    (solve : HybridErrorCoordinateSolve system lower) :
    Solves system solve.assembled := by
  exact glue_solves system solve.lower_callClosed solve.dag_exact
    solve.separator_consistent

/-- Under uniqueness, the assembled hybrid equilibrium agrees pointwise with
the whole-graph equilibrium. -/
theorem HybridErrorCoordinateSolve.assembled_eq_global
    {system : CallSystem Head Answer}
    {lower : Head → Prop} [DecidablePred lower]
    (solve : HybridErrorCoordinateSolve system lower)
    (global : Head → Answer) (globalSolves : Solves system global)
    (unique : ∀ left right : Head → Answer,
      Solves system left → Solves system right → left = right) :
    solve.assembled = global := by
  exact unique solve.assembled global solve.assembled_solves globalSolves

/-! ## Positive and negative separator fixtures -/

def twoHeadHybridSolve :
    HybridErrorCoordinateSolve twoHead (fun head ↦ head = false) where
  dagSolution := fun _ ↦ 7
  localSolution := fun _ ↦ 7
  lower_callClosed := by
    intro head dependency headLower call
    exact call.2
  dag_exact := by
    intro head headLower
    have : head = false := headLower
    simp [twoHead, this]
  separator_consistent := by
    intro head headUpper
    have : head = true := by
      cases head with
      | false => exact absurd rfl headUpper
      | true => rfl
    simp [twoHead, glue, this]

theorem twoHeadHybridSolve_is_global :
    Solves twoHead twoHeadHybridSolve.assembled ∧
      twoHeadHybridSolve.assembled true = 7 ∧
      twoHeadHybridSolve.assembled false = 7 := by
  refine ⟨twoHeadHybridSolve.assembled_solves, ?_⟩
  decide

/-- Local update for the upper head when its separator is incorrectly frozen
at zero. -/
def frozenZeroUpperStep (upperValue : Nat) : Nat :=
  twoHead.step (fun head ↦ if head then upperValue else 0) true

theorem frozenZeroUpperStep_converges_to_zero :
    Function.IsFixedPt frozenZeroUpperStep 0 := by
  simp [Function.IsFixedPt, frozenZeroUpperStep, twoHead]

/-- The locally converged upper value and the independently solved lower value
assemble to a non-equilibrium when the separator was frozen inconsistently. -/
theorem frozen_separator_converges_to_wrong_global_equilibrium :
    Function.IsFixedPt frozenZeroUpperStep 0 ∧
      ¬ Solves twoHead
        (glue (fun head ↦ head = true) (fun _ ↦ 0) (fun _ ↦ 7)) := by
  exact ⟨frozenZeroUpperStep_converges_to_zero, twoHead_topDown_fails⟩

/-! ## Finite local state, credit, and work bounds -/

section FiniteBounds

variable {State Credit : Type*}
variable [NormedAddCommGroup State] [NormedSpace ℝ State]
variable [NormedAddCommGroup Credit] [NormedSpace ℝ Credit]

/-- Existing damped-cycle contraction and active-depth accounting compose into
one SCC-local state/credit/work certificate. -/
theorem localSCC_state_credit_work_bounds
    {cycle : State →L[ℝ] State} {factor fraction : ℝ}
    (cycleContracts : ContractsBy cycle factor)
    (factorNonnegative : 0 ≤ factor)
    (fractionNonnegative : 0 ≤ fraction)
    (fractionAtMostOne : fraction ≤ 1)
    (steps : ℕ) (forcing exact : State)
    (exactSolution : exact - cycle exact = forcing)
    (readout : State →L[ℝ] Credit)
    (primaryWork activeDepth totalDepth : ℕ)
    (activeDepthBound : activeDepth ≤ totalDepth) :
    let approximate := refinedCycleCorrection fraction cycle steps forcing
    let errorBudget :=
      ((1 - fraction) + fraction * factor) ^ steps * ‖exact‖
    ‖approximate - exact‖ ≤ errorBudget ∧
      ‖readout approximate - readout exact‖ ≤ ‖readout‖ * errorBudget ∧
      composedRefinementMatmulWork primaryWork steps activeDepth ≤
        composedRefinementMatmulWork primaryWork steps totalDepth := by
  dsimp only
  have stateBound := refinedCycle_error_le cycleContracts factorNonnegative
    fractionNonnegative fractionAtMostOne steps forcing exact exactSolution
  refine ⟨stateBound, ?_,
    composedRefinementMatmulWork_le_dense activeDepthBound⟩
  calc
    ‖readout (refinedCycleCorrection fraction cycle steps forcing) -
        readout exact‖ =
        ‖readout
          (refinedCycleCorrection fraction cycle steps forcing - exact)‖ := by
      rw [map_sub]
    _ ≤ ‖readout‖ *
        ‖refinedCycleCorrection fraction cycle steps forcing - exact‖ :=
      readout.le_opNorm _
    _ ≤ ‖readout‖ *
        (((1 - fraction) + fraction * factor) ^ steps * ‖exact‖) :=
      mul_le_mul_of_nonneg_left stateBound (norm_nonneg readout)

end FiniteBounds

end SCCHybridEquivalence

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
