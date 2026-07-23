import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Equivalence
import Mathlib.Data.List.Basic

/-!
# Finite separation fixtures for credit transport

These fixtures witness the invalid converses in the credit-equivalence lattice.
They are deliberately small enough for kernel reduction while remaining
non-vacuous: states move, trajectories differ, stochastic supports differ, and
resource coordinates disagree.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Counterexamples

private def siteLocalAudit : LocalityAudit Unit where
  scope := .strictlySiteLocal
  dependsOn := fun _ _ => False

private def noOracle : OracleAudit where
  accesses := []

/-- A reusable scalar machine with a fixed zero objective. -/
private def natSystem (initial : Nat) (next : Nat → Nat) :
    CreditTransportSystem Unit Unit Nat Unit Nat Nat where
  objective := fun _ _ => 0
  initialState := fun _ _ => initial
  enabled := fun _ _ _ _ => True
  transition := fun _ _ _ state => next state
  signal := fun _ _ state => state
  readUpdate := fun _ _ state => state
  eventCost := fun _ _ _ _ => { scalarWork := 1, criticalPathSpan := 1 }
  oracleAudit := noOracle
  localityAudit := siteLocalAudit

/-- Immediate contraction to the common equilibrium zero. -/
def jumpToZero : CreditTransportSystem Unit Unit Nat Unit Nat Nat :=
  natSystem 2 (fun _ => 0)

/-- Slower contraction to the same equilibrium. -/
def decrementToZero : CreditTransportSystem Unit Unit Nat Unit Nat Nat :=
  natSystem 2 (fun state => state - 1)

theorem jump_decrement_objectiveEquivalent :
    ObjectiveEquivalent jumpToZero decrementToZero := by
  intro _ _
  rfl

theorem jump_decrement_equilibriumCreditEquivalent :
    EquilibriumCreditEquivalent jumpToZero decrementToZero := by
  intro _ _
  refine ⟨0, 0, ?_, ?_, rfl, rfl⟩
  · intro event _
    cases event
    rfl
  · intro event _
    cases event
    rfl

private theorem oneEventPaired : List.Forall₂ Eq [()] [()] :=
  .cons rfl .nil

/-- Equal objectives do not imply equal finite trajectories.  The same witness
also separates equilibrium credit from finite settling. -/
theorem jump_decrement_not_finiteTrajectoryEquivalent
    (stateRel : Nat → Nat → Prop) :
    ¬ FiniteTrajectoryEquivalent jumpToZero decrementToZero Eq stateRel := by
  intro finite
  have traceEquality :=
    finite.signal_traces_eq (problem := ()) (parameter := ()) oneEventPaired
  norm_num [CreditTransportSystem.signalTrace, CreditTransportSystem.trace,
    CreditTransportSystem.traceFrom, jumpToZero, decrementToZero, natSystem] at traceEquality

theorem objectiveEquivalence_does_not_imply_finiteTrajectory :
    ObjectiveEquivalent jumpToZero decrementToZero ∧
      ∀ stateRel : Nat → Nat → Prop,
        ¬ FiniteTrajectoryEquivalent jumpToZero decrementToZero Eq stateRel :=
  ⟨jump_decrement_objectiveEquivalent,
    jump_decrement_not_finiteTrajectoryEquivalent⟩

theorem equilibriumCreditEquivalence_does_not_imply_finiteTrajectory :
    EquilibriumCreditEquivalent jumpToZero decrementToZero ∧
      ∀ stateRel : Nat → Nat → Prop,
        ¬ FiniteTrajectoryEquivalent jumpToZero decrementToZero Eq stateRel :=
  ⟨jump_decrement_equilibriumCreditEquivalent,
    jump_decrement_not_finiteTrajectoryEquivalent⟩

/-- Two events are needed to reach state two. -/
def slowTwoStep : CreditTransportSystem Unit Unit Nat Unit Nat Nat :=
  natSystem 0 (fun state => state + 1)

/-- State two is reached in one event and then retained. -/
def fastThenStay : CreditTransportSystem Unit Unit Nat Unit Nat Nat :=
  natSystem 0 (fun _ => 2)

private theorem twoEventsPaired : List.Forall₂ Eq [(), ()] [(), ()] :=
  .cons rfl (.cons rfl .nil)

def UpdateEqualAt
    {LocalState₁ LocalState₂ Event₁ Event₂ Signal Update : Type*}
    (left : CreditTransportSystem Unit Unit LocalState₁ Event₁ Signal Update)
    (right : CreditTransportSystem Unit Unit LocalState₂ Event₂ Signal Update)
    (leftEvents : List Event₁) (rightEvents : List Event₂) : Prop :=
  left.finalUpdate () () leftEvents = right.finalUpdate () () rightEvents

theorem slow_fast_twoEvent_updateEqual :
    UpdateEqualAt slowTwoStep fastThenStay [(), ()] [(), ()] := by
  rfl

theorem slow_fast_twoEvent_signalTraces_ne :
    slowTwoStep.signalTrace () () [(), ()] ≠
      fastThenStay.signalTrace () () [(), ()] := by
  decide

/-- Equality of one selected finite-horizon update leaves intermediate credit
unconstrained. -/
theorem oneHorizon_updateEquivalence_does_not_imply_finiteTrajectory :
    UpdateEqualAt slowTwoStep fastThenStay [(), ()] [(), ()] ∧
      slowTwoStep.signalTrace () () [(), ()] ≠
        fastThenStay.signalTrace () () [(), ()] :=
  ⟨slow_fast_twoEvent_updateEqual, slow_fast_twoEvent_signalTraces_ne⟩

/-- Integer outcome with a natural multiplicity, sufficient for an exact mean
and support counterexample without floating-point probabilities. -/
structure WeightedIntOutcome where
  value : Int
  multiplicity : Nat
  deriving DecidableEq, Repr

def weightedTotal : List WeightedIntOutcome → Int
  | [] => 0
  | outcome :: outcomes =>
      Int.ofNat outcome.multiplicity * outcome.value + weightedTotal outcomes

def outcomeSupport (outcomes : List WeightedIntOutcome) : List Int :=
  outcomes.map WeightedIntOutcome.value

def deterministicZero : List WeightedIntOutcome :=
  [{ value := 0, multiplicity := 2 }]

def symmetricPlusMinus : List WeightedIntOutcome :=
  [{ value := -1, multiplicity := 1 }, { value := 1, multiplicity := 1 }]

theorem equalExpectedUpdate_unequalSupport :
    weightedTotal deterministicZero = weightedTotal symmetricPlusMinus ∧
      outcomeSupport deterministicZero ≠ outcomeSupport symmetricPlusMinus := by
  norm_num [weightedTotal, deterministicZero, symmetricPlusMinus, outcomeSupport]

/-- A constant surrogate loss cannot distinguish two disjoint terminal
supports. -/
def constantLoss (_ : Bool) : Nat := 1

def supportLoss (support : List Bool) : Nat :=
  (support.map constantLoss).sum

theorem equalExpectedLoss_disjointTerminalSupport :
    supportLoss [false] = supportLoss [true] ∧
      List.Disjoint [false] [true] := by
  constructor
  · rfl
  · simp

/-- A downstream policy can erase update-space separation. -/
def downstreamSum (update : Nat × Nat) : Nat := update.1 + update.2

theorem separatedUpdates_sameDownstreamBehavior :
    (1, 0) ≠ (0, 1) ∧
      downstreamSum (1, 0) = downstreamSum (0, 1) := by
  decide

/-- An exact reverse oracle paired with a site-local label is inconsistent. -/
def mislabeledReverseOracle : OracleAudit where
  accesses := [.exactReverseVjp]

def falselySiteLocal : LocalityAudit Unit where
  scope := .strictlySiteLocal
  dependsOn := fun _ _ => False

def honestlyGlobalReverse : LocalityAudit Unit where
  scope := .globalReverse
  dependsOn := fun _ _ => True

theorem exactReverse_siteLocal_inconsistent :
    ¬ OracleLocalityConsistent mislabeledReverseOracle falselySiteLocal := by
  simp [OracleLocalityConsistent, OracleAudit.Declares,
    mislabeledReverseOracle, falselySiteLocal,
    LocalityClass.NoBroaderThan, LocalityClass.rank]

theorem exactReverse_globalReverse_consistent :
    OracleLocalityConsistent mislabeledReverseOracle honestlyGlobalReverse := by
  simp [OracleLocalityConsistent, OracleAudit.Declares,
    mislabeledReverseOracle, honestlyGlobalReverse,
    LocalityClass.NoBroaderThan, LocalityClass.rank]

/-- Equal scalar operation counts can hide different span, memory, and
synchronization costs. -/
def longThinCost : ResourceVector where
  scalarWork := 10
  criticalPathSpan := 10
  persistentMemory := 1
  peakTemporaryMemory := 1

def shortWideCost : ResourceVector where
  scalarWork := 10
  criticalPathSpan := 1
  persistentMemory := 10
  peakTemporaryMemory := 10
  synchronizationRounds := 1

theorem equalScalarWork_unequalSystemCost :
    longThinCost.scalarWork = shortWideCost.scalarWork ∧
      longThinCost ≠ shortWideCost := by
  decide

#print axioms objectiveEquivalence_does_not_imply_finiteTrajectory
#print axioms equilibriumCreditEquivalence_does_not_imply_finiteTrajectory
#print axioms oneHorizon_updateEquivalence_does_not_imply_finiteTrajectory
#print axioms equalExpectedUpdate_unequalSupport
#print axioms equalExpectedLoss_disjointTerminalSupport
#print axioms separatedUpdates_sameDownstreamBehavior
#print axioms exactReverse_siteLocal_inconsistent
#print axioms equalScalarWork_unequalSystemCost

end Counterexamples

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
