import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RecurrentIndependentMechanisms

/-!
# Competitive independent mechanisms

Parascandolo et al., *Learning Independent Causal Mechanisms*
(arXiv:1712.00961), Section 3.2, train only the expert that wins a data point
while leaving every other expert unchanged.  This file isolates the algebraic
consequence of that execution rule.

When each expert transition reads only its own state, updates assigned to
disjoint expert sets commute exactly, even when they use different inputs and
different transition families.  Singleton winners are the source algorithm's
special case.  An overlapping-winner fixture shows why disjointness is
essential: two noncommuting updates to the same expert remain order-sensitive.

The theorem concerns state locality and execution order.  It does not claim
that competition discovers the data-generating mechanisms, that winners are
unique, or that the learned experts generalize.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace CompetitiveIndependentMechanisms

open RecurrentIndependentMechanisms

variable {Mechanism Input Hidden : Type*} [DecidableEq Mechanism]

/-- A winner-only update is the singleton-active-set specialization of the
recurrent-independent-mechanism transition. -/
def winnerStep
    (winner : Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    State Mechanism Hidden :=
  independentStep {winner} dynamics input state

/-- Every nonwinning expert remains exactly unchanged. -/
theorem winnerStep_eq_of_ne
    (winner : Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (input : Input)
    (state : State Mechanism Hidden)
    {expert : Mechanism}
    (different : expert ≠ winner) :
    winnerStep winner dynamics input state expert = state expert := by
  simp [winnerStep, independentStep, different]

/-- Updates with disjoint write sets commute exactly when each local
transition reads only its own expert state.  The two updates may carry
different inputs and use different transition families. -/
theorem independentStep_commute_of_disjoint
    (firstActive secondActive : Finset Mechanism)
    (firstDynamics secondDynamics : Dynamics Mechanism Input Hidden)
    (firstInput secondInput : Input)
    (state : State Mechanism Hidden)
    (disjoint : Disjoint firstActive secondActive) :
    independentStep firstActive firstDynamics firstInput
        (independentStep secondActive secondDynamics secondInput state) =
      independentStep secondActive secondDynamics secondInput
        (independentStep firstActive firstDynamics firstInput state) := by
  funext expert
  by_cases firstMembership : expert ∈ firstActive
  · by_cases secondMembership : expert ∈ secondActive
    · exact
        (Finset.disjoint_left.mp disjoint firstMembership secondMembership).elim
    · simp [independentStep, firstMembership, secondMembership]
  · by_cases secondMembership : expert ∈ secondActive
    · simp [independentStep, firstMembership, secondMembership]
    · simp [independentStep, firstMembership, secondMembership]

/-- Winner-only updates assigned to distinct experts commute. -/
theorem winnerStep_commute_of_ne
    {firstWinner secondWinner : Mechanism}
    (different : firstWinner ≠ secondWinner)
    (firstDynamics secondDynamics : Dynamics Mechanism Input Hidden)
    (firstInput secondInput : Input)
    (state : State Mechanism Hidden) :
    winnerStep firstWinner firstDynamics firstInput
        (winnerStep secondWinner secondDynamics secondInput state) =
      winnerStep secondWinner secondDynamics secondInput
        (winnerStep firstWinner firstDynamics firstInput state) := by
  apply independentStep_commute_of_disjoint
  simp [Finset.disjoint_singleton_left, different]

/-! ## Executable positive and negative fixtures -/

abbrev TwoExperts := Fin 2

def zeroExpertState : State TwoExperts ℕ :=
  fun _ => 0

def addOneDynamics : Dynamics TwoExperts Unit ℕ :=
  fun _expert hidden _input => hidden + 1

def addTenDynamics : Dynamics TwoExperts Unit ℕ :=
  fun _expert hidden _input => hidden + 10

theorem distinct_winners_commute :
    winnerStep 0 addOneDynamics ()
        (winnerStep 1 addTenDynamics () zeroExpertState) =
      winnerStep 1 addTenDynamics ()
        (winnerStep 0 addOneDynamics () zeroExpertState) := by
  exact winnerStep_commute_of_ne (by decide) _ _ _ _ _

def doubleDynamics : Dynamics TwoExperts Unit ℕ :=
  fun _expert hidden _input => 2 * hidden

/-- Disjointness is a real boundary: adding one and doubling the same expert
produce different final states in the two possible orders. -/
theorem overlapping_winner_updates_do_not_commute :
    winnerStep 0 addOneDynamics ()
        (winnerStep 0 doubleDynamics () zeroExpertState) ≠
      winnerStep 0 doubleDynamics ()
        (winnerStep 0 addOneDynamics () zeroExpertState) := by
  intro equalStates
  have atWinner := congrFun equalStates 0
  norm_num [winnerStep, independentStep, addOneDynamics, doubleDynamics,
    zeroExpertState] at atWinner

#print axioms winnerStep_eq_of_ne
#print axioms independentStep_commute_of_disjoint
#print axioms winnerStep_commute_of_ne
#print axioms distinct_winners_commute
#print axioms overlapping_winner_updates_do_not_commute

end CompetitiveIndependentMechanisms

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
