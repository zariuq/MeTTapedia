import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Recurrent independent mechanisms

Goyal et al., *Recurrent Independent Mechanisms* (arXiv:1909.10893),
separate one recurrent step into three decisions:

* an attention-derived finite set of active mechanisms;
* a mechanism-local recurrent transition for every active mechanism, while
  inactive mechanisms remain unchanged;
* a communication phase in which active mechanisms may read the complete
  post-transition state, while inactive mechanisms again remain unchanged.

This file isolates those execution invariants independently of the particular
top-k selector, GRU or LSTM cell, and key-value attention implementation.  It
proves exact inactive-state preservation, bounds the support of a step by the
active set, and shows that changing transition functions outside the active set
cannot affect the result.  A two-mechanism fixture also records the important
boundary: sparse updating does not imply that active mechanisms are
informationally independent of dormant memory, because communication may read
inactive state.

No theorem here claims that a learned selector discovers causal mechanisms, or
that sparse execution improves generalization or computational cost.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace RecurrentIndependentMechanisms

/-- A bank of mechanism states. -/
abbrev State (Mechanism Hidden : Type*) := Mechanism → Hidden

/-- One separately parameterized local transition per mechanism. -/
abbrev Dynamics (Mechanism Input Hidden : Type*) :=
  Mechanism → Hidden → Input → Hidden

/-- An active mechanism may communicate with the entire intermediate state.
The final argument is its own intermediate state, making residual
communication a direct instance. -/
abbrev Communicator (Mechanism Hidden : Type*) :=
  Mechanism → State Mechanism Hidden → Hidden → Hidden

variable {Mechanism Input Hidden : Type*} [DecidableEq Mechanism]

/-- Source Section 2.3: update active mechanisms with their own dynamics and
leave every inactive mechanism untouched. -/
def independentStep
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    State Mechanism Hidden :=
  fun mechanism =>
    if mechanism ∈ active then
      dynamics mechanism (state mechanism) input
    else
      state mechanism

/-- Source Section 2.4: active mechanisms may read the complete intermediate
state, whereas inactive mechanisms remain untouched. -/
def communicationStep
    (active : Finset Mechanism)
    (communicate : Communicator Mechanism Hidden)
    (state : State Mechanism Hidden) :
    State Mechanism Hidden :=
  fun mechanism =>
    if mechanism ∈ active then
      communicate mechanism state (state mechanism)
    else
      state mechanism

/-- One sparse recurrent-independent-mechanism step. -/
def step
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    State Mechanism Hidden :=
  communicationStep active communicate
    (independentStep active dynamics input state)

/-- Inactive mechanisms remain exactly unchanged through both phases. -/
theorem step_eq_of_not_mem
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden)
    {mechanism : Mechanism}
    (inactive : mechanism ∉ active) :
    step active dynamics communicate input state mechanism =
      state mechanism := by
  simp [step, communicationStep, independentStep, inactive]

/-- The independent phase only consults the local transition associated with
the queried active mechanism. -/
theorem independentStep_eq_of_mem
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (input : Input)
    (state : State Mechanism Hidden)
    {mechanism : Mechanism}
    (activated : mechanism ∈ active) :
    independentStep active dynamics input state mechanism =
      dynamics mechanism (state mechanism) input := by
  simp [independentStep, activated]

/-- Replacing transition functions outside the active set cannot change the
independent phase. -/
theorem independentStep_eq_of_dynamics_agree_on_active
    (active : Finset Mechanism)
    (left right : Dynamics Mechanism Input Hidden)
    (input : Input)
    (state : State Mechanism Hidden)
    (agree : ∀ mechanism ∈ active, left mechanism = right mechanism) :
    independentStep active left input state =
      independentStep active right input state := by
  funext mechanism
  by_cases activated : mechanism ∈ active
  · simp [independentStep, activated, agree mechanism activated]
  · simp [independentStep, activated]

/-- The same locality survives the communication phase because both runs
present the communicator with the identical intermediate state. -/
theorem step_eq_of_dynamics_agree_on_active
    (active : Finset Mechanism)
    (left right : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden)
    (agree : ∀ mechanism ∈ active, left mechanism = right mechanism) :
    step active left communicate input state =
      step active right communicate input state := by
  rw [step, step, independentStep_eq_of_dynamics_agree_on_active
    active left right input state agree]

/-- Coordinates changed by one sparse step. -/
def changedMechanisms
    [Fintype Mechanism] [DecidableEq Hidden]
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    Finset Mechanism :=
  Finset.univ.filter fun mechanism =>
    step active dynamics communicate input state mechanism ≠ state mechanism

/-- The actual write support is contained in the selected active set. -/
theorem changedMechanisms_subset_active
    [Fintype Mechanism] [DecidableEq Hidden]
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    changedMechanisms active dynamics communicate input state ⊆ active := by
  intro mechanism changed
  simp only [changedMechanisms, Finset.mem_filter, Finset.mem_univ, true_and] at changed
  by_contra inactive
  exact changed
    (step_eq_of_not_mem active dynamics communicate input state inactive)

/-- Consequently, one step changes no more coordinates than its activation
budget permits. -/
theorem card_changedMechanisms_le_active
    [Fintype Mechanism] [DecidableEq Hidden]
    (active : Finset Mechanism)
    (dynamics : Dynamics Mechanism Input Hidden)
    (communicate : Communicator Mechanism Hidden)
    (input : Input)
    (state : State Mechanism Hidden) :
    (changedMechanisms active dynamics communicate input state).card ≤
      active.card :=
  Finset.card_le_card
    (changedMechanisms_subset_active active dynamics communicate input state)

/-! ## Executable positive and negative fixtures -/

abbrev TwoMechanisms := Fin 2

def activateFirst : Finset TwoMechanisms := {0}

def initialFixture : State TwoMechanisms ℕ
  | 0 => 3
  | 1 => 7

def incrementDynamics : Dynamics TwoMechanisms Unit ℕ :=
  fun _mechanism hidden _input => hidden + 1

def identityCommunication : Communicator TwoMechanisms ℕ :=
  fun _mechanism _state own => own

theorem sparse_update :
    step activateFirst incrementDynamics identityCommunication ()
          initialFixture 0 = 4 ∧
      step activateFirst incrementDynamics identityCommunication ()
          initialFixture 1 = 7 := by
  decide

/-- Communication may use dormant memory without mutating it. -/
def readDormantCommunication : Communicator TwoMechanisms ℕ :=
  fun mechanism state own =>
    if mechanism = 0 then own + state 1 else own

theorem active_mechanism_reads_inactive_memory :
    step activateFirst incrementDynamics readDormantCommunication ()
          initialFixture 0 = 11 ∧
      step activateFirst incrementDynamics readDormantCommunication ()
          initialFixture 1 = 7 := by
  decide

/-- Sparse write support is not a claim of informational independence:
changing only dormant memory can change an active mechanism after
communication. -/
theorem sparse_update_does_not_imply_active_output_independence :
    let changedDormant : State TwoMechanisms ℕ :=
      fun mechanism => if mechanism = 1 then 9 else initialFixture mechanism
    step activateFirst incrementDynamics readDormantCommunication ()
        initialFixture 0 ≠
      step activateFirst incrementDynamics readDormantCommunication ()
        changedDormant 0 := by
  decide

#print axioms step_eq_of_not_mem
#print axioms independentStep_eq_of_dynamics_agree_on_active
#print axioms step_eq_of_dynamics_agree_on_active
#print axioms changedMechanisms_subset_active
#print axioms card_changedMechanisms_le_active
#print axioms sparse_update_does_not_imply_active_output_independence

end RecurrentIndependentMechanisms

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
