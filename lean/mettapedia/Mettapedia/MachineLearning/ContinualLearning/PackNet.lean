import Mathlib.Tactic

/-!
# Iterative parameter packing

Mallya and Lazebnik (2018), *PackNet: Adding Multiple Tasks to a Single
Network by Iterative Pruning*, assign surviving weights permanently to the
task that first claimed them.  Later training updates only still-free
parameters.  At inference, task `t` enables exactly the parameters whose
birth task is at most `t`, so later tasks reuse earlier weights while later
assignments are invisible to earlier tasks.

This file gives that ownership discipline an executable semantics.  Any
finite sequence of free-parameter updates and strictly later assignments
preserves an earlier task's masked weights and linear readout exactly.  A
single birth label determines a monotone suffix of task masks, recovering the
source's compressed-mask observation.

Two boundaries prevent overclaiming.  Once no parameter is free, the training
operator is the identity, so preservation has exhausted plasticity.
Furthermore, task-specific masked activations cannot in general be recovered
by summing post-nonlinearity contributions: a concrete rectifier fixture
records the source's simultaneous-inference warning.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace PackNet

noncomputable section

/-- A packed parameter has a real value and either no owner or the task that
first claimed it. -/
structure State (Parameter : Type*) where
  weight : Parameter → ℝ
  owner : Parameter → Option ℕ

/-- A task sees all parameters born no later than itself and no free or future
parameters. -/
def maskedWeight
    (state : State Parameter) (task : ℕ) (parameter : Parameter) : ℝ :=
  match state.owner parameter with
  | none => 0
  | some birth =>
      if birth ≤ task then state.weight parameter else 0

/-- The proposition underlying a task's binary inference mask. -/
def Visible
    (state : State Parameter) (task : ℕ) (parameter : Parameter) : Prop :=
  ∃ birth, state.owner parameter = some birth ∧ birth ≤ task

/-- A training displacement changes exactly the still-free parameters. -/
def freeUpdate
    (state : State Parameter) (displacement : Parameter → ℝ) :
    State Parameter where
  weight parameter :=
    match state.owner parameter with
    | none => state.weight parameter + displacement parameter
    | some _ => state.weight parameter
  owner := state.owner

/-- Claim a selected subset of free parameters for the current task.  Already
owned parameters retain both their value and their original birth label. -/
def assignFree
    (state : State Parameter) (task : ℕ)
    (selected : Parameter → Bool) : State Parameter where
  weight := state.weight
  owner parameter :=
    match state.owner parameter, selected parameter with
    | none, true => some task
    | owner, _ => owner

/-- Free-parameter training cannot alter any already-defined task mask. -/
@[simp] theorem maskedWeight_freeUpdate
    (state : State Parameter) (displacement : Parameter → ℝ) (task : ℕ) :
    maskedWeight (freeUpdate state displacement) task =
      maskedWeight state task := by
  funext parameter
  simp [maskedWeight, freeUpdate]
  split <;> rfl

/-- Assigning free parameters to a strictly later task leaves an earlier
task's masked weights exactly unchanged. -/
theorem maskedWeight_assignFree_of_lt
    (state : State Parameter) (current earlier : ℕ)
    (selected : Parameter → Bool) (later : earlier < current) :
    maskedWeight (assignFree state current selected) earlier =
      maskedWeight state earlier := by
  funext parameter
  cases ownerEquation : state.owner parameter with
  | none =>
      cases selectedEquation : selected parameter <;>
        simp [maskedWeight, assignFree, ownerEquation,
          selectedEquation, Nat.not_le.mpr later]
  | some birth =>
      cases selectedEquation : selected parameter <;>
        simp [maskedWeight, assignFree, ownerEquation, selectedEquation]

/-- A typed trace of operations that occur strictly after `earlier`. -/
inductive LaterStep (Parameter : Type*) (earlier : ℕ)
  | update (displacement : Parameter → ℝ)
  | assign
      (task : ℕ) (later : earlier < task) (selected : Parameter → Bool)

def applyLaterStep
    (state : State Parameter) :
    LaterStep Parameter earlier → State Parameter
  | .update displacement => freeUpdate state displacement
  | .assign task _ selected => assignFree state task selected

def runLaterSteps
    (state : State Parameter) :
    List (LaterStep Parameter earlier) → State Parameter
  | [] => state
  | step :: rest =>
      runLaterSteps (applyLaterStep state step) rest

/-- One admissible later operation preserves the earlier mask. -/
theorem maskedWeight_applyLaterStep
    (state : State Parameter) (step : LaterStep Parameter earlier) :
    maskedWeight (applyLaterStep state step) earlier =
      maskedWeight state earlier := by
  cases step with
  | update displacement =>
      exact maskedWeight_freeUpdate state displacement earlier
  | assign task later selected =>
      exact maskedWeight_assignFree_of_lt
        state task earlier selected later

/-- PackNet's architectural no-forgetting core: every finite admissible future
trace preserves the earlier task's complete masked parameter vector. -/
theorem maskedWeight_runLaterSteps
    (state : State Parameter)
    (steps : List (LaterStep Parameter earlier)) :
    maskedWeight (runLaterSteps state steps) earlier =
      maskedWeight state earlier := by
  induction steps generalizing state with
  | nil =>
      rfl
  | cons step rest inductionHypothesis =>
      rw [runLaterSteps, inductionHypothesis,
        maskedWeight_applyLaterStep]

/-- A finite linear layer evaluated under the selected task mask. -/
def linearReadout
    [Fintype Parameter]
    (state : State Parameter) (task : ℕ)
    (input : Parameter → ℝ) : ℝ :=
  ∑ parameter, maskedWeight state task parameter * input parameter

/-- The same finite trace preserves every earlier masked linear readout. -/
theorem linearReadout_runLaterSteps
    [Fintype Parameter]
    (state : State Parameter)
    (steps : List (LaterStep Parameter earlier))
    (input : Parameter → ℝ) :
    linearReadout (runLaterSteps state steps) earlier input =
      linearReadout state earlier input := by
  simp [linearReadout, maskedWeight_runLaterSteps]

/-! ## Mask compression and reuse -/

/-- Once a parameter is visible, every later task sees it as well. -/
theorem visible_mono
    (state : State Parameter) (parameter : Parameter)
    {earlier later : ℕ}
    (visible : Visible state earlier parameter)
    (ordered : earlier ≤ later) :
    Visible state later parameter := by
  rcases visible with ⟨birth, owner, born⟩
  exact ⟨birth, owner, born.trans ordered⟩

/-- An owned parameter becomes visible exactly at and after its birth task. -/
theorem visible_iff_birth_le
    (state : State Parameter) (parameter : Parameter)
    (birth task : ℕ)
    (owner : state.owner parameter = some birth) :
    Visible state task parameter ↔ birth ≤ task := by
  constructor
  · rintro ⟨otherBirth, otherOwner, visible⟩
    rw [owner] at otherOwner
    cases Option.some.inj otherOwner
    exact visible
  · intro visible
    exact ⟨birth, owner, visible⟩

/-- A later task reuses an earlier task's parameter value without copying it. -/
theorem maskedWeight_eq_weight_of_birth_le
    (state : State Parameter) (parameter : Parameter)
    (birth task : ℕ)
    (owner : state.owner parameter = some birth)
    (visible : birth ≤ task) :
    maskedWeight state task parameter = state.weight parameter := by
  simp [maskedWeight, owner, visible]

/-! ## Capacity and nonlinearity boundaries -/

/-- No parameter remains available for a new task. -/
def HasNoFreeParameters (state : State Parameter) : Prop :=
  ∀ parameter, state.owner parameter ≠ none

/-- Once capacity is exhausted, every attempted free-parameter training step
is the identity. -/
theorem freeUpdate_eq_of_noFreeParameters
    (state : State Parameter) (displacement : Parameter → ℝ)
    (exhausted : HasNoFreeParameters state) :
    freeUpdate state displacement = state := by
  cases state with
  | mk weight owner =>
      simp only [freeUpdate]
      rw [State.mk.injEq]
      constructor
      · funext parameter
        cases ownerEquation : owner parameter with
        | none =>
            exact False.elim (exhausted parameter ownerEquation)
        | some task =>
            rfl
      · rfl

/-- Scalar rectifier used only to state the simultaneous-inference boundary. -/
def relu (value : ℝ) : ℝ :=
  max value 0

/-- Parameter-wise task superposition does not commute with nonlinear
activation.  Hence one full-network pass cannot generally be decomposed into
all task-specific masked responses after the activation. -/
theorem relu_taskContributions_not_additive :
    relu ((1 : ℝ) + (-2)) ≠ relu 1 + relu (-2) := by
  norm_num [relu, max_def]

/-! ## Executable ownership fixtures -/

abbrev TwoParameters := Fin 2

def packedFixture : State TwoParameters where
  weight parameter := if parameter = 0 then 3 else 5
  owner parameter := if parameter = 0 then some 0 else none

/-- Task zero sees its owned weight and masks the still-free parameter. -/
theorem initial_mask :
    maskedWeight packedFixture 0 0 = 3 ∧
      maskedWeight packedFixture 0 1 = 0 := by
  norm_num [maskedWeight, packedFixture]

/-- A free update followed by assignment to task one leaves task zero
unchanged while making the newly claimed weight available to task one. -/
theorem later_assignment_preserves_old_and_enables_new :
    let updated :=
      freeUpdate packedFixture
        (fun parameter => if parameter = 1 then 2 else 0)
    let assigned :=
      assignFree updated 1 (fun parameter => parameter = 1)
    maskedWeight assigned 0 0 = 3 ∧
      maskedWeight assigned 0 1 = 0 ∧
      maskedWeight assigned 1 0 = 3 ∧
      maskedWeight assigned 1 1 = 7 := by
  norm_num [maskedWeight, packedFixture, freeUpdate, assignFree]

#print axioms maskedWeight_runLaterSteps
#print axioms linearReadout_runLaterSteps
#print axioms visible_mono
#print axioms visible_iff_birth_le
#print axioms freeUpdate_eq_of_noFreeParameters
#print axioms relu_taskContributions_not_additive
#print axioms later_assignment_preserves_old_and_enables_new

end

end PackNet

end Mettapedia.MachineLearning.ContinualLearning
