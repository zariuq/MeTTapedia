import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics

/-!
# Linear state-space cells and associative scan

An input-driven affine state-space cell has transition `x ↦ A x + B u + b`
and a linear readout.  A unit-gate one-slot workspace recovers this transition
on the nose; a fixed gate recovers the usual damped interpolation toward it.

Affine state transitions compose associatively.  The prefix scan of those
transitions therefore computes exactly the ordinary sequential trajectory.
This is a correctness license for parallel prefix implementations, not a
performance theorem and not a nonlinear selective-SSM claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

universe uState uInput uOutput

/-! ## Input-driven affine cell -/

/-- A real linear time-invariant state-space cell with affine state bias and
linear readout. -/
structure LinearStateSpaceCell
    (State : Type uState) (Input : Type uInput) (Output : Type uOutput)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output] where
  stateTransition : State →L[ℝ] State
  inputTransition : Input →L[ℝ] State
  bias : State
  readout : State →L[ℝ] Output

namespace LinearStateSpaceCell

variable {State : Type uState} {Input : Type uInput} {Output : Type uOutput}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Input] [NormedSpace ℝ Input]
  [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- Standard affine LTI state transition. -/
noncomputable def step (cell : LinearStateSpaceCell State Input Output)
    (state : State) (input : Input) : State :=
  cell.stateTransition state + cell.inputTransition input + cell.bias

/-- Standard linear state readout. -/
noncomputable def output (cell : LinearStateSpaceCell State Input Output)
    (state : State) : Output :=
  cell.readout state

/-- One reusable operator whose proposal is the next LTI state and whose gate
is fixed. -/
noncomputable def fixedGateWorkspaceFamily
    (cell : LinearStateSpaceCell State Input Output) (input : Input) (gate : ℝ) :
    GatedOperatorFamily (Fin 1) (Fin 1) State Unit Unit where
  read := fun _ _ => ()
  transform := fun _ _ => ()
  gate := fun _ _ _ _ => gate
  write := fun _ workspace _ _ => cell.step (workspace 0) input

/-- Fixed-gate workspace instantiation: one workspace step is exactly damped
interpolation toward the affine LTI proposal. -/
theorem fixedGateWorkspaceStep_eq_standard
    (cell : LinearStateSpaceCell State Input Output)
    (input : Input) (gate : ℝ) (workspace : Workspace (Fin 1) State) :
    (cell.fixedGateWorkspaceFamily input gate).step workspace 0 =
      workspace 0 + gate • (cell.step (workspace 0) input - workspace 0) := by
  simp [fixedGateWorkspaceFamily, GatedOperatorFamily.step,
    GatedOperatorFamily.operatorAverageScale, GatedOperatorFamily.gateAt,
    GatedOperatorFamily.contentAt, GatedOperatorFamily.latent]

/-- Unit-gate workspace instantiation: the workspace step recovers the LTI SSM
transition `A x + B u + b` on the nose. -/
theorem unitGateWorkspaceStep_eq_lti
    (cell : LinearStateSpaceCell State Input Output)
    (input : Input) (workspace : Workspace (Fin 1) State) :
    (cell.fixedGateWorkspaceFamily input 1).step workspace 0 =
      cell.stateTransition (workspace 0) + cell.inputTransition input + cell.bias := by
  rw [cell.fixedGateWorkspaceStep_eq_standard]
  simp [step]

end LinearStateSpaceCell

/-! ## Affine-transition monoid -/

/-- An affine endomorphism represented by its linear part and offset. -/
structure AffineTransition
    (State : Type uState) [NormedAddCommGroup State] [NormedSpace ℝ State] where
  linear : State →L[ℝ] State
  offset : State

namespace AffineTransition

variable {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Extensionality for the linear and offset representation. -/
@[ext] theorem ext'
    {first second : AffineTransition State}
    (hlinear : first.linear = second.linear)
    (hoffset : first.offset = second.offset) : first = second := by
  cases first
  cases second
  cases hlinear
  cases hoffset
  rfl

/-- Apply an affine transition to a state. -/
noncomputable def act (transition : AffineTransition State) (state : State) : State :=
  transition.linear state + transition.offset

/-- Sequential composition: `first.compose second` means apply `first`, then
`second`.  This orientation makes a left-to-right scan follow input order. -/
noncomputable def compose
    (first second : AffineTransition State) : AffineTransition State where
  linear := second.linear.comp first.linear
  offset := second.linear first.offset + second.offset

/-- Identity affine transition. -/
noncomputable def identity : AffineTransition State where
  linear := ContinuousLinearMap.id ℝ State
  offset := 0

@[simp] theorem act_compose
    (first second : AffineTransition State) (state : State) :
    (first.compose second).act state = second.act (first.act state) := by
  simp [act, compose, map_add, add_assoc]

@[simp] theorem act_identity (state : State) :
    (identity : AffineTransition State).act state = state := by
  simp [act, identity]

theorem compose_assoc (first second third : AffineTransition State) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  apply AffineTransition.ext'
  · ext state
    rfl
  · simp [compose, map_add, add_assoc]

theorem identity_compose (transition : AffineTransition State) :
    identity.compose transition = transition := by
  apply AffineTransition.ext'
  · ext state
    rfl
  · simp [identity, compose]

theorem compose_identity (transition : AffineTransition State) :
    transition.compose identity = transition := by
  apply AffineTransition.ext'
  · ext state
    rfl
  · simp [identity, compose]

noncomputable instance : Monoid (AffineTransition State) where
  one := identity
  mul := compose
  one_mul := identity_compose
  mul_one := compose_identity
  mul_assoc := compose_assoc

@[simp] theorem act_one (state : State) :
    (1 : AffineTransition State).act state = state :=
  act_identity state

@[simp] theorem act_mul
    (first second : AffineTransition State) (state : State) :
    (first * second).act state = second.act (first.act state) :=
  act_compose first second state

end AffineTransition

/-! ## SSM transition scan -/

namespace LinearStateSpaceCell

variable {State : Type uState} {Input : Type uInput} {Output : Type uOutput}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Input] [NormedSpace ℝ Input]
  [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- Affine transition contributed by one input token. -/
noncomputable def affineTransition
    (cell : LinearStateSpaceCell State Input Output) (input : Input) :
    AffineTransition State where
  linear := cell.stateTransition
  offset := cell.inputTransition input + cell.bias

@[simp] theorem affineTransition_act
    (cell : LinearStateSpaceCell State Input Output)
    (input : Input) (state : State) :
    (cell.affineTransition input).act state = cell.step state input := by
  simp [affineTransition, AffineTransition.act, step, add_assoc]

/-- Prefix scan from an accumulated affine transition. -/
noncomputable def affineScanFrom
    (cell : LinearStateSpaceCell State Input Output) :
    AffineTransition State → List Input → List (AffineTransition State)
  | accumulator, [] => [accumulator]
  | accumulator, input :: inputs =>
      accumulator :: affineScanFrom cell
        (accumulator * cell.affineTransition input) inputs

/-- Prefix scan of affine transitions.  Associativity of the monoid is the
algebraic condition required by a parallel prefix implementation. -/
noncomputable def affinePrefixScan
    (cell : LinearStateSpaceCell State Input Output) (inputs : List Input) :
    List (AffineTransition State) :=
  affineScanFrom cell 1 inputs

/-- Sequential trajectory from an accumulated state. -/
noncomputable def trajectoryFrom
    (cell : LinearStateSpaceCell State Input Output) :
    State → List Input → List State
  | state, [] => [state]
  | state, input :: inputs =>
      state :: trajectoryFrom cell (cell.step state input) inputs

/-- Ordinary sequential state trajectory, including the initial state. -/
noncomputable def trajectory
    (cell : LinearStateSpaceCell State Input Output)
    (initial : State) (inputs : List Input) : List State :=
  trajectoryFrom cell initial inputs

private theorem affinePrefixScan_correct_aux
    (cell : LinearStateSpaceCell State Input Output)
    (initial state : State) (inputs : List Input)
    (accumulator : AffineTransition State)
    (haccumulator : accumulator.act initial = state) :
    (cell.affineScanFrom accumulator inputs).map
        (fun transition => transition.act initial) =
      cell.trajectoryFrom state inputs := by
  induction inputs generalizing accumulator state with
  | nil =>
      change [accumulator.act initial] = [state]
      rw [haccumulator]
  | cons input inputs ih =>
      simp only [affineScanFrom, trajectoryFrom, List.map_cons]
      rw [haccumulator]
      congr 1
      apply ih
      simp [haccumulator]

/-- Parallel-scan correctness crown: applying every affine prefix product to
the initial state yields exactly the sequential LTI trajectory. -/
theorem affinePrefixScan_correct
    (cell : LinearStateSpaceCell State Input Output)
    (initial : State) (inputs : List Input) :
    (cell.affinePrefixScan inputs).map
        (fun transition => transition.act initial) =
      cell.trajectory initial inputs := by
  apply affinePrefixScan_correct_aux cell initial initial inputs 1
  exact AffineTransition.act_one initial

end LinearStateSpaceCell

/-! ## Positive and negative scan fixtures -/

namespace StateSpaceFixtures

/-- Scalar affine cell `x ↦ 2x + u`. -/
noncomputable def scalarCell : LinearStateSpaceCell ℝ ℝ ℝ where
  stateTransition := 2 • ContinuousLinearMap.id ℝ ℝ
  inputTransition := ContinuousLinearMap.id ℝ ℝ
  bias := 0
  readout := ContinuousLinearMap.id ℝ ℝ

/-- The scan and sequential recurrence agree on a concrete two-input path. -/
theorem scalarCell_scan_positiveExample :
    ((scalarCell.affinePrefixScan [1, 2]).map
      (fun transition => transition.act 0)) = [0, 1, 4] := by
  rw [LinearStateSpaceCell.affinePrefixScan_correct]
  norm_num [LinearStateSpaceCell.trajectory, LinearStateSpaceCell.trajectoryFrom,
    LinearStateSpaceCell.step, scalarCell]

/-- Affine composition is associative but not commutative; reversing token
order changes this trajectory. -/
theorem scalarCell_orderMatters_negativeExample :
    (scalarCell.affineTransition 1 * scalarCell.affineTransition 2).act 0 ≠
      (scalarCell.affineTransition 2 * scalarCell.affineTransition 1).act 0 := by
  norm_num [AffineTransition.act_mul, LinearStateSpaceCell.affineTransition_act,
    LinearStateSpaceCell.step, scalarCell]

end StateSpaceFixtures

#print axioms LinearStateSpaceCell.fixedGateWorkspaceStep_eq_standard
#print axioms LinearStateSpaceCell.unitGateWorkspaceStep_eq_lti
#print axioms AffineTransition.compose_assoc
#print axioms LinearStateSpaceCell.affinePrefixScan_correct
#print axioms StateSpaceFixtures.scalarCell_scan_positiveExample
#print axioms StateSpaceFixtures.scalarCell_orderMatters_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
