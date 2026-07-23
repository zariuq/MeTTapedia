import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TemporalEquilibrium
import Mathlib.Tactic

/-!
# Auxiliary splitting, detached objectives, and optimizer transport

These mechanisms occupy three different layers of a training system.
Auxiliary-variable methods update blocks of a constrained surrogate.  Detached
local objectives supply credit from an objective other than the terminal task.
Optimizer transport transforms a credit vector after that vector already
exists.  Keeping the layers separate prevents local improvement or positive
definiteness from being promoted into an unsupported task-descent claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

/-! ## Convex consensus splitting -/

structure ConsensusState where
  x : ℝ
  z : ℝ
  scaledDual : ℝ

/-- One scaled-ADMM step for
`min (x-1)^2/2 + (z+1)^2/2` subject to `x=z`, at penalty one. -/
noncomputable def consensusStep (state : ConsensusState) : ConsensusState :=
  let nextX := (1 + state.z - state.scaledDual) / 2
  let nextZ := (nextX + state.scaledDual - 1) / 2
  { x := nextX
    z := nextZ
    scaledDual := state.scaledDual + nextX - nextZ }

noncomputable def consensusObjective (state : ConsensusState) : ℝ :=
  (state.x - 1) ^ 2 / 2 + (state.z + 1) ^ 2 / 2

def consensusResidual (state : ConsensusState) : ℝ := state.x - state.z

def consensusFixedPoint : ConsensusState :=
  { x := 0, z := 0, scaledDual := 1 }

theorem consensusStep_fixed : consensusStep consensusFixedPoint = consensusFixedPoint := by
  norm_num [consensusStep, consensusFixedPoint]

/-- On the constraint, the convex objective is minimized uniquely at zero. -/
theorem consensus_constrained_objective_gap (value : ℝ) :
    consensusObjective { x := value, z := value, scaledDual := 0 } =
      value ^ 2 + 1 := by
  simp [consensusObjective]
  ring

theorem consensus_constrained_minimum (value : ℝ) :
    1 ≤ consensusObjective { x := value, z := value, scaledDual := 0 } := by
  rw [consensus_constrained_objective_gap]
  nlinarith [sq_nonneg value]

def consensusInitial : ConsensusState := { x := 0, z := 0, scaledDual := 0 }

theorem consensus_first_three_steps :
    consensusStep consensusInitial =
        { x := 1 / 2, z := -1 / 4, scaledDual := 3 / 4 } ∧
    consensusStep (consensusStep consensusInitial) =
        { x := 0, z := -1 / 8, scaledDual := 7 / 8 } ∧
    consensusStep (consensusStep (consensusStep consensusInitial)) =
        { x := 0, z := -1 / 16, scaledDual := 15 / 16 } := by
  norm_num [consensusStep, consensusInitial]

theorem consensus_residual_halves_after_first_step :
    |consensusResidual
        (consensusStep (consensusStep (consensusStep consensusInitial)))| =
      |consensusResidual (consensusStep (consensusStep consensusInitial))| / 2 := by
  norm_num [consensusResidual, consensusStep, consensusInitial, abs_of_nonneg]

def auxiliaryBlockOracle : OracleAudit where
  accesses := [.auxiliaryBlockSolve, .auxiliaryBlockSolve]

/-! ## Nonconvex alternating-minimization boundary -/

noncomputable def factorLoss (weight activation : ℝ) : ℝ :=
  (weight * activation - 1) ^ 2 / 2

/-- At the origin each individual block is flat: every update of one block
while the other stays zero is a block minimizer with the same loss. -/
theorem factorLoss_zero_activation_flat (weight : ℝ) :
    factorLoss weight 0 = factorLoss 0 0 := by
  simp [factorLoss]

theorem factorLoss_zero_weight_flat (activation : ℝ) :
    factorLoss 0 activation = factorLoss 0 0 := by
  simp [factorLoss]

/-- The coordinatewise stall is not globally optimal. -/
theorem factorLoss_coordinatewise_stall_not_global :
    factorLoss 0 0 = 1 / 2 ∧ factorLoss 1 1 = 0 ∧
      factorLoss 1 1 < factorLoss 0 0 := by
  norm_num [factorLoss]

/-! ## Detached local objectives -/

noncomputable def halfSquaredLoss (value target : ℝ) : ℝ := (value - target) ^ 2 / 2

noncomputable def localRepresentationLoss (representation : ℝ) : ℝ :=
  halfSquaredLoss representation 1

noncomputable def alignedTerminalLoss (representation : ℝ) : ℝ :=
  halfSquaredLoss representation 1

noncomputable def opposedTerminalLoss (representation : ℝ) : ℝ :=
  halfSquaredLoss (-representation) 1

theorem aligned_local_update_improves_both :
    localRepresentationLoss 1 < localRepresentationLoss 0 ∧
      alignedTerminalLoss 1 < alignedTerminalLoss 0 := by
  norm_num [localRepresentationLoss, alignedTerminalLoss, halfSquaredLoss]

/-- The identical representation update can solve its detached local objective
while making a sign-opposed terminal readout four times worse. -/
theorem local_improvement_can_worsen_terminal :
    localRepresentationLoss 1 = 0 ∧
      localRepresentationLoss 1 < localRepresentationLoss 0 ∧
      opposedTerminalLoss 1 = 4 * opposedTerminalLoss 0 := by
  norm_num [localRepresentationLoss, opposedTerminalLoss, halfSquaredLoss]

def detachedLocalObjectiveOracle : OracleAudit where
  accesses := [.detachedLocalObjective]
  teacherDependent := true

/-! ## Post-credit optimizer transport -/

namespace FeedbackMap2

/-- A symmetric positive-definite map used to separate exact-gradient and
inexact-credit composition. -/
def reversingPreconditioner : FeedbackMap2 :=
  { row00 := 1, row01 := -2, row10 := -2, row11 := 5 }

theorem reversingPreconditioner_quadratic_form (vector : CreditVec2) :
    vector.dot (reversingPreconditioner.apply vector) =
      (vector.first - 2 * vector.second) ^ 2 + vector.second ^ 2 := by
  simp [CreditVec2.dot, apply, reversingPreconditioner]
  ring

/-- The concrete map is genuinely positive definite, not merely declared so. -/
theorem reversingPreconditioner_positive
    (vector : CreditVec2) (nonzero : vector ≠ CreditVec2.zero) :
    0 < vector.dot (reversingPreconditioner.apply vector) := by
  rw [reversingPreconditioner_quadratic_form]
  by_cases secondZero : vector.second = 0
  · have firstNonzero : vector.first ≠ 0 := by
      intro firstZero
      apply nonzero
      ext <;> simp [CreditVec2.zero, firstZero, secondZero]
    rw [secondZero]
    simpa using sq_pos_of_ne_zero firstNonzero
  · have secondSquarePositive : 0 < vector.second ^ 2 := sq_pos_of_ne_zero secondZero
    nlinarith [sq_nonneg (vector.first - 2 * vector.second)]

/-- Positive-definite transport preserves a positive exact-gradient margin. -/
theorem reversingPreconditioner_exact_gradient_margin
    (gradient : CreditVec2) (nonzero : gradient ≠ CreditVec2.zero) :
    0 < gradient.dot (reversingPreconditioner.apply gradient) :=
  reversingPreconditioner_positive gradient nonzero

/-- Positive definiteness does not preserve alignment of an arbitrary inexact
credit vector with the true task gradient. -/
theorem reversingPreconditioner_reverses_inexact_credit :
    let gradient : CreditVec2 := ⟨1, 0⟩
    let alternativeCredit : CreditVec2 := ⟨1, 1⟩
    0 < gradient.dot alternativeCredit ∧
      gradient.dot (reversingPreconditioner.apply alternativeCredit) < 0 := by
  norm_num [CreditVec2.dot, apply, reversingPreconditioner]

end FeedbackMap2

def parameterTransportOracle : OracleAudit where
  accesses := [.parameterUpdateTransform]

#print axioms consensus_constrained_minimum
#print axioms consensus_residual_halves_after_first_step
#print axioms factorLoss_coordinatewise_stall_not_global
#print axioms aligned_local_update_improves_both
#print axioms local_improvement_can_worsen_terminal
#print axioms FeedbackMap2.reversingPreconditioner_positive
#print axioms FeedbackMap2.reversingPreconditioner_reverses_inexact_credit

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
