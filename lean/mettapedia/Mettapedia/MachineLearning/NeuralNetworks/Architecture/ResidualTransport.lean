import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ReZeroIgnition

/-!
# Residual transport and depth propagation

He, Zhang, Ren, and Sun, *Deep Residual Learning for Image Recognition*
(2015), define residual blocks by

`stateNext = branch state + state`

and projection blocks by

`stateNext = branch state + skip state`

in Equations (1)--(2).  This module recovers those architectures over an
arbitrary real normed state space and derives a reusable finite-depth
propagation theorem.  A residual branch with pairwise rate `L` gives its
whole block rate at most `1 + L`; a heterogeneous stack is therefore bounded
by the product of those factors.

The skip connection preserves the identity when every residual branch is
zero.  It does not by itself make a block nonexpansive: the identity branch
doubles the state.  Likewise, a projection shortcut is an identity endpoint
only when the projection itself is the identity.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace ResidualTransport

noncomputable section

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- One source Equation (1) residual block. -/
structure ResidualLayer (State : Type*) where
  branch : State → State

namespace ResidualLayer

/-- Execute one residual block. -/
def apply (layer : ResidualLayer State) (state : State) : State :=
  state + layer.branch state

/-- A residual block is the unit-gate member of the zero-gated family. -/
def asGated (layer : ResidualLayer State) :
    ReZeroIgnition.GatedResidualLayer State :=
  { gate := 1, branch := layer.branch }

@[simp]
theorem asGated_apply (layer : ResidualLayer State) (state : State) :
    layer.asGated.apply state = layer.apply state := by
  simp [asGated, apply, ReZeroIgnition.GatedResidualLayer.apply]

omit [NormedSpace ℝ State] in
/-- The exact identity endpoint of a residual block. -/
@[simp]
theorem apply_zero_branch (state : State) :
    (ResidualLayer.mk fun _ : State => 0).apply state = state := by
  simp [apply]

/-- A pairwise branch-rate certificate. -/
def BranchPairBound
    (layer : ResidualLayer State) (rate : ℝ) : Prop :=
  ∀ left right,
    ‖layer.branch left - layer.branch right‖ ≤
      rate * ‖left - right‖

omit [NormedSpace ℝ State] in
/-- Adding the identity skip increases a certified branch rate `rate` to at
most `1 + rate`. -/
theorem norm_apply_sub_apply_le
    (layer : ResidualLayer State) (rate : ℝ)
    (bound : layer.BranchPairBound rate)
    (left right : State) :
    ‖layer.apply left - layer.apply right‖ ≤
      (1 + rate) * ‖left - right‖ := by
  have expansion :
      layer.apply left - layer.apply right =
        (left - right) + (layer.branch left - layer.branch right) := by
    simp [apply]
    abel
  rw [expansion]
  calc
    ‖(left - right) +
        (layer.branch left - layer.branch right)‖ ≤
      ‖left - right‖ +
        ‖layer.branch left - layer.branch right‖ := norm_add_le _ _
    _ ≤ ‖left - right‖ + rate * ‖left - right‖ := by
      gcongr
      exact bound left right
    _ = (1 + rate) * ‖left - right‖ := by ring

end ResidualLayer

/-- A residual block paired with the nonnegative branch-rate certificate
used by the finite-depth theorem. -/
structure RatedResidualLayer (State : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State] where
  layer : ResidualLayer State
  rate : ℝ
  rate_nonnegative : 0 ≤ rate
  branch_pair_bound : layer.BranchPairBound rate

/-- Execute heterogeneous residual blocks in source order. -/
def runRated : List (RatedResidualLayer State) → State → State
  | [], state => state
  | layer :: layers, state =>
      runRated layers (layer.layer.apply state)

/-- Product propagation budget of a heterogeneous residual stack. -/
def residualRateProduct : List (RatedResidualLayer State) → ℝ
  | [] => 1
  | layer :: layers =>
      (1 + layer.rate) * residualRateProduct layers

theorem residualRateProduct_nonnegative
    (layers : List (RatedResidualLayer State)) :
    0 ≤ residualRateProduct layers := by
  induction layers with
  | nil => simp [residualRateProduct]
  | cons layer layers inductionHypothesis =>
      simp only [residualRateProduct]
      exact mul_nonneg (by linarith [layer.rate_nonnegative])
        inductionHypothesis

/-- Reusable depth theorem: the end-to-end pairwise rate is at most the
product of the residual-block factors. -/
theorem norm_runRated_sub_runRated_le
    (layers : List (RatedResidualLayer State))
    (left right : State) :
    ‖runRated layers left - runRated layers right‖ ≤
      residualRateProduct layers * ‖left - right‖ := by
  induction layers generalizing left right with
  | nil =>
      simp [runRated, residualRateProduct]
  | cons layer layers inductionHypothesis =>
      have blockBound :=
        layer.layer.norm_apply_sub_apply_le layer.rate
          layer.branch_pair_bound left right
      calc
        ‖runRated (layer :: layers) left -
            runRated (layer :: layers) right‖ =
          ‖runRated layers (layer.layer.apply left) -
            runRated layers (layer.layer.apply right)‖ := rfl
        _ ≤ residualRateProduct layers *
            ‖layer.layer.apply left - layer.layer.apply right‖ :=
          inductionHypothesis _ _
        _ ≤ residualRateProduct layers *
            ((1 + layer.rate) * ‖left - right‖) := by
          exact mul_le_mul_of_nonneg_left blockBound
            (residualRateProduct_nonnegative layers)
        _ = residualRateProduct (layer :: layers) *
            ‖left - right‖ := by
          simp [residualRateProduct]
          ring

/-- A stack of zero residual branches is exactly the identity, at every
finite depth. -/
theorem run_zero_branches
    (depth : ℕ) (state : State) :
    runRated
      (List.replicate depth
        { layer := ⟨fun _ : State => 0⟩
          rate := 0
          rate_nonnegative := le_rfl
          branch_pair_bound := by simp [ResidualLayer.BranchPairBound] })
      state =
    state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [List.replicate_succ, runRated, ResidualLayer.apply,
        inductionHypothesis]

/-! ## Projection shortcuts and negative boundaries -/

/-- Source Equation (2), allowing the skip path to change dimensions. -/
def projectedResidual
    {Input Output : Type*} [Add Output]
    (branch skip : Input → Output) (input : Input) : Output :=
  branch input + skip input

omit [NormedSpace ℝ State] in
@[simp]
theorem projectedResidual_zero_branch_identity_skip
    (state : State) :
    projectedResidual (fun _ : State => 0) id state = state := by
  simp [projectedResidual]

/-- A projection shortcut is not automatically an identity map. -/
theorem zero_projection_is_not_identity :
    projectedResidual (fun _ : ℝ => 0) (fun _ => 0) 1 ≠ 1 := by
  norm_num [projectedResidual]

/-- Negative fixture: an identity residual branch makes the block double its
input, so the skip connection alone does not ensure nonexpansiveness. -/
theorem identity_branch_expands :
    let layer : ResidualLayer ℝ := ⟨id⟩
    ‖layer.apply 1 - layer.apply 0‖ >
      ‖(1 : ℝ) - 0‖ := by
  norm_num [ResidualLayer.apply]

#print axioms ResidualLayer.asGated_apply
#print axioms ResidualLayer.norm_apply_sub_apply_le
#print axioms norm_runRated_sub_runRated_le
#print axioms run_zero_branches
#print axioms projectedResidual_zero_branch_identity_skip
#print axioms zero_projection_is_not_identity
#print axioms identity_branch_expands

end

end ResidualTransport

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
