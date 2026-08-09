import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CertifiedDampedDescent
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DAGScheduleExactness

/-!
# Energy-derived transport on finite ranked tensor DAGs

This file separates genuine local-state settling from abstract reverse-error
recursion.  It defines the gradient of the unchanged ranked-DAG PC energy,
an actual synchronous masked state update, and an actual reverse-ranked state
sweep.  Exact difference-matrix theorems characterize their information
transport.  In particular, synchronous influence advances by one edge of its
one-step interaction graph per iteration, while a complete reverse-ranked
sweep composes all rank-local state updates in one sweep.

The final section identifies the collapse boundary.  At a frozen feedforward
state, complete reverse force gives ordinary reverse-mode occurrence credit.
Thus any different credit requires state displacement or incomplete reverse
force (which can arise from finite settling, precision, or curvature), not a
renamed reverse sweep.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Matrix

section EnergyGradient

variable {Node Edge Coord : Type*}
  [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]

/-- Diagonal coordinate precision used by `rankedDAGStateEnergy`. -/
noncomputable def rankedDAGPrecisionMatrix
    (G : RankedDAGTensor Node Edge Coord) : Matrix Coord Coord ℝ :=
  Matrix.diagonal G.precision

/-- Precision-weighted local-error force. -/
noncomputable def rankedDAGLocalForce
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) : Coord → ℝ :=
  rankedDAGPrecisionMatrix G *ᵥ rankedDAGStateToError G state

/-- Gradient of the unchanged PC energy with respect to all state
coordinates. -/
noncomputable def rankedDAGStateGradient
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) : Coord → ℝ :=
  (rankedDAGErrorJacobianMatrix G)ᵀ *ᵥ rankedDAGLocalForce G state

/-- A state perturbation changes local error by the triangular Jacobian. -/
theorem rankedDAGStateToError_add_smul
    (G : RankedDAGTensor Node Edge Coord)
    (state direction : Coord → ℝ) (step : ℝ) :
    rankedDAGStateToError G (state + step • direction) =
      rankedDAGStateToError G state +
        step • (rankedDAGErrorJacobianMatrix G *ᵥ direction) := by
  unfold rankedDAGStateToError
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  module

/-- Exact quadratic expansion along every state direction.  Its linear term
is the inner product with `rankedDAGStateGradient`, so the update below is
energy-derived rather than an abstract error recursion. -/
theorem rankedDAGStateGradient_dot_direction
    (G : RankedDAGTensor Node Edge Coord)
    (state direction : Coord → ℝ) :
    (∑ coordinate : Coord,
        rankedDAGStateGradient G state coordinate * direction coordinate) =
      ∑ coordinate : Coord,
        G.precision coordinate * rankedDAGStateToError G state coordinate *
          (rankedDAGErrorJacobianMatrix G *ᵥ direction) coordinate := by
  classical
  unfold rankedDAGStateGradient rankedDAGLocalForce rankedDAGPrecisionMatrix
  change ((rankedDAGErrorJacobianMatrix G)ᵀ *ᵥ
      (Matrix.diagonal G.precision *ᵥ rankedDAGStateToError G state)) ⬝ᵥ
        direction = _
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal]

theorem rankedDAGStateEnergy_add_smul_exact
    (G : RankedDAGTensor Node Edge Coord)
    (state direction : Coord → ℝ) (step : ℝ) :
    rankedDAGStateEnergy G (state + step • direction) =
      rankedDAGStateEnergy G state +
        step * (∑ coordinate : Coord,
          rankedDAGStateGradient G state coordinate * direction coordinate) +
        (step ^ 2 / 2) *
          (∑ coordinate : Coord,
            G.precision coordinate *
              (rankedDAGErrorJacobianMatrix G *ᵥ direction) coordinate ^ 2) := by
  classical
  rw [rankedDAGStateEnergy, rankedDAGStateEnergy,
    rankedDAGStateToError_add_smul]
  rw [rankedDAGStateGradient_dot_direction]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  ring

/-- Mask selecting the state coordinates that are allowed to settle. -/
noncomputable def rankedDAGMovableMask
    (movable : Finset Coord) : Matrix Coord Coord ℝ :=
  Matrix.diagonal (fun coordinate => if coordinate ∈ movable then 1 else 0)

/-- Actual synchronous local-state gradient update.  Clamped coordinates are
left unchanged. -/
noncomputable def rankedDAGSynchronousStateStep
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (state : Coord → ℝ) : Coord → ℝ :=
  state - rate • (rankedDAGMovableMask movable *ᵥ rankedDAGStateGradient G state)

/-- Hessian of the affine ranked-DAG PC energy. -/
noncomputable def rankedDAGStateHessianMatrix
    (G : RankedDAGTensor Node Edge Coord) : Matrix Coord Coord ℝ :=
  (rankedDAGErrorJacobianMatrix G)ᵀ *
    rankedDAGPrecisionMatrix G * rankedDAGErrorJacobianMatrix G

/-- Difference propagator for one synchronous state update. -/
noncomputable def rankedDAGSynchronousDifferenceMatrix
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) : Matrix Coord Coord ℝ :=
  1 - rate • (rankedDAGMovableMask movable * rankedDAGStateHessianMatrix G)

theorem rankedDAGStateGradient_sub
    (G : RankedDAGTensor Node Edge Coord) (state₁ state₂ : Coord → ℝ) :
    rankedDAGStateGradient G state₁ - rankedDAGStateGradient G state₂ =
      rankedDAGStateHessianMatrix G *ᵥ (state₁ - state₂) := by
  unfold rankedDAGStateGradient rankedDAGLocalForce
  rw [← Matrix.mulVec_sub, ← Matrix.mulVec_sub]
  have herror :
      rankedDAGStateToError G state₁ - rankedDAGStateToError G state₂ =
        rankedDAGErrorJacobianMatrix G *ᵥ (state₁ - state₂) := by
    unfold rankedDAGStateToError
    rw [sub_sub_sub_cancel_right, Matrix.mulVec_sub]
  rw [herror, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem rankedDAGSynchronousStateStep_sub
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (state₁ state₂ : Coord → ℝ) :
    rankedDAGSynchronousStateStep G movable rate state₁ -
        rankedDAGSynchronousStateStep G movable rate state₂ =
      rankedDAGSynchronousDifferenceMatrix G movable rate *ᵥ
        (state₁ - state₂) := by
  unfold rankedDAGSynchronousStateStep rankedDAGSynchronousDifferenceMatrix
  rw [sub_sub_sub_comm, ← smul_sub, ← Matrix.mulVec_sub,
    rankedDAGStateGradient_sub, Matrix.mulVec_mulVec]
  funext coordinate
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- Finite run of the actual synchronous state update. -/
noncomputable def rankedDAGSynchronousRun
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) : ℕ → (Coord → ℝ) → (Coord → ℝ)
  | 0, state => state
  | steps + 1, state =>
      rankedDAGSynchronousStateStep G movable rate
        (rankedDAGSynchronousRun G movable rate steps state)

theorem rankedDAGSynchronousRun_sub
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (steps : ℕ) (state₁ state₂ : Coord → ℝ) :
    rankedDAGSynchronousRun G movable rate steps state₁ -
        rankedDAGSynchronousRun G movable rate steps state₂ =
      (rankedDAGSynchronousDifferenceMatrix G movable rate ^ steps) *ᵥ
        (state₁ - state₂) := by
  induction steps with
  | zero => simp [rankedDAGSynchronousRun]
  | succ steps ih =>
      rw [rankedDAGSynchronousRun, rankedDAGSynchronousRun,
        rankedDAGSynchronousStateStep_sub, ih, pow_succ',
        Matrix.mulVec_mulVec]

/-! ## Exact synchronous wavefront -/

/-- A length-indexed path in the one-step dependency graph of a matrix.
Orientation is from the perturbed source coordinate to the observed target. -/
inductive MatrixInfluencePath
    (matrix : Matrix Coord Coord ℝ) : ℕ → Coord → Coord → Prop
  | nil (coordinate : Coord) : MatrixInfluencePath matrix 0 coordinate coordinate
  | cons {steps : ℕ} {source middle target : Coord}
      (first : matrix middle source ≠ 0)
      (rest : MatrixInfluencePath matrix steps middle target) :
      MatrixInfluencePath matrix (steps + 1) source target

/-- A nonzero matrix-power coefficient is witnessed by a path containing one
one-step interaction per iteration. -/
theorem matrixPow_ne_zero_has_influencePath
    (matrix : Matrix Coord Coord ℝ) (steps : ℕ) (source target : Coord)
    (hnonzero : (matrix ^ steps) target source ≠ 0) :
    MatrixInfluencePath matrix steps source target := by
  classical
  induction steps generalizing source target with
  | zero =>
      have heq : target = source := by
        simpa [Matrix.one_apply] using hnonzero
      subst target
      exact MatrixInfluencePath.nil source
  | succ steps ih =>
      rw [pow_succ, Matrix.mul_apply] at hnonzero
      obtain ⟨middle, _hmiddle, hproduct⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero hnonzero
      have hparts := mul_ne_zero_iff.mp hproduct
      exact MatrixInfluencePath.cons hparts.2
        (ih middle target hparts.1)

theorem matrixPow_apply_eq_zero_of_no_influencePath
    (matrix : Matrix Coord Coord ℝ) (steps : ℕ) (source target : Coord)
    (hnoPath : ¬ MatrixInfluencePath matrix steps source target) :
    (matrix ^ steps) target source = 0 := by
  by_contra hnonzero
  exact hnoPath (matrixPow_ne_zero_has_influencePath
    matrix steps source target hnonzero)

/-- Exact response to a single-coordinate perturbation. -/
theorem rankedDAGSynchronousRun_impulse_response
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate amplitude : ℝ) (steps : ℕ) (state : Coord → ℝ)
    (source target : Coord) :
    rankedDAGSynchronousRun G movable rate steps
          (state + Pi.single source amplitude) target -
        rankedDAGSynchronousRun G movable rate steps state target =
      amplitude *
        (rankedDAGSynchronousDifferenceMatrix G movable rate ^ steps)
          target source := by
  have hrun := rankedDAGSynchronousRun_sub
    G movable rate steps (state + Pi.single source amplitude) state
  have hat := congrFun hrun target
  simpa [Matrix.mulVec_single, mul_comm] using hat

/-- One-edge-per-iteration wavefront: if the one-step interaction graph has
no path of length `steps`, the actual synchronous state settle cannot yet
carry a coordinate perturbation there. -/
theorem rankedDAGSynchronousRun_off_wavefront
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate amplitude : ℝ) (steps : ℕ) (state : Coord → ℝ)
    (source target : Coord)
    (hnoPath : ¬ MatrixInfluencePath
      (rankedDAGSynchronousDifferenceMatrix G movable rate)
        steps source target) :
    rankedDAGSynchronousRun G movable rate steps
          (state + Pi.single source amplitude) target =
        rankedDAGSynchronousRun G movable rate steps state target := by
  rw [← sub_eq_zero]
  rw [rankedDAGSynchronousRun_impulse_response]
  rw [matrixPow_apply_eq_zero_of_no_influencePath _ _ _ _ hnoPath]
  simp

end EnergyGradient

/-! ## Actual reverse-ranked local-state sweep -/

section ReverseRankSweep

variable {Node Edge Coord : Type*}
  [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]

/-- Mask for one movable node rank. -/
noncomputable def rankedDAGRankMask
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rank : ℕ) : Matrix Coord Coord ℝ :=
  Matrix.diagonal (fun coordinate =>
    if coordinate ∈ movable ∧ G.rank (G.owner coordinate) = rank then 1 else 0)

/-- One actual energy-gradient update of all movable states at one rank. -/
noncomputable def rankedDAGRankStateStep
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (rank : ℕ) (state : Coord → ℝ) : Coord → ℝ :=
  state - rate • (rankedDAGRankMask G movable rank *ᵥ
    rankedDAGStateGradient G state)

noncomputable def rankedDAGRankDifferenceMatrix
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (rank : ℕ) : Matrix Coord Coord ℝ :=
  1 - rate • (rankedDAGRankMask G movable rank *
    rankedDAGStateHessianMatrix G)

theorem rankedDAGRankStateStep_sub
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (rank : ℕ) (state₁ state₂ : Coord → ℝ) :
    rankedDAGRankStateStep G movable rate rank state₁ -
        rankedDAGRankStateStep G movable rate rank state₂ =
      rankedDAGRankDifferenceMatrix G movable rate rank *ᵥ
        (state₁ - state₂) := by
  unfold rankedDAGRankStateStep rankedDAGRankDifferenceMatrix
  rw [sub_sub_sub_comm, ← smul_sub, ← Matrix.mulVec_sub,
    rankedDAGStateGradient_sub, Matrix.mulVec_mulVec]
  funext coordinate
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- Apply ranks `last, last-1, ..., 0`.  Thus a call with `last + 1`
performs one complete admissible reverse-ranked sweep. -/
noncomputable def rankedDAGReverseRankSweepAux
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) : ℕ → (Coord → ℝ) → (Coord → ℝ)
  | 0, state => state
  | last + 1, state =>
      rankedDAGReverseRankSweepAux G movable rate last
        (rankedDAGRankStateStep G movable rate last state)

/-- Exact difference matrix of the same reverse-ranked sweep. -/
noncomputable def rankedDAGReverseRankSweepMatrixAux
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) : ℕ → Matrix Coord Coord ℝ
  | 0 => 1
  | last + 1 =>
      rankedDAGReverseRankSweepMatrixAux G movable rate last *
        rankedDAGRankDifferenceMatrix G movable rate last

noncomputable def rankedDAGReverseRankSweep
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (state : Coord → ℝ) : Coord → ℝ :=
  rankedDAGReverseRankSweepAux G movable rate
    (rankedDAGMaxCoordinateRank G + 1) state

noncomputable def rankedDAGReverseRankSweepMatrix
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) : Matrix Coord Coord ℝ :=
  rankedDAGReverseRankSweepMatrixAux G movable rate
    (rankedDAGMaxCoordinateRank G + 1)

theorem rankedDAGReverseRankSweepAux_sub
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate : ℝ) (ranks : ℕ) (state₁ state₂ : Coord → ℝ) :
    rankedDAGReverseRankSweepAux G movable rate ranks state₁ -
        rankedDAGReverseRankSweepAux G movable rate ranks state₂ =
      rankedDAGReverseRankSweepMatrixAux G movable rate ranks *ᵥ
        (state₁ - state₂) := by
  induction ranks generalizing state₁ state₂ with
  | zero => simp [rankedDAGReverseRankSweepAux,
      rankedDAGReverseRankSweepMatrixAux]
  | succ ranks ih =>
      rw [rankedDAGReverseRankSweepAux, rankedDAGReverseRankSweepAux,
        rankedDAGReverseRankSweepMatrixAux, ih,
        rankedDAGRankStateStep_sub, Matrix.mulVec_mulVec]

/-- Exact one-sweep transport characterization.  Every numerical influence
of a complete reverse-ranked sweep is exactly a coefficient of the ordered
product of its genuine rank-local state-update matrices. -/
theorem rankedDAGReverseRankSweep_impulse_response
    (G : RankedDAGTensor Node Edge Coord) (movable : Finset Coord)
    (rate amplitude : ℝ) (state : Coord → ℝ) (source target : Coord) :
    rankedDAGReverseRankSweep G movable rate
          (state + Pi.single source amplitude) target -
        rankedDAGReverseRankSweep G movable rate state target =
      amplitude * rankedDAGReverseRankSweepMatrix G movable rate target source := by
  have hsweep := rankedDAGReverseRankSweepAux_sub G movable rate
    (rankedDAGMaxCoordinateRank G + 1)
    (state + Pi.single source amplitude) state
  have hat := congrFun hsweep target
  simpa [rankedDAGReverseRankSweep, rankedDAGReverseRankSweepMatrix,
    Matrix.mulVec_single, mul_comm] using hat

end ReverseRankSweep

/-! ## Frozen-state reverse-mode boundary -/

section FrozenBoundary

variable {Node Edge Coord : Type*}
  [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]

/-- Complete reverse transport of a terminal/task force through the ranked
linear DAG. -/
noncomputable def rankedDAGCompleteReverseForce
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ) : Coord → ℝ :=
  (rankedDAGResolventMatrix G)ᵀ *ᵥ taskForce

/-- Complete reverse transport solves the triangular reverse equation. -/
theorem rankedDAGCompleteReverseForce_satisfies
    (G : RankedDAGTensor Node Edge Coord) (taskForce : Coord → ℝ) :
    (rankedDAGErrorJacobianMatrix G)ᵀ *ᵥ
        rankedDAGCompleteReverseForce G taskForce = taskForce := by
  unfold rankedDAGCompleteReverseForce
  rw [Matrix.mulVec_mulVec]
  have htranspose :
      (rankedDAGErrorJacobianMatrix G)ᵀ *
          (rankedDAGResolventMatrix G)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, rankedDAG_resolvent_mul_errorJacobian,
      Matrix.transpose_one]
  rw [htranspose, Matrix.one_mulVec]

/-- The complete reverse force is the unique solution of the triangular
reverse equation. -/
theorem rankedDAGCompleteReverseForce_unique
    (G : RankedDAGTensor Node Edge Coord) (taskForce force : Coord → ℝ)
    (hforce : (rankedDAGErrorJacobianMatrix G)ᵀ *ᵥ force = taskForce) :
    force = rankedDAGCompleteReverseForce G taskForce := by
  have htranspose :
      (rankedDAGResolventMatrix G)ᵀ *
          (rankedDAGErrorJacobianMatrix G)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, rankedDAG_errorJacobian_mul_resolvent,
      Matrix.transpose_one]
  calc
    force = 1 *ᵥ force := by rw [Matrix.one_mulVec]
    _ = ((rankedDAGResolventMatrix G)ᵀ *
          (rankedDAGErrorJacobianMatrix G)ᵀ) *ᵥ force := by rw [htranspose]
    _ = (rankedDAGResolventMatrix G)ᵀ *ᵥ
          ((rankedDAGErrorJacobianMatrix G)ᵀ *ᵥ force) := by
      rw [Matrix.mulVec_mulVec]
    _ = (rankedDAGResolventMatrix G)ᵀ *ᵥ taskForce := by rw [hforce]
    _ = rankedDAGCompleteReverseForce G taskForce := rfl

/-- Local occurrence credit from an independently supplied state and force. -/
noncomputable def rankedDAGOccurrenceCreditFromForce
    (G : RankedDAGTensor Node Edge Coord) (state force : Coord → ℝ)
    (edge : Edge) (output input : Coord) : ℝ :=
  if G.target edge = G.owner output ∧ G.source edge = G.owner input then
    -force output * state input
  else 0

/-- Ordinary reverse-mode occurrence credit at the frozen feedforward
state. -/
noncomputable def rankedDAGBackpropOccurrenceCredit
    (G : RankedDAGTensor Node Edge Coord) (forwardState taskForce : Coord → ℝ)
    (edge : Edge) (output input : Coord) : ℝ :=
  rankedDAGOccurrenceCreditFromForce G forwardState
    (rankedDAGCompleteReverseForce G taskForce) edge output input

/-- Frozen-state complete reverse transport is exactly ordinary reverse-mode
parameter credit.  The transported force is certified by
`rankedDAGCompleteReverseForce_satisfies`; no state settling is relabeled as
reverse recursion here. -/
theorem rankedDAG_frozen_completeReverse_credit_eq_backprop
    (G : RankedDAGTensor Node Edge Coord) (forwardState taskForce : Coord → ℝ)
    (edge : Edge) (output input : Coord) :
    rankedDAGOccurrenceCreditFromForce G forwardState
        (rankedDAGCompleteReverseForce G taskForce) edge output input =
      rankedDAGBackpropOccurrenceCredit G forwardState taskForce
        edge output input := by
  rfl

/-- Sharp departure boundary at one occurrence: if finite-state PC credit
differs from BP, then either the local state moved or its local force is not
the complete reverse force. -/
theorem rankedDAG_credit_departure_requires_displacement_or_incomplete_force
    (G : RankedDAGTensor Node Edge Coord)
    (forwardState settledState taskForce settledForce : Coord → ℝ)
    (edge : Edge) (output input : Coord)
    (hdeparture :
      rankedDAGOccurrenceCreditFromForce G settledState settledForce
          edge output input ≠
        rankedDAGBackpropOccurrenceCredit G forwardState taskForce
          edge output input) :
    settledState ≠ forwardState ∨
      settledForce ≠ rankedDAGCompleteReverseForce G taskForce := by
  by_contra hboundary
  push Not at hboundary
  exact hdeparture (by simp [rankedDAGBackpropOccurrenceCredit,
    hboundary.1, hboundary.2])

end FrozenBoundary

/-! ## Executable four-node chain fixtures -/

/-- Four scalar nodes embedded in the tensor interface. -/
noncomputable def rankedTensorChain4 :
    RankedDAGTensor (Fin 4) (Fin 3) (Fin 4) where
  source := fun edge => edge.castSucc
  target := fun edge => edge.succ
  owner := id
  rank := fun node => node.val
  forward := by
    intro edge
    exact edge.castSucc_lt_succ
  weight := fun _edge _output _input => 1
  offset := fun coordinate => if coordinate = 0 then 1 else 0
  precision := fun _coordinate => 1
  precision_pos := by intro _coordinate; norm_num

def rankedTensorChain4Movable : Finset (Fin 4) := {1, 2}

def rankedTensorChain4FeedforwardMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  fun output input => if output.val = input.val + 1 then 1 else 0

theorem rankedTensorChain4_feedforwardMatrix_eq :
    rankedDAGFeedforwardMatrix rankedTensorChain4 =
      rankedTensorChain4FeedforwardMatrix := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    norm_num [rankedDAGFeedforwardMatrix, rankedTensorChain4,
      rankedTensorChain4FeedforwardMatrix, Fin.sum_univ_succ]
  all_goals decide

theorem rankedTensorChain4_maxCoordinateRank_eq_three :
    rankedDAGMaxCoordinateRank rankedTensorChain4 = 3 := by
  norm_num [rankedDAGMaxCoordinateRank, rankedTensorChain4]
  all_goals decide

@[simp] theorem rankedTensorChain4_owner (coordinate : Fin 4) :
    rankedTensorChain4.owner coordinate = coordinate := rfl

@[simp] theorem rankedTensorChain4_rank (coordinate : Fin 4) :
    rankedTensorChain4.rank coordinate = coordinate.val := rfl

@[simp] private theorem fin4_zero_ne_one : (0 : Fin 4) ≠ 1 := by decide
@[simp] private theorem fin4_zero_ne_two : (0 : Fin 4) ≠ 2 := by decide
@[simp] private theorem fin4_zero_ne_three : (0 : Fin 4) ≠ 3 := by decide
@[simp] private theorem fin4_one_ne_zero : (1 : Fin 4) ≠ 0 := by decide
@[simp] private theorem fin4_one_ne_two : (1 : Fin 4) ≠ 2 := by decide
@[simp] private theorem fin4_one_ne_three : (1 : Fin 4) ≠ 3 := by decide
@[simp] private theorem fin4_two_ne_zero : (2 : Fin 4) ≠ 0 := by decide
@[simp] private theorem fin4_two_ne_one : (2 : Fin 4) ≠ 1 := by decide
@[simp] private theorem fin4_two_ne_three : (2 : Fin 4) ≠ 3 := by decide
@[simp] private theorem fin4_three_ne_zero : (3 : Fin 4) ≠ 0 := by decide
@[simp] private theorem fin4_three_ne_one : (3 : Fin 4) ≠ 1 := by decide
@[simp] private theorem fin4_three_ne_two : (3 : Fin 4) ≠ 2 := by decide

private theorem fin4_cases (coordinate : Fin 4) :
    coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 ∨ coordinate = 3 := by
  omega

@[simp] private theorem fin4_filter_val_one_card :
    (Finset.univ.filter (fun coordinate : Fin 4 => coordinate.val = 1)).card = 1 := by
  decide

@[simp] private theorem fin4_filter_val_two_card :
    (Finset.univ.filter (fun coordinate : Fin 4 => coordinate.val = 2)).card = 1 := by
  decide

@[simp] private theorem fin4_filter_val_three_card :
    (Finset.univ.filter (fun coordinate : Fin 4 => coordinate.val = 3)).card = 1 := by
  decide

noncomputable def rankedTensorChain4ForwardState : Fin 4 → ℝ := fun _ => 1

noncomputable def rankedTensorChain4TaskState : Fin 4 → ℝ :=
  fun coordinate => if coordinate = 3 then 2 else 1

noncomputable def rankedTensorChain4SyncOneState : Fin 4 → ℝ :=
  fun coordinate => if coordinate = 2 then 3 / 2 else
    if coordinate = 3 then 2 else 1

noncomputable def rankedTensorChain4SyncTwoState : Fin 4 → ℝ :=
  fun coordinate =>
    if coordinate = 1 then 5 / 4 else if coordinate = 2 then 3 / 2 else
      if coordinate = 3 then 2 else 1

@[simp] theorem rankedTensorChain4_error_zero (state : Fin 4 → ℝ) :
    rankedDAGStateToError rankedTensorChain4 state 0 = state 0 - 1 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

@[simp] theorem rankedTensorChain4_error_one (state : Fin 4 → ℝ) :
    rankedDAGStateToError rankedTensorChain4 state 1 = state 1 - state 0 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_neg (by decide : (1 : Fin 4) ≠ Fin.succ (2 : Fin 3))]
  ring

@[simp] theorem rankedTensorChain4_error_two (state : Fin 4 → ℝ) :
    rankedDAGStateToError rankedTensorChain4 state 2 = state 2 - state 1 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_neg (by decide : (2 : Fin 4) ≠ Fin.succ (2 : Fin 3))]
  ring

@[simp] theorem rankedTensorChain4_error_three (state : Fin 4 → ℝ) :
    rankedDAGStateToError rankedTensorChain4 state 3 = state 3 - state 2 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_pos (by decide : (3 : Fin 4) = Fin.succ (2 : Fin 3))]
  rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
  ring

@[simp] theorem rankedTensorChain4_gradient_zero (state : Fin 4 → ℝ) :
    rankedDAGStateGradient rankedTensorChain4 state 0 =
      rankedDAGStateToError rankedTensorChain4 state 0 -
        rankedDAGStateToError rankedTensorChain4 state 1 := by
  unfold rankedDAGStateGradient rankedDAGLocalForce
    rankedDAGPrecisionMatrix rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

@[simp] theorem rankedTensorChain4_gradient_one (state : Fin 4 → ℝ) :
    rankedDAGStateGradient rankedTensorChain4 state 1 =
      rankedDAGStateToError rankedTensorChain4 state 1 -
        rankedDAGStateToError rankedTensorChain4 state 2 := by
  unfold rankedDAGStateGradient rankedDAGLocalForce
    rankedDAGPrecisionMatrix rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_neg (by decide : Fin.succ (2 : Fin 3) ≠ (1 : Fin 4))]
  ring

@[simp] theorem rankedTensorChain4_gradient_two (state : Fin 4 → ℝ) :
    rankedDAGStateGradient rankedTensorChain4 state 2 =
      rankedDAGStateToError rankedTensorChain4 state 2 -
        rankedDAGStateToError rankedTensorChain4 state 3 := by
  unfold rankedDAGStateGradient rankedDAGLocalForce
    rankedDAGPrecisionMatrix rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_neg (by decide : Fin.succ (2 : Fin 3) ≠ (2 : Fin 4))]
  rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]
  ring

@[simp] theorem rankedTensorChain4_gradient_three (state : Fin 4 → ℝ) :
    rankedDAGStateGradient rankedTensorChain4 state 3 =
      rankedDAGStateToError rankedTensorChain4 state 3 := by
  unfold rankedDAGStateGradient rankedDAGLocalForce
    rankedDAGPrecisionMatrix rankedDAGErrorJacobianMatrix
  rw [rankedTensorChain4_feedforwardMatrix_eq]
  norm_num [
    rankedTensorChain4FeedforwardMatrix, rankedTensorChain4,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [if_pos (by decide : Fin.succ (2 : Fin 3) = (3 : Fin 4))]
  rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide]

theorem rankedTensorChain4_task_eq_forward_add_terminalImpulse :
    rankedTensorChain4TaskState =
      rankedTensorChain4ForwardState + Pi.single 3 1 := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedTensorChain4TaskState, rankedTensorChain4ForwardState]

@[simp] theorem rankedTensorChain4_forward_gradient_zero :
    rankedDAGStateGradient rankedTensorChain4
      rankedTensorChain4ForwardState = 0 := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedTensorChain4ForwardState]

theorem rankedTensorChain4_synchronousStep_task :
    rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2) rankedTensorChain4TaskState =
        rankedTensorChain4SyncOneState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGSynchronousStateStep, rankedDAGMovableMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable, rankedTensorChain4TaskState,
      rankedTensorChain4SyncOneState]

theorem rankedTensorChain4_synchronousStep_syncOne :
    rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2) rankedTensorChain4SyncOneState =
        rankedTensorChain4SyncTwoState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGSynchronousStateStep, rankedDAGMovableMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable, rankedTensorChain4SyncOneState,
      rankedTensorChain4SyncTwoState]

@[simp] theorem rankedTensorChain4_synchronousStep_forward :
    rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2) rankedTensorChain4ForwardState =
        rankedTensorChain4ForwardState := by
  simp [rankedDAGSynchronousStateStep]

theorem rankedTensorChain4_sync_one_cannot_reach_node_one :
    rankedDAGSynchronousRun rankedTensorChain4 rankedTensorChain4Movable
        (1 / 2) 1 rankedTensorChain4TaskState 1 =
      rankedDAGSynchronousRun rankedTensorChain4 rankedTensorChain4Movable
        (1 / 2) 1 rankedTensorChain4ForwardState 1 := by
  change rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2) rankedTensorChain4TaskState 1 =
    rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2) rankedTensorChain4ForwardState 1
  rw [rankedTensorChain4_synchronousStep_task,
    rankedTensorChain4_synchronousStep_forward]
  rfl

theorem rankedTensorChain4_sync_two_state_exact :
    rankedDAGSynchronousRun rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) 2 rankedTensorChain4TaskState = rankedTensorChain4SyncTwoState := by
  change rankedDAGSynchronousStateStep rankedTensorChain4
      rankedTensorChain4Movable (1 / 2)
        (rankedDAGSynchronousStateStep rankedTensorChain4
          rankedTensorChain4Movable (1 / 2) rankedTensorChain4TaskState) = _
  rw [rankedTensorChain4_synchronousStep_task,
    rankedTensorChain4_synchronousStep_syncOne]

/-- Positive transport fixture: real synchronous state movement produces a
nonzero upstream local occurrence credit after the two-edge wavefront arrives. -/
theorem rankedTensorChain4_sync_two_upstream_credit_nonzero :
    rankedDAGStateDetachedCredit rankedTensorChain4
        (rankedDAGSynchronousRun rankedTensorChain4 rankedTensorChain4Movable
          (1 / 2) 2 rankedTensorChain4TaskState)
        0 1 0 = -(1 / 4) := by
  rw [rankedTensorChain4_sync_two_state_exact]
  rw [rankedDAGStateDetachedCredit, if_pos]
  · rw [rankedTensorChain4_error_one]
    norm_num [rankedTensorChain4, rankedTensorChain4SyncTwoState]
  · exact ⟨rfl, rfl⟩

theorem rankedTensorChain4_rankStep_three_task :
    rankedDAGRankStateStep rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) 3 rankedTensorChain4TaskState = rankedTensorChain4TaskState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGRankStateStep, rankedDAGRankMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable,
      rankedTensorChain4TaskState]

theorem rankedTensorChain4_rankStep_two_task :
    rankedDAGRankStateStep rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) 2 rankedTensorChain4TaskState = rankedTensorChain4SyncOneState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGRankStateStep, rankedDAGRankMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable,
      rankedTensorChain4TaskState, rankedTensorChain4SyncOneState]

theorem rankedTensorChain4_rankStep_one_syncOne :
    rankedDAGRankStateStep rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) 1 rankedTensorChain4SyncOneState = rankedTensorChain4SyncTwoState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGRankStateStep, rankedDAGRankMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable,
      rankedTensorChain4SyncOneState, rankedTensorChain4SyncTwoState]

theorem rankedTensorChain4_rankStep_zero_syncTwo :
    rankedDAGRankStateStep rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) 0 rankedTensorChain4SyncTwoState = rankedTensorChain4SyncTwoState := by
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate <;>
    norm_num [rankedDAGRankStateStep, rankedDAGRankMask,
      Matrix.mulVec_diagonal,
      rankedTensorChain4Movable,
      rankedTensorChain4SyncTwoState]

@[simp] theorem rankedTensorChain4_rankStep_forward (rate : ℝ) (rank : ℕ) :
    rankedDAGRankStateStep rankedTensorChain4 rankedTensorChain4Movable
      rate rank rankedTensorChain4ForwardState =
        rankedTensorChain4ForwardState := by
  simp [rankedDAGRankStateStep]

/-- A complete reverse-ranked state sweep transports the same task innovation
through both hidden ranks in one sweep. -/
theorem rankedTensorChain4_reverseSweep_state_exact :
    rankedDAGReverseRankSweep rankedTensorChain4 rankedTensorChain4Movable
      (1 / 2) rankedTensorChain4TaskState = rankedTensorChain4SyncTwoState := by
  rw [rankedDAGReverseRankSweep,
    rankedTensorChain4_maxCoordinateRank_eq_three]
  norm_num [rankedDAGReverseRankSweepAux,
    rankedTensorChain4_rankStep_three_task,
    rankedTensorChain4_rankStep_two_task,
    rankedTensorChain4_rankStep_one_syncOne,
    rankedTensorChain4_rankStep_zero_syncTwo]

theorem rankedTensorChain4_reverseSweep_upstream_credit_nonzero :
    rankedDAGStateDetachedCredit rankedTensorChain4
        (rankedDAGReverseRankSweep rankedTensorChain4
          rankedTensorChain4Movable (1 / 2) rankedTensorChain4TaskState)
        0 1 0 = -(1 / 4) := by
  rw [rankedTensorChain4_reverseSweep_state_exact]
  rw [rankedDAGStateDetachedCredit, if_pos]
  · rw [rankedTensorChain4_error_one]
    norm_num [rankedTensorChain4, rankedTensorChain4SyncTwoState]
  · exact ⟨rfl, rfl⟩

/-- Negative fixture: zero terminal innovation leaves the forward state fixed
and produces zero local credit. -/
theorem rankedTensorChain4_zero_terminal_innovation_negative :
    rankedDAGReverseRankSweep rankedTensorChain4 rankedTensorChain4Movable
        (1 / 2) rankedTensorChain4ForwardState =
        rankedTensorChain4ForwardState ∧
      rankedDAGStateDetachedCredit rankedTensorChain4
        rankedTensorChain4ForwardState 0 1 0 = 0 := by
  constructor
  · rw [rankedDAGReverseRankSweep,
      rankedTensorChain4_maxCoordinateRank_eq_three]
    simp [rankedDAGReverseRankSweepAux]
  · rw [rankedDAGStateDetachedCredit, if_pos]
    · rw [rankedTensorChain4_error_one]
      norm_num [rankedTensorChain4, rankedTensorChain4ForwardState]
    · exact ⟨rfl, rfl⟩

noncomputable def rankedTensorChain4TerminalForce : Fin 4 → ℝ :=
  fun coordinate => if coordinate = 3 then 1 else 0

theorem rankedTensorChain4_completeReverseForce_all_one :
    rankedDAGCompleteReverseForce rankedTensorChain4
      rankedTensorChain4TerminalForce = fun _coordinate => 1 := by
  symm
  apply rankedDAGCompleteReverseForce_unique
  funext coordinate
  rcases fin4_cases coordinate with h | h | h | h <;> subst coordinate
  all_goals
    unfold rankedDAGErrorJacobianMatrix
    rw [rankedTensorChain4_feedforwardMatrix_eq]
    norm_num [rankedTensorChain4FeedforwardMatrix,
      rankedTensorChain4TerminalForce, Matrix.one_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Boundary fixture: frozen-state complete reverse transport equals BP. -/
theorem rankedTensorChain4_frozen_completeReverse_eq_bp :
    rankedDAGOccurrenceCreditFromForce rankedTensorChain4
        rankedTensorChain4ForwardState
        (rankedDAGCompleteReverseForce rankedTensorChain4
          rankedTensorChain4TerminalForce) 0 1 0 =
      rankedDAGBackpropOccurrenceCredit rankedTensorChain4
        rankedTensorChain4ForwardState rankedTensorChain4TerminalForce
        0 1 0 := by
  exact rankedDAG_frozen_completeReverse_credit_eq_backprop _ _ _ _ _ _

/-- Bounded-conditioning departure fixture.  Every precision is exactly one,
yet the moved state changes complete-reverse occurrence credit from `-1` to
`-5/4`.  The departure is therefore genuine state displacement, not a renamed
reverse sweep or ill-conditioned precision. -/
theorem rankedTensorChain4_moved_state_completeReverse_credit_departure :
    (∀ coordinate, rankedTensorChain4.precision coordinate = 1) ∧
      rankedDAGOccurrenceCreditFromForce rankedTensorChain4
          rankedTensorChain4SyncTwoState
          (rankedDAGCompleteReverseForce rankedTensorChain4
            rankedTensorChain4TerminalForce) 1 2 1 = -(5 / 4) ∧
      rankedDAGBackpropOccurrenceCredit rankedTensorChain4
          rankedTensorChain4ForwardState rankedTensorChain4TerminalForce
          1 2 1 = -1 := by
  constructor
  · intro coordinate
    rfl
  rw [rankedTensorChain4_completeReverseForce_all_one]
  constructor
  · norm_num [rankedDAGOccurrenceCreditFromForce, rankedTensorChain4,
      rankedTensorChain4SyncTwoState]
  · rw [rankedDAGBackpropOccurrenceCredit,
      rankedTensorChain4_completeReverseForce_all_one]
    norm_num [rankedDAGOccurrenceCreditFromForce, rankedTensorChain4,
      rankedTensorChain4ForwardState]

/-! ## Repeated-occurrence omission fixture -/

/-- Two occurrences connect node `0` to node `1`; the third connects `1` to
`2`.  The parallel occurrences are intentionally distinct edge slots. -/
noncomputable def rankedTensorRepeated3 :
    RankedDAGTensor (Fin 3) (Fin 3) (Fin 3) :=
  sharedLatentDAGTensor dagMultiParentGraph

/-- Incorrect comparison graph obtained by dropping one of the two parallel
occurrences from node `0` to node `1`. -/
noncomputable def rankedTensorRepeated3Omitted :
    RankedDAGTensor (Fin 3) (Fin 2) (Fin 3) where
  source := fun edge => edge.castSucc
  target := fun edge => edge.succ
  owner := id
  rank := fun node => node.val
  forward := by
    intro edge
    exact edge.castSucc_lt_succ
  weight := fun _edge _output _input => 1
  offset := fun _coordinate => 0
  precision := fun _coordinate => 1
  precision_pos := by intro _coordinate; norm_num

def rankedTensorRepeated3Matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun output input =>
    if output = 1 ∧ input = 0 then 2 else
      if output = 2 ∧ input = 1 then 1 else 0

def rankedTensorRepeated3OmittedMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun output input =>
    if output = 1 ∧ input = 0 then 1 else
      if output = 2 ∧ input = 1 then 1 else 0

theorem rankedTensorRepeated3_feedforwardMatrix_eq :
    rankedDAGFeedforwardMatrix rankedTensorRepeated3 =
      rankedTensorRepeated3Matrix := by
  classical
  ext output input
  simp only [rankedDAGFeedforwardMatrix, Fin.sum_univ_succ]
  fin_cases output <;> fin_cases input <;>
    norm_num [rankedTensorRepeated3, rankedTensorRepeated3Matrix,
      sharedLatentDAGTensor, dagMultiParentGraph, Fin.ext_iff]

theorem rankedTensorRepeated3Omitted_feedforwardMatrix_eq :
    rankedDAGFeedforwardMatrix rankedTensorRepeated3Omitted =
      rankedTensorRepeated3OmittedMatrix := by
  classical
  ext output input
  simp only [rankedDAGFeedforwardMatrix, Fin.sum_univ_succ]
  fin_cases output <;> fin_cases input <;>
    norm_num [rankedTensorRepeated3Omitted,
      rankedTensorRepeated3OmittedMatrix, Fin.ext_iff]

noncomputable def rankedTensorRepeated3State : Fin 3 → ℝ :=
  fun coordinate => if coordinate = 0 then 1 else 2

theorem rankedTensorRepeated3_error_one_eq_zero :
    rankedDAGStateToError rankedTensorRepeated3
      rankedTensorRepeated3State 1 = 0 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorRepeated3_feedforwardMatrix_eq]
  norm_num [rankedTensorRepeated3Matrix, rankedTensorRepeated3,
    sharedLatentDAGTensor, dagMultiParentGraph, rankedTensorRepeated3State,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [show (1 : Fin 3) ≠ 2 by decide]

theorem rankedTensorRepeated3Omitted_error_one_eq_one :
    rankedDAGStateToError rankedTensorRepeated3Omitted
      rankedTensorRepeated3State 1 = 1 := by
  unfold rankedDAGStateToError rankedDAGErrorJacobianMatrix
  rw [rankedTensorRepeated3Omitted_feedforwardMatrix_eq]
  norm_num [rankedTensorRepeated3OmittedMatrix,
    rankedTensorRepeated3Omitted, rankedTensorRepeated3State,
    Matrix.one_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [show (1 : Fin 3) ≠ 2 by decide]
  norm_num

/-- Dropping one repeated occurrence changes an actual detached local credit:
the correct multiplicity gives zero while the omitted graph gives `-1`. -/
theorem rankedTensorRepeated3_omitted_occurrence_incorrect_credit :
    rankedDAGStateDetachedCredit rankedTensorRepeated3
        rankedTensorRepeated3State 0 1 0 = 0 ∧
      rankedDAGStateDetachedCredit rankedTensorRepeated3Omitted
        rankedTensorRepeated3State 0 1 0 = -1 ∧
      rankedDAGStateDetachedCredit rankedTensorRepeated3
          rankedTensorRepeated3State 0 1 0 ≠
        rankedDAGStateDetachedCredit rankedTensorRepeated3Omitted
          rankedTensorRepeated3State 0 1 0 := by
  constructor
  · rw [rankedDAGStateDetachedCredit, if_pos]
    · rw [rankedTensorRepeated3_error_one_eq_zero]
      norm_num
    · exact ⟨rfl, rfl⟩
  constructor
  · rw [rankedDAGStateDetachedCredit, if_pos]
    · rw [rankedTensorRepeated3Omitted_error_one_eq_one]
      norm_num [rankedTensorRepeated3Omitted, rankedTensorRepeated3State]
    · exact ⟨rfl, rfl⟩
  · rw [rankedDAGStateDetachedCredit, if_pos,
      rankedDAGStateDetachedCredit, if_pos]
    · rw [rankedTensorRepeated3_error_one_eq_zero,
        rankedTensorRepeated3Omitted_error_one_eq_one]
      norm_num [rankedTensorRepeated3Omitted, rankedTensorRepeated3State]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

#print axioms rankedDAGStateEnergy_add_smul_exact
#print axioms rankedDAGSynchronousRun_off_wavefront
#print axioms rankedDAGReverseRankSweep_impulse_response
#print axioms rankedDAGCompleteReverseForce_satisfies
#print axioms rankedDAG_credit_departure_requires_displacement_or_incomplete_force
#print axioms rankedTensorChain4_sync_one_cannot_reach_node_one
#print axioms rankedTensorChain4_sync_two_upstream_credit_nonzero
#print axioms rankedTensorChain4_reverseSweep_upstream_credit_nonzero
#print axioms rankedTensorChain4_zero_terminal_innovation_negative
#print axioms rankedTensorChain4_frozen_completeReverse_eq_bp
#print axioms rankedTensorChain4_moved_state_completeReverse_credit_departure
#print axioms rankedTensorRepeated3_omitted_occurrence_incorrect_credit

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
