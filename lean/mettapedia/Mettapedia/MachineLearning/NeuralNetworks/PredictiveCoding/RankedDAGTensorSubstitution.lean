import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ArbitraryGraphReverseRecursion
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ErrorStateReparameterization

/-!
# Finite ranked-DAG tensor substitution

This file lifts the state/error coordinate change from scalar chains to a
finite-dimensional ranked computation DAG.  Coordinates have explicit owner
nodes, so the slice owned by one node is its finite-dimensional local state.
Every edge occurrence contributes separately to the feedforward matrix;
parallel occurrences therefore retain their multiplicity.

The strict rank makes the feedforward matrix nilpotent.  Its finite geometric
series is the inverse of the triangular state-to-error Jacobian.  This gives
both coordinate inverse laws, exact energy transport, critical-point
correspondence, and detached local-credit transport without a scalar
surrogate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Matrix

/-- A finite ranked DAG with a finite coordinate carrier.  The coordinates
owned by a node form that node's finite-dimensional local state.  `weight e`
is the linear map contributed by one edge occurrence; endpoint ownership is
enforced when the aggregate feedforward matrix is formed. -/
structure RankedDAGTensor
    (Node Edge Coord : Type*) [Fintype Node] [Fintype Edge] [Fintype Coord] where
  source : Edge → Node
  target : Edge → Node
  owner : Coord → Node
  rank : Node → ℕ
  forward : ∀ e, rank (source e) < rank (target e)
  weight : Edge → Matrix Coord Coord ℝ
  offset : Coord → ℝ
  precision : Coord → ℝ
  precision_pos : ∀ coordinate, 0 < precision coordinate

/-- Canonical scalar embedding of the established `SharedLatentDAG`
abstraction.  Each node owns one coordinate, every existing edge occurrence
is retained, and clamping remains a separate update-mask concern. -/
noncomputable def sharedLatentDAGTensor
    {Node Edge : Type*} [Fintype Node] [Fintype Edge]
    (G : SharedLatentDAG Node Edge) : RankedDAGTensor Node Edge Node where
  source := G.source
  target := G.target
  owner := id
  rank := G.rank
  forward := G.forward
  weight := fun edge _output _input => G.gain edge
  offset := G.offset
  precision := G.precision
  precision_pos := G.precision_pos

section Substitution

variable {Node Edge Coord : Type*}
  [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]

/-- Node-indexed state slice.  This makes the local tensor space explicit
without requiring every node to have the same number of coordinates. -/
def rankedDAGNodeState
    (G : RankedDAGTensor Node Edge Coord) (node : Node) :=
  {coordinate : Coord // G.owner coordinate = node} → ℝ

/-- Aggregate feedforward operator.  The sum is over edge occurrences, not
endpoint pairs, so repeated slots remain repeated summands. -/
noncomputable def rankedDAGFeedforwardMatrix
    (G : RankedDAGTensor Node Edge Coord) : Matrix Coord Coord ℝ :=
  fun output input =>
    ∑ edge : Edge,
      if G.source edge = G.owner input ∧ G.target edge = G.owner output then
        G.weight edge output input
      else 0

/-- On the canonical scalar embedding, the tensor feedforward entry is the
established shared-DAG edge-occurrence sum. -/
theorem sharedLatentDAGTensor_feedforwardMatrix_apply
    (G : SharedLatentDAG Node Edge) (output input : Node) :
    rankedDAGFeedforwardMatrix (sharedLatentDAGTensor G) output input =
      ∑ edge : Edge,
        if G.source edge = input ∧ G.target edge = output then
          G.gain edge
        else 0 := by
  rfl

/-- Maximum rank of a coordinate owner. -/
noncomputable def rankedDAGMaxCoordinateRank
    (G : RankedDAGTensor Node Edge Coord) : ℕ :=
  Finset.univ.sup (fun coordinate => G.rank (G.owner coordinate))

omit [DecidableEq Node] [DecidableEq Coord] in
theorem rankedDAG_coordinateRank_le_max
    (G : RankedDAGTensor Node Edge Coord) (coordinate : Coord) :
    G.rank (G.owner coordinate) ≤ rankedDAGMaxCoordinateRank G := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun coordinate : Coord => G.rank (G.owner coordinate))
    (Finset.mem_univ coordinate)

omit [DecidableEq Coord] in
/-- A feedforward matrix entry is zero unless its input owner has strictly
smaller rank than its output owner. -/
theorem rankedDAGFeedforwardMatrix_apply_eq_zero_of_not_rank_lt
    (G : RankedDAGTensor Node Edge Coord) (output input : Coord)
    (hnot : ¬ G.rank (G.owner input) < G.rank (G.owner output)) :
    rankedDAGFeedforwardMatrix G output input = 0 := by
  classical
  unfold rankedDAGFeedforwardMatrix
  apply Finset.sum_eq_zero
  intro edge _hedge
  by_cases hendpoints :
      G.source edge = G.owner input ∧ G.target edge = G.owner output
  · have hforward := G.forward edge
    rw [hendpoints.1, hendpoints.2] at hforward
    exact (hnot hforward).elim
  · simp [hendpoints]

/-- Rank support of every matrix power.  A nonzero `steps`-fold feedforward
term must advance rank by at least `steps`. -/
theorem rankedDAGFeedforwardMatrix_pow_apply_eq_zero_of_rank_lt
    (G : RankedDAGTensor Node Edge Coord) (steps : ℕ)
    (output input : Coord)
    (hrank : G.rank (G.owner output) < G.rank (G.owner input) + steps) :
    (rankedDAGFeedforwardMatrix G ^ steps) output input = 0 := by
  classical
  induction steps generalizing output input with
  | zero =>
      have hne : output ≠ input := by
        intro h
        subst output
        omega
      simp [hne]
  | succ steps ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro middle _hmiddle
      by_cases hprefix :
          G.rank (G.owner middle) + steps ≤ G.rank (G.owner output)
      · have hnotEdge :
            ¬ G.rank (G.owner input) < G.rank (G.owner middle) := by
          intro hedge
          omega
        rw [rankedDAGFeedforwardMatrix_apply_eq_zero_of_not_rank_lt
          G middle input hnotEdge]
        simp
      · have hprefix' :
            G.rank (G.owner output) <
              G.rank (G.owner middle) + steps := Nat.lt_of_not_ge hprefix
        rw [ih output middle hprefix']
        simp

/-- Strict ranking makes the aggregate feedforward matrix nilpotent. -/
theorem rankedDAGFeedforwardMatrix_nilpotent
    (G : RankedDAGTensor Node Edge Coord) :
    rankedDAGFeedforwardMatrix G ^ (rankedDAGMaxCoordinateRank G + 1) = 0 := by
  ext output input
  apply rankedDAGFeedforwardMatrix_pow_apply_eq_zero_of_rank_lt
  have hmax := rankedDAG_coordinateRank_le_max G output
  omega

/-- Finite inverse series for the triangular state-to-error Jacobian. -/
noncomputable def rankedDAGResolventMatrix
    (G : RankedDAGTensor Node Edge Coord) : Matrix Coord Coord ℝ :=
  ∑ power ∈ Finset.range (rankedDAGMaxCoordinateRank G + 1),
    rankedDAGFeedforwardMatrix G ^ power

/-- Jacobian of state-to-local-error coordinates. -/
noncomputable def rankedDAGErrorJacobianMatrix
    (G : RankedDAGTensor Node Edge Coord) : Matrix Coord Coord ℝ :=
  1 - rankedDAGFeedforwardMatrix G

theorem rankedDAG_resolvent_mul_errorJacobian
    (G : RankedDAGTensor Node Edge Coord) :
    rankedDAGResolventMatrix G * rankedDAGErrorJacobianMatrix G = 1 := by
  unfold rankedDAGResolventMatrix rankedDAGErrorJacobianMatrix
  rw [geom_sum_mul_neg]
  rw [rankedDAGFeedforwardMatrix_nilpotent]
  simp

theorem rankedDAG_errorJacobian_mul_resolvent
    (G : RankedDAGTensor Node Edge Coord) :
    rankedDAGErrorJacobianMatrix G * rankedDAGResolventMatrix G = 1 := by
  unfold rankedDAGResolventMatrix rankedDAGErrorJacobianMatrix
  rw [mul_neg_geom_sum]
  rw [rankedDAGFeedforwardMatrix_nilpotent]
  simp

/-- Honest state-to-local-error map on the whole tensor DAG. -/
noncomputable def rankedDAGStateToError
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) : Coord → ℝ :=
  rankedDAGErrorJacobianMatrix G *ᵥ state - G.offset

/-- Honest local-error-to-state reconstruction. -/
noncomputable def rankedDAGErrorToState
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ) : Coord → ℝ :=
  rankedDAGResolventMatrix G *ᵥ (error + G.offset)

/-- Extracting local errors after ranked reconstruction is the identity. -/
theorem rankedDAGStateToError_errorToState
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ) :
    rankedDAGStateToError G (rankedDAGErrorToState G error) = error := by
  funext coordinate
  unfold rankedDAGStateToError rankedDAGErrorToState
  rw [Matrix.mulVec_mulVec, rankedDAG_errorJacobian_mul_resolvent,
    Matrix.one_mulVec]
  simp

/-- Reconstructing a state from its local errors is the identity. -/
theorem rankedDAGErrorToState_stateToError
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) :
    rankedDAGErrorToState G (rankedDAGStateToError G state) = state := by
  unfold rankedDAGErrorToState rankedDAGStateToError
  have hoffset :
      rankedDAGErrorJacobianMatrix G *ᵥ state - G.offset + G.offset =
        rankedDAGErrorJacobianMatrix G *ᵥ state := sub_add_cancel _ _
  rw [hoffset, Matrix.mulVec_mulVec, rankedDAG_resolvent_mul_errorJacobian,
    Matrix.one_mulVec]

/-- Exact state/error equivalence for a finite ranked tensor DAG. -/
noncomputable def rankedDAGStateErrorEquiv
    (G : RankedDAGTensor Node Edge Coord) :
    (Coord → ℝ) ≃ (Coord → ℝ) where
  toFun := rankedDAGErrorToState G
  invFun := rankedDAGStateToError G
  left_inv := rankedDAGStateToError_errorToState G
  right_inv := rankedDAGErrorToState_stateToError G

/-! ## Energy and detached local credit -/

/-- The unchanged diagonal-precision PC energy in state coordinates. -/
noncomputable def rankedDAGStateEnergy
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ coordinate : Coord,
    G.precision coordinate * (rankedDAGStateToError G state coordinate) ^ 2

/-- The same PC energy written in local-error coordinates. -/
noncomputable def rankedDAGErrorEnergy
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ coordinate : Coord,
    G.precision coordinate * (error coordinate) ^ 2

/-- Exact PC-energy equality under the coordinate change. -/
theorem rankedDAGErrorEnergy_eq_stateEnergy
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ) :
    rankedDAGErrorEnergy G error =
      rankedDAGStateEnergy G (rankedDAGErrorToState G error) := by
  simp [rankedDAGErrorEnergy, rankedDAGStateEnergy,
    rankedDAGStateToError_errorToState]

/-- Detached local parameter gradient for one edge occurrence and one matrix
entry, evaluated in state coordinates.  The source activity is held fixed. -/
noncomputable def rankedDAGStateDetachedCredit
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ)
    (edge : Edge) (output input : Coord) : ℝ :=
  if G.target edge = G.owner output ∧ G.source edge = G.owner input then
    -G.precision output * rankedDAGStateToError G state output * state input
  else 0

/-- The corresponding detached local gradient evaluated in error
coordinates, after reconstructing the same state. -/
noncomputable def rankedDAGErrorDetachedCredit
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ)
    (edge : Edge) (output input : Coord) : ℝ :=
  if G.target edge = G.owner output ∧ G.source edge = G.owner input then
    -G.precision output * error output *
      rankedDAGErrorToState G error input
  else 0

/-- Detached local parameter credit is identical at corresponding
state/error points, edge occurrence by edge occurrence. -/
theorem rankedDAG_detachedCredit_transport
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ)
    (edge : Edge) (output input : Coord) :
    rankedDAGStateDetachedCredit G (rankedDAGErrorToState G error)
        edge output input =
      rankedDAGErrorDetachedCredit G error edge output input := by
  simp [rankedDAGStateDetachedCredit, rankedDAGErrorDetachedCredit,
    rankedDAGStateToError_errorToState]

/-! ## Triangular differential and critical points -/

/-- Continuous-linear triangular state-to-error Jacobian. -/
noncomputable def rankedDAGErrorJacobian
    (G : RankedDAGTensor Node Edge Coord) :
    (Coord → ℝ) →L[ℝ] (Coord → ℝ) :=
  (Matrix.toLin' (rankedDAGErrorJacobianMatrix G)).toContinuousLinearMap

/-- Continuous-linear inverse Jacobian. -/
noncomputable def rankedDAGInverseJacobian
    (G : RankedDAGTensor Node Edge Coord) :
    (Coord → ℝ) →L[ℝ] (Coord → ℝ) :=
  (Matrix.toLin' (rankedDAGResolventMatrix G)).toContinuousLinearMap

theorem rankedDAGStateToError_hasFDerivAt
    (G : RankedDAGTensor Node Edge Coord) (state : Coord → ℝ) :
    HasFDerivAt (rankedDAGStateToError G)
      (rankedDAGErrorJacobian G) state := by
  exact (rankedDAGErrorJacobian G).hasFDerivAt.sub_const G.offset

theorem rankedDAGErrorToState_hasFDerivAt
    (G : RankedDAGTensor Node Edge Coord) (error : Coord → ℝ) :
    HasFDerivAt (rankedDAGErrorToState G)
      (rankedDAGInverseJacobian G) error := by
  change HasFDerivAt
    (fun current => rankedDAGInverseJacobian G (current + G.offset))
    (rankedDAGInverseJacobian G) error
  simpa using (rankedDAGInverseJacobian G).hasFDerivAt.comp error
    ((hasFDerivAt_id error).add_const G.offset)

/-- The triangular Jacobian has the finite-series right inverse needed to
reflect vanishing differentials. -/
theorem rankedDAGJacobian_comp_inverse
    (G : RankedDAGTensor Node Edge Coord) :
    rankedDAGErrorJacobian G ∘L rankedDAGInverseJacobian G =
      ContinuousLinearMap.id ℝ (Coord → ℝ) := by
  apply ContinuousLinearMap.ext
  intro vector
  change rankedDAGErrorJacobianMatrix G *ᵥ
      (rankedDAGResolventMatrix G *ᵥ vector) = vector
  rw [Matrix.mulVec_mulVec, rankedDAG_errorJacobian_mul_resolvent,
    Matrix.one_mulVec]

/-- Vanishing of an energy differential is preserved and reflected by the
ranked-DAG state/error coordinate change. -/
theorem rankedDAG_criticalDifferential_iff
    (G : RankedDAGTensor Node Edge Coord)
    (stateDifferential : (Coord → ℝ) →L[ℝ] ℝ) :
    stateDifferential ∘L rankedDAGErrorJacobian G = 0 ↔
      stateDifferential = 0 := by
  exact differential_comp_eq_zero_iff_of_rightInverse
    stateDifferential (rankedDAGErrorJacobian G)
      (rankedDAGInverseJacobian G) (rankedDAGJacobian_comp_inverse G)

end Substitution

/-! ## Non-scalar node-state fixture -/

/-- Two ranked nodes, each owning two independent coordinate channels.  The
single edge occurrence carries the identity map between corresponding
channels. -/
noncomputable def rankedTensorTwoNodeTwoChannel :
    RankedDAGTensor (Fin 2) (Fin 1) (Fin 2 × Fin 2) where
  source := fun _edge => 0
  target := fun _edge => 1
  owner := Prod.fst
  rank := fun node => node.val
  forward := by intro _edge; norm_num
  weight := fun _edge output input => if output.2 = input.2 then 1 else 0
  offset := fun coordinate => if coordinate.1 = 0 then 1 else 0
  precision := fun _coordinate => 1
  precision_pos := by intro _coordinate; norm_num

/-- Every local node state in the fixture has at least two distinct
coordinates, ruling out a scalar surrogate. -/
theorem rankedTensorTwoNodeTwoChannel_nodeState_nonScalar (node : Fin 2) :
    ∃ coordinate₀ coordinate₁ :
        {coordinate : Fin 2 × Fin 2 //
          rankedTensorTwoNodeTwoChannel.owner coordinate = node},
      coordinate₀ ≠ coordinate₁ := by
  let coordinate₀ :
      {coordinate : Fin 2 × Fin 2 //
        rankedTensorTwoNodeTwoChannel.owner coordinate = node} :=
    ⟨(node, 0), rfl⟩
  let coordinate₁ :
      {coordinate : Fin 2 × Fin 2 //
        rankedTensorTwoNodeTwoChannel.owner coordinate = node} :=
    ⟨(node, 1), rfl⟩
  refine ⟨coordinate₀, coordinate₁, ?_⟩
  intro heq
  have hchannel := congrArg (fun coordinate => coordinate.val.2) heq
  norm_num [coordinate₀, coordinate₁] at hchannel

/-- The exact inverse license specializes to the genuinely two-channel node
state fixture. -/
theorem rankedTensorTwoNodeTwoChannel_inverse
    (error : (Fin 2 × Fin 2) → ℝ) :
    rankedDAGStateToError rankedTensorTwoNodeTwoChannel
        (rankedDAGErrorToState rankedTensorTwoNodeTwoChannel error) = error := by
  exact rankedDAGStateToError_errorToState _ _

/-- The unchanged energy equality also specializes to the two-channel
fixture. -/
theorem rankedTensorTwoNodeTwoChannel_energy_eq
    (error : (Fin 2 × Fin 2) → ℝ) :
    rankedDAGErrorEnergy rankedTensorTwoNodeTwoChannel error =
      rankedDAGStateEnergy rankedTensorTwoNodeTwoChannel
        (rankedDAGErrorToState rankedTensorTwoNodeTwoChannel error) := by
  exact rankedDAGErrorEnergy_eq_stateEnergy _ _

#print axioms rankedDAGFeedforwardMatrix_nilpotent
#print axioms rankedDAGStateToError_errorToState
#print axioms rankedDAGErrorToState_stateToError
#print axioms rankedDAGErrorEnergy_eq_stateEnergy
#print axioms rankedDAG_detachedCredit_transport
#print axioms rankedDAGStateToError_hasFDerivAt
#print axioms rankedDAGJacobian_comp_inverse
#print axioms rankedDAG_criticalDifferential_iff
#print axioms rankedTensorTwoNodeTwoChannel_inverse
#print axioms rankedTensorTwoNodeTwoChannel_energy_eq

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
