import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ResidualTransport
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LayerNormalizationBoundary

/-!
# Pre-LN and Post-LN residual boundaries

Xiong et al., *On Layer Normalization in the Transformer Architecture*
(2020), distinguish the source-order equations

* Pre-LN: `stateNext = state + branch (normalize state)`;
* Post-LN: `stateNext = normalize (state + branch state)`.

This module isolates the architecture-level distinction independently of a
particular attention or feed-forward branch.  Its main update-zero consequence
is exact: a zero Pre-LN branch preserves the internal state, while a zero
Post-LN branch still applies normalization.  The distinction persists through
arbitrary finite stacks.

The pairwise-rate theorems are a reusable generalization.  If normalization
has rate `N` and the branch has rate `B`, the Pre-LN block has rate at most
`1 + B*N`, whereas the Post-LN block has rate at most `N*(1 + B)`.  No claim
about optimization, gradient concentration, or warm-up removal follows
without the additional hypotheses used by the source.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace PrePostLayerNormBoundary

noncomputable section

variable {State : Type*}

/-- One source-order Pre-LN residual block. -/
def preNormBlock [Add State]
    (normalize branch : State → State) (state : State) : State :=
  state + branch (normalize state)

/-- One source-order Post-LN residual block. -/
def postNormBlock
    (normalize : State → State) [Add State]
    (branch : State → State) (state : State) : State :=
  normalize (state + branch state)

/-- A zero Post-LN branch still applies the normalizer. -/
@[simp]
theorem postNormBlock_zero_branch
    (normalize : State → State) [AddMonoid State]
    (state : State) :
    postNormBlock normalize (fun _ => 0) state = normalize state := by
  simp [postNormBlock]

/-- A zero Pre-LN branch preserves the internal residual state exactly. -/
@[simp]
theorem preNormBlock_zero_branch [AddMonoid State]
    (normalize : State → State) (state : State) :
    preNormBlock normalize (fun _ => 0) state = state := by
  simp [preNormBlock]

/-- At a zero branch, Post-LN preserves a state exactly if and only if that
state is already a fixed point of the normalizer. -/
theorem postNormBlock_zero_branch_eq_iff
    [AddMonoid State] (normalize : State → State) (state : State) :
    postNormBlock normalize (fun _ => 0) state = state ↔
      normalize state = state := by
  simp

/-! ## Propagation rates -/

variable [NormedAddCommGroup State]

/-- Pairwise rate certificate for an arbitrary state transform. -/
def PairBound (transform : State → State) (rate : ℝ) : Prop :=
  ∀ left right,
    ‖transform left - transform right‖ ≤
      rate * ‖left - right‖

/-- Pre-LN exposes the unnormalized identity path, giving rate
`1 + branchRate * normalizeRate`. -/
theorem norm_preNormBlock_sub_preNormBlock_le
    (normalize branch : State → State)
    (normalizeRate branchRate : ℝ)
    (branchRateNonnegative : 0 ≤ branchRate)
    (normalizeBound : PairBound normalize normalizeRate)
    (branchBound : PairBound branch branchRate)
    (left right : State) :
    ‖preNormBlock normalize branch left -
        preNormBlock normalize branch right‖ ≤
      (1 + branchRate * normalizeRate) *
        ‖left - right‖ := by
  have expansion :
      preNormBlock normalize branch left -
          preNormBlock normalize branch right =
        (left - right) +
          (branch (normalize left) - branch (normalize right)) := by
    simp [preNormBlock]
    abel
  rw [expansion]
  calc
    ‖(left - right) +
        (branch (normalize left) - branch (normalize right))‖ ≤
      ‖left - right‖ +
        ‖branch (normalize left) - branch (normalize right)‖ :=
      norm_add_le _ _
    _ ≤ ‖left - right‖ +
        branchRate * ‖normalize left - normalize right‖ := by
      gcongr
      exact branchBound _ _
    _ ≤ ‖left - right‖ +
        branchRate * (normalizeRate * ‖left - right‖) := by
      gcongr
      exact normalizeBound _ _
    _ = (1 + branchRate * normalizeRate) *
        ‖left - right‖ := by ring

/-- Post-LN places normalization after the entire residual block, giving
rate `normalizeRate * (1 + branchRate)`. -/
theorem norm_postNormBlock_sub_postNormBlock_le
    (normalize branch : State → State)
    (normalizeRate branchRate : ℝ)
    (normalizeRateNonnegative : 0 ≤ normalizeRate)
    (normalizeBound : PairBound normalize normalizeRate)
    (branchBound : PairBound branch branchRate)
    (left right : State) :
    ‖postNormBlock normalize branch left -
        postNormBlock normalize branch right‖ ≤
      normalizeRate * (1 + branchRate) *
        ‖left - right‖ := by
  have residualBound :
      ‖(left + branch left) - (right + branch right)‖ ≤
        (1 + branchRate) * ‖left - right‖ := by
    have expansion :
        (left + branch left) - (right + branch right) =
          (left - right) + (branch left - branch right) := by
      abel
    rw [expansion]
    calc
      ‖(left - right) + (branch left - branch right)‖ ≤
        ‖left - right‖ + ‖branch left - branch right‖ :=
          norm_add_le _ _
      _ ≤ ‖left - right‖ +
          branchRate * ‖left - right‖ := by
        gcongr
        exact branchBound _ _
      _ = (1 + branchRate) * ‖left - right‖ := by ring
  calc
    ‖postNormBlock normalize branch left -
        postNormBlock normalize branch right‖ ≤
      normalizeRate *
        ‖(left + branch left) - (right + branch right)‖ := by
      exact normalizeBound _ _
    _ ≤ normalizeRate *
        ((1 + branchRate) * ‖left - right‖) := by
      exact mul_le_mul_of_nonneg_left residualBound
        normalizeRateNonnegative
    _ = normalizeRate * (1 + branchRate) *
        ‖left - right‖ := by ring

/-! ## Update-zero stacks -/

/-- Run a finite stack of zero-branch Pre-LN blocks.  The normalizers may
differ at every layer. -/
def runZeroPreNorm
    (normalizers : List (State → State)) (state : State) : State :=
  normalizers.foldl
    (fun current normalize =>
      preNormBlock normalize (fun _ => 0) current)
    state

/-- Every finite zero-branch Pre-LN stack is exactly identity internally. -/
theorem runZeroPreNorm_eq_identity
    (normalizers : List (State → State)) (state : State) :
    runZeroPreNorm normalizers state = state := by
  simp [runZeroPreNorm]

/-- Run a finite stack of zero-branch Post-LN blocks. -/
def runZeroPostNorm
    (normalizers : List (State → State)) (state : State) : State :=
  normalizers.foldl
    (fun current normalize =>
      postNormBlock normalize (fun _ => 0) current)
    state

/-- In contrast, zero-branch Post-LN is iteration of the supplied
normalizers, not an identity stack. -/
theorem runZeroPostNorm_cons
    (normalizers : List (State → State))
    (normalize : State → State) (state : State) :
    runZeroPostNorm (normalize :: normalizers) state =
      runZeroPostNorm normalizers (normalize state) := by
  simp [runZeroPostNorm]

/-! ## Exact layer-normalization fixture -/

private def nonNormalizedPair (index : Fin 2) : ℝ :=
  if index = 0 then 1 else 3

theorem nonNormalizedPair_mean :
    LayerNormalizationBoundary.layerMean nonNormalizedPair = 2 := by
  unfold LayerNormalizationBoundary.layerMean
  rw [Fin.sum_univ_two]
  norm_num [nonNormalizedPair]

theorem nonNormalizedPair_variance :
    LayerNormalizationBoundary.layerVariance nonNormalizedPair = 1 := by
  unfold LayerNormalizationBoundary.layerVariance
  rw [Fin.sum_univ_two]
  norm_num [LayerNormalizationBoundary.layerCentered,
    nonNormalizedPair_mean, nonNormalizedPair]

theorem nonNormalizedPair_exactNormalize_zero :
    LayerNormalizationBoundary.exactLayerNormalize nonNormalizedPair 0 =
      -1 := by
  rw [LayerNormalizationBoundary.exactLayerNormalize,
    LayerNormalizationBoundary.layerCentered,
    nonNormalizedPair_mean, LayerNormalizationBoundary.layerStd,
    nonNormalizedPair_variance]
  norm_num [nonNormalizedPair]

/-- Source-faithful negative fixture: with exact layer normalization and a
zero residual branch, Post-LN changes a non-normalized activation. -/
theorem exactLayerNorm_post_zero_not_identity :
    postNormBlock
        LayerNormalizationBoundary.exactLayerNormalize
        (fun _ : Fin 2 → ℝ => 0)
        nonNormalizedPair ≠
      nonNormalizedPair := by
  intro equality
  have coordinateEquality := congrFun equality 0
  rw [postNormBlock_zero_branch,
    nonNormalizedPair_exactNormalize_zero] at coordinateEquality
  norm_num [nonNormalizedPair] at coordinateEquality

/-- The corresponding zero-branch Pre-LN block preserves the same activation
exactly. -/
theorem exactLayerNorm_pre_zero_identity :
    preNormBlock
        LayerNormalizationBoundary.exactLayerNormalize
        (fun _ : Fin 2 → ℝ => 0)
        nonNormalizedPair =
      nonNormalizedPair := by
  exact preNormBlock_zero_branch _ _

#print axioms preNormBlock_zero_branch
#print axioms postNormBlock_zero_branch_eq_iff
#print axioms norm_preNormBlock_sub_preNormBlock_le
#print axioms norm_postNormBlock_sub_postNormBlock_le
#print axioms runZeroPreNorm_eq_identity
#print axioms runZeroPostNorm_cons
#print axioms exactLayerNorm_post_zero_not_identity
#print axioms exactLayerNorm_pre_zero_identity

end

end PrePostLayerNormBoundary

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
