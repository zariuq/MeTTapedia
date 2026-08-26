import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryNonlinearVectorPC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LogitLossCurvature

/-!
# Exact grouped information objective for local action-memory PC

The deployed task term is not ordinary one-target cross entropy.  A token
cross entropy is first averaged within each alternative, alternative losses
are marginalized by a positive prior inside each sequence group, and
precision-weighted current and replay group means are combined.  Auxiliary
heads are frozen at the local-PC boundary and therefore contribute only an
additive constant.

This module constructs that hierarchy as one differentiable finite-batch
functional.  Freezing all rows except one yields exactly the `TaskFunctional`
consumed by `ActionMemoryNonlinearVectorPC.localEnergy`; thus the local
state-gradient theorem applies to the registered grouped objective rather than
to a substituted single-target loss.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryNonlinearVectorPC

open scoped InnerProductSpace BigOperators
open InnerProduct
open LogitLossCurvature

noncomputable section

local instance (priority := 2000) groupedInformationRealModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

private theorem algebraRealModule_eq_exact :
    (NormedAlgebra.toNormedSpace ℝ).toModule =
      RCLike.toInnerProductSpaceReal.toModule := by
  apply Module.ext
  rfl

private abbrev AlgebraRealHasDerivAt (function : ℝ → ℝ)
    (derivative point : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule inferInstance inferInstance
    function derivative point

private theorem algebraHasDerivAt_to_exact {function : ℝ → ℝ}
    {derivative point : ℝ}
    (derivativeWitness : AlgebraRealHasDerivAt function derivative point) :
    ExactRealHasDerivAt function derivative point := by
  simpa only [AlgebraRealHasDerivAt, ExactRealHasDerivAt,
    algebraRealModule_eq_exact] using derivativeWitness

abbrev PolicyBatch (rows actions : ℕ) :=
  EuclideanSpace ℝ (Fin rows × Fin actions)

def batchRow {rows actions : ℕ} (batch : PolicyBatch rows actions)
    (row : Fin rows) : PolicyRow actions :=
  WithLp.toLp 2 fun action => batch (row, action)

def replaceBatchRow {rows actions : ℕ} (batch : PolicyBatch rows actions)
    (row : Fin rows) (logits : PolicyRow actions) : PolicyBatch rows actions :=
  WithLp.toLp 2 fun coordinate =>
    if coordinate.1 = row then logits coordinate.2 else batch coordinate

def embedBatchRow {rows actions : ℕ} (row : Fin rows)
    (direction : PolicyRow actions) : PolicyBatch rows actions :=
  WithLp.toLp 2 fun coordinate =>
    if coordinate.1 = row then direction coordinate.2 else 0

structure BatchTaskFunctional (rows actions : ℕ) where
  value : PolicyBatch rows actions → ℝ
  gradient : PolicyBatch rows actions → PolicyBatch rows actions
  directionalDerivative : ∀ logits direction,
    ExactRealHasDerivAt (fun time : ℝ => value (logits + time • direction))
      ⟪gradient logits, direction⟫_ℝ 0

theorem batchRow_add_smul {rows actions : ℕ}
    (batch direction : PolicyBatch rows actions) (row : Fin rows) (time : ℝ) :
    batchRow (batch + time • direction) row =
      batchRow batch row + time • batchRow direction row := by
  ext action
  rfl

theorem replaceBatchRow_line {rows actions : ℕ}
    (batch : PolicyBatch rows actions) (row : Fin rows)
    (logits direction : PolicyRow actions) (time : ℝ) :
    replaceBatchRow batch row (logits + time • direction) =
      replaceBatchRow batch row logits + time • embedBatchRow row direction := by
  ext coordinate
  by_cases same : coordinate.1 = row <;>
    simp [replaceBatchRow, embedBatchRow, same]

theorem inner_embedBatchRow {rows actions : ℕ} (row : Fin rows)
    (batch : PolicyBatch rows actions) (direction : PolicyRow actions) :
    ⟪batch, embedBatchRow row direction⟫_ℝ =
      ⟪batchRow batch row, direction⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  classical
  calc
    (∑ coordinate : Fin rows × Fin actions,
        @inner ℝ ℝ _ (batch coordinate) (embedBatchRow row direction coordinate)) =
      ∑ action : Fin actions,
        @inner ℝ ℝ _ (batch (row, action)) (direction action) := by
          rw [Fintype.sum_prod_type]
          calc
            (∑ candidate : Fin rows, ∑ action : Fin actions,
                @inner ℝ ℝ _ (batch (candidate, action))
                  (embedBatchRow row direction (candidate, action))) =
              ∑ candidate : Fin rows,
                if candidate = row then
                  ∑ action : Fin actions,
                    @inner ℝ ℝ _ (batch (row, action)) (direction action)
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro candidate _
                  by_cases same : candidate = row
                  · subst candidate
                    simp [embedBatchRow]
                  · simp [embedBatchRow, same]
            _ = _ := by simp
    _ = _ := rfl

theorem inner_embedBatchRow_left {rows actions : ℕ} (row : Fin rows)
    (gradient : PolicyRow actions) (batch : PolicyBatch rows actions) :
    ⟪embedBatchRow row gradient, batch⟫_ℝ =
      ⟪gradient, batchRow batch row⟫_ℝ := by
  rw [real_inner_comm, inner_embedBatchRow, real_inner_comm]

/-! ## Exact token cross entropy -/

private theorem hasDerivAt_expExact (input : ℝ) :
    ExactRealHasDerivAt Real.exp (Real.exp input) input := by
  simpa using Real.hasDerivAt_exp input

theorem hasDerivAt_categoricalCrossEntropy_plusLine {actions : ℕ}
    [NeZero actions] (target : Fin actions)
    (logits direction : PolicyRow actions) :
    ExactRealHasDerivAt
      (fun time : ℝ => categoricalCrossEntropy target (logits + time • direction))
      ⟪categoricalCrossEntropyGradient target logits, direction⟫_ℝ 0 := by
  classical
  have exponentialLine : ExactRealHasDerivAt
      (fun time : ℝ => ∑ action : Fin actions,
        Real.exp (logits action + time * direction action))
      (∑ action : Fin actions, Real.exp (logits action) * direction action) 0 := by
    apply HasDerivAt.fun_sum
    intro action _
    have affine : ExactRealHasDerivAt
        (fun time : ℝ => logits action + time * direction action)
        (direction action) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
        (direction action)).const_add (logits action)
    have composed := (hasDerivAt_expExact
      (logits action + 0 * direction action)).comp 0 affine
    have converted := algebraHasDerivAt_to_exact composed
    convert converted using 1
    · funext time
      rfl
    · simp only [zero_mul, add_zero]
  have totalPositive :
      0 < ∑ action : Fin actions, Real.exp (logits action) := by
    exact Finset.sum_pos (fun action _ => Real.exp_pos (logits action))
      Finset.univ_nonempty
  have totalNonzeroAtLine :
      (∑ action : Fin actions,
        Real.exp (logits action + 0 * direction action)) ≠ 0 := by
    simpa using ne_of_gt totalPositive
  have logLine := exponentialLine.log totalNonzeroAtLine
  have targetLine : ExactRealHasDerivAt
      (fun time : ℝ => logits target + time * direction target)
      (direction target) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (direction target)).const_add (logits target)
  have combined := logLine.sub targetLine
  have functionEquality :
      (fun time : ℝ => categoricalCrossEntropy target
        (logits + time • direction)) =
      (fun time : ℝ =>
        Real.log (∑ action : Fin actions,
          Real.exp (logits action + time * direction action)) -
        (logits target + time * direction target)) := by
    funext time
    rfl
  rw [functionEquality]
  apply combined.congr_deriv
  simp only [zero_mul, add_zero]
  rw [PiLp.inner_apply]
  simp only [categoricalCrossEntropyGradient, RCLike.inner_apply,
    conj_trivial, PiLp.toLp_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_div]
  have indicatorSum :
      (∑ action : Fin actions,
        direction action * (if action = target then 1 else 0)) =
      direction target := by simp
  rw [indicatorSum]
  congr 1
  apply Finset.sum_congr rfl
  intro action _
  rw [categoricalExpSum]
  ring

def tokenTask {rows actions : ℕ} [NeZero actions]
    (row : Fin rows) (target : Fin actions) : BatchTaskFunctional rows actions where
  value batch := categoricalCrossEntropy target (batchRow batch row)
  gradient batch := WithLp.toLp 2 fun coordinate =>
    if coordinate.1 = row then
      categoricalCrossEntropyGradient target (batchRow batch row) coordinate.2
    else 0
  directionalDerivative batch direction := by
    have derivative := hasDerivAt_categoricalCrossEntropy_plusLine target
      (batchRow batch row) (batchRow direction row)
    have functionEquality :
        (fun time : ℝ => categoricalCrossEntropy target
          (batchRow (batch + time • direction) row)) =
        (fun time : ℝ => categoricalCrossEntropy target
          (batchRow batch row + time • batchRow direction row)) := by
      funext time
      rw [batchRow_add_smul]
    rw [functionEquality]
    apply derivative.congr_deriv
    simpa only [embedBatchRow] using
      (inner_embedBatchRow_left row
        (categoricalCrossEntropyGradient target (batchRow batch row)) direction).symm

/-! ## Differentiable finite objective algebra -/

def BatchTaskFunctional.zero {rows actions : ℕ} :
    BatchTaskFunctional rows actions where
  value _ := 0
  gradient _ := 0
  directionalDerivative _ _ := by
    simpa using hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))

def BatchTaskFunctional.add {rows actions : ℕ}
    (left right : BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions where
  value logits := left.value logits + right.value logits
  gradient logits := left.gradient logits + right.gradient logits
  directionalDerivative logits direction := by
    apply ((left.directionalDerivative logits direction).add
      (right.directionalDerivative logits direction)).congr_deriv
    rw [inner_add_left]

def BatchTaskFunctional.scale {rows actions : ℕ} (scalar : ℝ)
    (task : BatchTaskFunctional rows actions) : BatchTaskFunctional rows actions where
  value logits := scalar * task.value logits
  gradient logits := scalar • task.gradient logits
  directionalDerivative logits direction := by
    have derivative := (task.directionalDerivative logits direction).const_mul scalar
    apply derivative.congr_deriv
    rw [real_inner_smul_left]

def BatchTaskFunctional.sum {rows actions : ℕ} {Index : Type*}
    [Fintype Index] (tasks : Index → BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions where
  value logits := ∑ index, (tasks index).value logits
  gradient logits := ∑ index, (tasks index).gradient logits
  directionalDerivative logits direction := by
    have derivative := HasDerivAt.fun_sum (u := Finset.univ)
      (fun index _ => (tasks index).directionalDerivative logits direction)
    apply derivative.congr_deriv
    rw [sum_inner]

def BatchTaskFunctional.mean {rows actions : ℕ} {Index : Type*}
    [Fintype Index] [Nonempty Index]
    (tasks : Index → BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions :=
  (BatchTaskFunctional.sum tasks).scale ((Fintype.card Index : ℝ)⁻¹)

/-! ## Per-alternative means and prior-marginalized sequence groups -/

def alternativeMeanNLL {rows actions tokens : ℕ} [NeZero actions]
    [NeZero tokens] (tokenRow : Fin tokens → Fin rows)
    (target : Fin tokens → Fin actions) : BatchTaskFunctional rows actions :=
  BatchTaskFunctional.mean fun token => tokenTask (tokenRow token) (target token)

structure PositivePrior (Alternative : Type*) [Fintype Alternative] where
  weight : Alternative → ℝ
  positive : ∀ alternative, 0 < weight alternative

def marginalNormalizer {rows actions : ℕ} {Alternative : Type*}
    [Fintype Alternative] (prior : PositivePrior Alternative)
    (alternatives : Alternative → BatchTaskFunctional rows actions)
    (logits : PolicyBatch rows actions) : ℝ :=
  ∑ alternative, prior.weight alternative *
    Real.exp (-(alternatives alternative).value logits)

theorem marginalNormalizer_pos {rows actions : ℕ} {Alternative : Type*}
    [Fintype Alternative] [Nonempty Alternative]
    (prior : PositivePrior Alternative)
    (alternatives : Alternative → BatchTaskFunctional rows actions)
    (logits : PolicyBatch rows actions) :
    0 < marginalNormalizer prior alternatives logits := by
  apply Finset.sum_pos
  · intro alternative _
    exact mul_pos (prior.positive alternative)
      (Real.exp_pos (-(alternatives alternative).value logits))
  · exact Finset.univ_nonempty

def marginalGroupTask {rows actions : ℕ} {Alternative : Type*}
    [Fintype Alternative] [Nonempty Alternative]
    (prior : PositivePrior Alternative)
    (alternatives : Alternative → BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions where
  value logits := -Real.log (marginalNormalizer prior alternatives logits)
  gradient logits :=
    ∑ alternative,
      (prior.weight alternative *
        Real.exp (-(alternatives alternative).value logits) /
          marginalNormalizer prior alternatives logits) •
        (alternatives alternative).gradient logits
  directionalDerivative logits direction := by
    have eachDerivative (alternative : Alternative) : ExactRealHasDerivAt
        (fun time : ℝ => prior.weight alternative *
          Real.exp (-(alternatives alternative).value (logits + time • direction)))
        (-(prior.weight alternative *
          Real.exp (-(alternatives alternative).value logits) *
            ⟪(alternatives alternative).gradient logits, direction⟫_ℝ)) 0 := by
      have base := (alternatives alternative).directionalDerivative logits direction
      have negated := base.neg
      have exponentiated :=
        (hasDerivAt_expExact
          (-((alternatives alternative).value (logits + 0 • direction)))).comp 0 negated
      have convertedExponentiated := algebraHasDerivAt_to_exact exponentiated
      have directExponential : ExactRealHasDerivAt
          (fun time : ℝ => Real.exp
            (-(alternatives alternative).value (logits + time • direction)))
          (-(Real.exp (-(alternatives alternative).value logits) *
            ⟪(alternatives alternative).gradient logits, direction⟫_ℝ)) 0 := by
        convert convertedExponentiated using 1
        · rfl
        · simp only [zero_smul, add_zero]
          ring
      have weighted := directExponential.const_mul (prior.weight alternative)
      apply weighted.congr_deriv
      ring
    have normalizerDerivative := HasDerivAt.fun_sum (u := Finset.univ)
      (fun alternative _ => eachDerivative alternative)
    have normalizerNonzero :
        (∑ alternative, prior.weight alternative *
          Real.exp (-(alternatives alternative).value
            (logits + (0 : ℝ) • direction))) ≠ 0 := by
      simpa [marginalNormalizer] using ne_of_gt
        (marginalNormalizer_pos prior alternatives logits)
    have logarithm := normalizerDerivative.log normalizerNonzero |>.neg
    apply logarithm.congr_deriv
    simp only [zero_smul, add_zero]
    rw [sum_inner]
    simp only [real_inner_smul_left]
    unfold marginalNormalizer
    field_simp [normalizerNonzero]
    simp only [Finset.sum_neg_distrib]
    rw [← Finset.sum_div]
    ring

inductive InformationRole where
  | current
  | replay
deriving DecidableEq

structure RolePartition (Group : Type*) [Fintype Group] where
  role : Group → InformationRole
  currentNonempty : (Finset.univ.filter fun group => role group = .current).Nonempty
  replayNonempty : (Finset.univ.filter fun group => role group = .replay).Nonempty

def roleMean {rows actions : ℕ} {Group : Type*} [Fintype Group]
    (partition : RolePartition Group) (selectedRole : InformationRole)
    (precision : Group → ℝ)
    (groups : Group → BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions :=
  let selected := Finset.univ.filter fun group => partition.role group = selectedRole
  (BatchTaskFunctional.sum fun group : selected =>
    (groups group.1).scale (precision group.1)).scale ((selected.card : ℝ)⁻¹)

def precisionWeightedInformationTask {rows actions : ℕ} {Group : Type*}
    [Fintype Group] (partition : RolePartition Group)
    (precision : Group → ℝ) (retentionExchangeRate : ℝ)
    (groups : Group → BatchTaskFunctional rows actions) :
    BatchTaskFunctional rows actions :=
  (roleMean partition .current precision groups).add
    ((roleMean partition .replay precision groups).scale retentionExchangeRate)

/-! ## Routed-row mean energy -/

def routedRows {rows actions : ℕ} (inputs : Fin rows → Inputs actions) :
    Finset (Fin rows) :=
  Finset.univ.filter fun row => (inputs row).routed.Nonempty

def finiteSelectedMean {Index : Type*} [Fintype Index] [DecidableEq Index]
    (selected : Finset Index) (value : Index → ℝ) : ℝ :=
  if selected.Nonempty then
    (selected.card : ℝ)⁻¹ * ∑ index ∈ selected, value index
  else 0

def routedResidualMean {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (dynamics : Dynamics) : ℝ :=
  finiteSelectedMean (routedRows inputs) fun row =>
    residualEnergy parameters (inputs row) dynamics (states row)

def patchedPolicyBatch {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width) :
    PolicyBatch rows actions :=
  WithLp.toLp 2 fun coordinate =>
    patchedLogits parameters (inputs coordinate.1) (states coordinate.1).1 coordinate.2

/-- Exact batch energy used at the local-PC boundary: the residual energy is
the mean over routed rows, while the task is the already-grouped information
functional over the whole policy-logit batch.  With no routed rows the
residual term is exactly zero; the optimizer transition separately enforces
the registered no-route skip. -/
def routedBatchEnergy {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (task : BatchTaskFunctional rows actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) : ℝ :=
  routedResidualMean parameters inputs states dynamics +
    parameters.taskPrecision *
      task.value (patchedPolicyBatch parameters inputs states) +
    frozenAuxiliary

theorem patchedPolicyBatch_row {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (row : Fin rows) :
    batchRow (patchedPolicyBatch parameters inputs states) row =
      patchedLogits parameters (inputs row) (states row).1 := by
  rfl

theorem patchedPolicyBatch_illegal_eq_base {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (row : Fin rows) (action : Fin actions)
    (illegal : action ∉ (inputs row).legal) :
    patchedPolicyBatch parameters inputs states (row, action) =
      (inputs row).baseLogits action := by
  apply patchedLogits_outside_mutable
  intro mutable
  exact illegal (Finset.mem_of_mem_inter_right mutable)

theorem patchedPolicyBatch_unrouted_eq_base {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (row : Fin rows) (action : Fin actions)
    (unrouted : action ∉ (inputs row).routed) :
    patchedPolicyBatch parameters inputs states (row, action) =
      (inputs row).baseLogits action := by
  apply patchedLogits_outside_mutable
  intro mutable
  exact unrouted (Finset.mem_of_mem_inter_left mutable)

theorem routedBatchEnergy_one_row {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Fin 1 → Inputs actions)
    (states : Fin 1 → State width) (task : BatchTaskFunctional 1 actions)
    (dynamics : Dynamics) (frozenAuxiliary : ℝ)
    (routed : (inputs 0).routed.Nonempty) :
    routedBatchEnergy parameters inputs states task dynamics frozenAuxiliary =
      residualEnergy parameters (inputs 0) dynamics (states 0) +
      parameters.taskPrecision *
          task.value (patchedPolicyBatch parameters inputs states) +
        frozenAuxiliary := by
  have selected : routedRows inputs = {0} := by
    ext row
    fin_cases row
    simp [routedRows, routed]
  simp [routedBatchEnergy, routedResidualMean, finiteSelectedMean, selected]

theorem routedBatchEnergy_no_routed_rows {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (task : BatchTaskFunctional rows actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (noneRouted : routedRows inputs = ∅) :
    routedBatchEnergy parameters inputs states task dynamics frozenAuxiliary =
      parameters.taskPrecision *
        task.value (patchedPolicyBatch parameters inputs states) +
      frozenAuxiliary := by
  simp [routedBatchEnergy, routedResidualMean, finiteSelectedMean, noneRouted]

/-- Averaging over every batch row is not the routed-row mean: a large
unrouted residual must not dilute or inflate the local-PC residual term. -/
theorem all_row_mean_differs_from_routed_mean_fixture :
    finiteSelectedMean ({0} : Finset (Fin 2))
        (fun row => if row = 0 then 2 else 50) = 2 ∧
      (2 : ℝ)⁻¹ * ∑ row : Fin 2, (if row = 0 then 2 else 50) = 26 := by
  norm_num [finiteSelectedMean, Fin.sum_univ_two]

/-! ## Exact row restriction used by local PC -/

def freezeOtherRows {rows actions : ℕ}
    (batchTask : BatchTaskFunctional rows actions)
    (frozenBatch : PolicyBatch rows actions) (row : Fin rows) :
    TaskFunctional actions where
  value logits := batchTask.value (replaceBatchRow frozenBatch row logits)
  gradient logits := batchRow
    (batchTask.gradient (replaceBatchRow frozenBatch row logits)) row
  directionalDerivative logits direction := by
    have derivative := batchTask.directionalDerivative
      (replaceBatchRow frozenBatch row logits) (embedBatchRow row direction)
    have functionEquality :
        (fun time : ℝ => batchTask.value
          (replaceBatchRow frozenBatch row (logits + time • direction))) =
        (fun time : ℝ => batchTask.value
          (replaceBatchRow frozenBatch row logits +
            time • embedBatchRow row direction)) := by
      funext time
      rw [replaceBatchRow_line]
    rw [functionEquality]
    apply derivative.congr_deriv
    exact inner_embedBatchRow row _ direction

/-- Frozen auxiliary heads are exactly an additive constant at the local
policy-logit boundary, so they have zero directional derivative. -/
theorem frozenAuxiliaryBatch_has_zero_derivative {rows actions : ℕ}
    (frozenAuxiliary : ℝ) (_logits _direction : PolicyBatch rows actions) :
    HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 := by
  exact hasDerivAt_const _ _

/-! ## Positive and negative semantic fixtures -/

theorem two_identical_alternatives_marginal_eq_single
    (loss : ℝ) :
    -Real.log ((1 / 2 : ℝ) * Real.exp (-loss) +
      (1 / 2 : ℝ) * Real.exp (-loss)) = loss := by
  rw [← add_mul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul]
  rw [Real.log_exp]
  ring

theorem marginal_group_is_not_arithmetic_mean_fixture :
    -Real.log ((1 / 2 : ℝ) * Real.exp (-(0 : ℝ)) +
      (1 / 2 : ℝ) * Real.exp (-(2 : ℝ))) ≠ (0 + 2) / 2 := by
  intro equality
  have expPositive := Real.exp_pos (-2)
  have expLtOne : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have sumBounds : (1 / 2 : ℝ) <
      (1 / 2 : ℝ) * Real.exp (-(0 : ℝ)) +
        (1 / 2 : ℝ) * Real.exp (-(2 : ℝ)) := by
    norm_num
    positivity
  have expOneGtTwo : (2 : ℝ) < Real.exp 1 := by
    have bound := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at bound ⊢
    exact bound
  have expNegOneLtHalf : Real.exp (-1) < (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) expOneGtTwo)
  have expNegOneLtSum : Real.exp (-1) <
      (1 / 2 : ℝ) * Real.exp (-(0 : ℝ)) +
        (1 / 2 : ℝ) * Real.exp (-(2 : ℝ)) :=
    lt_trans expNegOneLtHalf sumBounds
  have sumPositive : 0 <
      (1 / 2 : ℝ) * Real.exp (-(0 : ℝ)) +
        (1 / 2 : ℝ) * Real.exp (-(2 : ℝ)) := lt_trans (Real.exp_pos (-1)) expNegOneLtSum
  have logStrict := Real.strictMonoOn_log
    (Real.exp_pos (-1)) sumPositive expNegOneLtSum
  rw [Real.log_exp] at logStrict
  rw [show (0 + 2 : ℝ) / 2 = 1 by norm_num] at equality
  nlinarith

theorem ignoring_group_marginal_changes_objective_fixture :
    let alternativeLoss : Fin 2 → ℝ := fun index => if index = 0 then 0 else 2
    (∑ index, alternativeLoss index) / 2 = 1 ∧
      -Real.log (∑ index, (1 / 2 : ℝ) * Real.exp (-alternativeLoss index)) ≠ 1 := by
  dsimp only
  constructor
  · norm_num [Fin.sum_univ_two]
  · simpa [Fin.sum_univ_two] using marginal_group_is_not_arithmetic_mean_fixture

#print axioms hasDerivAt_categoricalCrossEntropy_plusLine
#print axioms tokenTask
#print axioms marginalNormalizer_pos
#print axioms marginalGroupTask
#print axioms routedBatchEnergy_one_row
#print axioms routedBatchEnergy_no_routed_rows
#print axioms all_row_mean_differs_from_routed_mean_fixture
#print axioms patchedPolicyBatch_illegal_eq_base
#print axioms freezeOtherRows
#print axioms two_identical_alternatives_marginal_eq_single
#print axioms marginal_group_is_not_arithmetic_mean_fixture

end
end ActionMemoryNonlinearVectorPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
