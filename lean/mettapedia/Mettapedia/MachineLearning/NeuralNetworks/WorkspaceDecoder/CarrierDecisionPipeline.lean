import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitialization
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EncoderEquivariance

/-!
# Carrier decision and policy-readout pipeline

The typed-workspace and selective-belief decoders expose different fast-state
charts, but their final policy path has the same structure: select the active
fixed address, pool allocated addresses, combine those values with a control
vector, read the encoded source through masked softmax attention, score the
registered operators, and finally apply the checker-owned legal mask.

This module states the ideal-real finite maps independently of tensor layout.
The final mask is represented by `Option`: an illegal operator has no score at
all. Consequently no learned decision state, attention map, operator
embedding, or bias can create legal support. A source checker separately pins
the concrete Python expressions. Binary32 primitives and trained parameters
remain separate replay obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open scoped BigOperators

/-! ## Allocated-slot pooling -/

/-- Number of allocated addresses in a finite mask. -/
def allocatedCount {Slot : Type*} [Fintype Slot]
    (allocated : Slot → Bool) : ℕ :=
  (Finset.univ.filter fun slot ↦ allocated slot = true).card

/-- Exact-real interpretation of the source masked mean. The denominator is
clamped at one, so the empty mask returns the additive zero. -/
noncomputable def sourceMaskedMean
    {Slot : Type*} [Fintype Slot]
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (allocated : Slot → Bool) (value : Slot → Value) : Value :=
  (((Nat.max (allocatedCount allocated) 1 : ℕ) : ℝ)⁻¹) •
    ∑ slot, if allocated slot then value slot else 0

theorem sourceMaskedMean_eq_zero_of_none
    {Slot : Type*} [Fintype Slot]
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (allocated : Slot → Bool) (value : Slot → Value)
    (noneAllocated : ∀ slot, allocated slot = false) :
    sourceMaskedMean allocated value = 0 := by
  simp [sourceMaskedMean, allocatedCount, noneAllocated]

/-- Values at inactive addresses cannot affect the pooled state. -/
theorem sourceMaskedMean_congr_on_allocated
    {Slot : Type*} [Fintype Slot]
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (allocated : Slot → Bool) (left right : Slot → Value)
    (agree : ∀ slot, allocated slot = true → left slot = right slot) :
    sourceMaskedMean allocated left = sourceMaskedMean allocated right := by
  unfold sourceMaskedMean
  apply congrArg
  apply Finset.sum_congr rfl
  intro slot _membership
  by_cases active : allocated slot = true
  · simp [active, agree slot active]
  · have inactive : allocated slot = false := Bool.eq_false_of_not_eq_true active
    simp [inactive]

/-! ## Permanent active-address injection -/

/-- Add the current typed-hole vector at exactly the active permanent address. -/
def injectActive
    {Slot Value : Type*} [DecidableEq Slot] [Add Value]
    (contents : Slot → Value) (active : Slot) (typed : Value) : Slot → Value :=
  fun slot ↦ if slot = active then contents slot + typed else contents slot

@[simp] theorem injectActive_at
    {Slot Value : Type*} [DecidableEq Slot] [Add Value]
    (contents : Slot → Value) (active : Slot) (typed : Value) :
    injectActive contents active typed active = contents active + typed := by
  simp [injectActive]

theorem injectActive_away
    {Slot Value : Type*} [DecidableEq Slot] [Add Value]
    (contents : Slot → Value) (active other : Slot) (typed : Value)
    (different : other ≠ active) :
    injectActive contents active typed other = contents other := by
  simp [injectActive, different]

/-! ## Query-to-key masked attention -/

/-- Masked exponential for a query whose type is separate from its key set. -/
noncomputable def queryMaskedExp {Key : Type*}
    (active : Key → Bool) (score : Key → ℝ) (key : Key) : ℝ :=
  if active key then Real.exp (score key) else 0

/-- Denominator of one query-to-key masked-softmax row. -/
noncomputable def queryNormalizer {Key : Type*} [Fintype Key]
    (active : Key → Bool) (score : Key → ℝ) : ℝ :=
  ∑ key, queryMaskedExp active score key

/-- Exact finite masked-softmax weight for a query-to-key read. -/
noncomputable def querySoftmaxWeight {Key : Type*} [Fintype Key]
    (active : Key → Bool) (score : Key → ℝ) (key : Key) : ℝ :=
  queryMaskedExp active score key / queryNormalizer active score

theorem queryMaskedExp_nonnegative {Key : Type*}
    (active : Key → Bool) (score : Key → ℝ) (key : Key) :
    0 ≤ queryMaskedExp active score key := by
  by_cases enabled : active key
  · simp [queryMaskedExp, enabled, (Real.exp_pos _).le]
  · simp [queryMaskedExp, enabled]

theorem queryNormalizer_positive {Key : Type*} [Fintype Key]
    (active : Key → Bool) (score : Key → ℝ)
    (nonempty : ∃ key, active key = true) :
    0 < queryNormalizer active score := by
  obtain ⟨key, keyActive⟩ := nonempty
  unfold queryNormalizer
  apply Finset.sum_pos'
  · intro candidate _membership
    exact queryMaskedExp_nonnegative active score candidate
  · exact ⟨key, Finset.mem_univ key, by
      simp [queryMaskedExp, keyActive, Real.exp_pos]⟩

/-- Every nonempty masked-softmax query row sums to one. -/
theorem querySoftmaxWeight_sum_one {Key : Type*} [Fintype Key]
    (active : Key → Bool) (score : Key → ℝ)
    (nonempty : ∃ key, active key = true) :
    ∑ key, querySoftmaxWeight active score key = 1 := by
  have denominatorNonzero : queryNormalizer active score ≠ 0 :=
    ne_of_gt (queryNormalizer_positive active score nonempty)
  change (∑ key, queryMaskedExp active score key /
    queryNormalizer active score) = 1
  rw [← Finset.sum_div]
  exact div_self denominatorNonzero

theorem querySoftmaxWeight_inactive {Key : Type*} [Fintype Key]
    (active : Key → Bool) (score : Key → ℝ) (key : Key)
    (inactive : active key = false) :
    querySoftmaxWeight active score key = 0 := by
  simp [querySoftmaxWeight, queryMaskedExp, inactive]

/-- Source-shaped memory or workspace read after masking and softmax. -/
noncomputable def queryRead
    {Key : Type*} [Fintype Key]
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (active : Key → Bool) (score : Key → ℝ) (value : Key → Value) : Value :=
  ∑ key, querySoftmaxWeight active score key • value key

theorem queryRead_eq_zero_of_none
    {Key : Type*} [Fintype Key]
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (active : Key → Bool) (score : Key → ℝ) (value : Key → Value)
    (noneActive : ∀ key, active key = false) :
    queryRead active score value = 0 := by
  simp [queryRead, querySoftmaxWeight, queryMaskedExp, queryNormalizer,
    noneActive]

/-! ## Carrier controls and shared decision state -/

/-- Workspace control: state input and source summary share one affine branch. -/
def workspaceControl
    {Input Hidden : Type*} [Add Input]
    (activate : Hidden → Hidden) (controlProjection : Input → Hidden)
    (stateInput sourceSummary : Input) : Hidden :=
  activate (controlProjection (stateInput + sourceSummary))

/-- Belief control adds a separate typed-hole projection after the common
state-plus-summary projection. -/
def beliefControl
    {Input Hole Hidden : Type*} [Add Input] [Add Hidden]
    (activate : Hidden → Hidden) (controlProjection : Input → Hidden)
    (holeControlProjection : Hole → Hidden)
    (stateInput sourceSummary : Input) (holeType : Hole) : Hidden :=
  activate
    (controlProjection (stateInput + sourceSummary) +
      holeControlProjection holeType)

theorem beliefControl_zero_hole_eq_workspace
    {Input Hole Hidden : Type*} [Add Input] [AddMonoid Hidden]
    (activate : Hidden → Hidden) (controlProjection : Input → Hidden)
    (holeControlProjection : Hole → Hidden)
    (stateInput sourceSummary : Input) (holeType : Hole)
    (zeroHole : holeControlProjection holeType = 0) :
    beliefControl activate controlProjection holeControlProjection
        stateInput sourceSummary holeType =
      workspaceControl activate controlProjection stateInput sourceSummary := by
  simp [beliefControl, workspaceControl, zeroHole]

/-- Common carrier-to-policy waist. Argument order matches the concrete
concatenation: active address, allocated mean, then control. -/
def sourceDecisionState
    {Visible Decision : Type*}
    (activate : Decision → Decision)
    (outputProjection : Visible → Visible → Visible → Decision)
    (active pooled control : Visible) : Decision :=
  activate (outputProjection active pooled control)

/-! ## Operator scoring with checker-owned support -/

/-- Raw learned score before the legal-action mask. -/
def sourceOperatorScore
    {Operator Readout Embedding : Type*}
    (pairing : Readout → Embedding → ℝ)
    (operatorEmbedding : Operator → Embedding) (bias : Operator → ℝ)
    (readout : Readout) (operator : Operator) : ℝ :=
  pairing readout (operatorEmbedding operator) + bias operator

/-- `none` is the ideal semantic image of source `-inf` masking. -/
def legalMaskedScore {Operator : Type*}
    (legal : Operator → Bool) (score : Operator → ℝ)
    (operator : Operator) : Option ℝ :=
  if legal operator then some (score operator) else none

@[simp] theorem legalMaskedScore_isSome
    {Operator : Type*} (legal : Operator → Bool) (score : Operator → ℝ)
    (operator : Operator) :
    (legalMaskedScore legal score operator).isSome = legal operator := by
  cases enabled : legal operator <;> simp [legalMaskedScore, enabled]

theorem legalMaskedScore_eq_none_iff
    {Operator : Type*} (legal : Operator → Bool) (score : Operator → ℝ)
    (operator : Operator) :
    legalMaskedScore legal score operator = none ↔ legal operator = false := by
  cases enabled : legal operator <;> simp [legalMaskedScore, enabled]

theorem legalMaskedScore_eq_some_iff
    {Operator : Type*} (legal : Operator → Bool) (score : Operator → ℝ)
    (operator : Operator) (value : ℝ) :
    legalMaskedScore legal score operator = some value ↔
      legal operator = true ∧ score operator = value := by
  cases enabled : legal operator <;> simp [legalMaskedScore, enabled]

/-- Learned scores can reorder legal operators but cannot change support. -/
theorem legalMaskedScore_support_independent
    {Operator : Type*} (legal : Operator → Bool)
    (left right : Operator → ℝ) (operator : Operator) :
    (legalMaskedScore legal left operator).isSome =
      (legalMaskedScore legal right operator).isSome := by
  simp

/-- Complete ideal-real host readout: masked memory attention, a learned
decision/context readout, operator embedding pairing and bias, then the legal
mask. -/
noncomputable def sourcePolicyReadout
    {MemoryKey Operator MemoryValue Decision Readout Embedding : Type*}
    [Fintype MemoryKey]
    [AddCommMonoid MemoryValue] [Module ℝ MemoryValue]
    (memoryActive : MemoryKey → Bool)
    (memoryScore : Decision → MemoryKey → ℝ)
    (memoryValue : MemoryKey → MemoryValue)
    (readout : Decision → MemoryValue → Readout)
    (pairing : Readout → Embedding → ℝ)
    (operatorEmbedding : Operator → Embedding)
    (bias : Operator → ℝ) (legal : Operator → Bool)
    (decision : Decision) (operator : Operator) : Option ℝ :=
  let context := queryRead memoryActive (memoryScore decision) memoryValue
  let visible := readout decision context
  legalMaskedScore legal
    (sourceOperatorScore pairing operatorEmbedding bias visible) operator

/-- The concrete readout's support is exactly the external legal mask,
independently of every learned map before it. -/
@[simp] theorem sourcePolicyReadout_isSome
    {MemoryKey Operator MemoryValue Decision Readout Embedding : Type*}
    [Fintype MemoryKey]
    [AddCommMonoid MemoryValue] [Module ℝ MemoryValue]
    (memoryActive : MemoryKey → Bool)
    (memoryScore : Decision → MemoryKey → ℝ)
    (memoryValue : MemoryKey → MemoryValue)
    (readout : Decision → MemoryValue → Readout)
    (pairing : Readout → Embedding → ℝ)
    (operatorEmbedding : Operator → Embedding)
    (bias : Operator → ℝ) (legal : Operator → Bool)
    (decision : Decision) (operator : Operator) :
    (sourcePolicyReadout memoryActive memoryScore memoryValue readout
      pairing operatorEmbedding bias legal decision operator).isSome =
        legal operator := by
  simp [sourcePolicyReadout]

/-! ## Positive and negative fixtures -/

namespace CarrierDecisionPipelineFixtures

/-- The clamped denominator makes an empty finite pool exactly zero. -/
theorem empty_masked_mean_exact :
    sourceMaskedMean (fun _ : Bool ↦ false)
      (fun key ↦ if key then (7 : ℝ) else 3) = 0 := by
  exact sourceMaskedMean_eq_zero_of_none _ _ (by simp)

/-- With both Boolean slots active, the source masked mean is arithmetic. -/
theorem two_slot_masked_mean_exact :
    sourceMaskedMean (fun _ : Bool ↦ true)
      (fun key ↦ if key then (6 : ℝ) else 2) = 4 := by
  norm_num [sourceMaskedMean, allocatedCount]

/-- Active-address injection leaves every other permanent address unchanged. -/
theorem active_injection_exact :
    injectActive (fun key : Bool ↦ if key then (5 : ℤ) else 2)
      false 7 false = 9 ∧
    injectActive (fun key : Bool ↦ if key then (5 : ℤ) else 2)
      false 7 true = 5 := by
  norm_num [injectActive]

/-- Injecting the current hole type into every slot is not the source map. -/
theorem broadcast_injection_is_wrong :
    injectActive (fun key : Bool ↦ if key then (5 : ℤ) else 2)
      false 7 true ≠
    ((fun key : Bool ↦ if key then (5 : ℤ) else 2) true + 7) := by
  norm_num [injectActive]

/-- A one-key mask makes attention read exactly that key's value. -/
theorem singleton_query_read_exact :
    queryRead (fun key : Bool ↦ !key) (fun _ ↦ 0)
      (fun key ↦ if key then (7 : ℝ) else 3) = 3 := by
  norm_num [queryRead, querySoftmaxWeight, queryMaskedExp, queryNormalizer]

/-- Belief control genuinely has a typed-hole branch absent from workspace
control. -/
theorem belief_and_workspace_control_can_differ :
    beliefControl id id id (1 : ℤ) 2 4 ≠
      workspaceControl id id (1 : ℤ) 2 := by
  norm_num [beliefControl, workspaceControl]

/-- Concatenation order is observable to a non-symmetric output projection. -/
theorem active_pooled_order_is_not_interchangeable :
    sourceDecisionState id (fun active pooled control : ℤ ↦
      100 * active + 10 * pooled + control) 1 2 3 ≠
    sourceDecisionState id (fun active pooled control : ℤ ↦
      100 * active + 10 * pooled + control) 2 1 3 := by
  norm_num [sourceDecisionState]

/-- Legal operators retain their learned score exactly. -/
theorem legal_operator_score_exact :
    legalMaskedScore (fun operator : Bool ↦ !operator)
      (fun _ ↦ (7 : ℝ)) false = some 7 := by
  norm_num [legalMaskedScore]

/-- Removing the final mask admits an operator that the checker rejects. -/
theorem omitted_legal_mask_is_wrong :
    legalMaskedScore (fun operator : Bool ↦ !operator)
      (fun _ ↦ (7 : ℝ)) true ≠ some 7 := by
  simp [legalMaskedScore]

end CarrierDecisionPipelineFixtures

#print axioms sourceMaskedMean_eq_zero_of_none
#print axioms sourceMaskedMean_congr_on_allocated
#print axioms injectActive_at
#print axioms injectActive_away
#print axioms querySoftmaxWeight_sum_one
#print axioms querySoftmaxWeight_inactive
#print axioms queryRead_eq_zero_of_none
#print axioms beliefControl_zero_hole_eq_workspace
#print axioms legalMaskedScore_isSome
#print axioms legalMaskedScore_eq_none_iff
#print axioms legalMaskedScore_eq_some_iff
#print axioms legalMaskedScore_support_independent
#print axioms sourcePolicyReadout_isSome
#print axioms CarrierDecisionPipelineFixtures.empty_masked_mean_exact
#print axioms CarrierDecisionPipelineFixtures.two_slot_masked_mean_exact
#print axioms CarrierDecisionPipelineFixtures.active_injection_exact
#print axioms CarrierDecisionPipelineFixtures.broadcast_injection_is_wrong
#print axioms CarrierDecisionPipelineFixtures.singleton_query_read_exact
#print axioms CarrierDecisionPipelineFixtures.belief_and_workspace_control_can_differ
#print axioms CarrierDecisionPipelineFixtures.active_pooled_order_is_not_interchangeable
#print axioms CarrierDecisionPipelineFixtures.legal_operator_score_exact
#print axioms CarrierDecisionPipelineFixtures.omitted_legal_mask_is_wrong

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
