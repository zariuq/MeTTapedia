import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCanaryAdmission

/-!
# Conserved causal credit for weighted-GSLT learning

This module formalizes a minimal task-sensitive extension of event-local
weighted-GSLT plasticity.  A firing may issue a bounded linear receipt.  A
later local redemption consumes exactly that receipt and reassigns one of a
fixed number of credit quanta.  Expiration consumes a receipt without changing
credit.  All three are constructors of one transition relation.

The construction makes four design constraints structural:

* a weight-changing redemption requires causal evidence;
* the evidence is single-use;
* credit is quantized and conserved rather than created by potentiation; and
* finite synapse, neuron, receipt-slot, and credit-slot types give a finite
  operational state space.

The two-choice instance supplies both boundaries.  Equal exposure followed
only by receipt expiration changes no weights.  Redeeming two target receipts
moves two reserve quanta to the target and solves the rewarded-choice task.
Redeeming two later distractor receipts transfers those same quanta away from
the target and learns the reversed task, demonstrating relearning without
raising a ceiling or increasing the budget.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTConservedCredit

open WeightedGSLTBehavioralAdequacy
open WeightedGSLTFiniteAdmission

/-! ## Finite linear-resource state -/

/-- Every credit quantum belongs either to a synapse or to the reserve of a
postsynaptic neuron. -/
inductive CreditAccount (Synapse Neuron : Type*) where
  | synapse (synapse : Synapse)
  | reserve (neuron : Neuron)
deriving DecidableEq, Fintype

/-- A bounded receipt bank and a fixed bank of credit quanta.  Receipt slots
give linear receipts explicit identities.  Credit slots give conservation by
construction: transitions may reassign slots but cannot create or delete them.
-/
structure CreditState (Synapse Neuron : Type*)
    (receiptSlots creditBudget : ℕ) where
  receipts : Fin receiptSlots → Option Synapse
  allocation : Fin creditBudget → CreditAccount Synapse Neuron
deriving DecidableEq, Fintype

/-- The three event forms in the integrated transition relation. -/
inductive CreditAction (Synapse : Type*) (receiptSlots creditBudget : ℕ) where
  | fire (receiptSlot : Fin receiptSlots) (synapse : Synapse)
  | redeem (receiptSlot : Fin receiptSlots) (creditSlot : Fin creditBudget)
      (synapse : Synapse)
  | expire (receiptSlot : Fin receiptSlots)
deriving DecidableEq, Fintype

/-- A donor account is local when it belongs to the same postsynaptic neuron as
the credited synapse. -/
def LocalDonor {Synapse Neuron : Type*} (post : Synapse → Neuron)
    (target : Synapse) : CreditAccount Synapse Neuron → Prop
  | .synapse donor => post donor = post target
  | .reserve neuron => neuron = post target

instance instDecidableLocalDonor {Synapse Neuron : Type*}
    [DecidableEq Neuron] (post : Synapse → Neuron) (target : Synapse)
    (donor : CreditAccount Synapse Neuron) : Decidable (LocalDonor post target donor) :=
  match donor with
  | .synapse source => inferInstanceAs (Decidable (post source = post target))
  | .reserve neuron => inferInstanceAs (Decidable (neuron = post target))

def issueReceipt {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) (synapse : Synapse) :
    CreditState Synapse Neuron receiptSlots creditBudget where
  receipts := Function.update state.receipts slot (some synapse)
  allocation := state.allocation

def consumeReceipt {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    CreditState Synapse Neuron receiptSlots creditBudget where
  receipts := Function.update state.receipts slot none
  allocation := state.allocation

def assignCredit {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin creditBudget)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin creditBudget) (account : CreditAccount Synapse Neuron) :
    CreditState Synapse Neuron receiptSlots creditBudget where
  receipts := state.receipts
  allocation := Function.update state.allocation slot account

/-- The complete local transition.  Firing requires an empty receipt slot;
redemption requires a matching receipt, a local donor, and a genuine transfer;
expiration requires an occupied receipt slot. -/
def integratedStep {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CreditState Synapse Neuron receiptSlots creditBudget) :
    CreditAction Synapse receiptSlots creditBudget →
      Option (CreditState Synapse Neuron receiptSlots creditBudget)
  | .fire receiptSlot synapse =>
      if state.receipts receiptSlot = none then
        some (issueReceipt state receiptSlot synapse)
      else none
  | .redeem receiptSlot creditSlot synapse =>
      let donor := state.allocation creditSlot
      if state.receipts receiptSlot = some synapse ∧
          LocalDonor post synapse donor ∧
          donor ≠ .synapse synapse then
        some (assignCredit (consumeReceipt state receiptSlot)
          creditSlot (.synapse synapse))
      else none
  | .expire receiptSlot =>
      if state.receipts receiptSlot ≠ none then
        some (consumeReceipt state receiptSlot)
      else none

def Step {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CreditState Synapse Neuron receiptSlots creditBudget)
    (action : CreditAction Synapse receiptSlots creditBudget)
    (target : CreditState Synapse Neuron receiptSlots creditBudget) : Prop :=
  integratedStep post source action = some target

/-- Execute a chronological event list. -/
def run {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CreditState Synapse Neuron receiptSlots creditBudget →
    List (CreditAction Synapse receiptSlots creditBudget) →
      Option (CreditState Synapse Neuron receiptSlots creditBudget)
  | state, [] => some state
  | state, action :: rest =>
      (integratedStep post state action).bind fun next => run post next rest

theorem run_append {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (first second : List (CreditAction Synapse receiptSlots creditBudget)) :
    run post state (first ++ second) =
      (run post state first).bind fun middle => run post middle second := by
  induction first generalizing state with
  | nil => simp [run]
  | cons action rest ih =>
      simp only [List.cons_append, run]
      cases hstep : integratedStep post state action with
      | none => simp
      | some middle => simp [ih]

/-! ## Exact transition laws -/

@[simp]
theorem issueReceipt_receipt_same {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) (synapse : Synapse) :
    (issueReceipt state slot synapse).receipts slot = some synapse := by
  simp [issueReceipt]

@[simp]
theorem issueReceipt_allocation {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) (synapse : Synapse) :
    (issueReceipt state slot synapse).allocation = state.allocation := rfl

@[simp]
theorem consumeReceipt_receipt_same {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    (consumeReceipt state slot).receipts slot = none := by
  simp [consumeReceipt]

@[simp]
theorem consumeReceipt_allocation {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin receiptSlots)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    (consumeReceipt state slot).allocation = state.allocation := rfl

@[simp]
theorem assignCredit_receipts {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin creditBudget)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin creditBudget) (account : CreditAccount Synapse Neuron) :
    (assignCredit state slot account).receipts = state.receipts := rfl

@[simp]
theorem assignCredit_allocation_same {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq (Fin creditBudget)]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin creditBudget) (account : CreditAccount Synapse Neuron) :
    (assignCredit state slot account).allocation slot = account := by
  simp [assignCredit]

theorem step_fire_iff {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) (synapse : Synapse) :
    Step post source (.fire slot synapse) target ↔
      source.receipts slot = none ∧ target = issueReceipt source slot synapse := by
  simp [Step, integratedStep, eq_comm]

theorem step_redeem_iff {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (creditSlot : Fin creditBudget)
    (synapse : Synapse) :
    Step post source (.redeem receiptSlot creditSlot synapse) target ↔
      source.receipts receiptSlot = some synapse ∧
      LocalDonor post synapse (source.allocation creditSlot) ∧
      source.allocation creditSlot ≠ .synapse synapse ∧
      target = assignCredit (consumeReceipt source receiptSlot)
        creditSlot (.synapse synapse) := by
  simp [Step, integratedStep, eq_comm, and_assoc]

theorem step_expire_iff {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    Step post source (.expire slot) target ↔
      source.receipts slot ≠ none ∧ target = consumeReceipt source slot := by
  simp [Step, integratedStep, eq_comm]

/-- Successful redemption requires the matching causal receipt. -/
theorem redeem_requires_receipt {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {creditSlot : Fin creditBudget}
    {synapse : Synapse}
    (hstep : Step post source (.redeem receiptSlot creditSlot synapse) target) :
    source.receipts receiptSlot = some synapse :=
  (step_redeem_iff post source target receiptSlot creditSlot synapse).mp hstep |>.1

/-- The transition relation enforces postsynaptic locality of every donor. -/
theorem redeem_donor_is_local {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {creditSlot : Fin creditBudget}
    {synapse : Synapse}
    (hstep : Step post source (.redeem receiptSlot creditSlot synapse) target) :
    LocalDonor post synapse (source.allocation creditSlot) :=
  (step_redeem_iff post source target receiptSlot creditSlot synapse).mp hstep |>.2.1

/-- A redemption consumes its receipt. -/
theorem redeem_consumes_receipt {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {creditSlot : Fin creditBudget}
    {synapse : Synapse}
    (hstep : Step post source (.redeem receiptSlot creditSlot synapse) target) :
    target.receipts receiptSlot = none := by
  rcases (step_redeem_iff post source target receiptSlot creditSlot synapse).mp hstep with
    ⟨_, _, _, rfl⟩
  simp

/-- A consumed receipt cannot fund a second redemption. -/
theorem redeemed_receipt_is_single_use {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {firstCredit secondCredit : Fin creditBudget}
    {synapse : Synapse}
    (hstep : Step post source (.redeem receiptSlot firstCredit synapse) target) :
    integratedStep post target (.redeem receiptSlot secondCredit synapse) = none := by
  have hnone := redeem_consumes_receipt hstep
  simp [integratedStep, hnone]

/-- A purported redemption with no receipt is rejected. -/
theorem redemption_without_receipt_fails {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (creditSlot : Fin creditBudget)
    (synapse : Synapse) (hnone : state.receipts receiptSlot = none) :
    integratedStep post state (.redeem receiptSlot creditSlot synapse) = none := by
  simp [integratedStep, hnone]

/-- A receipt cannot move credit from a different postsynaptic neighborhood. -/
theorem nonlocal_redemption_fails {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (creditSlot : Fin creditBudget)
    (synapse : Synapse)
    (hreceipt : state.receipts receiptSlot = some synapse)
    (hnonlocal : ¬ LocalDonor post synapse (state.allocation creditSlot)) :
    integratedStep post state (.redeem receiptSlot creditSlot synapse) = none := by
  simp [integratedStep, hreceipt, hnonlocal]

/-- Reassigning a quantum to its current owner is not counted as learning. -/
theorem self_redemption_fails {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (creditSlot : Fin creditBudget)
    (synapse : Synapse)
    (howner : state.allocation creditSlot = .synapse synapse) :
    integratedStep post state (.redeem receiptSlot creditSlot synapse) = none := by
  simp [integratedStep, howner]

/-- Redemption reassigns exactly one named credit slot. -/
theorem redeem_reassigns_one_credit {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {creditSlot : Fin creditBudget}
    {synapse : Synapse}
    (hstep : Step post source (.redeem receiptSlot creditSlot synapse) target) :
    target.allocation =
      Function.update source.allocation creditSlot (.synapse synapse) := by
  rcases (step_redeem_iff post source target receiptSlot creditSlot synapse).mp hstep with
    ⟨_, _, _, rfl⟩
  rfl

/-- Any weight-state change is accompanied by a receipt-state change.  There is
no successful map-only learning transition. -/
theorem allocation_change_implies_receipt_change {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {action : CreditAction Synapse receiptSlots creditBudget}
    (hstep : Step post source action target)
    (hallocation : source.allocation ≠ target.allocation) :
    source.receipts ≠ target.receipts := by
  cases action with
  | fire slot synapse =>
      rcases (step_fire_iff post source target slot synapse).mp hstep with ⟨_, rfl⟩
      exact (hallocation rfl).elim
  | expire slot =>
      rcases (step_expire_iff post source target slot).mp hstep with ⟨_, rfl⟩
      exact (hallocation rfl).elim
  | redeem receiptSlot creditSlot synapse =>
      rcases (step_redeem_iff post source target receiptSlot creditSlot synapse).mp hstep with
        ⟨hreceipt, _, _, rfl⟩
      intro hreceipts
      have hatSlot := congrFun hreceipts receiptSlot
      simp only [assignCredit, consumeReceipt, Function.update_self] at hatSlot
      rw [hreceipt] at hatSlot
      cases hatSlot

/-! ## Conservation, finiteness, and structural histories -/

def accountCredits {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (account : CreditAccount Synapse Neuron) : ℕ :=
  (Finset.univ.filter fun slot => state.allocation slot = account).card

def totalCredits {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CreditState Synapse Neuron receiptSlots creditBudget) : ℕ :=
  ∑ account : CreditAccount Synapse Neuron, accountCredits state account

/-- The credit budget is an invariant of the state type itself. -/
theorem totalCredits_eq_budget {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CreditState Synapse Neuron receiptSlots creditBudget) :
    totalCredits state = creditBudget := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin creditBudget)))
    (t := (Finset.univ : Finset (CreditAccount Synapse Neuron)))
    (f := state.allocation) (by intro slot _; exact Finset.mem_univ _)
  simpa [totalCredits, accountCredits] using hfiber.symm

theorem accountCredits_le_budget {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (account : CreditAccount Synapse Neuron) :
    accountCredits state account ≤ creditBudget := by
  unfold accountCredits
  calc
    (Finset.univ.filter fun slot => state.allocation slot = account).card ≤
        (Finset.univ : Finset (Fin creditBudget)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = creditBudget := by simp

theorem step_conserves_totalCredits {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {action : CreditAction Synapse receiptSlots creditBudget}
    (_hstep : Step post source action target) :
    totalCredits target = totalCredits source := by
  rw [totalCredits_eq_budget, totalCredits_eq_budget]

/-- The operational state and action spaces are finite whenever the graph's
synapse and neuron types are finite. -/
theorem creditState_finite {Synapse Neuron : Type*}
    (receiptSlots creditBudget : ℕ)
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron] :
    Finite (CreditState Synapse Neuron receiptSlots creditBudget) := by
  infer_instance

theorem creditAction_finite {Synapse : Type*}
    (receiptSlots creditBudget : ℕ)
    [Fintype Synapse] [DecidableEq Synapse] :
    Finite (CreditAction Synapse receiptSlots creditBudget) := by
  infer_instance

/-- Structural actions may issue or expire receipts but never redeem them. -/
inductive StructuralAction {Synapse : Type*} {receiptSlots creditBudget : ℕ} :
    CreditAction Synapse receiptSlots creditBudget → Prop where
  | fire (slot : Fin receiptSlots) (synapse : Synapse) :
      StructuralAction (.fire slot synapse)
  | expire (slot : Fin receiptSlots) : StructuralAction (.expire slot)

theorem structural_step_preserves_allocation {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CreditState Synapse Neuron receiptSlots creditBudget}
    {action : CreditAction Synapse receiptSlots creditBudget}
    (hstep : Step post source action target) (hstructural : StructuralAction action) :
    target.allocation = source.allocation := by
  cases hstructural with
  | fire slot synapse =>
      rcases (step_fire_iff post source target slot synapse).mp hstep with ⟨_, rfl⟩
      rfl
  | expire slot =>
      rcases (step_expire_iff post source target slot).mp hstep with ⟨_, rfl⟩
      rfl

/-- Exposure and receipt expiry alone cannot change the learned map. -/
theorem structural_run_preserves_allocation {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget)
    (actions : List (CreditAction Synapse receiptSlots creditBudget))
    (hstructural : ∀ action ∈ actions, StructuralAction action)
    (hrun : run post source actions = some target) :
    target.allocation = source.allocation := by
  induction actions generalizing source with
  | nil =>
      simp [run] at hrun
      subst target
      rfl
  | cons action rest ih =>
      simp only [run] at hrun
      cases hnext : integratedStep post source action with
      | none => simp [hnext] at hrun
      | some middle =>
          simp [hnext] at hrun
          have hfirst : StructuralAction action := hstructural action (by simp)
          have hrest : ∀ next ∈ rest, StructuralAction next := by
            intro next hmem
            exact hstructural next (by simp [hmem])
          have hallocFirst : middle.allocation = source.allocation :=
            structural_step_preserves_allocation (post := post)
              (source := source) (target := middle) (action := action) hnext hfirst
          exact (ih middle hrest hrun).trans hallocFirst

/-- Real-valued efficacy derived from a fixed number of quantized credits. -/
noncomputable def derivedWeight {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (synapse : Synapse) : ℝ :=
  base + quantum * accountCredits state (.synapse synapse)

theorem derivedWeight_lower_bound {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ) (hquantum : 0 ≤ quantum)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (synapse : Synapse) :
    base ≤ derivedWeight base quantum state synapse := by
  simp only [derivedWeight, le_add_iff_nonneg_right]
  positivity

theorem derivedWeight_upper_bound {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ) (hquantum : 0 ≤ quantum)
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (synapse : Synapse) :
    derivedWeight base quantum state synapse ≤ base + quantum * creditBudget := by
  simp only [derivedWeight, add_le_add_iff_left]
  apply mul_le_mul_of_nonneg_left _ hquantum
  exact_mod_cast accountCredits_le_budget state (.synapse synapse)

/-- Without redemption, even the derived real-valued weight map is unchanged. -/
theorem structural_run_preserves_derivedWeight {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ} [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget)
    (actions : List (CreditAction Synapse receiptSlots creditBudget))
    (hstructural : ∀ action ∈ actions, StructuralAction action)
    (hrun : run post source actions = some target)
    (base quantum : ℝ) :
    derivedWeight base quantum target = derivedWeight base quantum source := by
  have hallocation := structural_run_preserves_allocation
    post source target actions hstructural hrun
  funext synapse
  simp [derivedWeight, accountCredits, hallocation]

/-- The finite operational relation obtained by forgetting which action labels
an edge.  It can be admitted by the generic bottom-class theory. -/
def OperationalStep {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CreditState Synapse Neuron receiptSlots creditBudget) : Prop :=
  ∃ action, Step post source action target

theorem bottomAdmission_sound_for_conservedCredit
    {Synapse Neuron : Type*} {receiptSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {initial : CreditState Synapse Neuron receiptSlots creditBudget}
    {good : CreditState Synapse Neuron receiptSlots creditBudget → Prop}
    (hadmit : BottomAdmissible (OperationalStep post) initial good) :
    FairlyReliable (OperationalStep post) initial good :=
  bottomAdmissible_implies_fairlyReliable hadmit

/-! ## Exact two-choice learning and relearning -/

abbrev ChoiceAccount := CreditAccount ChoiceSynapse Unit
abbrev ChoiceCreditState := CreditState ChoiceSynapse Unit 1 4
abbrev ChoiceCreditAction := CreditAction ChoiceSynapse 1 4

def choicePost (_ : ChoiceSynapse) : Unit := ()

def emptyReceipts : Fin 1 → Option ChoiceSynapse := fun _ => none

/-- One target quantum, one distractor quantum, and two reserve quanta. -/
def initialChoiceAllocation : Fin 4 → ChoiceAccount := fun slot =>
  if slot = 0 then .synapse .target
  else if slot = 1 then .synapse .distractor
  else .reserve ()

def initialChoiceState : ChoiceCreditState where
  receipts := emptyReceipts
  allocation := initialChoiceAllocation

/-- Three target quanta and one distractor quantum. -/
def targetLearnedAllocation : Fin 4 → ChoiceAccount := fun slot =>
  if slot = 1 then .synapse .distractor else .synapse .target

def targetLearnedState : ChoiceCreditState where
  receipts := emptyReceipts
  allocation := targetLearnedAllocation

/-- One target quantum and three distractor quanta. -/
def distractorLearnedAllocation : Fin 4 → ChoiceAccount := fun slot =>
  if slot = 0 then .synapse .target else .synapse .distractor

def distractorLearnedState : ChoiceCreditState where
  receipts := emptyReceipts
  allocation := distractorLearnedAllocation

def uncreditedEpisode : List ChoiceCreditAction :=
  [ .fire 0 .target
  , .expire 0
  , .fire 0 .distractor
  , .expire 0 ]

def targetCreditEpisode : List ChoiceCreditAction :=
  [ .fire 0 .target
  , .redeem 0 2 .target
  , .fire 0 .distractor
  , .expire 0
  , .fire 0 .target
  , .redeem 0 3 .target
  , .fire 0 .distractor
  , .expire 0 ]

/-- Reassign the two quanta learned by the target; no reserve growth occurs. -/
def reverseCreditEpisode : List ChoiceCreditAction :=
  [ .fire 0 .distractor
  , .redeem 0 2 .distractor
  , .fire 0 .distractor
  , .redeem 0 3 .distractor ]

theorem uncreditedEpisode_is_structural :
    ∀ action ∈ uncreditedEpisode, StructuralAction action := by
  intro action haction
  simp only [uncreditedEpisode, List.mem_cons] at haction
  simp only [List.not_mem_nil, or_false] at haction
  rcases haction with rfl | rfl | rfl | rfl
  · exact StructuralAction.fire _ _
  · exact StructuralAction.expire _
  · exact StructuralAction.fire _ _
  · exact StructuralAction.expire _

theorem run_uncreditedEpisode :
    run choicePost initialChoiceState uncreditedEpisode = some initialChoiceState := by
  simp [run, integratedStep, uncreditedEpisode, initialChoiceState,
    emptyReceipts, issueReceipt, consumeReceipt]

theorem run_targetCreditEpisode :
    run choicePost initialChoiceState targetCreditEpisode = some targetLearnedState := by
  simp [run, integratedStep, targetCreditEpisode, choicePost, LocalDonor,
    initialChoiceState, targetLearnedState, emptyReceipts,
    initialChoiceAllocation,
    issueReceipt, consumeReceipt, assignCredit]
  funext slot
  fin_cases slot <;> rfl

theorem run_reverseCreditEpisode :
    run choicePost targetLearnedState reverseCreditEpisode = some distractorLearnedState := by
  simp [run, integratedStep, reverseCreditEpisode, choicePost, LocalDonor,
    targetLearnedState, distractorLearnedState, emptyReceipts,
    targetLearnedAllocation,
    issueReceipt, consumeReceipt, assignCredit]
  funext slot
  fin_cases slot <;> rfl

theorem run_learn_then_reverse :
    run choicePost initialChoiceState (targetCreditEpisode ++ reverseCreditEpisode) =
      some distractorLearnedState := by
  rw [run_append, run_targetCreditEpisode]
  exact run_reverseCreditEpisode

theorem initial_target_credits :
    accountCredits initialChoiceState (.synapse .target) = 1 := by decide

theorem initial_distractor_credits :
    accountCredits initialChoiceState (.synapse .distractor) = 1 := by decide

theorem targetLearned_target_credits :
    accountCredits targetLearnedState (.synapse .target) = 3 := by decide

theorem targetLearned_distractor_credits :
    accountCredits targetLearnedState (.synapse .distractor) = 1 := by decide

theorem distractorLearned_target_credits :
    accountCredits distractorLearnedState (.synapse .target) = 1 := by decide

theorem distractorLearned_distractor_credits :
    accountCredits distractorLearnedState (.synapse .distractor) = 3 := by decide

theorem initial_total_credit : totalCredits initialChoiceState = 4 :=
  totalCredits_eq_budget initialChoiceState

theorem targetLearned_total_credit : totalCredits targetLearnedState = 4 :=
  totalCredits_eq_budget targetLearnedState

theorem distractorLearned_total_credit : totalCredits distractorLearnedState = 4 :=
  totalCredits_eq_budget distractorLearnedState

noncomputable def creditChoiceWeights (state : ChoiceCreditState) :
    WeightMap ChoiceSynapse :=
  derivedWeight 0 1 state

theorem initialChoiceWeights_eq_uniform :
    creditChoiceWeights initialChoiceState = uniformChoiceWeights := by
  funext synapse
  cases synapse <;>
    norm_num [creditChoiceWeights, derivedWeight, uniformChoiceWeights,
      initial_target_credits, initial_distractor_credits]

theorem targetLearned_weights :
    creditChoiceWeights targetLearnedState .target = 3 ∧
      creditChoiceWeights targetLearnedState .distractor = 1 := by
  constructor <;>
    norm_num [creditChoiceWeights, derivedWeight,
      targetLearned_target_credits, targetLearned_distractor_credits]

theorem distractorLearned_weights :
    creditChoiceWeights distractorLearnedState .target = 1 ∧
      creditChoiceWeights distractorLearnedState .distractor = 3 := by
  constructor <;>
    norm_num [creditChoiceWeights, derivedWeight,
      distractorLearned_target_credits, distractorLearned_distractor_credits]

theorem uncredited_equal_exposure_fails_target_task :
    ¬ rewardedChoiceTask.Solves (creditChoiceWeights initialChoiceState) := by
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    initialChoiceWeights_eq_uniform, uniformChoiceWeights]

theorem target_credit_solves_target_task :
    rewardedChoiceTask.Solves (creditChoiceWeights targetLearnedState) := by
  rcases targetLearned_weights with ⟨htarget, hdistractor⟩
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    htarget, hdistractor]

noncomputable def distractorChoiceProbability
    (weights : WeightMap ChoiceSynapse) : ℝ :=
  weights .distractor / (weights .target + weights .distractor)

noncomputable def distractorChoiceTask : BehavioralTask ChoiceSynapse ℝ where
  admissible := choiceAdmissible
  evaluate := distractorChoiceProbability
  accepts := fun probability => (3 / 4 : ℝ) ≤ probability

def distractorWitness : WeightMap ChoiceSynapse
  | .target => 1
  | .distractor => 3

theorem distractorChoice_representable : Representable distractorChoiceTask := by
  refine ⟨distractorWitness, ?_, ?_⟩
  · intro synapse
    cases synapse <;> norm_num [distractorWitness, choiceAdmissible]
  · norm_num [BehavioralTask.Solves, distractorChoiceTask,
      distractorChoiceProbability, distractorWitness]

theorem reverse_credit_solves_distractor_task :
    distractorChoiceTask.Solves (creditChoiceWeights distractorLearnedState) := by
  rcases distractorLearned_weights with ⟨htarget, hdistractor⟩
  norm_num [BehavioralTask.Solves, distractorChoiceTask,
    distractorChoiceProbability, htarget, hdistractor]

theorem reverse_credit_leaves_target_task :
    ¬ rewardedChoiceTask.Solves (creditChoiceWeights distractorLearnedState) := by
  rcases distractorLearned_weights with ⟨htarget, hdistractor⟩
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    htarget, hdistractor]

/-- Headline make-or-break result: exposure without redemption does not learn,
local conserved credit learns the rewarded target, and the same fixed budget
can subsequently be reassigned to learn the reversed task. -/
theorem conserved_credit_learns_and_relearns :
    (run choicePost initialChoiceState uncreditedEpisode = some initialChoiceState) ∧
    (run choicePost initialChoiceState targetCreditEpisode = some targetLearnedState) ∧
    rewardedChoiceTask.Solves (creditChoiceWeights targetLearnedState) ∧
    (run choicePost targetLearnedState reverseCreditEpisode =
      some distractorLearnedState) ∧
    (run choicePost initialChoiceState
      (targetCreditEpisode ++ reverseCreditEpisode) = some distractorLearnedState) ∧
    distractorChoiceTask.Solves (creditChoiceWeights distractorLearnedState) :=
  ⟨run_uncreditedEpisode, run_targetCreditEpisode,
    target_credit_solves_target_task, run_reverseCreditEpisode,
    run_learn_then_reverse, reverse_credit_solves_distractor_task⟩

#print axioms redeem_requires_receipt
#print axioms redeemed_receipt_is_single_use
#print axioms nonlocal_redemption_fails
#print axioms redeem_reassigns_one_credit
#print axioms allocation_change_implies_receipt_change
#print axioms totalCredits_eq_budget
#print axioms derivedWeight_upper_bound
#print axioms structural_run_preserves_allocation
#print axioms structural_run_preserves_derivedWeight
#print axioms bottomAdmission_sound_for_conservedCredit
#print axioms conserved_credit_learns_and_relearns

end WeightedGSLTConservedCredit
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
