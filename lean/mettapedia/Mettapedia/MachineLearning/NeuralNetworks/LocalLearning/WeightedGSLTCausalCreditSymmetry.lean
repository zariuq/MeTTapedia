import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCausalCreditConcurrency

/-!
# Slot-renaming symmetry for conserved causal credit

Receipt, signal, and credit slots are finite implementation resources.  Their
names must not become observable learning data.  This module proves that the
complete causal-credit transition system is equivariant under independent
permutations of all three slot banks.  Runs transport pointwise, while credit
counts and derived weights are invariant.

The closing counterexample records the boundary: relabeling state without
relabeling its action is not a symmetry.  Slot names are unobservable only
under coherent renaming of the whole operational presentation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTCausalCreditSymmetry

open WeightedGSLTBehavioralAdequacy
open WeightedGSLTConservedCredit
open WeightedGSLTCausalCredit

/-! ## Reindexing finite banks -/

/-- Transport a slot-indexed bank along an equivalence. -/
def reindex {α β γ : Type*} (equiv : α ≃ β) (bank : α → γ) : β → γ :=
  fun slot => bank (equiv.symm slot)

@[simp]
theorem reindex_apply {α β γ : Type*} (equiv : α ≃ β) (bank : α → γ)
    (slot : α) :
    reindex equiv bank (equiv slot) = bank slot := by
  simp [reindex]

/-- Reindexing commutes with updating the correspondingly renamed slot. -/
theorem reindex_update {α β γ : Type*}
    [DecidableEq α] [DecidableEq β]
    (equiv : α ≃ β) (bank : α → γ) (slot : α) (value : γ) :
    reindex equiv (Function.update bank slot value) =
      Function.update (reindex equiv bank) (equiv slot) value := by
  funext target
  by_cases htarget : target = equiv slot
  · subst target
    simp [reindex]
  · have hinverse : equiv.symm target ≠ slot := by
      intro h
      apply htarget
      rw [← equiv.apply_symm_apply target, h]
    simp [reindex, htarget, hinverse]

/-- Independently rename receipt and credit slots in the core state. -/
def relabelCore {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget) :
    CreditState Synapse Neuron receiptSlots creditBudget where
  receipts := reindex receiptPerm state.receipts
  allocation := reindex creditPerm state.allocation

/-- Independently rename all three finite resource banks. -/
def relabelState {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget where
  core := relabelCore receiptPerm creditPerm state.core
  signals := reindex signalPerm state.signals

/-- Rename every slot mentioned by an action. -/
def relabelAction {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget)) :
    CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget →
      CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget
  | .fire receiptSlot synapse => .fire (receiptPerm receiptSlot) synapse
  | .signal signalSlot neuron => .signal (signalPerm signalSlot) neuron
  | .redeem receiptSlot signalSlot creditSlot synapse =>
      .redeem (receiptPerm receiptSlot) (signalPerm signalSlot)
        (creditPerm creditSlot) synapse
  | .expireReceipt receiptSlot => .expireReceipt (receiptPerm receiptSlot)
  | .expireSignal signalSlot => .expireSignal (signalPerm signalSlot)

/-- Rename the two slot banks used by the conserved-credit core action. -/
def relabelCoreAction {Synapse : Type*}
    {receiptSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget)) :
    CreditAction Synapse receiptSlots creditBudget →
      CreditAction Synapse receiptSlots creditBudget
  | .fire receiptSlot synapse => .fire (receiptPerm receiptSlot) synapse
  | .redeem receiptSlot creditSlot synapse =>
      .redeem (receiptPerm receiptSlot) (creditPerm creditSlot) synapse
  | .expire receiptSlot => .expire (receiptPerm receiptSlot)

@[simp]
theorem relabelCore_receipt {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    (relabelCore receiptPerm creditPerm state).receipts (receiptPerm slot) =
      state.receipts slot := by
  simp [relabelCore]

@[simp]
theorem relabelCore_allocation {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin creditBudget) :
    (relabelCore receiptPerm creditPerm state).allocation (creditPerm slot) =
      state.allocation slot := by
  simp [relabelCore]

@[simp]
theorem relabelState_signal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    (relabelState receiptPerm signalPerm creditPerm state).signals (signalPerm slot) =
      state.signals slot := by
  simp [relabelState]

@[simp]
theorem relabelState_core {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) :
    (relabelState receiptPerm signalPerm creditPerm state).core =
      relabelCore receiptPerm creditPerm state.core := rfl

theorem relabelCore_issueReceipt {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin receiptSlots)]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) (synapse : Synapse) :
    relabelCore receiptPerm creditPerm (issueReceipt state slot synapse) =
      issueReceipt (relabelCore receiptPerm creditPerm state)
        (receiptPerm slot) synapse := by
  exact congrArg₂ CreditState.mk
    (reindex_update receiptPerm state.receipts slot (some synapse)) rfl

theorem relabelCore_consumeReceipt {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin receiptSlots)]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin receiptSlots) :
    relabelCore receiptPerm creditPerm (consumeReceipt state slot) =
      consumeReceipt (relabelCore receiptPerm creditPerm state)
        (receiptPerm slot) := by
  exact congrArg₂ CreditState.mk
    (reindex_update receiptPerm state.receipts slot none) rfl

theorem relabelCore_assignCredit {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq (Fin creditBudget)]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (slot : Fin creditBudget) (account : CreditAccount Synapse Neuron) :
    relabelCore receiptPerm creditPerm (assignCredit state slot account) =
      assignCredit (relabelCore receiptPerm creditPerm state)
        (creditPerm slot) account := by
  exact congrArg₂ CreditState.mk rfl
    (reindex_update creditPerm state.allocation slot account)

theorem relabelState_replaceCore {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (core : CreditState Synapse Neuron receiptSlots creditBudget) :
    relabelState receiptPerm signalPerm creditPerm (replaceCore state core) =
      replaceCore (relabelState receiptPerm signalPerm creditPerm state)
        (relabelCore receiptPerm creditPerm core) := rfl

theorem relabelState_issueSignal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) (neuron : Neuron) :
    relabelState receiptPerm signalPerm creditPerm (issueSignal state slot neuron) =
      issueSignal (relabelState receiptPerm signalPerm creditPerm state)
        (signalPerm slot) neuron := by
  exact congrArg₂ CausalCreditState.mk rfl
    (reindex_update signalPerm state.signals slot (some neuron))

theorem relabelState_consumeSignal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    relabelState receiptPerm signalPerm creditPerm (consumeSignal state slot) =
      consumeSignal (relabelState receiptPerm signalPerm creditPerm state)
        (signalPerm slot) := by
  exact congrArg₂ CausalCreditState.mk rfl
    (reindex_update signalPerm state.signals slot none)

/-- Applying a permutation and then its inverse recovers the complete state. -/
theorem relabelState_symm_apply {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) :
    relabelState receiptPerm.symm signalPerm.symm creditPerm.symm
        (relabelState receiptPerm signalPerm creditPerm state) = state := by
  cases state with
  | mk core signals =>
      cases core with
      | mk receipts allocation =>
          exact congrArg₂ CausalCreditState.mk
            (congrArg₂ CreditState.mk
              (by funext slot; simp [relabelState, relabelCore, reindex])
              (by funext slot; simp [relabelState, relabelCore, reindex]))
            (by funext slot; simp [relabelState, relabelCore, reindex])

theorem relabelState_injective {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget)) :
    Function.Injective
      (relabelState receiptPerm signalPerm creditPerm :
        CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget →
          CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) := by
  intro first second heq
  have hinverse := congrArg
    (relabelState receiptPerm.symm signalPerm.symm creditPerm.symm) heq
  simpa [relabelState_symm_apply] using hinverse

/-- The conserved-credit core step is itself equivariant under receipt- and
credit-slot renaming. -/
theorem integratedStep_relabel {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (action : CreditAction Synapse receiptSlots creditBudget) :
    integratedStep post (relabelCore receiptPerm creditPerm state)
        (relabelCoreAction receiptPerm creditPerm action) =
      (integratedStep post state action).map
        (relabelCore receiptPerm creditPerm) := by
  cases action with
  | fire receiptSlot synapse =>
      simp [relabelCoreAction, integratedStep, relabelCore_receipt,
        relabelCore_issueReceipt]
  | redeem receiptSlot creditSlot synapse =>
      simp [relabelCoreAction, integratedStep, relabelCore_receipt,
        relabelCore_allocation, relabelCore_consumeReceipt,
        relabelCore_assignCredit]
  | expire receiptSlot =>
      simp only [relabelCoreAction, integratedStep, relabelCore_receipt]
      by_cases hnone : state.receipts receiptSlot = none
      · simp [hnone]
      · simp_all only [ite_not, if_false, Option.map_some]
        rw [relabelCore_consumeReceipt]

/-! ## Equivariance of steps and runs -/

/-- Coherent renaming of every finite resource bank commutes with one complete
causal-credit transition, including rejection. -/
theorem causalIntegratedStep_relabel {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    causalIntegratedStep post
        (relabelState receiptPerm signalPerm creditPerm state)
        (relabelAction receiptPerm signalPerm creditPerm action) =
      (causalIntegratedStep post state action).map
        (relabelState receiptPerm signalPerm creditPerm) := by
  cases action with
  | fire receiptSlot synapse =>
      simp only [relabelAction, causalIntegratedStep]
      rw [show CreditAction.fire (receiptPerm receiptSlot) synapse =
        relabelCoreAction receiptPerm creditPerm (.fire receiptSlot synapse) from rfl]
      rw [relabelState_core]
      rw [integratedStep_relabel]
      cases integratedStep post state.core (.fire receiptSlot synapse) <;>
        simp [relabelState_replaceCore]
  | signal signalSlot neuron =>
      simp [relabelAction, causalIntegratedStep, relabelState_signal,
        relabelState_issueSignal]
  | redeem receiptSlot signalSlot creditSlot synapse =>
      simp only [relabelAction, causalIntegratedStep, relabelState_signal]
      by_cases hsignal : state.signals signalSlot = some (post synapse)
      · simp only [hsignal, ↓reduceIte]
        rw [show CreditAction.redeem (receiptPerm receiptSlot)
            (creditPerm creditSlot) synapse =
          relabelCoreAction receiptPerm creditPerm
            (.redeem receiptSlot creditSlot synapse) from rfl]
        rw [relabelState_core]
        rw [integratedStep_relabel]
        cases integratedStep post state.core (.redeem receiptSlot creditSlot synapse) <;>
          simp [relabelState_replaceCore, relabelState_consumeSignal]
      · simp [hsignal]
  | expireReceipt receiptSlot =>
      simp only [relabelAction, causalIntegratedStep]
      rw [show CreditAction.expire (receiptPerm receiptSlot) =
        relabelCoreAction receiptPerm creditPerm (.expire receiptSlot) from rfl]
      rw [relabelState_core]
      rw [integratedStep_relabel]
      cases integratedStep post state.core (.expire receiptSlot) <;>
        simp [relabelState_replaceCore]
  | expireSignal signalSlot =>
      simp only [relabelAction, causalIntegratedStep, relabelState_signal]
      by_cases hnone : state.signals signalSlot = none
      · simp [hnone]
      · simp_all only [ite_not, if_false, Option.map_some]
        rw [relabelState_consumeSignal]

/-- The labelled step relation is equivariant. -/
theorem CausalStep_relabel_iff {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    CausalStep post
        (relabelState receiptPerm signalPerm creditPerm source)
        (relabelAction receiptPerm signalPerm creditPerm action)
        (relabelState receiptPerm signalPerm creditPerm target) ↔
      CausalStep post source action target := by
  unfold CausalStep
  rw [causalIntegratedStep_relabel]
  constructor
  · intro hstep
    rcases Option.map_eq_some_iff.mp hstep with ⟨middle, hmiddle, heq⟩
    have : middle = target :=
      relabelState_injective receiptPerm signalPerm creditPerm heq
    simpa [this] using hmiddle
  · intro hstep
    rw [hstep]
    rfl

/-- Rename every action in a chronological history. -/
def relabelHistory {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :=
  actions.map (relabelAction receiptPerm signalPerm creditPerm)

/-- Coherent slot renaming commutes with an arbitrary finite run, including
failed runs. -/
theorem causalRun_relabel {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (signalPerm : Equiv.Perm (Fin signalSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    causalRun post (relabelState receiptPerm signalPerm creditPerm state)
        (relabelHistory receiptPerm signalPerm creditPerm actions) =
      (causalRun post state actions).map
        (relabelState receiptPerm signalPerm creditPerm) := by
  induction actions generalizing state with
  | nil => simp [causalRun, relabelHistory]
  | cons action rest ih =>
      simp only [relabelHistory, List.map_cons, causalRun]
      rw [causalIntegratedStep_relabel]
      cases hstep : causalIntegratedStep post state action with
      | none => simp
      | some next =>
          simp only [Option.map_some, Option.bind_some]
          exact ih next

/-! ## Observable invariance -/

/-- Credit ownership counts do not depend on the names of credit slots. -/
theorem accountCredits_relabelCore {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (state : CreditState Synapse Neuron receiptSlots creditBudget)
    (account : CreditAccount Synapse Neuron) :
    accountCredits (relabelCore receiptPerm creditPerm state) account =
      accountCredits state account := by
  unfold accountCredits
  apply Finset.card_bij (fun slot _ => creditPerm.symm slot)
  · intro slot hslot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hslot ⊢
    simpa [relabelCore, reindex] using hslot
  · intro first hfirst second hsecond heq
    exact creditPerm.symm.injective heq
  · intro slot hslot
    refine ⟨creditPerm slot, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hslot ⊢
    simpa [relabelCore, reindex] using hslot

/-- The real-valued efficacy map derived from conserved credits is invariant
under all slot renamings. -/
theorem derivedWeight_relabelCore {Synapse Neuron : Type*}
    {receiptSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (receiptPerm : Equiv.Perm (Fin receiptSlots))
    (creditPerm : Equiv.Perm (Fin creditBudget))
    (base quantum : ℝ)
    (state : CreditState Synapse Neuron receiptSlots creditBudget) :
    derivedWeight base quantum (relabelCore receiptPerm creditPerm state) =
      derivedWeight base quantum state := by
  funext synapse
  simp [derivedWeight, accountCredits_relabelCore]

/-! ## Positive and negative canaries -/

abbrev TwoReceiptState := CausalCreditState ChoiceSynapse Unit 2 1 1
abbrev TwoReceiptAction := CausalCreditAction ChoiceSynapse Unit 2 1 1

def asymmetricReceiptState : TwoReceiptState where
  core :=
    { receipts := fun slot => if slot = 0 then some .target else none
      allocation := fun _ => .reserve () }
  signals := fun _ => none

def swapReceipts : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- A coherent swap preserves the rejected firing transition. -/
theorem coherent_receipt_swap_preserves_rejection :
    causalIntegratedStep choicePost
        (relabelState swapReceipts (Equiv.refl _) (Equiv.refl _)
          asymmetricReceiptState)
        (relabelAction swapReceipts (Equiv.refl _) (Equiv.refl _)
          (.fire 0 .distractor : TwoReceiptAction)) = none := by
  rw [causalIntegratedStep_relabel]
  rfl

/-- Relabeling only the state is not a symmetry: an action aimed at the old
slot name can change from rejected to enabled. -/
theorem state_only_receipt_swap_changes_behavior :
    causalIntegratedStep choicePost asymmetricReceiptState
        (.fire 0 .distractor) = none ∧
      ∃ target,
        causalIntegratedStep choicePost
          (relabelState swapReceipts (Equiv.refl _) (Equiv.refl _)
            asymmetricReceiptState)
          (.fire 0 .distractor) = some target := by
  constructor
  · rfl
  · refine ⟨replaceCore
      (relabelState swapReceipts (Equiv.refl _) (Equiv.refl _)
        asymmetricReceiptState)
      (issueReceipt
        (relabelCore swapReceipts (Equiv.refl _) asymmetricReceiptState.core)
        0 .distractor), ?_⟩
    simp [causalIntegratedStep, integratedStep, relabelState, relabelCore,
      reindex, asymmetricReceiptState, swapReceipts]

#print axioms causalIntegratedStep_relabel
#print axioms CausalStep_relabel_iff
#print axioms causalRun_relabel
#print axioms derivedWeight_relabelCore
#print axioms coherent_receipt_swap_preserves_rejection
#print axioms state_only_receipt_swap_changes_behavior

end WeightedGSLTCausalCreditSymmetry
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
