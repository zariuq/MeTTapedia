import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTConservedCredit

/-!
# Explicit causal signals for conserved weighted-GSLT credit

`WeightedGSLTConservedCredit` makes receipts linear and the credit allocation
finite and conserved.  This module also makes the success modulator an explicit
bounded resource.  A redemption must consume both

* a receipt naming the synapse whose firing is being credited, and
* a success signal naming that synapse's postsynaptic neuron.

The signal is therefore not an inexhaustible label attached to a transition.
It occupies a state slot, can be issued only into an empty slot, and is consumed
by redemption.  The exact two-choice instance replays learning and reversal
through this stronger transition system.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTCausalCredit

open WeightedGSLTBehavioralAdequacy
open WeightedGSLTFiniteAdmission
open WeightedGSLTConservedCredit

/-- Conserved-credit state plus a bounded bank of neuron-addressed success
signals. -/
structure CausalCreditState (Synapse Neuron : Type*)
    (receiptSlots signalSlots creditBudget : ℕ) where
  core : CreditState Synapse Neuron receiptSlots creditBudget
  signals : Fin signalSlots → Option Neuron
deriving DecidableEq, Fintype

/-- Every constructor is an event in the same operational relation. -/
inductive CausalCreditAction (Synapse Neuron : Type*)
    (receiptSlots signalSlots creditBudget : ℕ) where
  | fire (receiptSlot : Fin receiptSlots) (synapse : Synapse)
  | signal (signalSlot : Fin signalSlots) (neuron : Neuron)
  | redeem (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
      (creditSlot : Fin creditBudget) (synapse : Synapse)
  | expireReceipt (receiptSlot : Fin receiptSlots)
  | expireSignal (signalSlot : Fin signalSlots)
deriving DecidableEq, Fintype

def replaceCore {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (core : CreditState Synapse Neuron receiptSlots creditBudget) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget where
  core := core
  signals := state.signals

def issueSignal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) (neuron : Neuron) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget where
  core := state.core
  signals := Function.update state.signals slot (some neuron)

def consumeSignal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget where
  core := state.core
  signals := Function.update state.signals slot none

/-- An explicit-signal transition.  The core allocation engine still enforces
receipt matching, donor locality, and genuine transfer. -/
def causalIntegratedStep {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) :
    CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget →
      Option (CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
  | .fire receiptSlot synapse =>
      (integratedStep post state.core (.fire receiptSlot synapse)).map
        (replaceCore state)
  | .signal signalSlot neuron =>
      if state.signals signalSlot = none then
        some (issueSignal state signalSlot neuron)
      else none
  | .redeem receiptSlot signalSlot creditSlot synapse =>
      if state.signals signalSlot = some (post synapse) then
        (integratedStep post state.core (.redeem receiptSlot creditSlot synapse)).map
          (fun nextCore => consumeSignal (replaceCore state nextCore) signalSlot)
      else none
  | .expireReceipt receiptSlot =>
      (integratedStep post state.core (.expire receiptSlot)).map
        (replaceCore state)
  | .expireSignal signalSlot =>
      if state.signals signalSlot ≠ none then
        some (consumeSignal state signalSlot)
      else none

def CausalStep {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget)
    (target : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) : Prop :=
  causalIntegratedStep post source action = some target

def causalRun {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget →
    List (CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget) →
      Option (CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
  | state, [] => some state
  | state, action :: rest =>
      (causalIntegratedStep post state action).bind fun next => causalRun post next rest

theorem causalRun_append {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (first second :
      List (CausalCreditAction Synapse Neuron receiptSlots signalSlots creditBudget)) :
    causalRun post state (first ++ second) =
      (causalRun post state first).bind fun middle => causalRun post middle second := by
  induction first generalizing state with
  | nil => simp [causalRun]
  | cons action rest ih =>
      simp only [List.cons_append, causalRun]
      cases hstep : causalIntegratedStep post state action with
      | none => simp
      | some middle => simp [ih]

/-! ## Two-resource causality and linearity -/

@[simp]
theorem issueSignal_signal_same {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) (neuron : Neuron) :
    (issueSignal state slot neuron).signals slot = some neuron := by
  simp [issueSignal]

@[simp]
theorem issueSignal_core {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) (neuron : Neuron) :
    (issueSignal state slot neuron).core = state.core := rfl

@[simp]
theorem consumeSignal_signal_same {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    (consumeSignal state slot).signals slot = none := by
  simp [consumeSignal]

@[simp]
theorem consumeSignal_core {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq (Fin signalSlots)]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    (consumeSignal state slot).core = state.core := rfl

/-- Signal storage is affine: an occupied slot cannot be overwritten. -/
theorem signal_into_occupied_slot_fails {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) (neuron : Neuron)
    (hoccupied : state.signals slot ≠ none) :
    causalIntegratedStep post state (.signal slot neuron) = none := by
  simp [causalIntegratedStep, hoccupied]

theorem causal_redeem_data {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    source.signals signalSlot = some (post synapse) ∧
      ∃ nextCore,
        Step post source.core (.redeem receiptSlot creditSlot synapse) nextCore ∧
        target = consumeSignal (replaceCore source nextCore) signalSlot := by
  change (if source.signals signalSlot = some (post synapse) then
      Option.map (fun nextCore =>
        consumeSignal (replaceCore source nextCore) signalSlot)
        (integratedStep post source.core
          (.redeem receiptSlot creditSlot synapse))
    else none) = some target at hstep
  split at hstep
  · rename_i hsignal
    rcases Option.map_eq_some_iff.mp hstep with ⟨nextCore, hcore, htarget⟩
    exact ⟨hsignal, nextCore, hcore, htarget.symm⟩
  · simp at hstep

theorem causal_redeem_requires_signal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    source.signals signalSlot = some (post synapse) :=
  (causal_redeem_data hstep).1

theorem causal_redeem_core_step {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    ∃ nextCore, Step post source.core (.redeem receiptSlot creditSlot synapse) nextCore := by
  rcases (causal_redeem_data hstep).2 with ⟨nextCore, hcore, _⟩
  exact ⟨nextCore, hcore⟩

/-- Redemption requires both resources, not merely an action label. -/
theorem causal_redeem_requires_receipt {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    source.core.receipts receiptSlot = some synapse := by
  rcases causal_redeem_core_step hstep with ⟨nextCore, hcore⟩
  exact redeem_requires_receipt hcore

theorem causal_redeem_consumes_signal {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    target.signals signalSlot = none := by
  rcases (causal_redeem_data hstep).2 with ⟨nextCore, _, rfl⟩
  simp

theorem causal_redeem_consumes_receipt {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    target.core.receipts receiptSlot = none := by
  rcases (causal_redeem_data hstep).2 with ⟨nextCore, hcore, rfl⟩
  exact redeem_consumes_receipt hcore

/-- Neither resource can be reused for another redemption. -/
theorem causal_redemption_is_single_use {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {firstCredit secondCredit : Fin creditBudget} {synapse : Synapse}
    (hstep : CausalStep post source
      (.redeem receiptSlot signalSlot firstCredit synapse) target) :
    causalIntegratedStep post target
      (.redeem receiptSlot signalSlot secondCredit synapse) = none := by
  have hsignal := causal_redeem_consumes_signal hstep
  simp [causalIntegratedStep, hsignal]

/-- An otherwise valid receipt cannot be redeemed without a matching success
signal. -/
theorem causal_redemption_without_signal_fails {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (synapse : Synapse)
    (hnone : state.signals signalSlot = none) :
    causalIntegratedStep post state
      (.redeem receiptSlot signalSlot creditSlot synapse) = none := by
  simp [causalIntegratedStep, hnone]

/-- A signal for another neuron cannot authorize local credit. -/
theorem causal_redemption_with_wrong_signal_fails {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (synapse : Synapse) (neuron : Neuron)
    (hsignal : state.signals signalSlot = some neuron)
    (hwrong : neuron ≠ post synapse) :
    causalIntegratedStep post state
      (.redeem receiptSlot signalSlot creditSlot synapse) = none := by
  have hne : state.signals signalSlot ≠ some (post synapse) := by
    rw [hsignal]
    simp [hwrong]
  simp [causalIntegratedStep, hne]

/-- An otherwise valid signal cannot be redeemed without a receipt. -/
theorem causal_redemption_without_receipt_fails {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (synapse : Synapse)
    (hsignal : state.signals signalSlot = some (post synapse))
    (hnone : state.core.receipts receiptSlot = none) :
    causalIntegratedStep post state
      (.redeem receiptSlot signalSlot creditSlot synapse) = none := by
  simp [causalIntegratedStep, hsignal,
    redemption_without_receipt_fails post state.core receiptSlot creditSlot synapse hnone]

def causalTotalCredits {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) : ℕ :=
  totalCredits state.core

theorem causalTotalCredits_eq_budget {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) :
    causalTotalCredits state = creditBudget :=
  totalCredits_eq_budget state.core

theorem causalState_finite {Synapse Neuron : Type*}
    (receiptSlots signalSlots creditBudget : ℕ)
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron] :
    Finite (CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) := by
  infer_instance

def CausalOperationalStep {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : ℕ}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target :
      CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget) : Prop :=
  ∃ action, CausalStep post source action target

theorem bottomAdmission_sound_for_causalCredit
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : ℕ}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {initial : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget}
    {good : CausalCreditState Synapse Neuron receiptSlots signalSlots creditBudget → Prop}
    (hadmit : BottomAdmissible (CausalOperationalStep post) initial good) :
    FairlyReliable (CausalOperationalStep post) initial good :=
  bottomAdmissible_implies_fairlyReliable hadmit

/-! ## Exact signaled choice experiment -/

abbrev CausalChoiceState := CausalCreditState ChoiceSynapse Unit 1 1 4
abbrev CausalChoiceAction := CausalCreditAction ChoiceSynapse Unit 1 1 4

def emptySignals : Fin 1 → Option Unit := fun _ => none

def causalInitialChoiceState : CausalChoiceState where
  core := initialChoiceState
  signals := emptySignals

def causalTargetLearnedState : CausalChoiceState where
  core := targetLearnedState
  signals := emptySignals

def causalDistractorLearnedState : CausalChoiceState where
  core := distractorLearnedState
  signals := emptySignals

def causalUncreditedEpisode : List CausalChoiceAction :=
  [ .fire 0 .target
  , .expireReceipt 0
  , .fire 0 .distractor
  , .expireReceipt 0 ]

def causalTargetCreditEpisode : List CausalChoiceAction :=
  [ .fire 0 .target
  , .signal 0 ()
  , .redeem 0 0 2 .target
  , .fire 0 .distractor
  , .expireReceipt 0
  , .fire 0 .target
  , .signal 0 ()
  , .redeem 0 0 3 .target
  , .fire 0 .distractor
  , .expireReceipt 0 ]

def causalReverseCreditEpisode : List CausalChoiceAction :=
  [ .fire 0 .distractor
  , .signal 0 ()
  , .redeem 0 0 2 .distractor
  , .fire 0 .distractor
  , .signal 0 ()
  , .redeem 0 0 3 .distractor ]

theorem causalRun_uncreditedEpisode :
    causalRun choicePost causalInitialChoiceState causalUncreditedEpisode =
      some causalInitialChoiceState := by
  simp [causalRun, causalIntegratedStep, integratedStep, causalUncreditedEpisode,
    causalInitialChoiceState, initialChoiceState,
    emptyReceipts, replaceCore, issueReceipt, consumeReceipt]

theorem causalRun_targetCreditEpisode :
    causalRun choicePost causalInitialChoiceState causalTargetCreditEpisode =
      some causalTargetLearnedState := by
  simp [causalRun, causalIntegratedStep, integratedStep, causalTargetCreditEpisode,
    choicePost, LocalDonor, causalInitialChoiceState, causalTargetLearnedState,
    initialChoiceState, targetLearnedState, emptySignals,
    emptyReceipts, initialChoiceAllocation, replaceCore, issueSignal, consumeSignal,
    issueReceipt, consumeReceipt, assignCredit]
  funext slot
  fin_cases slot <;> rfl

theorem causalRun_reverseCreditEpisode :
    causalRun choicePost causalTargetLearnedState causalReverseCreditEpisode =
      some causalDistractorLearnedState := by
  simp [causalRun, causalIntegratedStep, integratedStep, causalReverseCreditEpisode,
    choicePost, LocalDonor, causalTargetLearnedState, causalDistractorLearnedState,
    targetLearnedState, distractorLearnedState, emptySignals,
    emptyReceipts, targetLearnedAllocation, replaceCore, issueSignal, consumeSignal,
    issueReceipt, consumeReceipt, assignCredit]
  funext slot
  fin_cases slot <;> rfl

theorem causalRun_learn_then_reverse :
    causalRun choicePost causalInitialChoiceState
      (causalTargetCreditEpisode ++ causalReverseCreditEpisode) =
        some causalDistractorLearnedState := by
  rw [causalRun_append, causalRun_targetCreditEpisode]
  exact causalRun_reverseCreditEpisode

noncomputable def causalChoiceWeights (state : CausalChoiceState) :
    WeightMap ChoiceSynapse :=
  creditChoiceWeights state.core

theorem causal_uncredited_fails_target_task :
    ¬ rewardedChoiceTask.Solves (causalChoiceWeights causalInitialChoiceState) :=
  uncredited_equal_exposure_fails_target_task

theorem causal_target_credit_solves_target_task :
    rewardedChoiceTask.Solves (causalChoiceWeights causalTargetLearnedState) :=
  target_credit_solves_target_task

theorem causal_reverse_credit_solves_distractor_task :
    distractorChoiceTask.Solves
      (causalChoiceWeights causalDistractorLearnedState) :=
  reverse_credit_solves_distractor_task

/-- Explicit success signals, causal receipts, and conserved credit suffice for
learning and later reversing the same finite choice mechanism. -/
theorem causal_credit_learns_and_relearns :
    (causalRun choicePost causalInitialChoiceState causalUncreditedEpisode =
      some causalInitialChoiceState) ∧
    (causalRun choicePost causalInitialChoiceState causalTargetCreditEpisode =
      some causalTargetLearnedState) ∧
    rewardedChoiceTask.Solves (causalChoiceWeights causalTargetLearnedState) ∧
    (causalRun choicePost causalInitialChoiceState
      (causalTargetCreditEpisode ++ causalReverseCreditEpisode) =
        some causalDistractorLearnedState) ∧
    distractorChoiceTask.Solves
      (causalChoiceWeights causalDistractorLearnedState) :=
  ⟨causalRun_uncreditedEpisode, causalRun_targetCreditEpisode,
    causal_target_credit_solves_target_task, causalRun_learn_then_reverse,
    causal_reverse_credit_solves_distractor_task⟩

#print axioms causal_redeem_requires_signal
#print axioms causal_redeem_requires_receipt
#print axioms causal_redeem_consumes_signal
#print axioms causal_redeem_consumes_receipt
#print axioms causal_redemption_is_single_use
#print axioms signal_into_occupied_slot_fails
#print axioms causal_redemption_with_wrong_signal_fails
#print axioms causalTotalCredits_eq_budget
#print axioms bottomAdmission_sound_for_causalCredit
#print axioms causal_credit_learns_and_relearns

end WeightedGSLTCausalCredit
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
