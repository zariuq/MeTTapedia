import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCausalCredit
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelWave
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mathlib.Data.Nat.Pairing

/-!
# Internalizing conserved causal credit in pure rho

This module begins the operational bridge from the finite conserved-credit
learner to the original, undecorated rho calculus.  It does not erase the
linear resources.  Instead, each resource is represented by an ordinary rho
message at a closed quoted name, and a redemption is represented by a
three-communication protocol:

1. consume the causal receipt;
2. consume the neuron-addressed success signal;
3. consume the selected donor-credit quantum; then
4. reissue the empty receipt slot, empty signal slot, and reassigned credit.

The intermediate terms are the administrative reductions of the
internalizing interpreter.  A separate negative theorem exhibits the boundary
of the image-context discipline: a target context with the receipt channel can
consume the receipt before the protocol does.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTRhoInternalization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment
open WeightedGSLTBehavioralAdequacy
open WeightedGSLTConservedCredit
open WeightedGSLTCausalCredit

/-! ## Closed, pairwise distinguishable metabolic names -/

/-- The inert payload used by every resource message. -/
def rhoZero : Pattern := .apply "PZero" []

@[simp]
theorem semanticNormalize_rhoZero :
    semanticNormalizeProc rhoZero = rhoZero := rfl

@[simp]
theorem semanticSubstProc_rhoZero
    (depth : Nat) (replacement : Pattern) :
    semanticSubstProc depth replacement rhoZero = rhoZero := rfl

@[simp]
theorem binderSafeAt_rhoZero (depth : Nat) :
    binderSafeAt "NQuote" depth rhoZero = true := rfl

/-- A closed process family whose rho I/O count is exactly its index. -/
def markerProcess : Nat → Pattern
  | 0 => rhoZero
  | n + 1 =>
      .apply "POutput"
        [.apply "NQuote" [markerProcess n], rhoZero]

/-- Resource channel `n` is the quotation of the `n`th marker process. -/
def markerName (n : Nat) : Pattern :=
  .apply "NQuote" [markerProcess n]

private theorem semanticNormalize_marker : ∀ n,
    semanticNormalizeProc (markerProcess n) = markerProcess n ∧
      semanticNormalizeName (markerName n) = markerName n
  | 0 => by
      constructor <;> rfl
  | n + 1 => by
      obtain ⟨processIH, nameIH⟩ := semanticNormalize_marker n
      have nameIH' :
          semanticNormalizeName (.apply "NQuote" [markerProcess n]) =
            .apply "NQuote" [markerProcess n] := by
        simpa only [markerName] using nameIH
      have processNext :
          semanticNormalizeProc (markerProcess (n + 1)) =
            markerProcess (n + 1) := by
        simp [markerProcess, semanticNormalizeProc, nameIH']
      refine ⟨processNext, ?_⟩
      change Pattern.apply "NQuote"
          [semanticNormalizeProc (markerProcess (n + 1))] =
        Pattern.apply "NQuote" [markerProcess (n + 1)]
      rw [processNext]

@[simp]
theorem semanticNormalize_markerProcess (n : Nat) :
    semanticNormalizeProc (markerProcess n) = markerProcess n :=
  (semanticNormalize_marker n).1

@[simp]
theorem semanticNormalize_markerName (n : Nat) :
    semanticNormalizeName (markerName n) = markerName n :=
  (semanticNormalize_marker n).2

@[simp]
theorem semanticSubstName_markerName
    (depth : Nat) (replacement : Pattern) (n : Nat) :
    semanticSubstName depth replacement (markerName n) = markerName n := by
  simp only [semanticSubstName, semanticSubstNameMark]
  rw [semanticNormalize_markerName]
  rfl

theorem markerProcess_wellSorted : ∀ n,
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (markerProcess n)
  | 0 => .unit
  | n + 1 =>
      .output (.quote (markerProcess_wellSorted n)) .unit

theorem markerProcess_binderSafe : ∀ n,
    binderSafeAt "NQuote" 0 (markerProcess n) = true
  | 0 => rfl
  | n + 1 => by
      simp [markerProcess, rhoZero, binderSafeAt, binderSafeListAt,
        markerProcess_binderSafe n]

/-- Every metabolic name used below inhabits the closed name fiber of the
authored pure-rho calculus. -/
theorem markerName_closed (n : Nat) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoName (markerName n) := by
  apply (rhoClosedTermWellSorted_name_iff _).mpr
  exact ⟨.quote (markerProcess_wellSorted n), by
    simp [markerName, binderSafeAt,
      markerProcess_binderSafe n]⟩

@[simp]
theorem ioCount_markerProcess : ∀ n,
    Reduction.ioCount (markerProcess n) = n
  | 0 => by simp [markerProcess, rhoZero, Reduction.ioCount]
  | n + 1 => by
      simp [markerProcess, rhoZero, Reduction.ioCount,
        ioCount_markerProcess n, Nat.add_comm]

@[simp]
theorem ioCount_markerName (n : Nat) :
    Reduction.ioCount (markerName n) = n := by
  simp [markerName, Reduction.ioCount, ioCount_markerProcess]

/-- Channel codes are not merely syntactically different: structural
congruence cannot identify two different marker names. -/
theorem markerName_structural_injective {m n : Nat}
    (equivalent : StructuralCongruence (markerName m) (markerName n)) :
    m = n := by
  have counts := Reduction.ioCount_SC equivalent
  simpa using counts

/-! ## Resource-channel identity -/

/-- Every observable resource state receives its own metabolic channel.  Empty
slots and occupied slots are intentionally different channels: ordinary rho
COMM matching then enforces the finite-state guard without a meta-level test. -/
inductive CreditImageChannel (Synapse Neuron : Type*)
    (receiptSlots signalSlots creditBudget : Nat) where
  | receiptEmpty (slot : Fin receiptSlots)
  | receiptFull (slot : Fin receiptSlots) (synapse : Synapse)
  | signalEmpty (slot : Fin signalSlots)
  | signalFull (slot : Fin signalSlots) (neuron : Neuron)
  | creditAt (slot : Fin creditBudget)
      (account : CreditAccount Synapse Neuron)
deriving DecidableEq, Fintype

/-- Canonical finite enumeration of resource channels. -/
noncomputable def imageChannelCode
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (channel : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) : Nat :=
  (Fintype.equivFin _ channel).val

theorem imageChannelCode_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron] :
    Function.Injective
      (imageChannelCode :
        CreditImageChannel Synapse Neuron receiptSlots signalSlots creditBudget → Nat) := by
  intro left right equal
  exact (Fintype.equivFin _).injective (Fin.ext equal)

/-- The actual pure-rho name assigned to a finite resource channel. -/
noncomputable def imageChannelName
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (channel : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) : Pattern :=
  markerName (imageChannelCode channel)

/-- Distinct resource states cannot collapse under pure-rho structural
congruence. -/
theorem imageChannelName_structural_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    {left right : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget}
    (equivalent : StructuralCongruence
      (imageChannelName left) (imageChannelName right)) :
    left = right := by
  apply imageChannelCode_injective
  exact markerName_structural_injective equivalent

/-- Receipt-channel observation extracted from a causal-credit state. -/
def receiptChannel {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat}
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (slot : Fin receiptSlots) :
    CreditImageChannel Synapse Neuron receiptSlots signalSlots creditBudget :=
  match state.core.receipts slot with
  | none => .receiptEmpty slot
  | some synapse => .receiptFull slot synapse

/-- Signal-channel observation extracted from a causal-credit state. -/
def signalChannel {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat}
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (slot : Fin signalSlots) :
    CreditImageChannel Synapse Neuron receiptSlots signalSlots creditBudget :=
  match state.signals slot with
  | none => .signalEmpty slot
  | some neuron => .signalFull slot neuron

/-- Credit ownership is represented directly in the channel identity. -/
def creditChannel {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat}
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (slot : Fin creditBudget) :
    CreditImageChannel Synapse Neuron receiptSlots signalSlots creditBudget :=
  .creditAt slot (state.core.allocation slot)

theorem causalRedeem_source_receiptChannel
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    receiptChannel source receiptSlot = .receiptFull receiptSlot synapse := by
  simp [receiptChannel, causal_redeem_requires_receipt step]

theorem causalRedeem_source_signalChannel
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    signalChannel source signalSlot = .signalFull signalSlot (post synapse) := by
  simp [signalChannel, causal_redeem_requires_signal step]

theorem causalRedeem_target_receiptChannel
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    receiptChannel target receiptSlot = .receiptEmpty receiptSlot := by
  simp [receiptChannel, causal_redeem_consumes_receipt step]

theorem causalRedeem_target_signalChannel
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    signalChannel target signalSlot = .signalEmpty signalSlot := by
  simp [signalChannel, causal_redeem_consumes_signal step]

theorem causalRedeem_target_creditChannel
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    creditChannel target creditSlot = .creditAt creditSlot (.synapse synapse) := by
  rcases causal_redeem_data step with ⟨_signal, nextCore, coreStep, rfl⟩
  have allocation := redeem_reassigns_one_credit coreStep
  have atSlot := congrFun allocation creditSlot
  simpa [creditChannel, consumeSignal, replaceCore] using atSlot

theorem causalFire_channels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {synapse : Synapse}
    (step : CausalStep post source (.fire receiptSlot synapse) target) :
    receiptChannel source receiptSlot = .receiptEmpty receiptSlot ∧
      receiptChannel target receiptSlot = .receiptFull receiptSlot synapse := by
  change Option.map (replaceCore source)
    (if source.core.receipts receiptSlot = none then
      some (issueReceipt source.core receiptSlot synapse)
    else none) = some target at step
  split at step
  · rename_i empty
    simp only [Option.map_some, Option.some.injEq] at step
    subst target
    constructor
    · simp [receiptChannel, empty]
    · simp [receiptChannel, replaceCore, issueReceipt]
  · simp at step

theorem causalSignal_channels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {signalSlot : Fin signalSlots} {neuron : Neuron}
    (step : CausalStep post source (.signal signalSlot neuron) target) :
    signalChannel source signalSlot = .signalEmpty signalSlot ∧
      signalChannel target signalSlot = .signalFull signalSlot neuron := by
  change (if source.signals signalSlot = none then
      some (issueSignal source signalSlot neuron) else none) = some target at step
  split at step
  · rename_i empty
    simp only [Option.some.injEq] at step
    subst target
    constructor
    · simp [signalChannel, empty]
    · simp [signalChannel, issueSignal]
  · simp at step

theorem causalExpireReceipt_channels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots}
    (step : CausalStep post source (.expireReceipt receiptSlot) target) :
    source.core.receipts receiptSlot ≠ none ∧
      receiptChannel target receiptSlot = .receiptEmpty receiptSlot := by
  change Option.map (replaceCore source)
    (if source.core.receipts receiptSlot ≠ none then
      some (consumeReceipt source.core receiptSlot)
    else none) = some target at step
  split at step
  · rename_i occupied
    simp only [Option.map_some, Option.some.injEq] at step
    subst target
    exact ⟨occupied, by
      simp [receiptChannel, replaceCore, consumeReceipt]⟩
  · simp at step

theorem causalExpireSignal_channels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {signalSlot : Fin signalSlots}
    (step : CausalStep post source (.expireSignal signalSlot) target) :
    source.signals signalSlot ≠ none ∧
      signalChannel target signalSlot = .signalEmpty signalSlot := by
  change (if source.signals signalSlot ≠ none then
      some (consumeSignal source signalSlot) else none) = some target at step
  split at step
  · rename_i occupied
    simp only [Option.some.injEq] at step
    subst target
    exact ⟨occupied, by simp [signalChannel, consumeSignal]⟩
  · simp at step

/-! ## Recoverable image observables -/

/-- Credit owned by an account as read from the encoded credit-channel
family.  This is deliberately phrased through `creditChannel`, rather than by
reusing `accountCredits`, so that the next theorem is a genuine observation
transport result. -/
def imageAccountCredits {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (account : CreditAccount Synapse Neuron) : Nat :=
  (Finset.univ.filter fun slot =>
    creditChannel state slot = .creditAt slot account).card

theorem imageAccountCredits_eq_accountCredits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (account : CreditAccount Synapse Neuron) :
    imageAccountCredits state account = accountCredits state.core account := by
  simp [imageAccountCredits, accountCredits, creditChannel]

/-- The real-valued learned weight is recoverable exactly from the channel
image; the internalization loses no quantitative learning observable. -/
noncomputable def imageDerivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : Real)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) : Real :=
  base + quantum * imageAccountCredits state (.synapse synapse)

theorem imageDerivedWeight_eq_derivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : Real)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    imageDerivedWeight base quantum state synapse =
      derivedWeight base quantum state.core synapse := by
  simp [imageDerivedWeight, derivedWeight,
    imageAccountCredits_eq_accountCredits]

/-- Total credit reconstructed from the channel image. -/
def imageTotalCredits {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : Nat :=
  ∑ account : CreditAccount Synapse Neuron, imageAccountCredits state account

/-- Conservation transports through the image: decoding all credit-channel
owners always recovers exactly the fixed budget. -/
theorem imageTotalCredits_eq_budget
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    imageTotalCredits state = creditBudget := by
  simpa [imageTotalCredits, imageAccountCredits_eq_accountCredits,
    causalTotalCredits, totalCredits] using causalTotalCredits_eq_budget state

/-! ## Pure-rho resource messages and one-shot handlers -/

/-- One linear resource occurrence, represented by an ordinary rho output. -/
def resourceToken (channel : Nat) : Pattern :=
  commOut (markerName channel) rhoZero

/-- Syntactic resource tokens are injective in their numeric channel. -/
theorem resourceToken_injective : Function.Injective resourceToken := by
  intro left right equal
  have names : markerName left = markerName right := by
    simpa [resourceToken, commOut] using equal
  have counts := congrArg Reduction.ioCount names
  simpa using counts

/-- A one-use input on a resource channel.  The sent payload is intentionally
ignored; ownership is carried by the occurrence of the message itself. -/
def awaitResource (channel : Nat) (continuation : Pattern) : Pattern :=
  commIn (markerName channel) continuation

/-! ### Admission to the authored closed pure-rho carrier -/

/-- Closed pure-rho process predicate, retaining the authored sort and
quote-aware scope check rather than using raw `Pattern` closedness. -/
abbrev ClosedRhoProcess (process : Pattern) : Prop :=
  RhoClosedTermWellSorted
    Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc process

private theorem markerName_typed (channel : Nat) :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (markerName channel) :=
  ((rhoClosedTermWellSorted_name_iff _).mp (markerName_closed channel)).1

private theorem markerName_safe (channel : Nat) :
    binderSafeAt "NQuote" 0 (markerName channel) = true :=
  ((rhoClosedTermWellSorted_name_iff _).mp (markerName_closed channel)).2

theorem rhoZero_closed : ClosedRhoProcess rhoZero := by
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  exact ⟨.unit, rfl⟩

theorem resourceToken_closed (channel : Nat) :
    ClosedRhoProcess (resourceToken channel) := by
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  refine ⟨.output (markerName_typed channel) .unit, ?_⟩
  simp [resourceToken, commOut, binderSafeAt, binderSafeListAt,
    markerName_safe channel]

theorem awaitResource_closed (channel : Nat) {continuation : Pattern}
    (closed : ClosedRhoProcess continuation) :
    ClosedRhoProcess (awaitResource channel continuation) := by
  rcases (rhoClosedTermWellSorted_process_iff _).mp closed with
    ⟨continuationTyped, continuationSafe⟩
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  constructor
  · apply ProcWellSorted.input (markerName_typed channel)
    simpa using continuationTyped.weakenBoundRight
      [rhoReflectivePresentation.nameSort]
  · have safeUnderBinder :
        binderSafeAt "NQuote" 1 continuation = true :=
      binderSafeAt_mono "NQuote" continuationSafe (by omega)
    simp [awaitResource, commIn, binderSafeAt, binderSafeListAt,
      markerName_safe channel, safeUnderBinder]

theorem bag_closed (processes : List Pattern)
    (closed : ∀ process ∈ processes, ClosedRhoProcess process) :
    ClosedRhoProcess (bag processes) := by
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  constructor
  · apply ProcWellSorted.parallel
    rw [Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.procListWellSorted_iff_forall_mem]
    intro process membership
    exact ((rhoClosedTermWellSorted_process_iff _).mp
      (closed process membership)).1
  · simp only [bag, binderSafeAt]
    rw [binderSafeListAt_eq_true_iff]
    intro process membership
    exact ((rhoClosedTermWellSorted_process_iff _).mp
      (closed process membership)).2

/-- Flatten a nested bag at the head while preserving an arbitrary tail. -/
theorem bag_flatten_head (nested frame : List Pattern) :
    StructuralCongruence
      (bag (bag nested :: frame))
      (bag (nested ++ frame)) := by
  have moveNested : StructuralCongruence
      (bag (bag nested :: frame))
      (bag (frame ++ [bag nested])) := by
    apply bag_perm
    simpa using
      (List.perm_append_comm (l₁ := [bag nested]) (l₂ := frame))
  have flattenAtEnd : StructuralCongruence
      (bag (frame ++ [bag nested]))
      (bag (frame ++ nested)) := by
    simpa [bag] using StructuralCongruence.par_flatten frame nested
  have moveResult : StructuralCongruence
      (bag (frame ++ nested))
      (bag (nested ++ frame)) := by
    apply bag_perm
    exact List.perm_append_comm
  exact StructuralCongruence.trans _ _ _ moveNested
    (StructuralCongruence.trans _ _ _ flattenAtEnd moveResult)

@[simp]
theorem semanticSubstProc_resourceToken
    (depth : Nat) (replacement : Pattern) (channel : Nat) :
    semanticSubstProc depth replacement (resourceToken channel) =
      resourceToken channel := by
  unfold resourceToken commOut
  simp only [semanticSubstProc]
  rw [semanticSubstName_markerName, semanticSubstProc_rhoZero]

theorem semanticSubstProc_awaitResource
    (depth : Nat) (replacement : Pattern) (channel : Nat)
    (continuation : Pattern)
    (fixed : semanticSubstProc (depth + 1) replacement continuation =
      continuation) :
    semanticSubstProc depth replacement (awaitResource channel continuation) =
      awaitResource channel continuation := by
  unfold awaitResource commIn
  simp only [semanticSubstProc]
  rw [semanticSubstName_markerName, fixed]

/-- Substitution leaves the closed administrative protocol unchanged. -/
@[simp]
theorem semanticCommSubst_awaitResource
    (channel : Nat) (continuation : Pattern)
    (fixed : semanticSubstProc 1 (.apply "NQuote" [rhoZero]) continuation =
      continuation) :
    semanticCommSubst (awaitResource channel continuation) rhoZero =
      awaitResource channel continuation := by
  unfold semanticCommSubst
  rw [semanticNormalize_rhoZero]
  exact semanticSubstProc_awaitResource 0 _ channel continuation fixed

@[simp]
theorem semanticCommSubst_resourceToken (channel : Nat) :
    semanticCommSubst (resourceToken channel) rhoZero =
      resourceToken channel := by
  unfold semanticCommSubst
  rw [semanticNormalize_rhoZero]
  exact semanticSubstProc_resourceToken 0
    (.apply "NQuote" [rhoZero]) channel

/-! ### One-slot resource replacement -/

/-- The administrative process for every unary resource transition: acquire
the old state token and publish the new state token. -/
def replacementHandler (sourceChannel targetChannel : Nat) : Pattern :=
  awaitResource sourceChannel (resourceToken targetChannel)

def replacementSource (sourceChannel targetChannel : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([resourceToken sourceChannel,
    replacementHandler sourceChannel targetChannel] ++ frame)

def replacementTarget (targetChannel : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([resourceToken targetChannel] ++ frame)

theorem replacementHandler_closed (sourceChannel targetChannel : Nat) :
    ClosedRhoProcess (replacementHandler sourceChannel targetChannel) := by
  exact awaitResource_closed sourceChannel (resourceToken_closed targetChannel)

theorem replacementSource_closed (sourceChannel targetChannel : Nat)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (replacementSource sourceChannel targetChannel frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with (rfl | rfl) | membership
  · exact resourceToken_closed sourceChannel
  · exact replacementHandler_closed sourceChannel targetChannel
  · exact frameClosed process membership

theorem replacementTarget_closed (targetChannel : Nat)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (replacementTarget targetChannel frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with rfl | membership
  · exact resourceToken_closed targetChannel
  · exact frameClosed process membership

/-- Unary source actions compile to exactly one ordinary COMM step. -/
def replacement_internalizes (sourceChannel targetChannel : Nat)
    (frame : List Pattern) :
    ReducesN 1
      (replacementSource sourceChannel targetChannel frame)
      (replacementTarget targetChannel frame) := by
  have step := comm_at_head (markerName sourceChannel) rhoZero
    (resourceToken targetChannel) frame
  have resultFixed :
      commRes (resourceToken targetChannel) rhoZero =
        resourceToken targetChannel := by
    unfold commRes semanticCommSubst
    rw [semanticNormalize_rhoZero]
    exact semanticSubstProc_resourceToken 0
      (.apply "NQuote" [rhoZero]) targetChannel
  rw [resultFixed] at step
  exact .succ (by
    simpa [replacementSource, replacementTarget, replacementHandler,
      resourceToken, awaitResource] using step) (.zero _)

/-- The exact COMM record for a unary replacement.  It is the backward half
of the local correspondence: the consumed old token and handler are
recoverable from the record, rather than erased. -/
def replacementRecord (sourceChannel targetChannel : Nat)
    (frame : List Pattern) : CommRecord where
  channel := markerName sourceChannel
  inputBody := resourceToken targetChannel
  outputPayload := rhoZero
  rest := frame

theorem replacementRecord_preState
    (sourceChannel targetChannel : Nat) (frame : List Pattern) :
    (replacementRecord sourceChannel targetChannel frame).preState =
      replacementSource sourceChannel targetChannel frame := by
  rfl

theorem replacementRecord_postState
    (sourceChannel targetChannel : Nat) (frame : List Pattern) :
    (replacementRecord sourceChannel targetChannel frame).postState =
      replacementTarget targetChannel frame := by
  simp [replacementRecord, CommRecord.postState,
    replacementTarget]

/-- Logged unary internalization is a genuine COMM and exactly reconstructs
its compiler-generated source. -/
theorem replacementRecord_roundTrip
    (sourceChannel targetChannel : Nat) (frame : List Pattern) :
    Nonempty (Reduces
      (replacementSource sourceChannel targetChannel frame)
      (replacementTarget targetChannel frame)) ∧
    (replacementRecord sourceChannel targetChannel frame).preState =
      replacementSource sourceChannel targetChannel frame := by
  constructor
  · rw [← replacementRecord_preState,
      ← replacementRecord_postState]
    exact (replacementRecord sourceChannel targetChannel frame).forward
  · exact replacementRecord_preState sourceChannel targetChannel frame

/-- The executable one-step frontier of the closed, empty-context unary image
contains exactly its compiler-selected residual.  This is the smallest
reduction-reflection canary: no unlogged target branch exists when the
compiler supplies the whole context. -/
theorem replacementSource_empty_frontier
    (sourceChannel targetChannel : Nat) :
    Engine.reduceStep (replacementSource sourceChannel targetChannel []) 1 =
      [replacementTarget targetChannel []] := by
  simp [Engine.reduceStep, Engine.findAllComm, Engine.findInputPartner,
    Engine.matchOutput, Engine.matchInput, replacementSource,
    replacementTarget, replacementHandler, resourceToken, awaitResource,
    commOut, commIn, semanticCommSubst]
  constructor
  · simpa [resourceToken, commOut] using
      (semanticSubstProc_resourceToken 0
        (.apply "NQuote" [rhoZero]) targetChannel)
  · rfl

/-- Decode the canonical pre-state shape of a logged COMM record. -/
def decodeCommRecordPreState? : Pattern → Option CommRecord
  | .collection .hashBag
      (.apply "POutput" [outputChannel, payload] ::
       .apply "PInput" [inputChannel, .lambda none body] :: rest) none =>
      if outputChannel = inputChannel then
        some ⟨outputChannel, body, payload, rest⟩
      else none
  | _ => none

@[simp]
theorem decodeCommRecordPreState_preState (record : CommRecord) :
    decodeCommRecordPreState? record.preState = some record := by
  rcases record with ⟨channel, body, payload, rest⟩
  simp [CommRecord.preState, decodeCommRecordPreState?]

/-- Logged COMM pre-states are injective: the canonical output/input order
retains the channel, input body, output payload, and untouched frame. -/
theorem commRecord_preState_injective :
    Function.Injective CommRecord.preState := by
  intro left right equal
  have decoded := congrArg decodeCommRecordPreState? equal
  simpa using decoded

/-- Exact local reflection for logged unary COMM.  Any communication record
whose canonical pre-state is the compiler-generated unary source is the
compiler's record itself, so its post-state is the selected target. -/
theorem replacementRecord_reflects
    (sourceChannel targetChannel : Nat) (frame : List Pattern)
    (record : CommRecord)
    (preState : record.preState =
      replacementSource sourceChannel targetChannel frame) :
    record = replacementRecord sourceChannel targetChannel frame ∧
      record.postState = replacementTarget targetChannel frame := by
  have recordEqual : record =
      replacementRecord sourceChannel targetChannel frame := by
    apply commRecord_preState_injective
    rw [preState]
    exact replacementRecord_preState sourceChannel targetChannel frame |>.symm
  subst record
  exact ⟨rfl, replacementRecord_postState sourceChannel targetChannel frame⟩

/-- Capability-safe flat contexts for unary replacement contain only a
duplicate-free family of resource outputs, none on the private source
channel.  This is a concrete grammar, not an unrestricted target context. -/
def UnaryImageContext (sourceChannel : Nat) (frame : List Pattern) : Prop :=
  ∃ channels : List Nat,
    channels.Nodup ∧ sourceChannel ∉ channels ∧
      frame = channels.map resourceToken

/-- Every executable fuel-one reduct of a one-shot input in a capability-safe
image context is the compiler-selected residual.  This generic form also
covers the three nested stages of redemption. -/
theorem oneShotSource_imageContext_reflects
    (sourceChannel : Nat) (continuation : Pattern) (frame : List Pattern)
    (admitted : UnaryImageContext sourceChannel frame)
    (reduct : Pattern)
    (reduction : reduct ∈
      Engine.reduceStep
        (bag ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++ frame)) 1) :
    reduct = bag ([commRes continuation rhoZero] ++ frame) := by
  rcases admitted with ⟨channels, channelsNodup, fresh, rfl⟩
  change reduct ∈ Engine.reduceStep
    (.collection .hashBag ([resourceToken sourceChannel,
      awaitResource sourceChannel continuation] ++
        channels.map resourceToken) none) 1 at reduction
  rw [Engine.reduceStep_bag_one_eq_findAllComm] at reduction
  rcases Engine.findAllComm_spec reduction with
    ⟨outputIndex, outputBound, inputIndex, inputBound,
      outputName, payload, inputName, body,
      outputAt, inputAt, namesAgree, reductEqual⟩

  have inputMemErased :
      Pattern.apply "PInput" [inputName, .lambda none body] ∈
        ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            channels.map resourceToken).eraseIdx outputIndex := by
    rw [← inputAt]
    exact List.getElem_mem _
  have inputMem :
      Pattern.apply "PInput" [inputName, .lambda none body] ∈
        [resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            channels.map resourceToken := by
    simp only [List.mem_eraseIdx_iff_getElem] at inputMemErased
    rcases inputMemErased with ⟨index, indexBound, _, indexAt⟩
    rw [← indexAt]
    exact List.getElem_mem _
  have inputFields :
      inputName = markerName sourceChannel ∧
        body = continuation := by
    simpa [awaitResource, resourceToken,
      commIn, commOut] using inputMem
  rcases inputFields with ⟨inputNameEqual, bodyEqual⟩
  subst inputName
  subst body

  have outputMem :
      Pattern.apply "POutput" [outputName, payload] ∈
        [resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            channels.map resourceToken := by
    rw [← outputAt]
    exact List.getElem_mem _
  have outputCases :
      (outputName = markerName sourceChannel ∧ payload = rhoZero) ∨
      ∃ channel ∈ channels,
        markerName channel = outputName ∧ rhoZero = payload := by
    simpa [awaitResource, resourceToken,
      commIn, commOut] using outputMem
  have normalizedOutput :
      semanticNormalizeName outputName = markerName sourceChannel := by
    simpa using namesAgree
  have outputFields :
      outputName = markerName sourceChannel ∧ payload = rhoZero := by
    rcases outputCases with headOutput | frameOutput
    · exact headOutput
    · rcases frameOutput with
        ⟨channel, membership, channelName, payloadZero⟩
      have channelEqual : channel = sourceChannel := by
        have equalNames : markerName channel = markerName sourceChannel := by
          rw [← channelName] at normalizedOutput
          simpa using normalizedOutput
        have counts := congrArg Reduction.ioCount equalNames
        simpa using counts
      exact (fresh (channelEqual ▸ membership)).elim
  rcases outputFields with ⟨rfl, rfl⟩

  have mappedNodup : (channels.map resourceToken).Nodup :=
    channelsNodup.map resourceToken_injective
  have handlerNotMem :
      awaitResource sourceChannel continuation ∉
        channels.map resourceToken := by
    simp [awaitResource, resourceToken, commIn, commOut]
  have sourceNotMem :
      resourceToken sourceChannel ∉
        awaitResource sourceChannel continuation ::
          channels.map resourceToken := by
    simp only [List.mem_cons, not_or]
    constructor
    · simp [awaitResource, resourceToken, commIn, commOut]
    · simpa [List.mem_map, resourceToken_injective.eq_iff] using fresh
  have sourceNodup :
      ([resourceToken sourceChannel,
        awaitResource sourceChannel continuation] ++
          channels.map resourceToken).Nodup :=
    .cons sourceNotMem (.cons handlerNotMem mappedNodup)
  have outputIndexZero : outputIndex = 0 := by
    have getEqual :
        ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            channels.map resourceToken)[outputIndex] =
        ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            channels.map resourceToken)[0] := by
      simpa [resourceToken, commOut] using outputAt
    exact (sourceNodup.getElem_inj_iff
      (i := outputIndex) (hi := outputBound)
      (j := 0) (hj := by simp)).mp getEqual
  subst outputIndex

  have tailNodup :
      (awaitResource sourceChannel continuation ::
        channels.map resourceToken).Nodup := sourceNodup.tail
  have inputIndexZero : inputIndex = 0 := by
    have tailInputBound : inputIndex <
        (awaitResource sourceChannel continuation ::
          channels.map resourceToken).length := by
      simpa using inputBound
    have getEqual :
        (awaitResource sourceChannel continuation ::
          channels.map resourceToken)[inputIndex] =
        (awaitResource sourceChannel continuation ::
          channels.map resourceToken)[0] := by
      simpa [awaitResource, resourceToken,
        commIn, commOut] using inputAt
    exact (tailNodup.getElem_inj_iff
      (i := inputIndex) (hi := tailInputBound)
      (j := 0) (hj := by simp)).mp getEqual
  subst inputIndex
  rw [reductEqual]
  rfl

/-- Exact executable frontier characterization for the generic one-shot
protocol under the capability-safe image grammar. -/
theorem oneShotSource_imageContext_frontier_iff
    (sourceChannel : Nat) (continuation : Pattern) (frame : List Pattern)
    (admitted : UnaryImageContext sourceChannel frame)
    (reduct : Pattern) :
    reduct ∈ Engine.reduceStep
        (bag ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++ frame)) 1 ↔
      reduct = bag ([commRes continuation rhoZero] ++ frame) := by
  constructor
  · exact oneShotSource_imageContext_reflects
      sourceChannel continuation frame admitted reduct
  · intro equal
    subst reduct
    have member := Engine.comm_head_mem_reduceStep
      (nOut := markerName sourceChannel) (q := rhoZero)
      (nIn := markerName sourceChannel) (body := continuation)
      (rest := frame) rfl
    simpa [resourceToken, awaitResource, commOut, commIn, commRes] using member

/-- Exact one-step executable reflection for unary replacement under the
explicit capability-safe image-context grammar. -/
theorem replacementSource_imageContext_reflects
    (sourceChannel targetChannel : Nat) (frame : List Pattern)
    (admitted : UnaryImageContext sourceChannel frame)
    (reduct : Pattern)
    (reduction : reduct ∈
      Engine.reduceStep
        (replacementSource sourceChannel targetChannel frame) 1) :
    reduct = replacementTarget targetChannel frame := by
  have reflected := oneShotSource_imageContext_reflects
    sourceChannel (resourceToken targetChannel) frame admitted reduct
  have exactReduct := reflected (by
    simpa [replacementSource, replacementHandler] using reduction)
  simpa [replacementTarget, commRes, semanticCommSubst_resourceToken] using
    exactReduct

/-- Membership in the executable unary frontier is exactly equality with the
compiled target under the image-context discipline. -/
theorem replacementSource_imageContext_frontier_iff
    (sourceChannel targetChannel : Nat) (frame : List Pattern)
    (admitted : UnaryImageContext sourceChannel frame)
    (reduct : Pattern) :
    reduct ∈ Engine.reduceStep
        (replacementSource sourceChannel targetChannel frame) 1 ↔
      reduct = replacementTarget targetChannel frame := by
  constructor
  · exact replacementSource_imageContext_reflects
      sourceChannel targetChannel frame admitted reduct
  · intro equal
    subst reduct
    have member := Engine.comm_head_mem_reduceStep
      (nOut := markerName sourceChannel) (q := rhoZero)
      (nIn := markerName sourceChannel)
      (body := resourceToken targetChannel) (rest := frame) rfl
    rw [semanticCommSubst_resourceToken] at member
    simpa [replacementSource, replacementTarget, replacementHandler,
      resourceToken, awaitResource, commOut, commIn,
      semanticCommSubst] using member

/-! ### The dual input-only context used by fused control deployments -/

/-- Encode a channel/body pair as a one-shot rho input. -/
def awaitResourcePair (handler : Nat × Pattern) : Pattern :=
  awaitResource handler.1 handler.2

theorem awaitResourcePair_injective : Function.Injective awaitResourcePair := by
  intro left right equal
  have fields : markerName left.1 = markerName right.1 ∧ left.2 = right.2 := by
    simpa [awaitResourcePair, awaitResource, commIn] using equal
  have channels : left.1 = right.1 := by
    have counts := congrArg Reduction.ioCount fields.1
    simpa using counts
  exact Prod.ext channels fields.2

/-- A capability-safe dormant-handler context contains only a duplicate-free
list of one-shot inputs, none waiting on the active source channel. -/
def InputOnlyImageContext (sourceChannel : Nat)
    (frame : List Pattern) : Prop :=
  ∃ handlers : List (Nat × Pattern),
    handlers.Nodup ∧ sourceChannel ∉ handlers.map Prod.fst ∧
      frame = handlers.map awaitResourcePair

/-- Exact executable reflection for one active output/handler pair beside a
capability-safe input-only context.  Dormant handlers cannot communicate with
one another, and phase-channel freshness prevents them from stealing the
active token. -/
theorem oneShotSource_inputOnlyContext_frontier_iff
    (sourceChannel : Nat) (continuation : Pattern) (frame : List Pattern)
    (admitted : InputOnlyImageContext sourceChannel frame)
    (reduct : Pattern) :
    reduct ∈ Engine.reduceStep
        (bag ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++ frame)) 1 ↔
      reduct = bag ([commRes continuation rhoZero] ++ frame) := by
  rcases admitted with ⟨handlers, handlersNodup, fresh, rfl⟩
  constructor
  · intro reduction
    change reduct ∈ Engine.reduceStep
      (.collection .hashBag ([resourceToken sourceChannel,
        awaitResource sourceChannel continuation] ++
          handlers.map awaitResourcePair) none) 1 at reduction
    rw [Engine.reduceStep_bag_one_eq_findAllComm] at reduction
    rcases Engine.findAllComm_spec reduction with
      ⟨outputIndex, outputBound, inputIndex, inputBound,
        outputName, payload, inputName, body,
        outputAt, inputAt, namesAgree, reductEqual⟩

    have outputMem :
        Pattern.apply "POutput" [outputName, payload] ∈
          [resourceToken sourceChannel,
            awaitResource sourceChannel continuation] ++
              handlers.map awaitResourcePair := by
      rw [← outputAt]
      exact List.getElem_mem _
    have outputFields :
        outputName = markerName sourceChannel ∧ payload = rhoZero := by
      simpa [awaitResourcePair, awaitResource, resourceToken,
        commIn, commOut] using outputMem
    rcases outputFields with ⟨outputNameEqual, payloadEqual⟩
    subst outputName
    subst payload

    have inputMemErased :
        Pattern.apply "PInput" [inputName, .lambda none body] ∈
          ([resourceToken sourceChannel,
            awaitResource sourceChannel continuation] ++
              handlers.map awaitResourcePair).eraseIdx outputIndex := by
      rw [← inputAt]
      exact List.getElem_mem _
    have inputMem :
        Pattern.apply "PInput" [inputName, .lambda none body] ∈
          [resourceToken sourceChannel,
            awaitResource sourceChannel continuation] ++
              handlers.map awaitResourcePair := by
      simp only [List.mem_eraseIdx_iff_getElem] at inputMemErased
      rcases inputMemErased with ⟨index, indexBound, _, indexAt⟩
      rw [← indexAt]
      exact List.getElem_mem _
    have inputCases :
        (inputName = markerName sourceChannel ∧ body = continuation) ∨
        ∃ handler ∈ handlers,
          markerName handler.1 = inputName ∧ handler.2 = body := by
      simpa [awaitResourcePair, awaitResource, resourceToken,
        commIn, commOut] using inputMem
    have inputFields :
        inputName = markerName sourceChannel ∧ body = continuation := by
      rcases inputCases with active | dormant
      · exact active
      · rcases dormant with
          ⟨handler, membership, channelName, bodyName⟩
        have channelEqual : handler.1 = sourceChannel := by
          have equalNames : markerName handler.1 = markerName sourceChannel := by
            rw [← channelName] at namesAgree
            simpa using namesAgree.symm
          have counts := congrArg Reduction.ioCount equalNames
          simpa using counts
        have activeInMap : sourceChannel ∈ handlers.map Prod.fst := by
          rw [← channelEqual]
          exact List.mem_map.mpr ⟨handler, membership, rfl⟩
        exact (fresh activeInMap).elim
    rcases inputFields with ⟨inputNameEqual, bodyEqual⟩
    subst inputName
    subst body

    have mappedNodup : (handlers.map awaitResourcePair).Nodup :=
      handlersNodup.map awaitResourcePair_injective
    have handlerNotMem :
        awaitResource sourceChannel continuation ∉
          handlers.map awaitResourcePair := by
      intro membership
      rw [List.mem_map] at membership
      rcases membership with ⟨handler, handlerMem, handlerEqual⟩
      have pairEqual : handler = (sourceChannel, continuation) :=
        awaitResourcePair_injective (by
          simpa [awaitResourcePair] using handlerEqual)
      have handlerFirst : handler.1 = sourceChannel :=
        congrArg Prod.fst pairEqual
      have activeInMap : sourceChannel ∈ handlers.map Prod.fst := by
        exact List.mem_map.mpr ⟨handler, handlerMem, handlerFirst⟩
      exact fresh activeInMap
    have sourceNotMem :
        resourceToken sourceChannel ∉
          awaitResource sourceChannel continuation ::
            handlers.map awaitResourcePair := by
      simp [awaitResourcePair, awaitResource, resourceToken, commIn, commOut]
    have sourceNodup :
        ([resourceToken sourceChannel,
          awaitResource sourceChannel continuation] ++
            handlers.map awaitResourcePair).Nodup :=
      .cons sourceNotMem (.cons handlerNotMem mappedNodup)
    have outputIndexZero : outputIndex = 0 := by
      have getEqual :
          ([resourceToken sourceChannel,
            awaitResource sourceChannel continuation] ++
              handlers.map awaitResourcePair)[outputIndex] =
          ([resourceToken sourceChannel,
            awaitResource sourceChannel continuation] ++
              handlers.map awaitResourcePair)[0] := by
        simpa [resourceToken, commOut] using outputAt
      exact (sourceNodup.getElem_inj_iff
        (i := outputIndex) (hi := outputBound)
        (j := 0) (hj := by simp)).mp getEqual
    subst outputIndex
    have tailNodup :
        (awaitResource sourceChannel continuation ::
          handlers.map awaitResourcePair).Nodup := sourceNodup.tail
    have inputIndexZero : inputIndex = 0 := by
      have tailInputBound : inputIndex <
          (awaitResource sourceChannel continuation ::
            handlers.map awaitResourcePair).length := by
        simpa using inputBound
      have getEqual :
          (awaitResource sourceChannel continuation ::
            handlers.map awaitResourcePair)[inputIndex] =
          (awaitResource sourceChannel continuation ::
            handlers.map awaitResourcePair)[0] := by
        simpa [awaitResource, resourceToken, commIn, commOut] using inputAt
      exact (tailNodup.getElem_inj_iff
        (i := inputIndex) (hi := tailInputBound)
        (j := 0) (hj := by simp)).mp getEqual
    subst inputIndex
    rw [reductEqual]
    rfl
  · intro equal
    subst reduct
    have member := Engine.comm_head_mem_reduceStep
      (nOut := markerName sourceChannel) (q := rhoZero)
      (nIn := markerName sourceChannel) (body := continuation)
      (rest := handlers.map awaitResourcePair) rfl
    simpa [resourceToken, awaitResource, commOut, commIn, commRes] using member

/-- Reissue the three resources produced by a successful redemption. -/
def redemptionProducts
    (emptyReceipt emptySignal targetCredit : Nat) : Pattern :=
  bag [resourceToken emptyReceipt, resourceToken emptySignal,
    resourceToken targetCredit]

/-- The image of a redemption action.  The nesting makes resource acquisition
order explicit. -/
def redemptionHandler
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat) : Pattern :=
  awaitResource receipt
    (awaitResource signal
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)))

/-- A complete source image for one redemption, with an arbitrary inert frame.
The protocol input and all three resource messages are ordinary rho terms. -/
def redemptionSource
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([resourceToken receipt,
      redemptionHandler receipt signal donorCredit
        emptyReceipt emptySignal targetCredit,
      resourceToken signal,
      resourceToken donorCredit] ++ frame)

/-- The corresponding target image after all administrative reductions. -/
def redemptionTarget
    (emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([resourceToken emptyReceipt, resourceToken emptySignal,
    resourceToken targetCredit] ++ frame)

/-! ### Closed-carrier admission for the complete protocol -/

/-- Every successor resource family is a closed pure-rho process. -/
theorem redemptionProducts_closed
    (emptyReceipt emptySignal targetCredit : Nat) :
    ClosedRhoProcess
      (redemptionProducts emptyReceipt emptySignal targetCredit) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact resourceToken_closed emptyReceipt
  · exact resourceToken_closed emptySignal
  · exact resourceToken_closed targetCredit

/-- The nested one-shot interpreter is itself an ordinary closed rho
process. -/
theorem redemptionHandler_closed
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat) :
    ClosedRhoProcess
      (redemptionHandler receipt signal donorCredit
        emptyReceipt emptySignal targetCredit) := by
  apply awaitResource_closed
  apply awaitResource_closed
  apply awaitResource_closed
  exact redemptionProducts_closed emptyReceipt emptySignal targetCredit

/-- The complete source image is admitted by the authored pure-rho carrier
whenever its untouched context is. -/
theorem redemptionSource_closed
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess
      (redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with
    (rfl | rfl | rfl | rfl) | membership
  · exact resourceToken_closed receipt
  · exact redemptionHandler_closed receipt signal donorCredit
      emptyReceipt emptySignal targetCredit
  · exact resourceToken_closed signal
  · exact resourceToken_closed donorCredit
  · exact frameClosed process membership

/-- The complete target image is admitted by the authored pure-rho carrier
under the same frame condition. -/
theorem redemptionTarget_closed
    (emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with (rfl | rfl | rfl) | membership
  · exact resourceToken_closed emptyReceipt
  · exact resourceToken_closed emptySignal
  · exact resourceToken_closed targetCredit
  · exact frameClosed process membership

private theorem subst_redemptionProducts
    (emptyReceipt emptySignal targetCredit : Nat) (depth : Nat) :
    semanticSubstProc depth (.apply "NQuote" [rhoZero])
      (redemptionProducts emptyReceipt emptySignal targetCredit) =
        redemptionProducts emptyReceipt emptySignal targetCredit := by
  unfold redemptionProducts bag
  simp only [semanticSubstProc, semanticSubstProcList]
  rw [semanticSubstProc_resourceToken,
    semanticSubstProc_resourceToken,
    semanticSubstProc_resourceToken]

private theorem subst_finalAwait
    (donorCredit emptyReceipt emptySignal targetCredit : Nat) (depth : Nat) :
    semanticSubstProc depth (.apply "NQuote" [rhoZero])
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)) =
      awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit) := by
  apply semanticSubstProc_awaitResource
  exact subst_redemptionProducts emptyReceipt emptySignal targetCredit
    (depth + 1)

private theorem subst_signalAwait
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (depth : Nat) :
    semanticSubstProc depth (.apply "NQuote" [rhoZero])
      (awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit))) =
      awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)) := by
  apply semanticSubstProc_awaitResource
  exact subst_finalAwait donorCredit emptyReceipt emptySignal targetCredit
    (depth + 1)

private theorem commRes_redemptionHandler
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat) :
    commRes
      (awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)))
      rhoZero =
      awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)) := by
  unfold commRes
  apply semanticCommSubst_awaitResource
  exact subst_finalAwait donorCredit emptyReceipt emptySignal targetCredit 1

private theorem commRes_finalAwait
    (donorCredit emptyReceipt emptySignal targetCredit : Nat) :
    commRes
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit))
      rhoZero =
      awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit) := by
  unfold commRes
  apply semanticCommSubst_awaitResource
  exact subst_redemptionProducts emptyReceipt emptySignal targetCredit 1

private theorem commRes_redemptionProducts
    (emptyReceipt emptySignal targetCredit : Nat) :
    commRes (redemptionProducts emptyReceipt emptySignal targetCredit) rhoZero =
      redemptionProducts emptyReceipt emptySignal targetCredit := by
  unfold commRes semanticCommSubst
  rw [semanticNormalize_rhoZero]
  exact subst_redemptionProducts emptyReceipt emptySignal targetCredit 0

/-! ### Logged reduction reflection for the canonical redemption stages -/

/-- Canonical target syntax after the receipt communication. -/
def redemptionAfterReceipt
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([awaitResource signal
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)),
    resourceToken signal, resourceToken donorCredit] ++ frame)

/-- Canonical target syntax after the signal communication. -/
def redemptionAfterSignal
    (donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([awaitResource donorCredit
      (redemptionProducts emptyReceipt emptySignal targetCredit),
    resourceToken donorCredit] ++ frame)

/-- Logged receipt-acquisition record emitted by the redemption compiler. -/
def redemptionReceiptRecord
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : CommRecord where
  channel := markerName receipt
  inputBody := awaitResource signal
    (awaitResource donorCredit
      (redemptionProducts emptyReceipt emptySignal targetCredit))
  outputPayload := rhoZero
  rest := [resourceToken signal, resourceToken donorCredit] ++ frame

/-- Logged signal-acquisition record in output-first canonical order. -/
def redemptionSignalRecord
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : CommRecord where
  channel := markerName signal
  inputBody := awaitResource donorCredit
    (redemptionProducts emptyReceipt emptySignal targetCredit)
  outputPayload := rhoZero
  rest := [resourceToken donorCredit] ++ frame

/-- Logged donor-credit acquisition record in output-first canonical order. -/
def redemptionCreditRecord
    (donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) : CommRecord where
  channel := markerName donorCredit
  inputBody := redemptionProducts emptyReceipt emptySignal targetCredit
  outputPayload := rhoZero
  rest := frame

@[simp]
theorem redemptionReceiptRecord_preState
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    (redemptionReceiptRecord receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame).preState =
      redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame := rfl

@[simp]
theorem redemptionReceiptRecord_postState
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    (redemptionReceiptRecord receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame).postState =
      redemptionAfterReceipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame := by
  change bag ([commRes
      (awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)))
      rhoZero, resourceToken signal, resourceToken donorCredit] ++ frame) =
    redemptionAfterReceipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame
  rw [commRes_redemptionHandler]
  rfl

@[simp]
theorem redemptionSignalRecord_postState
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    (redemptionSignalRecord signal donorCredit
      emptyReceipt emptySignal targetCredit frame).postState =
      redemptionAfterSignal donorCredit
        emptyReceipt emptySignal targetCredit frame := by
  change bag ([commRes
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit))
      rhoZero, resourceToken donorCredit] ++ frame) =
    redemptionAfterSignal donorCredit
      emptyReceipt emptySignal targetCredit frame
  rw [commRes_finalAwait]
  rfl

/-- The first residual is structurally the canonical pre-state of the signal
record; the difference is only output/input order in the parallel bag. -/
theorem redemptionReceipt_to_signalRecord
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    StructuralCongruence
      (redemptionReceiptRecord receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionSignalRecord signal donorCredit
        emptyReceipt emptySignal targetCredit frame).preState := by
  rw [redemptionReceiptRecord_postState]
  apply bag_perm
  exact (List.Perm.swap
    (awaitResource signal
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)))
    (resourceToken signal) (resourceToken donorCredit :: frame)).symm

/-- The second residual is structurally the canonical pre-state of the donor
credit record. -/
theorem redemptionSignal_to_creditRecord
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    StructuralCongruence
      (redemptionSignalRecord signal donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionCreditRecord donorCredit
        emptyReceipt emptySignal targetCredit frame).preState := by
  rw [redemptionSignalRecord_postState]
  change StructuralCongruence
    (bag ([awaitResource donorCredit
      (redemptionProducts emptyReceipt emptySignal targetCredit),
      resourceToken donorCredit] ++ frame))
    (bag ([resourceToken donorCredit,
      awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)] ++ frame))
  apply bag_perm
  simpa using (List.Perm.swap
    (awaitResource donorCredit
      (redemptionProducts emptyReceipt emptySignal targetCredit))
    (resourceToken donorCredit) frame).symm

/-- Publishing the nested product bag is structurally the flat redemption
target. -/
theorem redemptionCreditRecord_postState_structural
    (donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    StructuralCongruence
      (redemptionCreditRecord donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
  change StructuralCongruence
    (bag (commRes
      (redemptionProducts emptyReceipt emptySignal targetCredit) rhoZero :: frame))
    (redemptionTarget emptyReceipt emptySignal targetCredit frame)
  rw [commRes_redemptionProducts]
  exact bag_flatten_head
    [resourceToken emptyReceipt, resourceToken emptySignal,
      resourceToken targetCredit] frame

/-- A canonical logged receipt step reflects uniquely to the compiler's first
redemption record. -/
theorem redemptionReceiptRecord_reflects
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) (record : CommRecord)
    (preState : record.preState =
      redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame) :
    record = redemptionReceiptRecord receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame := by
  apply commRecord_preState_injective
  rw [preState]
  exact (redemptionReceiptRecord_preState receipt signal donorCredit
    emptyReceipt emptySignal targetCredit frame).symm

/-- Canonical logged signal acquisition reflects uniquely to the compiler's
second redemption record. -/
theorem redemptionSignalRecord_reflects
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) (record : CommRecord)
    (preState : record.preState =
      (redemptionSignalRecord signal donorCredit
        emptyReceipt emptySignal targetCredit frame).preState) :
    record = redemptionSignalRecord signal donorCredit
      emptyReceipt emptySignal targetCredit frame :=
  commRecord_preState_injective preState

/-- Canonical logged donor acquisition reflects uniquely to the compiler's
third redemption record. -/
theorem redemptionCreditRecord_reflects
    (donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) (record : CommRecord)
    (preState : record.preState =
      (redemptionCreditRecord donorCredit
        emptyReceipt emptySignal targetCredit frame).preState) :
    record = redemptionCreditRecord donorCredit
      emptyReceipt emptySignal targetCredit frame :=
  commRecord_preState_injective preState

/-- Capability-safe redemption contexts contain a duplicate-free resource
frame whose channels are disjoint from the receipt, signal, and donor channels
consumed by the three-stage protocol. -/
def RedemptionImageContext
    (receipt signal donorCredit : Nat) (frame : List Pattern) : Prop :=
  ∃ channels : List Nat,
    (receipt :: signal :: donorCredit :: channels).Nodup ∧
      frame = channels.map resourceToken

theorem redemptionImageContext_receiptStage
    (receipt signal donorCredit : Nat) (frame : List Pattern)
    (admitted : RedemptionImageContext receipt signal donorCredit frame) :
    UnaryImageContext receipt
      ([resourceToken signal, resourceToken donorCredit] ++ frame) := by
  rcases admitted with ⟨channels, nodup, rfl⟩
  exact ⟨signal :: donorCredit :: channels, nodup.tail, nodup.notMem, rfl⟩

theorem redemptionImageContext_signalStage
    (receipt signal donorCredit : Nat) (frame : List Pattern)
    (admitted : RedemptionImageContext receipt signal donorCredit frame) :
    UnaryImageContext signal ([resourceToken donorCredit] ++ frame) := by
  rcases admitted with ⟨channels, nodup, rfl⟩
  exact ⟨donorCredit :: channels, nodup.tail.tail,
    nodup.tail.notMem, rfl⟩

theorem redemptionImageContext_creditStage
    (receipt signal donorCredit : Nat) (frame : List Pattern)
    (admitted : RedemptionImageContext receipt signal donorCredit frame) :
    UnaryImageContext donorCredit frame := by
  rcases admitted with ⟨channels, nodup, rfl⟩
  exact ⟨channels, nodup.tail.tail.tail,
    nodup.tail.tail.notMem, rfl⟩

/-- **Exact canonical image-context frontiers.**  At each output-first stage
of a redemption, the executable one-step frontier contains precisely the
logged compiler residual.  This is reduction reflection for the explicit
duplicate-free resource-context grammar, not for arbitrary rho contexts. -/
theorem redemption_imageContext_frontiers_iff
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern)
    (admitted : RedemptionImageContext receipt signal donorCredit frame) :
    (∀ reduct : Pattern,
      reduct ∈ Engine.reduceStep
        (redemptionReceiptRecord receipt signal donorCredit
          emptyReceipt emptySignal targetCredit frame).preState 1 ↔
      reduct =
        (redemptionReceiptRecord receipt signal donorCredit
          emptyReceipt emptySignal targetCredit frame).postState) ∧
    (∀ reduct : Pattern,
      reduct ∈ Engine.reduceStep
        (redemptionSignalRecord signal donorCredit
          emptyReceipt emptySignal targetCredit frame).preState 1 ↔
      reduct =
        (redemptionSignalRecord signal donorCredit
          emptyReceipt emptySignal targetCredit frame).postState) ∧
    (∀ reduct : Pattern,
      reduct ∈ Engine.reduceStep
        (redemptionCreditRecord donorCredit
          emptyReceipt emptySignal targetCredit frame).preState 1 ↔
      reduct =
        (redemptionCreditRecord donorCredit
          emptyReceipt emptySignal targetCredit frame).postState) := by
  refine ⟨?_, ?_, ?_⟩
  · intro reduct
    have exactFrontier := oneShotSource_imageContext_frontier_iff
      receipt
      (awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)))
      ([resourceToken signal, resourceToken donorCredit] ++ frame)
      (redemptionImageContext_receiptStage receipt signal donorCredit
        frame admitted) reduct
    simpa [redemptionReceiptRecord, CommRecord.preState,
      CommRecord.postState, resourceToken, awaitResource,
      commOut, commIn, commRes] using exactFrontier
  · intro reduct
    have exactFrontier := oneShotSource_imageContext_frontier_iff
      signal
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit))
      ([resourceToken donorCredit] ++ frame)
      (redemptionImageContext_signalStage receipt signal donorCredit
        frame admitted) reduct
    simpa [redemptionSignalRecord, CommRecord.preState,
      CommRecord.postState, resourceToken, awaitResource,
      commOut, commIn, commRes] using exactFrontier
  · intro reduct
    have exactFrontier := oneShotSource_imageContext_frontier_iff
      donorCredit
      (redemptionProducts emptyReceipt emptySignal targetCredit)
      frame
      (redemptionImageContext_creditStage receipt signal donorCredit
        frame admitted) reduct
    simpa [redemptionCreditRecord, CommRecord.preState,
      CommRecord.postState, resourceToken, awaitResource,
      commOut, commIn, commRes] using exactFrontier

/-- **Canonical three-COMM reflection.**  Each stage of a logged redemption
has one reconstructible compiler record; adjacent stages compose modulo only
parallel permutation, and the final nested products flatten to the declared
target. -/
theorem redemption_logged_reflection
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    (∀ record : CommRecord,
      record.preState = redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame →
      record = redemptionReceiptRecord receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame) ∧
    StructuralCongruence
      (redemptionReceiptRecord receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionSignalRecord signal donorCredit
        emptyReceipt emptySignal targetCredit frame).preState ∧
    StructuralCongruence
      (redemptionSignalRecord signal donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionCreditRecord donorCredit
        emptyReceipt emptySignal targetCredit frame).preState ∧
    StructuralCongruence
      (redemptionCreditRecord donorCredit
        emptyReceipt emptySignal targetCredit frame).postState
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
  exact ⟨redemptionReceiptRecord_reflects receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame,
    redemptionReceipt_to_signalRecord receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame,
    redemptionSignal_to_creditRecord signal donorCredit
      emptyReceipt emptySignal targetCredit frame,
    redemptionCreditRecord_postState_structural donorCredit
      emptyReceipt emptySignal targetCredit frame⟩

/-! ## The three administrative COMM steps -/

/-- The first administrative step consumes the receipt occurrence. -/
def redemption_receipt_step
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    Reduces
      (redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame)
      (bag ([awaitResource signal
          (awaitResource donorCredit
            (redemptionProducts emptyReceipt emptySignal targetCredit)),
        resourceToken signal, resourceToken donorCredit] ++ frame)) := by
  have step := comm_at_head (markerName receipt) rhoZero
    (awaitResource signal
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit)))
    ([resourceToken signal, resourceToken donorCredit] ++ frame)
  rw [commRes_redemptionHandler signal donorCredit
    emptyReceipt emptySignal targetCredit] at step
  simpa [redemptionSource, redemptionHandler, resourceToken, awaitResource,
    List.cons_append] using step

/-- The second administrative step consumes the success-signal occurrence. -/
def redemption_signal_step
    (signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    Reduces
      (bag ([awaitResource signal
          (awaitResource donorCredit
            (redemptionProducts emptyReceipt emptySignal targetCredit)),
        resourceToken signal, resourceToken donorCredit] ++ frame))
      (bag ([awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit),
        resourceToken donorCredit] ++ frame)) := by
  have sourcePerm : StructuralCongruence
      (bag ([awaitResource signal
          (awaitResource donorCredit
            (redemptionProducts emptyReceipt emptySignal targetCredit)),
        resourceToken signal, resourceToken donorCredit] ++ frame))
      (bag ([resourceToken signal,
        awaitResource signal
          (awaitResource donorCredit
            (redemptionProducts emptyReceipt emptySignal targetCredit)),
        resourceToken donorCredit] ++ frame)) := by
    apply bag_perm
    exact (List.Perm.swap
      (awaitResource signal
        (awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)))
      (resourceToken signal) (resourceToken donorCredit :: frame)).symm
  have step := comm_anywhere sourcePerm
  rw [commRes_finalAwait donorCredit emptyReceipt emptySignal targetCredit] at step
  simpa [resourceToken, awaitResource] using step

/-- The final administrative step consumes the donor quantum and publishes
the reassigned resources. -/
def redemption_credit_step
    (donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    Reduces
      (bag ([awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit),
        resourceToken donorCredit] ++ frame))
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
  have sourcePerm : StructuralCongruence
      (bag ([awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit),
        resourceToken donorCredit] ++ frame))
      (bag ([resourceToken donorCredit,
        awaitResource donorCredit
          (redemptionProducts emptyReceipt emptySignal targetCredit)] ++ frame)) := by
    apply bag_perm
    simpa using (List.Perm.swap
      (awaitResource donorCredit
        (redemptionProducts emptyReceipt emptySignal targetCredit))
      (resourceToken donorCredit) frame).symm
  have step := comm_anywhere sourcePerm
  have flatten : StructuralCongruence
      (bag (redemptionProducts emptyReceipt emptySignal targetCredit :: frame))
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
    let products := [resourceToken emptyReceipt, resourceToken emptySignal,
      resourceToken targetCredit]
    have moveNested : StructuralCongruence
        (bag (bag products :: frame))
        (bag (frame ++ [bag products])) := by
      apply bag_perm
      simpa using
        (List.perm_append_comm (l₁ := [bag products]) (l₂ := frame))
    have flattenAtEnd : StructuralCongruence
        (bag (frame ++ [bag products])) (bag (frame ++ products)) := by
      simpa [bag] using StructuralCongruence.par_flatten frame products
    have moveProducts : StructuralCongruence
        (bag (frame ++ products)) (bag (products ++ frame)) := by
      apply bag_perm
      exact List.perm_append_comm
    simpa [redemptionProducts, redemptionTarget, products] using
      StructuralCongruence.trans _ _ _ moveNested
        (StructuralCongruence.trans _ _ _ flattenAtEnd moveProducts)
  exact Reduces.equiv (StructuralCongruence.refl _) (by
    simpa [resourceToken, awaitResource, commRes_redemptionProducts] using step)
    flatten

/-- **Greg-style internalisation, local operational core.**  One atomic
conserved-credit redemption is simulated by exactly three ordinary pure-rho
COMM reductions, with every untouched process in `frame` preserved. -/
noncomputable def redemption_internalizes
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    ReducesN 3
      (redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit frame)
      (redemptionTarget emptyReceipt emptySignal targetCredit frame) := by
  exact .succ
    (redemption_receipt_step receipt signal donorCredit
      emptyReceipt emptySignal targetCredit frame)
    (.succ
      (redemption_signal_step signal donorCredit
        emptyReceipt emptySignal targetCredit frame)
      (.succ
        (redemption_credit_step donorCredit
          emptyReceipt emptySignal targetCredit frame)
        (.zero _)))

/-! ## State-indexed operational correspondence -/

/-- The concrete pure-rho source image of a valid causal redemption.  The
handler is specialized to the six resource observations at the source and
target states; no decorated constructor survives in the generated term. -/
noncomputable def causalRedemptionSource
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (frame : List Pattern) : Pattern :=
  redemptionSource
    (imageChannelCode (receiptChannel source receiptSlot))
    (imageChannelCode (signalChannel source signalSlot))
    (imageChannelCode (creditChannel source creditSlot))
    (imageChannelCode (receiptChannel target receiptSlot))
    (imageChannelCode (signalChannel target signalSlot))
    (imageChannelCode (creditChannel target creditSlot)) frame

/-- The concrete target image carries the three post-redemption resource
observations and preserves the same untouched frame. -/
noncomputable def causalRedemptionTarget
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (frame : List Pattern) : Pattern :=
  redemptionTarget
    (imageChannelCode (receiptChannel target receiptSlot))
    (imageChannelCode (signalChannel target signalSlot))
    (imageChannelCode (creditChannel target creditSlot)) frame

/-- A source-level causal redemption is simulated by exactly three COMM
steps in the original rho calculus.  The conjuncts make the correspondence
semantic rather than a mere instantiation of an untyped protocol: they record
the two consumed guards and all three resource observations published at the
target. -/
theorem causalRedemption_internalizes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target)
    (frame : List Pattern) :
    receiptChannel source receiptSlot = .receiptFull receiptSlot synapse ∧
      signalChannel source signalSlot = .signalFull signalSlot (post synapse) ∧
      Nonempty (ReducesN 3
        (causalRedemptionSource source target
          receiptSlot signalSlot creditSlot frame)
        (causalRedemptionTarget target
          receiptSlot signalSlot creditSlot frame)) ∧
      receiptChannel target receiptSlot = .receiptEmpty receiptSlot ∧
      signalChannel target signalSlot = .signalEmpty signalSlot ∧
      creditChannel target creditSlot =
        .creditAt creditSlot (.synapse synapse) := by
  refine ⟨causalRedeem_source_receiptChannel step,
    causalRedeem_source_signalChannel step, ?_,
    causalRedeem_target_receiptChannel step,
    causalRedeem_target_signalChannel step,
    causalRedeem_target_creditChannel step⟩
  exact ⟨redemption_internalizes
    (imageChannelCode (receiptChannel source receiptSlot))
    (imageChannelCode (signalChannel source signalSlot))
    (imageChannelCode (creditChannel source creditSlot))
    (imageChannelCode (receiptChannel target receiptSlot))
    (imageChannelCode (signalChannel target signalSlot))
    (imageChannelCode (creditChannel target creditSlot)) frame⟩

theorem causalRedemptionSource_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (causalRedemptionSource source target
      receiptSlot signalSlot creditSlot frame) := by
  apply redemptionSource_closed
  exact frameClosed

theorem causalRedemptionTarget_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (creditSlot : Fin creditBudget) (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (causalRedemptionTarget target
      receiptSlot signalSlot creditSlot frame) := by
  apply redemptionTarget_closed
  exact frameClosed

/-! ### The complete causal action compiler -/

/-- Unary actions use one administrative COMM; redemption consumes its three
guards in three. -/
def causalActionSteps {Synapse Neuron : Type*}
    {receiptSlots signalSlots creditBudget : Nat} :
    CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat
  | .redeem _ _ _ _ => 3
  | _ => 1

/-- Compilation of every causal-credit action into the original rho calculus.
The compiler reads only the source state and the action.  Its published
resource names are determined by the action, not supplied by the target. -/
noncomputable def causalActionSource
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (frame : List Pattern) : Pattern :=
  let code : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat := imageChannelCode
  match action with
  | .fire receiptSlot synapse =>
      replacementSource
        (code (receiptChannel source receiptSlot))
        (code (.receiptFull receiptSlot synapse)) frame
  | .signal signalSlot neuron =>
      replacementSource
        (code (signalChannel source signalSlot))
        (code (.signalFull signalSlot neuron)) frame
  | .redeem receiptSlot signalSlot creditSlot synapse =>
      redemptionSource
        (code (receiptChannel source receiptSlot))
        (code (signalChannel source signalSlot))
        (code (creditChannel source creditSlot))
        (code (.receiptEmpty receiptSlot))
        (code (.signalEmpty signalSlot))
        (code (.creditAt creditSlot (.synapse synapse))) frame
  | .expireReceipt receiptSlot =>
      replacementSource
        (code (receiptChannel source receiptSlot))
        (code (.receiptEmpty receiptSlot)) frame
  | .expireSignal signalSlot =>
      replacementSource
        (code (signalChannel source signalSlot))
        (code (.signalEmpty signalSlot)) frame

/-- The selected target-state observation after an action; the untouched
state is represented by the preserved frame. -/
noncomputable def causalActionTarget
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (frame : List Pattern) : Pattern :=
  let code : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat := imageChannelCode
  match action with
  | .fire receiptSlot _ =>
      replacementTarget
        (code (receiptChannel target receiptSlot)) frame
  | .signal signalSlot _ =>
      replacementTarget
        (code (signalChannel target signalSlot)) frame
  | .redeem receiptSlot signalSlot creditSlot _ =>
      redemptionTarget
        (code (receiptChannel target receiptSlot))
        (code (signalChannel target signalSlot))
        (code (creditChannel target creditSlot)) frame
  | .expireReceipt receiptSlot =>
      replacementTarget
        (code (receiptChannel target receiptSlot)) frame
  | .expireSignal signalSlot =>
      replacementTarget
        (code (signalChannel target signalSlot)) frame

/-- **Forward operational correspondence for the complete action language.**
Every valid causal-credit action compiles to its exact target observation in
the undecorated rho calculus, in one COMM for unary resource replacement and
three COMMs for redemption. -/
theorem causalAction_internalizes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (step : CausalStep post source action target)
    (frame : List Pattern) :
    Nonempty (ReducesN (causalActionSteps action)
      (causalActionSource source action frame)
      (causalActionTarget target action frame)) := by
  let code : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat := imageChannelCode
  cases action with
  | fire receiptSlot synapse =>
      have observations := causalFire_channels step
      simp only [causalActionSteps, causalActionSource, causalActionTarget]
      rw [observations.2]
      exact ⟨replacement_internalizes
        (code (receiptChannel source receiptSlot))
        (code (.receiptFull receiptSlot synapse)) frame⟩
  | signal signalSlot neuron =>
      have observations := causalSignal_channels step
      simp only [causalActionSteps, causalActionSource, causalActionTarget]
      rw [observations.2]
      exact ⟨replacement_internalizes
        (code (signalChannel source signalSlot))
        (code (.signalFull signalSlot neuron)) frame⟩
  | redeem receiptSlot signalSlot creditSlot synapse =>
      simp only [causalActionSteps, causalActionSource, causalActionTarget]
      rw [causalRedeem_target_receiptChannel step,
        causalRedeem_target_signalChannel step,
        causalRedeem_target_creditChannel step]
      exact ⟨redemption_internalizes
        (code (receiptChannel source receiptSlot))
        (code (signalChannel source signalSlot))
        (code (creditChannel source creditSlot))
        (code (.receiptEmpty receiptSlot))
        (code (.signalEmpty signalSlot))
        (code (.creditAt creditSlot (.synapse synapse))) frame⟩
  | expireReceipt receiptSlot =>
      have observations := causalExpireReceipt_channels step
      simp only [causalActionSteps, causalActionSource, causalActionTarget]
      rw [observations.2]
      exact ⟨replacement_internalizes
        (code (receiptChannel source receiptSlot))
        (code (.receiptEmpty receiptSlot)) frame⟩
  | expireSignal signalSlot =>
      have observations := causalExpireSignal_channels step
      simp only [causalActionSteps, causalActionSource, causalActionTarget]
      rw [observations.2]
      exact ⟨replacement_internalizes
        (code (signalChannel source signalSlot))
        (code (.signalEmpty signalSlot)) frame⟩

theorem causalActionSource_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (causalActionSource source action frame) := by
  cases action <;> simp only [causalActionSource]
  · apply replacementSource_closed
    exact frameClosed
  · apply replacementSource_closed
    exact frameClosed
  · apply redemptionSource_closed
    exact frameClosed
  · apply replacementSource_closed
    exact frameClosed
  · apply replacementSource_closed
    exact frameClosed

theorem causalActionTarget_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (causalActionTarget target action frame) := by
  cases action <;> simp only [causalActionTarget]
  · apply replacementTarget_closed
    exact frameClosed
  · apply replacementTarget_closed
    exact frameClosed
  · apply redemptionTarget_closed
    exact frameClosed
  · apply replacementTarget_closed
    exact frameClosed
  · apply replacementTarget_closed
    exact frameClosed

/-- **No forced retraction.**  The shipped count-only learner remains unable
to solve the equal-exposure rewarded task, while the conserved causal-credit
repair both learns/relearns and has every one of its operational actions
realized by closed terms of the original rho calculus.  Internalizability is
therefore a claim about the host calculus, not an identification of the two
learning rules. -/
theorem internalization_preserves_countOnly_boundary :
    (¬ ReliablyLearnsOn rewardedChoiceTask rewardedChoiceProtocol
      shippedChoiceLearner) ∧
    ((causalRun choicePost causalInitialChoiceState causalUncreditedEpisode =
        some causalInitialChoiceState) ∧
      (causalRun choicePost causalInitialChoiceState causalTargetCreditEpisode =
        some causalTargetLearnedState) ∧
      rewardedChoiceTask.Solves
        (causalChoiceWeights causalTargetLearnedState) ∧
      (causalRun choicePost causalInitialChoiceState
        (causalTargetCreditEpisode ++ causalReverseCreditEpisode) =
          some causalDistractorLearnedState) ∧
      distractorChoiceTask.Solves
        (causalChoiceWeights causalDistractorLearnedState)) ∧
    ∀ (source target : CausalChoiceState) (action : CausalChoiceAction),
      CausalStep choicePost source action target →
      ClosedRhoProcess (causalActionSource source action []) ∧
      ClosedRhoProcess (causalActionTarget target action []) ∧
      Nonempty (ReducesN (causalActionSteps action)
        (causalActionSource source action [])
        (causalActionTarget target action [])) := by
  refine ⟨shippedRule_not_reliably_learns_rewardedChoice,
    causal_credit_learns_and_relearns, ?_⟩
  intro source target action step
  refine ⟨causalActionSource_closed source action [] (by simp),
    causalActionTarget_closed target action [] (by simp), ?_⟩
  exact causalAction_internalizes choicePost source target action step []

/-! ### Whole source runs, internalized transition by transition -/

/-- A successful source run together with a closed pure-rho simulation
witness for every edge.  This deliberately does not claim that the individual
administrative terms have already been fused into one deployment; that
stronger scheduler-composition theorem is separate. -/
inductive PointwiseInternalizedRun
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget →
    List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) →
    CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget → Prop where
  | nil (state) : PointwiseInternalizedRun post state [] state
  | cons {source middle target action rest} :
      CausalStep post source action middle →
      ClosedRhoProcess (causalActionSource source action []) →
      ClosedRhoProcess (causalActionTarget middle action []) →
      Nonempty (ReducesN (causalActionSteps action)
        (causalActionSource source action [])
        (causalActionTarget middle action [])) →
      PointwiseInternalizedRun post middle rest target →
      PointwiseInternalizedRun post source (action :: rest) target

/-- Every successful finite causal run admits the pointwise pure-rho
certificate above. -/
theorem causalRun_internalizes_pointwise
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget))
    (run : causalRun post source actions = some target) :
    PointwiseInternalizedRun post source actions target := by
  induction actions generalizing source with
  | nil =>
      simp [causalRun] at run
      subst target
      exact .nil source
  | cons action rest ih =>
      simp only [causalRun] at run
      cases nextStep : causalIntegratedStep post source action with
      | none => simp [nextStep] at run
      | some middle =>
          simp [nextStep] at run
          exact .cons nextStep
            (causalActionSource_closed source action [] (by simp))
            (causalActionTarget_closed middle action [] (by simp))
            (causalAction_internalizes post source middle action nextStep [])
            (ih middle run)

theorem causalTargetCreditEpisode_internalizes_pointwise :
    PointwiseInternalizedRun choicePost causalInitialChoiceState
      causalTargetCreditEpisode causalTargetLearnedState :=
  causalRun_internalizes_pointwise choicePost
    causalInitialChoiceState causalTargetLearnedState
    causalTargetCreditEpisode causalRun_targetCreditEpisode

theorem causalLearnThenReverse_internalizes_pointwise :
    PointwiseInternalizedRun choicePost causalInitialChoiceState
      (causalTargetCreditEpisode ++ causalReverseCreditEpisode)
      causalDistractorLearnedState :=
  causalRun_internalizes_pointwise choicePost
    causalInitialChoiceState causalDistractorLearnedState
    (causalTargetCreditEpisode ++ causalReverseCreditEpisode)
    causalRun_learn_then_reverse

/-! ### A fused control deployment for complete finite runs

The resource-level compiler above remains the cost-accounted semantics: in
particular, redemption consumes its receipt, signal, and donor credit in three
COMM steps.  A validated finite run also admits a second, coarser control
image.  One linear token names the complete source state, and a list of
one-shot handlers advances that token through the already-validated source
trace.  This fuses the schedule into one persistent pure-rho deployment
without identifying the control token with any credit resource.

The two namespaces are disjoint by construction.  Resource channels occupy
the initial finite interval; control states are shifted above the cardinality
of the complete resource-channel type. -/

/-- A trace phase and complete causal-credit state receive a control channel
above every resource-channel code.  The phase prevents two occurrences of the
same source state in one trace from enabling the same one-shot handler. -/
noncomputable def controlStateCode
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (phase : Nat)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : Nat :=
  Fintype.card (CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) +
    Nat.pair phase (Fintype.equivFin _ state).val

theorem controlStateCode_pair_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron] :
    Function.Injective
      (fun indexed : Nat × CausalCreditState Synapse Neuron
          receiptSlots signalSlots creditBudget =>
        controlStateCode indexed.1 indexed.2) := by
  intro left right equal
  have paired :
      Nat.pair left.1 (Fintype.equivFin _ left.2).val =
        Nat.pair right.1 (Fintype.equivFin _ right.2).val := by
    exact Nat.add_left_cancel equal
  have coordinates :
      (left.1, (Fintype.equivFin _ left.2).val) =
        (right.1, (Fintype.equivFin _ right.2).val) := by
    apply Nat.pairEquiv.injective
    simpa [Nat.pairEquiv_apply, Function.uncurry] using paired
  have phases : left.1 = right.1 :=
    congrArg (fun pair : Nat × Nat => pair.1) coordinates
  have values :
      (Fintype.equivFin _ left.2).val =
        (Fintype.equivFin _ right.2).val :=
    congrArg (fun pair : Nat × Nat => pair.2) coordinates
  have states : left.2 = right.2 := by
    apply (Fintype.equivFin _).injective
    apply Fin.ext
    exact values
  exact Prod.ext phases states

theorem controlStateCode_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (phase : Nat) :
    Function.Injective
      (controlStateCode phase :
        CausalCreditState Synapse Neuron
          receiptSlots signalSlots creditBudget → Nat) := by
  intro left right equal
  have paired : (phase, left) = (phase, right) :=
    controlStateCode_pair_injective equal
  exact congrArg Prod.snd paired

/-- Distinct trace phases never share a control channel, even when the source
state itself repeats. -/
theorem controlStateCode_ne_of_phase_ne
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    {leftPhase rightPhase : Nat}
    (left right : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (differentPhase : leftPhase ≠ rightPhase) :
    controlStateCode leftPhase left ≠ controlStateCode rightPhase right := by
  intro equal
  have indexed : (leftPhase, left) = (rightPhase, right) :=
    controlStateCode_pair_injective equal
  exact differentPhase (congrArg Prod.fst indexed)

/-- Control-state names cannot alias any cost-accounted resource name. -/
theorem imageChannelCode_lt_controlStateCode
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (channel : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (phase : Nat)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    imageChannelCode channel < controlStateCode phase state := by
  have channelBound := (Fintype.equivFin _ channel).isLt
  simp only [imageChannelCode, controlStateCode]
  omega

/-- The single linear token for the fused trace-control layer. -/
noncomputable def controlStateToken
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (phase : Nat)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : Pattern :=
  resourceToken (controlStateCode phase state)

/-- A trace-control handler advances one validated source state to its exact
successor.  It is an ordinary one-shot rho input. -/
noncomputable def causalControlHandler
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (sourcePhase : Nat)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (targetPhase : Nat) : Pattern :=
  replacementHandler (controlStateCode sourcePhase source)
    (controlStateCode targetPhase target)

theorem controlStateToken_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (phase : Nat)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    ClosedRhoProcess (controlStateToken phase state) := by
  exact resourceToken_closed (controlStateCode phase state)

theorem causalControlHandler_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (sourcePhase : Nat)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (targetPhase : Nat) :
    ClosedRhoProcess
      (causalControlHandler sourcePhase source target targetPhase) := by
  exact replacementHandler_closed
    (controlStateCode sourcePhase source) (controlStateCode targetPhase target)

/-- Compile the handlers of a successful source trace.  An invalid source
action fails compilation rather than generating target code. -/
noncomputable def causalControlHandlers
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget →
    List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) → Option (List Pattern)
  | _, [] => some []
  | state, action :: rest =>
      match causalIntegratedStep post state action with
      | none => none
      | some next =>
          (causalControlHandlers post next rest).map fun handlers =>
            causalControlHandler (action :: rest).length state next
              rest.length :: handlers

/-- A structured view of the fused handler schedule.  Retaining each dormant
handler's source channel beside its continuation lets the reflection theorem
state, and prove, the phase-freshness invariant before erasing the structure
to target syntax. -/
noncomputable def causalControlHandlerPairs
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget →
    List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) →
      Option (List (Nat × Pattern))
  | _, [] => some []
  | state, action :: rest =>
      match causalIntegratedStep post state action with
      | none => none
      | some next =>
          (causalControlHandlerPairs post next rest).map fun handlers =>
            (controlStateCode (action :: rest).length state,
              controlStateToken rest.length next) :: handlers

/-- Erasing structured handler pairs produces exactly the original fused
control compiler, not a second target program. -/
theorem causalControlHandlerPairs_map
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    (causalControlHandlerPairs post source actions).map
        (List.map awaitResourcePair) =
      causalControlHandlers post source actions := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
      cases nextStep : causalIntegratedStep post source action with
      | none =>
          simp [causalControlHandlerPairs, causalControlHandlers, nextStep]
      | some next =>
          rw [causalControlHandlerPairs, causalControlHandlers, nextStep]
          simp only
          rw [← ih next]
          cases causalControlHandlerPairs post next rest <;>
            simp [causalControlHandler, replacementHandler,
              awaitResourcePair, controlStateToken]

/-- Successful structured compilation has no duplicate handler pair, and
every emitted handler source is a positive phase no larger than the source
trace length.  The phase bound is the invariant that prevents dormant
handlers from consuming the unique active control token. -/
theorem causalControlHandlerPairs_nodup_bounded
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget))
    (pairs : List (Nat × Pattern))
    (compiled : causalControlHandlerPairs post source actions = some pairs) :
    pairs.Nodup ∧
      ∀ pair ∈ pairs,
        ∃ (phase : Nat)
          (phaseState : CausalCreditState Synapse Neuron
            receiptSlots signalSlots creditBudget),
          0 < phase ∧ phase ≤ actions.length ∧
            pair.1 = controlStateCode phase phaseState := by
  induction actions generalizing source pairs with
  | nil =>
      simp [causalControlHandlerPairs] at compiled
      subst pairs
      simp
  | cons action rest ih =>
      cases nextStep : causalIntegratedStep post source action with
      | none =>
          simp [causalControlHandlerPairs, nextStep] at compiled
      | some next =>
          cases tailCompiled : causalControlHandlerPairs post next rest with
          | none =>
              simp [causalControlHandlerPairs, nextStep, tailCompiled] at compiled
          | some tailPairs =>
              simp [causalControlHandlerPairs, nextStep, tailCompiled] at compiled
              subst pairs
              rcases ih next tailPairs tailCompiled with
                ⟨tailNodup, tailBounded⟩
              constructor
              · apply List.nodup_cons.mpr
                constructor
                · intro headMem
                  rcases tailBounded _ headMem with
                    ⟨phase, phaseState, phasePositive, phaseBound, codeEqual⟩
                  have phaseDifferent : (action :: rest).length ≠ phase := by
                    simp only [List.length_cons]
                    omega
                  exact (controlStateCode_ne_of_phase_ne source phaseState
                    phaseDifferent) (by simpa using codeEqual)
                · exact tailNodup
              · intro pair membership
                simp only [List.mem_cons] at membership
                rcases membership with rfl | tailMem
                · exact ⟨(action :: rest).length, source, by simp,
                    le_rfl, rfl⟩
                · rcases tailBounded pair tailMem with
                    ⟨phase, phaseState, phasePositive, phaseBound, codeEqual⟩
                  exact ⟨phase, phaseState, phasePositive,
                    by simp only [List.length_cons]; omega, codeEqual⟩

/-- The closed source deployment places one state token beside the complete
one-shot handler schedule. -/
noncomputable def causalControlDeployment
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) : Option Pattern :=
  (causalControlHandlers post source actions).map fun handlers =>
    bag (controlStateToken actions.length source :: handlers)

/-- The final control image contains only the resulting state token. -/
noncomputable def causalControlFinal
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : Pattern :=
  bag [controlStateToken 0 target]

/-- Compilation succeeds exactly when the source operational run succeeds.
This is the fail-closed admission half of the control image: no invalid action
trace can acquire a pure-rho deployment merely by naming a desired target. -/
theorem causalControlHandlers_isSome_eq_causalRun_isSome
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    (causalControlHandlers post source actions).isSome =
      (causalRun post source actions).isSome := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
      cases nextStep : causalIntegratedStep post source action with
      | none =>
          simp [causalControlHandlers, causalRun, nextStep]
      | some middle =>
          simp [causalControlHandlers, causalRun, nextStep, ih middle]

theorem causalControlHandlerPairs_isSome_eq_causalRun_isSome
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    (causalControlHandlerPairs post source actions).isSome =
      (causalRun post source actions).isSome := by
  calc
    (causalControlHandlerPairs post source actions).isSome =
        ((causalControlHandlerPairs post source actions).map
          (List.map awaitResourcePair)).isSome := by simp
    _ = (causalControlHandlers post source actions).isSome :=
      congrArg Option.isSome
        (causalControlHandlerPairs_map post source actions)
    _ = (causalRun post source actions).isSome :=
      causalControlHandlers_isSome_eq_causalRun_isSome post source actions

theorem causalControlDeployment_isSome_eq_causalRun_isSome
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    (causalControlDeployment post source actions).isSome =
      (causalRun post source actions).isSome := by
  simp [causalControlDeployment,
    causalControlHandlers_isSome_eq_causalRun_isSome]

/-- At any successful control phase, the engine's complete fuel-one frontier
contains exactly the source successor.  This is reduction reflection, not
only forward simulation: no dormant compiled handler can create an
additional target reduction. -/
theorem causalControl_step_frontier_iff
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source next : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (rest : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget))
    (pairs : List (Nat × Pattern))
    (pairsCompiled :
      causalControlHandlerPairs post next rest = some pairs)
    (reduct : Pattern) :
    reduct ∈ Engine.reduceStep
        (bag (controlStateToken (action :: rest).length source ::
          causalControlHandler (action :: rest).length source next
            rest.length :: pairs.map awaitResourcePair)) 1 ↔
      reduct = bag (controlStateToken rest.length next ::
        pairs.map awaitResourcePair) := by
  rcases causalControlHandlerPairs_nodup_bounded
      post next rest pairs pairsCompiled with ⟨pairsNodup, bounded⟩
  have fresh :
      controlStateCode (action :: rest).length source ∉
        pairs.map Prod.fst := by
    intro membership
    rcases List.mem_map.mp membership with
      ⟨pair, pairMem, pairCode⟩
    rcases bounded pair pairMem with
      ⟨phase, phaseState, phasePositive, phaseBound, codeEqual⟩
    have phaseDifferent : (action :: rest).length ≠ phase := by
      simp only [List.length_cons]
      omega
    exact (controlStateCode_ne_of_phase_ne source phaseState
      phaseDifferent) (pairCode.symm.trans codeEqual)
  have admitted : InputOnlyImageContext
      (controlStateCode (action :: rest).length source)
      (pairs.map awaitResourcePair) :=
    ⟨pairs, pairsNodup, fresh, rfl⟩
  simpa [controlStateToken, causalControlHandler, replacementHandler,
      awaitResourcePair, commRes, semanticCommSubst_resourceToken] using
    oneShotSource_inputOnlyContext_frontier_iff
      (controlStateCode (action :: rest).length source)
      (controlStateToken rest.length next)
      (pairs.map awaitResourcePair) admitted reduct

/-- Exact frontier reflection at every suffix of a fused finite deployment.
The recursive property records the actual engine frontier at each source
step; it is false when either the source step or its remaining structured
handler schedule fails to compile. -/
noncomputable def FusedControlFrontiersExact
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron) :
    CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget →
    List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) → Prop
  | _, [] => True
  | state, action :: rest =>
      match causalIntegratedStep post state action with
      | none => False
      | some next =>
          match causalControlHandlerPairs post next rest with
          | none => False
          | some pairs =>
              (∀ reduct,
                reduct ∈ Engine.reduceStep
                    (bag (controlStateToken (action :: rest).length state ::
                      causalControlHandler (action :: rest).length state next
                        rest.length :: pairs.map awaitResourcePair)) 1 ↔
                  reduct = bag (controlStateToken rest.length next ::
                    pairs.map awaitResourcePair)) ∧
                FusedControlFrontiersExact post next rest

/-- Every successful finite source run has exact, singleton executable
frontiers throughout its fused pure-rho deployment.  Together with handler
erasure, this lifts the one-step capability-safe reflection theorem to the
whole phase-tagged compiler image. -/
theorem causalRun_fused_control_frontiers_exact
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget))
    (run : causalRun post source actions = some target) :
    FusedControlFrontiersExact post source actions := by
  induction actions generalizing source with
  | nil =>
      simp [FusedControlFrontiersExact]
  | cons action rest ih =>
      simp only [causalRun] at run
      cases nextStep : causalIntegratedStep post source action with
      | none => simp [nextStep] at run
      | some next =>
          simp only [nextStep, Option.bind_some] at run
          have pairsSome :
              (causalControlHandlerPairs post next rest).isSome = true := by
            rw [causalControlHandlerPairs_isSome_eq_causalRun_isSome]
            rw [run]
            rfl
          cases pairsCompiled : causalControlHandlerPairs post next rest with
          | none => simp [pairsCompiled] at pairsSome
          | some pairs =>
              rw [FusedControlFrontiersExact]
              simp only [nextStep, pairsCompiled]
              exact ⟨fun reduct => causalControl_step_frontier_iff
                  post source next action rest pairs pairsCompiled reduct,
                ih next run⟩

/-- Positive finite-run canary: the selective target-credit history has an
exact singleton engine frontier at every fused control phase. -/
theorem causalTargetCreditEpisode_fused_frontiers_exact :
    FusedControlFrontiersExact choicePost causalInitialChoiceState
      causalTargetCreditEpisode :=
  causalRun_fused_control_frontiers_exact choicePost
    causalInitialChoiceState causalTargetLearnedState
    causalTargetCreditEpisode causalRun_targetCreditEpisode

/-- Reversal canary: learning the target and then reallocating the conserved
credit toward the distractor retains exact frontiers throughout the longer
fused deployment. -/
theorem causalLearnThenReverse_fused_frontiers_exact :
    FusedControlFrontiersExact choicePost causalInitialChoiceState
      (causalTargetCreditEpisode ++ causalReverseCreditEpisode) :=
  causalRun_fused_control_frontiers_exact choicePost
    causalInitialChoiceState causalDistractorLearnedState
    (causalTargetCreditEpisode ++ causalReverseCreditEpisode)
    causalRun_learn_then_reverse

/-! ### Qualitative support does not determine transition intensity -/

/-- A minimal nonnegative, integer-valued transition-intensity annotation.
This is not assigned to rho COMM by the qualitative engine; it is used only
to state exactly what information a support relation forgets. -/
abbrev NatIntensityKernel (State : Type*) := State → State → Nat

/-- Forget intensity magnitude and retain only whether an edge is enabled. -/
def qualitativeSupport {State : Type*}
    (kernel : NatIntensityKernel State) : State → State → Prop :=
  fun source target => kernel source target ≠ 0

/-- A two-state kernel with one enabled edge of unit intensity. -/
def unitIntensity : NatIntensityKernel Bool
  | false, true => 1
  | _, _ => 0

/-- The same qualitative transition graph with twice the enabled intensity. -/
def doubleIntensity : NatIntensityKernel Bool
  | false, true => 2
  | _, _ => 0

theorem unitIntensity_edge_enabled :
    qualitativeSupport unitIntensity false true := by
  simp [qualitativeSupport, unitIntensity]

theorem unitIntensity_reverse_disabled :
    ¬ qualitativeSupport unitIntensity true false := by
  simp [qualitativeSupport, unitIntensity]

theorem unit_doubleIntensity_same_support :
    qualitativeSupport unitIntensity = qualitativeSupport doubleIntensity := by
  funext source target
  cases source <;> cases target <;>
    simp [qualitativeSupport, unitIntensity, doubleIntensity]

theorem unit_doubleIntensity_ne : unitIntensity ≠ doubleIntensity := by
  intro equal
  have edgeEqual := congrFun (congrFun equal false) true
  norm_num [unitIntensity, doubleIntensity] at edgeEqual

/-- A qualitative transition relation cannot identify a stochastic or timed
intensity annotation: even on two finite states, distinct nonnegative kernels
have exactly the same enabled-edge support. -/
theorem qualitativeSupport_not_injective :
    ¬ Function.Injective
      (qualitativeSupport (State := Bool)) := by
  intro injective
  exact unit_doubleIntensity_ne
    (injective unit_doubleIntensity_same_support)

@[simp]
theorem ioCount_resourceToken (channel : Nat) :
    Reduction.ioCount (resourceToken channel) = channel + 1 := by
  simp [resourceToken, commOut, rhoZero, Reduction.ioCount]
  omega

/-! ## A complete state image and syntax-level decoder -/

/-- The complete finite resource-channel inventory of a causal-credit state.
There is exactly one receipt token per receipt slot, one signal token per
signal slot, and one ownership token per conserved credit slot. -/
noncomputable def stateResourceChannels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    List (CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) :=
  ((Finset.univ : Finset (Fin receiptSlots)).toList.map
      (receiptChannel state)) ++
    ((Finset.univ : Finset (Fin signalSlots)).toList.map
      (signalChannel state)) ++
    ((Finset.univ : Finset (Fin creditBudget)).toList.map
      (creditChannel state))

/-- The flat target-level frame containing every linear resource of a source
state as an ordinary pure-rho output. -/
noncomputable def stateResourceFrame
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : List Pattern :=
  (stateResourceChannels state).map fun channel =>
    resourceToken (imageChannelCode channel)

/-- Complete pure-rho resource image of a source state. -/
noncomputable def stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) : Pattern :=
  bag (stateResourceFrame state)

/-- Read the top-level processes of a concrete pure-rho bag.  Non-bag terms
decode to the empty frame, so the observation is a total function on target
syntax rather than a re-use of the source state. -/
def resourceImageComponents : Pattern → List Pattern
  | .collection .hashBag processes none => processes
  | _ => []

@[simp]
theorem resourceImageComponents_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    resourceImageComponents (stateResourceImage state) =
      stateResourceFrame state := rfl

/-- Decode the finite set of typed resource-channel identities occurring as
top-level tokens of a target term. -/
noncomputable def decodedResourceChannels
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (image : Pattern) :
    Finset (CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) :=
  Finset.univ.filter fun channel =>
    resourceToken (imageChannelCode channel) ∈ resourceImageComponents image

/-- Count the credit slots assigned to an account by inspecting only the
concrete target term.  Slot identity is part of the channel, so duplicates of
an unrelated token cannot fabricate ownership of another slot. -/
noncomputable def decodedAccountCredits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (image : Pattern) (account : CreditAccount Synapse Neuron) : Nat :=
  (Finset.univ.filter fun slot : Fin creditBudget =>
    resourceToken (imageChannelCode
      ((CreditImageChannel.creditAt slot account) :
        CreditImageChannel Synapse Neuron
          receiptSlots signalSlots creditBudget)) ∈
        resourceImageComponents image).card

theorem codedResourceToken_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron] :
    Function.Injective (fun channel : CreditImageChannel Synapse Neuron
        receiptSlots signalSlots creditBudget =>
      resourceToken (imageChannelCode channel)) :=
  resourceToken_injective.comp imageChannelCode_injective

theorem codedResourceToken_mem_stateResourceFrame_iff
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (channel : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    resourceToken (imageChannelCode channel) ∈ stateResourceFrame state ↔
      channel ∈ stateResourceChannels state := by
  simp only [stateResourceFrame, List.mem_map]
  constructor
  · rintro ⟨candidate, membership, equal⟩
    have channelEqual : candidate = channel :=
      codedResourceToken_injective equal
    simpa [channelEqual] using membership
  · intro membership
    exact ⟨channel, membership, rfl⟩

/-- Decoding a complete state image recovers exactly its receipt, signal, and
credit channel inventory.  This is the complete term-level left inverse; it
does not receive the source state as an input. -/
theorem decodedResourceChannels_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    decodedResourceChannels (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) (stateResourceImage state) =
        (stateResourceChannels state).toFinset := by
  ext channel
  simp [decodedResourceChannels,
    codedResourceToken_mem_stateResourceFrame_iff]

/-- Complete state images inhabit the authored closed pure-rho carrier. -/
theorem stateResourceImage_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    ClosedRhoProcess (stateResourceImage state) := by
  apply bag_closed
  intro process membership
  simp only [stateResourceFrame, List.mem_map] at membership
  rcases membership with ⟨channel, _, rfl⟩
  exact resourceToken_closed (imageChannelCode channel)

@[simp]
theorem creditAt_mem_stateResourceChannels_iff
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (slot : Fin creditBudget) (account : CreditAccount Synapse Neuron) :
    CreditImageChannel.creditAt slot account ∈ stateResourceChannels state ↔
      state.core.allocation slot = account := by
  have receiptNe : ∀ receiptSlot,
      receiptChannel state receiptSlot ≠
        CreditImageChannel.creditAt slot account := by
    intro receiptSlot
    simp only [receiptChannel]
    split <;> simp
  have signalNe : ∀ signalSlot,
      signalChannel state signalSlot ≠
        CreditImageChannel.creditAt slot account := by
    intro signalSlot
    simp only [signalChannel]
    split <;> simp
  simp [stateResourceChannels, receiptNe, signalNe, creditChannel]

/-- The syntax-level decoder is a left inverse for account ownership on every
complete state image.  Unlike `imageAccountCredits_eq_accountCredits`, the
left-hand side receives only a pure-rho `Pattern`. -/
theorem decodedAccountCredits_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (account : CreditAccount Synapse Neuron) :
    decodedAccountCredits (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      (stateResourceImage state) account =
      accountCredits state.core account := by
  simp [decodedAccountCredits, accountCredits,
    codedResourceToken_mem_stateResourceFrame_iff]

/-- Quantized efficacy decoded from a concrete target term. -/
noncomputable def decodedDerivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : Real) (image : Pattern) (synapse : Synapse) : Real :=
  base + quantum *
    decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      image (.synapse synapse)

/-- Derived efficacy is recovered exactly from the complete pure-rho term;
no source-state argument remains on the decoded side. -/
theorem decodedDerivedWeight_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : Real)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    decodedDerivedWeight (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      base quantum (stateResourceImage state) synapse =
      derivedWeight base quantum state.core synapse := by
  simp [decodedDerivedWeight, derivedWeight,
    decodedAccountCredits_stateResourceImage]

/-- Total conserved credit decoded from a concrete target term. -/
noncomputable def decodedTotalCredits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (image : Pattern) : Nat :=
  ∑ account : CreditAccount Synapse Neuron,
    decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget) image account

/-- Conservation is visible in the target syntax: decoding every account in
a complete image recovers exactly the source type's fixed credit budget. -/
theorem decodedTotalCredits_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    decodedTotalCredits (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      (stateResourceImage state) = creditBudget := by
  simpa only [decodedTotalCredits,
    decodedAccountCredits_stateResourceImage, totalCredits] using
    (totalCredits_eq_budget state.core)

/-! ### Term-decoded learning canaries -/

/-- Choice weights observed solely from a concrete target image.  This is an
observable of target state, not yet a claim that the value parameterizes a
stochastic transition intensity. -/
noncomputable def decodedCausalChoiceWeights (image : Pattern) :
    WeightMap ChoiceSynapse := fun synapse =>
  decodedDerivedWeight (Synapse := ChoiceSynapse) (Neuron := Unit)
    (receiptSlots := 1) (signalSlots := 1) (creditBudget := 4)
    0 1 image synapse

theorem decodedCausalChoiceWeights_stateResourceImage
    (state : CausalChoiceState) :
    decodedCausalChoiceWeights (stateResourceImage state) =
      causalChoiceWeights state := by
  funext synapse
  simpa [decodedCausalChoiceWeights, causalChoiceWeights,
    creditChoiceWeights] using
    (decodedDerivedWeight_stateResourceImage (base := 0) (quantum := 1)
      state synapse)

/-- Positive canary: the target-credit image decodes to a weight map solving
the rewarded target-choice task. -/
theorem decodedTargetImage_solves_target_task :
    rewardedChoiceTask.Solves
      (decodedCausalChoiceWeights
        (stateResourceImage causalTargetLearnedState)) := by
  rw [decodedCausalChoiceWeights_stateResourceImage]
  exact causal_target_credit_solves_target_task

/-- Negative canary: the uncredited image retains equal exposure and does not
solve the rewarded target-choice task. -/
theorem decodedInitialImage_fails_target_task :
    ¬ rewardedChoiceTask.Solves
      (decodedCausalChoiceWeights
        (stateResourceImage causalInitialChoiceState)) := by
  rw [decodedCausalChoiceWeights_stateResourceImage]
  exact causal_uncredited_fails_target_task

/-- Reversal canary: reversing conserved credit changes the decoded target
term so that its recovered weight map solves the distractor task. -/
theorem decodedDistractorImage_solves_distractor_task :
    distractorChoiceTask.Solves
      (decodedCausalChoiceWeights
        (stateResourceImage causalDistractorLearnedState)) := by
  rw [decodedCausalChoiceWeights_stateResourceImage]
  exact causal_reverse_credit_solves_distractor_task

@[simp]
theorem ioCount_controlStateToken
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (phase : Nat)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    Reduction.ioCount (controlStateToken phase state) =
      controlStateCode phase state + 1 := by
  simp [controlStateToken]

/-- Final control images decode uniquely: structurally different source
states cannot be hidden behind the same emitted state token. -/
theorem causalControlFinal_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron] :
    Function.Injective
      (causalControlFinal :
        CausalCreditState Synapse Neuron
          receiptSlots signalSlots creditBudget → Pattern) := by
  intro left right equal
  have counts := congrArg Reduction.ioCount equal
  have codes : controlStateCode 0 left = controlStateCode 0 right := by
    simpa [causalControlFinal, bag, Reduction.ioCount] using counts
  exact controlStateCode_injective 0 codes

/-- Injectivity survives quotienting by the target calculus's structural
laws, not merely syntactic equality of the emitted bags. -/
theorem causalControlFinal_structural_injective
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    {left right : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    (equivalent : StructuralCongruence
      (causalControlFinal left) (causalControlFinal right)) :
    left = right := by
  have counts := Reduction.ioCount_SC equivalent
  have codes : controlStateCode 0 left = controlStateCode 0 right := by
    simpa [causalControlFinal, bag, Reduction.ioCount] using counts
  exact controlStateCode_injective 0 codes

/-- **Fused whole-run internalization.**  Every successful finite source run
compiles to one closed pure-rho deployment.  Its state token traverses the
precompiled one-shot handler chain in exactly one COMM per source action and
leaves exactly the final state token.  Invalid traces emit no deployment.

This theorem is about trace control, not resource cost: the independent
resource-level theorem above remains authoritative for the three-COMM causal
redemption protocol. -/
theorem causalRun_internalizes_fused_control
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget))
    (run : causalRun post source actions = some target) :
    ∃ handlers : List Pattern,
      causalControlHandlers post source actions = some handlers ∧
      causalControlDeployment post source actions =
        some (bag (controlStateToken actions.length source :: handlers)) ∧
      (∀ process ∈ handlers, ClosedRhoProcess process) ∧
      ClosedRhoProcess
        (bag (controlStateToken actions.length source :: handlers)) ∧
      ClosedRhoProcess (causalControlFinal target) ∧
      Nonempty (ReducesN actions.length
        (bag (controlStateToken actions.length source :: handlers))
        (causalControlFinal target)) := by
  induction actions generalizing source with
  | nil =>
      simp only [causalRun] at run
      have target_eq : target = source := (Option.some.inj run).symm
      subst target
      refine ⟨[], rfl, rfl, ?_, ?_, ?_, ⟨.zero _⟩⟩
      · simp
      · apply bag_closed
        intro process membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst process
        exact controlStateToken_closed 0 source
      · apply bag_closed
        intro process membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst process
        exact controlStateToken_closed 0 source
  | cons action rest ih =>
      simp only [causalRun] at run
      cases nextStep : causalIntegratedStep post source action with
      | none => simp [nextStep] at run
      | some middle =>
          simp only [nextStep, Option.bind_some] at run
          rcases ih middle run with
            ⟨handlers, handlersCompiled, deploymentCompiled,
              handlersClosed, _middleClosed, targetClosed, tailReduction⟩
          let handler := causalControlHandler (action :: rest).length
            source middle rest.length
          refine ⟨handler :: handlers, ?_, ?_, ?_, ?_, targetClosed, ?_⟩
          · simp [causalControlHandlers, nextStep, handlersCompiled, handler]
          · simp [causalControlDeployment, causalControlHandlers,
              nextStep, handlersCompiled, handler]
          · intro process membership
            simp only [List.mem_cons] at membership
            rcases membership with rfl | membership
            · exact causalControlHandler_closed (action :: rest).length
                source middle rest.length
            · exact handlersClosed process membership
          · apply bag_closed
            intro process membership
            simp only [List.mem_cons] at membership
            rcases membership with rfl | rfl | membership
            · exact controlStateToken_closed (action :: rest).length source
            · exact causalControlHandler_closed (action :: rest).length
                source middle rest.length
            · exact handlersClosed process membership
          · obtain ⟨tailReduction⟩ := tailReduction
            have first : ReducesN 1
                (bag (controlStateToken (action :: rest).length source ::
                  handler :: handlers))
                (bag (controlStateToken rest.length middle :: handlers)) := by
              simpa [controlStateToken, handler, causalControlHandler,
                replacementSource, replacementTarget] using
                replacement_internalizes
                  (controlStateCode (action :: rest).length source)
                  (controlStateCode rest.length middle) handlers
            have combined := reducesN_concat first tailReduction
            exact ⟨by
              simpa [causalControlFinal, Nat.add_comm] using combined⟩

/-- **Fail-closed operational correspondence for complete finite runs.**
Source execution succeeds exactly when the compiler emits a closed fused
deployment with an exact-length pure-rho execution to an injectively encoded
final state.  The backward implication is intentionally an admission result:
an invalid source trace cannot acquire a target execution because it emits no
deployment.  It does not assert full abstraction against arbitrary target
contexts outside the compiler image. -/
theorem causalRun_success_iff_fused_control_execution
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (post : Synapse → Neuron)
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (actions : List (CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget)) :
    (∃ target, causalRun post source actions = some target) ↔
      ∃ (handlers : List Pattern)
        (target : CausalCreditState Synapse Neuron
          receiptSlots signalSlots creditBudget),
        causalControlDeployment post source actions =
          some (bag (controlStateToken actions.length source :: handlers)) ∧
        (∀ process ∈ handlers, ClosedRhoProcess process) ∧
        ClosedRhoProcess
          (bag (controlStateToken actions.length source :: handlers)) ∧
        ClosedRhoProcess (causalControlFinal target) ∧
        Nonempty (ReducesN actions.length
          (bag (controlStateToken actions.length source :: handlers))
          (causalControlFinal target)) := by
  constructor
  · rintro ⟨target, run⟩
    rcases causalRun_internalizes_fused_control post source target actions run with
      ⟨handlers, _handlersCompiled, deploymentCompiled, handlersClosed,
        deploymentClosed, targetClosed, reduction⟩
    exact ⟨handlers, target, deploymentCompiled, handlersClosed,
      deploymentClosed, targetClosed, reduction⟩
  · rintro ⟨handlers, target, deploymentCompiled, _handlersClosed,
      _deploymentClosed, _targetClosed, _reduction⟩
    have deploymentSome :
        (causalControlDeployment post source actions).isSome = true := by
      rw [deploymentCompiled]
      rfl
    have runSome : (causalRun post source actions).isSome = true := by
      rw [← causalControlDeployment_isSome_eq_causalRun_isSome]
      exact deploymentSome
    cases runEquation : causalRun post source actions with
    | none => simp [runEquation] at runSome
    | some finalState => exact ⟨finalState, rfl⟩

theorem causalTargetCreditEpisode_internalizes_fused_control :
    ∃ handlers : List Pattern,
      causalControlHandlers choicePost causalInitialChoiceState
          causalTargetCreditEpisode = some handlers ∧
      causalControlDeployment choicePost causalInitialChoiceState
          causalTargetCreditEpisode =
        some (bag (controlStateToken causalTargetCreditEpisode.length
          causalInitialChoiceState :: handlers)) ∧
      (∀ process ∈ handlers, ClosedRhoProcess process) ∧
      ClosedRhoProcess
        (bag (controlStateToken causalTargetCreditEpisode.length
          causalInitialChoiceState :: handlers)) ∧
      ClosedRhoProcess (causalControlFinal causalTargetLearnedState) ∧
      Nonempty (ReducesN causalTargetCreditEpisode.length
        (bag (controlStateToken causalTargetCreditEpisode.length
          causalInitialChoiceState :: handlers))
        (causalControlFinal causalTargetLearnedState)) :=
  causalRun_internalizes_fused_control choicePost
    causalInitialChoiceState causalTargetLearnedState
    causalTargetCreditEpisode causalRun_targetCreditEpisode

theorem causalLearnThenReverse_internalizes_fused_control :
    ∃ handlers : List Pattern,
      causalControlHandlers choicePost causalInitialChoiceState
          (causalTargetCreditEpisode ++ causalReverseCreditEpisode) =
        some handlers ∧
      causalControlDeployment choicePost causalInitialChoiceState
          (causalTargetCreditEpisode ++ causalReverseCreditEpisode) =
        some (bag (controlStateToken
          (causalTargetCreditEpisode ++ causalReverseCreditEpisode).length
          causalInitialChoiceState :: handlers)) ∧
      (∀ process ∈ handlers, ClosedRhoProcess process) ∧
      ClosedRhoProcess
        (bag (controlStateToken
          (causalTargetCreditEpisode ++ causalReverseCreditEpisode).length
          causalInitialChoiceState :: handlers)) ∧
      ClosedRhoProcess (causalControlFinal causalDistractorLearnedState) ∧
      Nonempty (ReducesN
        (causalTargetCreditEpisode ++ causalReverseCreditEpisode).length
        (bag (controlStateToken
          (causalTargetCreditEpisode ++ causalReverseCreditEpisode).length
          causalInitialChoiceState :: handlers))
        (causalControlFinal causalDistractorLearnedState)) :=
  causalRun_internalizes_fused_control choicePost
    causalInitialChoiceState causalDistractorLearnedState
    (causalTargetCreditEpisode ++ causalReverseCreditEpisode)
    causalRun_learn_then_reverse

/-- Negative compiler canary: a redemption from the empty initial receipt and
signal banks is rejected before any pure-rho deployment is emitted. -/
theorem invalidInitialRedemption_controlDeployment_rejected :
    causalControlDeployment choicePost causalInitialChoiceState
      [.redeem 0 0 2 .target] = none := by
  simp [causalControlDeployment, causalControlHandlers,
    causalIntegratedStep, causalInitialChoiceState, emptySignals]

/-! ### A closed receipt-judging success contract

The primitive causal action language permits an explicit signal action, but
does not say which component is entitled to issue it.  The following finite
contract closes that gap for receipt-observable tasks.  A contract is a
decidable predicate on the synapse named by a live receipt.  Its rho image
can inspect the receipt only linearly: it consumes the accepted receipt,
consumes an empty signal-slot token, and then reissues the same receipt beside
the corresponding full signal token.  No oracle transition is added. -/

/-- A finite task contract evaluated on the synapse named by a causal
receipt.  `accepts` is executable data, not a proof supplied at redemption. -/
structure ReceiptSuccessContract (Synapse : Type*) where
  accepts : Synapse → Bool

def ReceiptSuccessContract.Authorizes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse]
    (contract : ReceiptSuccessContract Synapse)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (synapse : Synapse) : Bool :=
  contract.accepts synapse &&
    decide (state.core.receipts receiptSlot = some synapse)

theorem ReceiptSuccessContract.authorizes_eq_true_iff
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse]
    (contract : ReceiptSuccessContract Synapse)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (synapse : Synapse) :
    contract.Authorizes state receiptSlot synapse = true ↔
      contract.accepts synapse = true ∧
        state.core.receipts receiptSlot = some synapse := by
  simp [ReceiptSuccessContract.Authorizes]

/-- The two resources published after successful closed judging. -/
def receiptSuccessProducts (receipt signal : Nat) : Pattern :=
  bag [resourceToken receipt, resourceToken signal]

/-- A closed judge for one accepted receipt channel and one empty signal
slot.  Receipt observation is non-destructive at the protocol boundary
because the continuation republishes the same receipt token. -/
def receiptSuccessHandler
    (receipt emptySignal fullSignal : Nat) : Pattern :=
  awaitResource receipt
    (awaitResource emptySignal
      (receiptSuccessProducts receipt fullSignal))

def receiptSuccessSource
    (receipt emptySignal fullSignal : Nat)
    (frame : List Pattern) : Pattern :=
  bag ([resourceToken receipt,
    receiptSuccessHandler receipt emptySignal fullSignal,
    resourceToken emptySignal] ++ frame)

def receiptSuccessTarget
    (receipt fullSignal : Nat) (frame : List Pattern) : Pattern :=
  bag ([resourceToken receipt, resourceToken fullSignal] ++ frame)

theorem receiptSuccessProducts_closed (receipt signal : Nat) :
    ClosedRhoProcess (receiptSuccessProducts receipt signal) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact resourceToken_closed receipt
  · exact resourceToken_closed signal

theorem receiptSuccessHandler_closed
    (receipt emptySignal fullSignal : Nat) :
    ClosedRhoProcess
      (receiptSuccessHandler receipt emptySignal fullSignal) := by
  apply awaitResource_closed
  apply awaitResource_closed
  exact receiptSuccessProducts_closed receipt fullSignal

theorem receiptSuccessSource_closed
    (receipt emptySignal fullSignal : Nat) (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess
      (receiptSuccessSource receipt emptySignal fullSignal frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with (rfl | rfl | rfl) | membership
  · exact resourceToken_closed receipt
  · exact receiptSuccessHandler_closed receipt emptySignal fullSignal
  · exact resourceToken_closed emptySignal
  · exact frameClosed process membership

theorem receiptSuccessTarget_closed
    (receipt fullSignal : Nat) (frame : List Pattern)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    ClosedRhoProcess (receiptSuccessTarget receipt fullSignal frame) := by
  apply bag_closed
  intro process membership
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with (rfl | rfl) | membership
  · exact resourceToken_closed receipt
  · exact resourceToken_closed fullSignal
  · exact frameClosed process membership

private theorem subst_receiptSuccessProducts
    (receipt fullSignal depth : Nat) :
    semanticSubstProc depth (.apply "NQuote" [rhoZero])
      (receiptSuccessProducts receipt fullSignal) =
        receiptSuccessProducts receipt fullSignal := by
  unfold receiptSuccessProducts bag
  simp only [semanticSubstProc, semanticSubstProcList]
  rw [semanticSubstProc_resourceToken,
    semanticSubstProc_resourceToken]

private theorem commRes_receiptSuccessHandler
    (emptySignal receipt fullSignal : Nat) :
    commRes
      (awaitResource emptySignal
        (receiptSuccessProducts receipt fullSignal)) rhoZero =
      awaitResource emptySignal
        (receiptSuccessProducts receipt fullSignal) := by
  unfold commRes
  apply semanticCommSubst_awaitResource
  exact subst_receiptSuccessProducts receipt fullSignal 1

private theorem commRes_receiptSuccessProducts
    (receipt fullSignal : Nat) :
    commRes (receiptSuccessProducts receipt fullSignal) rhoZero =
      receiptSuccessProducts receipt fullSignal := by
  unfold commRes semanticCommSubst
  rw [semanticNormalize_rhoZero]
  exact subst_receiptSuccessProducts receipt fullSignal 0

def receiptSuccess_receipt_step
    (receipt emptySignal fullSignal : Nat) (frame : List Pattern) :
    Reduces
      (receiptSuccessSource receipt emptySignal fullSignal frame)
      (bag ([awaitResource emptySignal
          (receiptSuccessProducts receipt fullSignal),
        resourceToken emptySignal] ++ frame)) := by
  have step := comm_at_head (markerName receipt) rhoZero
    (awaitResource emptySignal
      (receiptSuccessProducts receipt fullSignal))
    (resourceToken emptySignal :: frame)
  rw [commRes_receiptSuccessHandler emptySignal receipt fullSignal] at step
  simpa [receiptSuccessSource, receiptSuccessHandler,
    resourceToken, awaitResource, List.cons_append] using step

def receiptSuccess_signal_step
    (receipt emptySignal fullSignal : Nat) (frame : List Pattern) :
    Reduces
      (bag ([awaitResource emptySignal
          (receiptSuccessProducts receipt fullSignal),
        resourceToken emptySignal] ++ frame))
      (receiptSuccessTarget receipt fullSignal frame) := by
  have sourcePerm : StructuralCongruence
      (bag ([awaitResource emptySignal
          (receiptSuccessProducts receipt fullSignal),
        resourceToken emptySignal] ++ frame))
      (bag ([resourceToken emptySignal,
        awaitResource emptySignal
          (receiptSuccessProducts receipt fullSignal)] ++ frame)) := by
    apply bag_perm
    simpa using (List.Perm.swap
      (awaitResource emptySignal
        (receiptSuccessProducts receipt fullSignal))
      (resourceToken emptySignal) frame).symm
  have step := comm_anywhere sourcePerm
  have flatten : StructuralCongruence
      (bag (receiptSuccessProducts receipt fullSignal :: frame))
      (receiptSuccessTarget receipt fullSignal frame) := by
    simpa [receiptSuccessProducts, receiptSuccessTarget] using
      bag_flatten_head
        [resourceToken receipt, resourceToken fullSignal] frame
  exact Reduces.equiv (StructuralCongruence.refl _) (by
    simpa [resourceToken, awaitResource,
      commRes_receiptSuccessProducts] using step) flatten

/-- Closed receipt judging takes exactly two ordinary COMM steps. -/
noncomputable def receiptSuccess_internalizes
    (receipt emptySignal fullSignal : Nat) (frame : List Pattern) :
    ReducesN 2
      (receiptSuccessSource receipt emptySignal fullSignal frame)
      (receiptSuccessTarget receipt fullSignal frame) := by
  exact .succ
    (receiptSuccess_receipt_step receipt emptySignal fullSignal frame)
    (.succ
      (receiptSuccess_signal_step receipt emptySignal fullSignal frame)
      (.zero _))

/-- Fail-closed compiler for one contract judgment.  The generated pair is
the pure-rho source and target; rejected receipts, mismatched receipt slots,
and occupied signal slots produce no code. -/
noncomputable def compileReceiptSuccess
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (contract : ReceiptSuccessContract Synapse)
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (synapse : Synapse) (frame : List Pattern) :
    Option (Pattern × Pattern) :=
  if contract.Authorizes state receiptSlot synapse &&
      decide (state.signals signalSlot = none) then
    let receipt := imageChannelCode
      (CreditImageChannel.receiptFull
        (Neuron := Neuron) (signalSlots := signalSlots)
        (creditBudget := creditBudget) receiptSlot synapse)
    let emptySignal := imageChannelCode
      (CreditImageChannel.signalEmpty
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (creditBudget := creditBudget) signalSlot)
    let fullSignal := imageChannelCode
      (CreditImageChannel.signalFull
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (creditBudget := creditBudget) signalSlot (post synapse))
    some (receiptSuccessSource receipt emptySignal fullSignal frame,
      receiptSuccessTarget receipt fullSignal frame)
  else none

theorem compileReceiptSuccess_isSome_iff
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (contract : ReceiptSuccessContract Synapse)
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (synapse : Synapse) (frame : List Pattern) :
    (compileReceiptSuccess contract post state receiptSlot signalSlot
      synapse frame).isSome ↔
      contract.Authorizes state receiptSlot synapse = true ∧
        state.signals signalSlot = none := by
  simp [compileReceiptSuccess]

/-- The accepted contract judgment is simultaneously a valid source-level
signal transition and a closed two-COMM pure-rho execution. -/
theorem authorizedReceiptSuccess_internalizes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (contract : ReceiptSuccessContract Synapse)
    (post : Synapse → Neuron)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (receiptSlot : Fin receiptSlots) (signalSlot : Fin signalSlots)
    (synapse : Synapse) (frame : List Pattern)
    (authorized : contract.Authorizes state receiptSlot synapse = true)
    (signalEmpty : state.signals signalSlot = none)
    (frameClosed : ∀ process ∈ frame, ClosedRhoProcess process) :
    let receipt := imageChannelCode
      (CreditImageChannel.receiptFull
        (Neuron := Neuron) (signalSlots := signalSlots)
        (creditBudget := creditBudget) receiptSlot synapse)
    let emptySignal := imageChannelCode
      (CreditImageChannel.signalEmpty
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (creditBudget := creditBudget) signalSlot)
    let fullSignal := imageChannelCode
      (CreditImageChannel.signalFull
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (creditBudget := creditBudget) signalSlot (post synapse))
    CausalStep post state (.signal signalSlot (post synapse))
        (issueSignal state signalSlot (post synapse)) ∧
      compileReceiptSuccess contract post state receiptSlot signalSlot
          synapse frame =
        some (receiptSuccessSource receipt emptySignal fullSignal frame,
          receiptSuccessTarget receipt fullSignal frame) ∧
      ClosedRhoProcess
        (receiptSuccessSource receipt emptySignal fullSignal frame) ∧
      ClosedRhoProcess (receiptSuccessTarget receipt fullSignal frame) ∧
      Nonempty (ReducesN 2
        (receiptSuccessSource receipt emptySignal fullSignal frame)
        (receiptSuccessTarget receipt fullSignal frame)) := by
  dsimp only
  refine ⟨?_, ?_, receiptSuccessSource_closed _ _ _ frame frameClosed,
    receiptSuccessTarget_closed _ _ frame frameClosed,
    ⟨receiptSuccess_internalizes _ _ _ frame⟩⟩
  · simp [CausalStep, causalIntegratedStep, signalEmpty]
  · simp [compileReceiptSuccess, authorized, signalEmpty]

/-- Rejected and accepted receipts inhabit structurally distinct rho names.
The closed judge therefore cannot accidentally authorize the rejected receipt
through name equivalence. -/
theorem rejectedReceipt_name_separated
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (contract : ReceiptSuccessContract Synapse)
    (slot : Fin receiptSlots) (accepted rejected : Synapse)
    (accepts : contract.accepts accepted = true)
    (rejects : contract.accepts rejected = false) :
    ¬ StructuralCongruence
      (imageChannelName
        (CreditImageChannel.receiptFull
          (Neuron := Neuron) (signalSlots := signalSlots)
          (creditBudget := creditBudget) slot rejected))
      (imageChannelName
        (CreditImageChannel.receiptFull
          (Neuron := Neuron) (signalSlots := signalSlots)
          (creditBudget := creditBudget) slot accepted)) := by
  intro equivalent
  have channelEqual := imageChannelName_structural_injective equivalent
  cases channelEqual
  rw [accepts] at rejects
  simp at rejects

/-- The concrete two-choice task accepts only the authored target receipt. -/
def choiceTargetReceiptContract : ReceiptSuccessContract ChoiceSynapse where
  accepts
    | .target => true
    | .distractor => false

@[simp]
theorem choiceTargetReceiptContract_accepts_target :
    choiceTargetReceiptContract.accepts .target = true := rfl

@[simp]
theorem choiceTargetReceiptContract_rejects_distractor :
    choiceTargetReceiptContract.accepts .distractor = false := rfl

theorem choiceReceiptNames_separated :
    ¬ StructuralCongruence
      (imageChannelName
        (CreditImageChannel.receiptFull
          (Neuron := Unit) (signalSlots := 1) (creditBudget := 4)
          (0 : Fin 1) ChoiceSynapse.distractor))
      (imageChannelName
        (CreditImageChannel.receiptFull
          (Neuron := Unit) (signalSlots := 1) (creditBudget := 4)
          (0 : Fin 1) ChoiceSynapse.target)) :=
  rejectedReceipt_name_separated choiceTargetReceiptContract 0
    .target .distractor rfl rfl

/-- Reachable states immediately after firing the two possible choices. -/
def causalTargetFiredState : CausalChoiceState :=
  replaceCore causalInitialChoiceState
    (issueReceipt causalInitialChoiceState.core 0 .target)

def causalDistractorFiredState : CausalChoiceState :=
  replaceCore causalInitialChoiceState
    (issueReceipt causalInitialChoiceState.core 0 .distractor)

theorem causalInitialChoice_fire_target :
    CausalStep choicePost causalInitialChoiceState (.fire 0 .target)
      causalTargetFiredState := by
  simp [CausalStep, causalIntegratedStep, causalTargetFiredState,
    integratedStep, causalInitialChoiceState, initialChoiceState, emptyReceipts,
    replaceCore, issueReceipt]

theorem causalInitialChoice_fire_distractor :
    CausalStep choicePost causalInitialChoiceState (.fire 0 .distractor)
      causalDistractorFiredState := by
  simp [CausalStep, causalIntegratedStep, causalDistractorFiredState,
    integratedStep, causalInitialChoiceState, initialChoiceState, emptyReceipts,
    replaceCore, issueReceipt]

@[simp]
theorem choiceTargetReceipt_authorized :
    choiceTargetReceiptContract.Authorizes
      causalTargetFiredState 0 .target = true := by
  simp [ReceiptSuccessContract.Authorizes, choiceTargetReceiptContract,
    causalTargetFiredState, causalInitialChoiceState, initialChoiceState,
    replaceCore, issueReceipt]

@[simp]
theorem choiceTargetFired_signal_empty :
    causalTargetFiredState.signals 0 = none := by
  simp [causalTargetFiredState, causalInitialChoiceState,
    replaceCore, emptySignals]

/-- Positive closed-contract canary: the reachable target receipt autonomously
admits a source-level signal and a closed two-COMM pure-rho execution. -/
theorem choiceTargetReceiptSuccess_closed_execution :
    CausalStep choicePost causalTargetFiredState (.signal 0 ())
        (issueSignal causalTargetFiredState 0 ()) ∧
      ∃ sourceImage targetImage : Pattern,
        compileReceiptSuccess choiceTargetReceiptContract choicePost
            causalTargetFiredState 0 0 .target [] =
          some (sourceImage, targetImage) ∧
        ClosedRhoProcess sourceImage ∧
        ClosedRhoProcess targetImage ∧
        Nonempty (ReducesN 2 sourceImage targetImage) := by
  have result := authorizedReceiptSuccess_internalizes
    choiceTargetReceiptContract choicePost causalTargetFiredState
    (0 : Fin 1) (0 : Fin 1) ChoiceSynapse.target []
    choiceTargetReceipt_authorized choiceTargetFired_signal_empty (by simp)
  dsimp only at result
  rcases result with
    ⟨sourceStep, compiled, sourceClosed, targetClosed, reduction⟩
  refine ⟨by simpa [choicePost] using sourceStep, ?_⟩
  exact ⟨_, _, compiled, sourceClosed, targetClosed, reduction⟩

/-- Negative closed-contract canary: firing the distractor creates a genuine
receipt, but the task contract emits no success deployment for it. -/
theorem choiceDistractorReceiptSuccess_rejected :
    compileReceiptSuccess choiceTargetReceiptContract choicePost
      causalDistractorFiredState 0 0 .distractor [] = none := by
  simp [compileReceiptSuccess, ReceiptSuccessContract.Authorizes,
    choiceTargetReceiptContract]

/-! ### Linear resource identity across the simulated step -/

/-- A consumed receipt is reissued on the empty-slot name, which is
structurally distinct from the occupied receipt name. -/
theorem causalRedeem_receiptName_changes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    ¬ StructuralCongruence
      (imageChannelName (receiptChannel source receiptSlot))
      (imageChannelName (receiptChannel target receiptSlot)) := by
  intro equivalent
  have sameChannel := imageChannelName_structural_injective equivalent
  rw [causalRedeem_source_receiptChannel step,
    causalRedeem_target_receiptChannel step] at sameChannel
  cases sameChannel

/-- A consumed success signal is likewise reissued on the empty-slot name. -/
theorem causalRedeem_signalName_changes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    ¬ StructuralCongruence
      (imageChannelName (signalChannel source signalSlot))
      (imageChannelName (signalChannel target signalSlot)) := by
  intro equivalent
  have sameChannel := imageChannelName_structural_injective equivalent
  rw [causalRedeem_source_signalChannel step,
    causalRedeem_target_signalChannel step] at sameChannel
  cases sameChannel

/-- A valid redemption is a genuine transfer, so the selected credit quantum
also moves to a structurally different owner channel. -/
theorem causalRedeem_creditName_changes
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    {post : Synapse → Neuron}
    {source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget}
    {receiptSlot : Fin receiptSlots} {signalSlot : Fin signalSlots}
    {creditSlot : Fin creditBudget} {synapse : Synapse}
    (step : CausalStep post source
      (.redeem receiptSlot signalSlot creditSlot synapse) target) :
    ¬ StructuralCongruence
      (imageChannelName (creditChannel source creditSlot))
      (imageChannelName (creditChannel target creditSlot)) := by
  rcases causal_redeem_core_step step with ⟨nextCore, coreStep⟩
  have ownerChanges :
      source.core.allocation creditSlot ≠ .synapse synapse :=
    ((step_redeem_iff post source.core nextCore
      receiptSlot creditSlot synapse).mp coreStep).2.2.1
  intro equivalent
  have sameChannel := imageChannelName_structural_injective equivalent
  rw [causalRedeem_target_creditChannel step] at sameChannel
  have ownerSame : source.core.allocation creditSlot = .synapse synapse := by
    simpa [creditChannel] using sameChannel
  exact ownerChanges ownerSame

/-- A minimal admitted image frame consists solely of resource messages
generated from typed credit-image channels.  Administrative handlers are
supplied by the compiler outside this untouched frame. -/
noncomputable def ResourceOnlyImageFrame
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (frame : List Pattern) : Prop :=
  ∃ channels : List (CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget),
    frame = channels.map fun channel =>
      resourceToken (imageChannelCode channel)

theorem resourceOnlyImageFrame_closed
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    {frame : List Pattern}
    (imageFrame : ResourceOnlyImageFrame
      (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) frame) :
    ∀ process ∈ frame, ClosedRhoProcess process := by
  rcases imageFrame with ⟨channels, rfl⟩
  intro process membership
  simp only [List.mem_map] at membership
  rcases membership with ⟨channel, _, rfl⟩
  exact resourceToken_closed (imageChannelCode channel)

/-! ## Image-context boundary -/

/-- A non-image context that knows the receipt name can consume it first and
leave the legitimate redemption handler without its first resource. -/
def predator (receipt : Nat) : Pattern :=
  awaitResource receipt rhoZero

/-- A bare receiver has the wrong constructor to be a compiled resource
message.  Thus the concrete predator below is outside the admitted untouched
image frame, not silently ruled out by the target calculus. -/
theorem predator_not_in_resourceOnlyImageFrame
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    {frame : List Pattern}
    (imageFrame : ResourceOnlyImageFrame
      (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) frame)
    (receipt : Nat) :
    predator receipt ∉ frame := by
  rcases imageFrame with ⟨channels, rfl⟩
  simp [predator, awaitResource, resourceToken, commIn, commOut]

/-- The predatory communication is an ordinary pure-rho step, not a new rule.
This is the exact interference that the admitted image-context discipline must
exclude when transporting linear ownership from cost-rho. -/
def predator_can_harvest_receipt
    (receipt signal donorCredit emptyReceipt emptySignal targetCredit : Nat)
    (frame : List Pattern) :
    Reduces
      (bag ([resourceToken receipt, predator receipt,
        redemptionHandler receipt signal donorCredit
          emptyReceipt emptySignal targetCredit,
        resourceToken signal, resourceToken donorCredit] ++ frame))
      (bag ([rhoZero,
        redemptionHandler receipt signal donorCredit
          emptyReceipt emptySignal targetCredit,
        resourceToken signal, resourceToken donorCredit] ++ frame)) := by
  have step := comm_at_head (markerName receipt) rhoZero rhoZero
    ([redemptionHandler receipt signal donorCredit
        emptyReceipt emptySignal targetCredit,
      resourceToken signal, resourceToken donorCredit] ++ frame)
  simpa [predator, resourceToken, awaitResource, commRes, rhoZero,
    semanticCommSubst, semanticSubstProc, semanticNormalizeProc,
    semanticNormalizeName, semanticNormalize_markerProcess,
    List.cons_append] using step

#print axioms markerName_closed
#print axioms markerName_structural_injective
#print axioms replacementRecord_roundTrip
#print axioms replacementSource_empty_frontier
#print axioms commRecord_preState_injective
#print axioms replacementRecord_reflects
#print axioms replacementSource_imageContext_frontier_iff
#print axioms redemption_imageContext_frontiers_iff
#print axioms redemption_logged_reflection
#print axioms redemption_internalizes
#print axioms imageTotalCredits_eq_budget
#print axioms decodedResourceChannels_stateResourceImage
#print axioms stateResourceImage_closed
#print axioms decodedAccountCredits_stateResourceImage
#print axioms decodedDerivedWeight_stateResourceImage
#print axioms decodedTotalCredits_stateResourceImage
#print axioms decodedTargetImage_solves_target_task
#print axioms decodedInitialImage_fails_target_task
#print axioms decodedDistractorImage_solves_distractor_task
#print axioms causalAction_internalizes
#print axioms causalRun_internalizes_pointwise
#print axioms causalControlHandlerPairs_map
#print axioms causalControlHandlerPairs_nodup_bounded
#print axioms causalControl_step_frontier_iff
#print axioms causalRun_fused_control_frontiers_exact
#print axioms causalTargetCreditEpisode_fused_frontiers_exact
#print axioms causalLearnThenReverse_fused_frontiers_exact
#print axioms qualitativeSupport_not_injective
#print axioms causalControlDeployment_isSome_eq_causalRun_isSome
#print axioms controlStateCode_ne_of_phase_ne
#print axioms causalControlFinal_structural_injective
#print axioms causalRun_internalizes_fused_control
#print axioms causalRun_success_iff_fused_control_execution
#print axioms invalidInitialRedemption_controlDeployment_rejected
#print axioms compileReceiptSuccess_isSome_iff
#print axioms authorizedReceiptSuccess_internalizes
#print axioms choiceTargetReceiptSuccess_closed_execution
#print axioms choiceDistractorReceiptSuccess_rejected
#print axioms internalization_preserves_countOnly_boundary
#print axioms causalRedeem_receiptName_changes
#print axioms causalRedeem_signalName_changes
#print axioms causalRedeem_creditName_changes
#print axioms predator_not_in_resourceOnlyImageFrame
#print axioms predator_can_harvest_receipt

end WeightedGSLTRhoInternalization
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
