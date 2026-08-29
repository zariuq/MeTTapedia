import Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily
import Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers

/-!
# Certified dispositions after an atomic conflict

An atomic conflict has one immediate meaning: the live snapshot and the
complete authored work list remain unchanged.  What happens next is a
controller choice, and the alternatives require different evidence:

* suspension retains the exact deferred receipt;
* refresh captures a new proposal whose certificate is indexed by the full
  current state;
* serial realization runs one permutation of the batch from that current
  state and proves agreement at the fresh state observer; and
* merge reruns an isolated contextual program from the current state, applies
  an authored permutation-invariant delta resolver, covers the exact pending
  occurrences, and proves agreement at the fresh state observer.

The envelope deliberately chooses none of these as a default.  In particular,
changing a revision is not refresh, serializability is not merge authority,
and a successful state merge is not authorization to perform the retained
external intents.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AtomicDeferredDisposition

open Mettapedia.GSLT.Core.AtomicCertifiedBatchFamily
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers

universe uRevision uItem uGuard uView uState uStateView uAccount
universe uDelta uAnswer uIntent

/-! ## The exact deferred context -/

/-- A conflict over a source-indexed family.  The proposal, complete live
snapshot, and proof of mismatch are retained together. -/
structure DeferredContext
    (Revision : Type uRevision)
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    (family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch) where
  proposal : CapturedFamilyProposal Revision family
  live : Snapshot Revision State
  conflict : ¬ Matches
    (AtomicCertifiedBatchFamily.transactionSpec
      (Revision := Revision) (family := family)) proposal live

namespace DeferredContext

variable
    {Revision : Type uRevision}
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard View}
    {semantics : ExecutionSemantics Item State StateView}
    {demand : Item → Account} {source : Account} {batch : List Item}
    {family : BulkCertifiedBatchFamily contract semantics Account demand
      source batch}

/-- The underlying atomic decision remains the proof-relevant deferred
constructor; no controller action has happened yet. -/
def decision (context : DeferredContext Revision family) :
    Decision
      (AtomicCertifiedBatchFamily.transactionSpec
        (Revision := Revision) (family := family))
      context.proposal context.live :=
  .deferred context.conflict

/-- The authored position-sensitive work retained by the conflict. -/
def pending (context : DeferredContext Revision family) : List Item :=
  context.decision.orderedLedger.pending

@[simp] theorem pending_eq_batch (context : DeferredContext Revision family) :
    context.pending = batch :=
  rfl

@[simp] theorem physicalSnapshot_eq_live
    (context : DeferredContext Revision family) :
    context.decision.physicalSnapshot = context.live :=
  rfl

/-! ## Fresh retry authority -/

/-- A refresh receipt is tied to the complete current snapshot.  It is not a
copy of the old proposal with a different revision. -/
structure FreshRetry (context : DeferredContext Revision family) where
  proposal : CapturedFamilyProposal Revision family
  capturedExact : proposal.captured = context.live

/-- Construct the canonical fresh receipt from the live snapshot. -/
def freshRetry (context : DeferredContext Revision family) :
    FreshRetry context where
  proposal := captureLive context.live
  capturedExact := rfl

theorem FreshRetry.matches
    {context : DeferredContext Revision family}
    (retry : FreshRetry context) :
    Matches
      (AtomicCertifiedBatchFamily.transactionSpec
        (Revision := Revision) (family := family))
      retry.proposal context.live := by
  exact
    ⟨congrArg Snapshot.revision retry.capturedExact.symm,
      congrArg Snapshot.state retry.capturedExact.symm⟩

/-! ## Fresh serial realization -/

/-- A serial fallback is a new semantic run from the current state.  Its
physical target may differ from the family's canonical target, but it must
agree at the declared state observer and use exactly the pending occurrence
bag. -/
structure FreshSerialReceipt (context : DeferredContext Revision family) where
  ordering : List Item
  sameOccurrences : ordering.Perm context.pending
  target : State
  run : semantics.run context.live.state ordering target
  observesFreshTarget :
    semantics.observe target =
      semantics.observe (family.targetAt context.live.state)
  nextRevision : Revision
  advanced : nextRevision ≠ context.live.revision

namespace FreshSerialReceipt

variable {context : DeferredContext Revision family}

def after (receipt : FreshSerialReceipt context) : Snapshot Revision State :=
  ⟨receipt.nextRevision, receipt.target⟩

/-- Serial execution retains every occurrence, although it may choose a
different authored ordering. -/
theorem occurrenceBag_exact (receipt : FreshSerialReceipt context) :
    (receipt.ordering : Multiset Item) = (context.pending : Multiset Item) :=
  Quot.sound receipt.sameOccurrences

/-- The fresh family certificate supplies the exact account remainder for a
complete serial realization.  This is a resource account, not an engine trace
cost receipt. -/
def accountAfter (_receipt : FreshSerialReceipt context) : Account :=
  (family.certifiedAt context.live.state).resources.frame

theorem account_conservation (receipt : FreshSerialReceipt context) :
    source = batchDemand demand batch + receipt.accountAfter :=
  (family.certifiedAt context.live.state).resources.source_eq

/-- Every permutation licensed by the fresh source-indexed certificate has a
serial receipt.  The theorem returns the operational target rather than
choosing one globally. -/
theorem exists_for_ordering
    (context : DeferredContext Revision family)
    (ordering : List Item) (sameOccurrences : ordering.Perm context.pending)
    (nextRevision : Revision) (advanced : nextRevision ≠ context.live.revision) :
    Nonempty (FreshSerialReceipt context) := by
  have permutesBatch : ordering.Perm batch := by
    simpa using sameOccurrences
  obtain ⟨target, run, observed⟩ :=
    (family.certifiedAt context.live.state).executionSerializable.2
      ordering permutesBatch
  exact ⟨{
    ordering := ordering
    sameOccurrences := sameOccurrences
    target := target
    run := run
    observesFreshTarget := observed
    nextRevision := nextRevision
    advanced := advanced }⟩

end FreshSerialReceipt

/-! ## Fresh contextual merge -/

/-- A merge receipt is stronger than a serial receipt in one direction and
weaker in another.  It requires an explicit isolated program and an
order-invariant delta resolver, while retaining every contextual world and
external intent.  It authorizes only the resulting state snapshot. -/
structure FreshMergeReceipt
    (context : DeferredContext Revision family)
    {Delta : Type uDelta} {Answer : Type uAnswer} {Intent : Type uIntent}
    (algebra : DeltaAlgebra State Delta)
    (resolver : AlternativeMerge Delta)
    (program : Program State Delta Answer Intent)
    (workOf : DeltaWorld State Delta Answer Intent → Item) where
  merged : Merged State Delta Answer Intent
  resolved :
    mergeWorlds algebra context.live.state resolver
        (runWorlds algebra program context.live.state) = some merged
  coversPending :
    (runWorlds algebra program context.live.state).map workOf = context.pending
  observesFreshTarget :
    semantics.observe merged.state =
      semantics.observe (family.targetAt context.live.state)
  nextRevision : Revision
  advanced : nextRevision ≠ context.live.revision

namespace FreshMergeReceipt

variable
    {context : DeferredContext Revision family}
    {Delta : Type uDelta} {Answer : Type uAnswer} {Intent : Type uIntent}
    {algebra : DeltaAlgebra State Delta}
    {resolver : AlternativeMerge Delta}
    {program : Program State Delta Answer Intent}
    {workOf : DeltaWorld State Delta Answer Intent → Item}

def after
    (receipt : FreshMergeReceipt context algebra resolver program workOf) :
    Snapshot Revision State :=
  ⟨receipt.nextRevision, receipt.merged.state⟩

/-- The actual isolated worlds are retained inside a successful merge; state
resolution does not erase their answers or deferred intents. -/
theorem worlds_exact
    (receipt : FreshMergeReceipt context algebra resolver program workOf) :
    receipt.merged.worlds = runWorlds algebra program context.live.state := by
  have resolved := receipt.resolved
  unfold mergeWorlds at resolved
  cases resolution : resolver.merge
      (worldDeltas (runWorlds algebra program context.live.state)) with
  | none => simp [resolution] at resolved
  | some delta =>
      simp only [resolution, Option.map_some, Option.some.injEq] at resolved
      rw [← resolved]

/-- The authored occurrence projection of the retained worlds is exactly the
ordered work returned by the atomic conflict. -/
theorem occurrenceOrder_exact
    (receipt : FreshMergeReceipt context algebra resolver program workOf) :
    receipt.merged.worlds.map workOf = context.pending := by
  rw [receipt.worlds_exact]
  exact receipt.coversPending

def accountAfter
    (_receipt : FreshMergeReceipt context algebra resolver program workOf) :
    Account :=
  (family.certifiedAt context.live.state).resources.frame

theorem account_conservation
    (receipt : FreshMergeReceipt context algebra resolver program workOf) :
    source = batchDemand demand batch + receipt.accountAfter :=
  (family.certifiedAt context.live.state).resources.source_eq

/-- Reordering the isolated worlds cannot change the resolver result. -/
theorem resolver_is_order_independent
    (_receipt : FreshMergeReceipt context algebra resolver program workOf)
    {reordered : List (DeltaWorld State Delta Answer Intent)}
    (permutation : reordered.Perm
      (runWorlds algebra program context.live.state)) :
    resolver.merge (worldDeltas reordered) =
      resolver.merge
        (worldDeltas (runWorlds algebra program context.live.state)) :=
  resolver.merge_worldDeltas_perm permutation

end FreshMergeReceipt

/-! ## One policy-neutral envelope -/

/-- A space kind supplies its delta algebra and isolated program, but the
controller still has to choose one evidence-bearing disposition. -/
inductive Disposition
    (context : DeferredContext Revision family)
    {Delta : Type uDelta} {Answer : Type uAnswer} {Intent : Type uIntent}
    (algebra : DeltaAlgebra State Delta)
    (resolver : AlternativeMerge Delta)
    (program : Program State Delta Answer Intent)
    (workOf : DeltaWorld State Delta Answer Intent → Item) where
  | suspend
  | refresh (receipt : FreshRetry context)
  | serialize (receipt : FreshSerialReceipt context)
  | merge (receipt : FreshMergeReceipt context algebra resolver program workOf)

namespace Disposition

variable
    {context : DeferredContext Revision family}
    {Delta : Type uDelta} {Answer : Type uAnswer} {Intent : Type uIntent}
    {algebra : DeltaAlgebra State Delta}
    {resolver : AlternativeMerge Delta}
    {program : Program State Delta Answer Intent}
    {workOf : DeltaWorld State Delta Answer Intent → Item}

/-- Refresh is still pending work.  Only serial realization or certified
merge moves occurrences to the executed side. -/
def executedWork :
    Disposition context algebra resolver program workOf → List Item
  | .suspend => []
  | .refresh _ => []
  | .serialize receipt => receipt.ordering
  | .merge _ => context.pending

def pendingWork :
    Disposition context algebra resolver program workOf → List Item
  | .suspend => context.pending
  | .refresh _ => context.pending
  | .serialize _ => []
  | .merge _ => []

/-- Every disposition partitions the exact deferred occurrence bag. -/
theorem occurrenceBag_accounts
    (disposition : Disposition context algebra resolver program workOf) :
    (disposition.executedWork : Multiset Item) +
        (disposition.pendingWork : Multiset Item) =
      (context.pending : Multiset Item) := by
  cases disposition with
  | suspend => simp [executedWork, pendingWork]
  | refresh _ => simp [executedWork, pendingWork]
  | serialize receipt =>
      simpa [executedWork, pendingWork] using receipt.occurrenceBag_exact
  | merge _ => simp [executedWork, pendingWork]

/-- Suspension and refresh leave physical state untouched.  Serial and merge
expose only their separately certified successor snapshots. -/
def physicalSnapshot :
    Disposition context algebra resolver program workOf →
      Snapshot Revision State
  | .suspend => context.live
  | .refresh _ => context.live
  | .serialize receipt => receipt.after
  | .merge receipt => receipt.after

/-- Funding remains untouched while work is suspended or merely refreshed.
A completed serial or merge realization exposes the fresh family's exact
resource frame. -/
def accountAfter :
    Disposition context algebra resolver program workOf → Account
  | .suspend => source
  | .refresh _ => source
  | .serialize receipt => receipt.accountAfter
  | .merge receipt => receipt.accountAfter

def chargedDemand :
    Disposition context algebra resolver program workOf → Account
  | .suspend => 0
  | .refresh _ => 0
  | .serialize _ => batchDemand demand batch
  | .merge _ => batchDemand demand batch

/-- The envelope conserves the independent resource account in every branch.
This says nothing about native engine-spent trace cost. -/
theorem account_conservation
    (disposition : Disposition context algebra resolver program workOf) :
    source = disposition.chargedDemand + disposition.accountAfter := by
  cases disposition with
  | suspend => simp [chargedDemand, accountAfter]
  | refresh _ => simp [chargedDemand, accountAfter]
  | serialize receipt => exact receipt.account_conservation
  | merge receipt => exact receipt.account_conservation

end Disposition

/-! ## Discriminating controls -/

namespace Canary

def boolFact : Bool → Nat
  | false => 1
  | true => 2

def factTarget (initial : Finset Nat) (ordering : List Bool) : Finset Nat :=
  initial ∪ (ordering.map boolFact).toFinset

def boolBagObserver : Mettapedia.Cybernetics.Observer
    (List Bool) (Multiset Bool) where
  observe items := (items : Multiset Bool)

def completeBoolBag : Contract Bool Unit (Multiset Bool) where
  observer := boolBagObserver
  demand := { completion := .completeBag }

def factSemantics : ExecutionSemantics Bool (Finset Nat) (Finset Nat) where
  run initial ordering target := target = factTarget initial ordering
  observe := id

def factDemand (_item : Bool) : Nat := 1
def factSource : Nat := 2
def factBatch : List Bool := [false, true]

theorem factTarget_perm (initial : Finset Nat)
    {first second : List Bool} (permutation : first.Perm second) :
    factTarget initial first = factTarget initial second := by
  unfold factTarget
  rw [List.toFinset_eq_of_perm _ _ (permutation.map boolFact)]

theorem factSerializes (initial : Finset Nat) :
    factSemantics.SerializesTo initial factBatch
      (factTarget initial factBatch) := by
  constructor
  · rfl
  · intro ordering permutation
    exact ⟨factTarget initial ordering, rfl,
      factTarget_perm initial permutation⟩

def factCertifiedAt (initial : Finset Nat) :
    CertifiedBatch completeBoolBag factSemantics initial
      (factTarget initial factBatch) Nat factDemand factSource factBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := factSerializes initial
  resources :=
    { frame := 0
      source_eq := by decide }

def factFamily :
    BulkCertifiedBatchFamily completeBoolBag factSemantics Nat factDemand
      factSource factBatch where
  targetAt initial := factTarget initial factBatch
  certifiedAt := factCertifiedAt
  bulkAuthorizedAt initial :=
    (factCertifiedAt initial).completeBag_dispatches_bulk rfl

def oldProposal : CapturedFamilyProposal Nat factFamily :=
  ⟨⟨7, ∅⟩⟩

def live : Snapshot Nat (Finset Nat) :=
  ⟨8, {0}⟩

def conflict : ¬ Matches
    (AtomicCertifiedBatchFamily.transactionSpec
      (Revision := Nat) (family := factFamily)) oldProposal live := by
  intro current
  have impossible := current.revision_eq
  norm_num [AtomicCertifiedBatchFamily.transactionSpec, oldProposal, live]
    at impossible

def context : DeferredContext Nat factFamily where
  proposal := oldProposal
  live := live
  conflict := conflict

def serialReceipt : FreshSerialReceipt context where
  ordering := [true, false]
  sameOccurrences := by decide
  target := {0, 1, 2}
  run := by
    change ({0, 1, 2} : Finset Nat) = factTarget {0} [true, false]
    decide
  observesFreshTarget := by decide
  nextRevision := 9
  advanced := by decide

open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary

def workOf
    (world : DeltaWorld (Finset Nat) (Finset Nat) Bool Bool) : Bool :=
  world.answer

def mergeReceipt :
    FreshMergeReceipt context factAlgebra (joinMerge (Finset Nat)) twoFacts
      workOf where
  merged :=
    { worlds := runWorlds factAlgebra twoFacts live.state
      delta := {1, 2}
      state := {0, 1, 2} }
  resolved := by decide
  coversPending := by decide
  observesFreshTarget := by decide
  nextRevision := 9
  advanced := by decide

abbrev TestDisposition :=
  Disposition context factAlgebra (joinMerge (Finset Nat)) twoFacts workOf

def suspended : TestDisposition := .suspend
def refreshed : TestDisposition := .refresh context.freshRetry
def serialized : TestDisposition := .serialize serialReceipt
def merged : TestDisposition := .merge mergeReceipt

/-- Positive control: all four policies account for the same two deferred
occurrences, while only serial and merge advance physical state. -/
theorem four_dispositions_preserve_occurrences_and_authority_phases :
    (suspended.executedWork : Multiset Bool) = 0 ∧
      suspended.pendingWork = factBatch ∧
      refreshed.physicalSnapshot = live ∧
      (serialized.executedWork : Multiset Bool) =
        (factBatch : Multiset Bool) ∧
      serialized.physicalSnapshot = ⟨9, {0, 1, 2}⟩ ∧
      merged.physicalSnapshot = ⟨9, {0, 1, 2}⟩ ∧
      mergeReceipt.merged.worlds.map workOf = factBatch := by
  decide

/-- Serial fallback may use a different physical ordering while remaining
equal at the complete-bag observer.  The ordered difference is not erased
from its receipt. -/
theorem serial_observer_equivalence_is_not_order_equality :
    serialReceipt.ordering ≠ factBatch ∧
      (serialReceipt.ordering : Multiset Bool) =
        (factBatch : Multiset Bool) ∧
      factSemantics.observe serialReceipt.target =
        factSemantics.observe (factFamily.targetAt live.state) := by
  decide

/-- The old proposal is not a fresh retry receipt for the changed live
snapshot. -/
theorem stale_proposal_cannot_masquerade_as_refresh :
    oldProposal.captured ≠ live := by
  decide

/-- A first-occurrence resolver cannot occupy the unordered merge boundary. -/
theorem first_occurrence_is_not_merge_authority :
    ¬ ∃ resolver : AlternativeMerge Bool,
      resolver.merge =
        Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary.firstMerge := by
  rintro ⟨resolver, equality⟩
  apply
    Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary.firstMerge_not_permutationInvariant
  intro first second permutation
  calc
    Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary.firstMerge first =
        resolver.merge first := congrFun equality.symm first
    _ = resolver.merge second := resolver.permutationInvariant permutation
    _ = Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary.firstMerge
        second := congrFun equality second

/-- All four branches conserve the separate funding account; refresh alone
does not consume it. -/
theorem four_dispositions_conserve_funding :
    factSource = suspended.chargedDemand + suspended.accountAfter ∧
      factSource = refreshed.chargedDemand + refreshed.accountAfter ∧
      factSource = serialized.chargedDemand + serialized.accountAfter ∧
      factSource = merged.chargedDemand + merged.accountAfter :=
  ⟨suspended.account_conservation, refreshed.account_conservation,
    serialized.account_conservation, merged.account_conservation⟩

end Canary

#print axioms DeferredContext.FreshRetry.matches
#print axioms FreshSerialReceipt.occurrenceBag_exact
#print axioms FreshSerialReceipt.exists_for_ordering
#print axioms FreshMergeReceipt.worlds_exact
#print axioms FreshMergeReceipt.resolver_is_order_independent
#print axioms Disposition.occurrenceBag_accounts
#print axioms Disposition.account_conservation
#print axioms Canary.four_dispositions_preserve_occurrences_and_authority_phases
#print axioms Canary.serial_observer_equivalence_is_not_order_equality
#print axioms Canary.stale_proposal_cannot_masquerade_as_refresh
#print axioms Canary.first_occurrence_is_not_merge_authority
#print axioms Canary.four_dispositions_conserve_funding

end DeferredContext

end Mettapedia.GSLT.Core.AtomicDeferredDisposition
