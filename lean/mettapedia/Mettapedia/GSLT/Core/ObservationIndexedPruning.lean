import Mettapedia.Cybernetics.ObservedVariety
import Mathlib.Data.Finsupp.Basic

/-!
# Observation-indexed scheduling, aggregation, and pruning

Control transformations are lawful relative to a declared observation, not
in the abstract.  This module gives the common interface and separates three
questions:

* accounting: which occurrences moved from live to pruned state;
* certification: which guard authorized the transformation;
* semantics: whether the declared observer sees the same result.

The canaries establish a strict ladder.

* Reordering is invisible to a bag observer but visible to a stream observer.
* Duplicate pruning is invisible to a set observer but visible to a bag
  observer.
* Weight-preserving aggregation can merge equal atoms while retaining their
  summed weight, although the raw weighted-occurrence bag changes.

Thus `once`, set, bag, weighted-bag, and ordered-stream consumers license
different transformations.  A sound guard may be partial: failure to prove
redundancy rejects pruning without turning the branch into a refutation.
This is suitable for higher-order settings where redundancy itself need not
be decidable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ObservationIndexedPruning

open Mettapedia.Cybernetics

universe uRevision uItem uReceipt uView

/-- A proposed control transformation together with an opaque receipt.  The
receipt does not manufacture semantic preservation; a guard must connect it
to a named observer. -/
structure Change (Item : Type uItem) (Receipt : Type uReceipt) where
  source : List Item
  target : List Item
  receipt : Receipt

/-- Exact lawfulness at one observation boundary. -/
def LawfulAt {Item : Type uItem} {View : Type uView}
    (observer : Observer (List Item) View)
    {Receipt : Type uReceipt} (change : Change Item Receipt) : Prop :=
  observer.observe change.source = observer.observe change.target

/-- A conditional implementation guard whose accepted changes are proved
invisible to its declared observer.  `accepts` is a proposition rather than a
mandatory Boolean decision procedure, so an implementation may conservatively
decline when no certificate is available. -/
structure Guard {Item : Type uItem} {View : Type uView}
    (observer : Observer (List Item) View) (Receipt : Type uReceipt) where
  accepts : Change Item Receipt -> Prop
  sound : forall change, accepts change -> LawfulAt observer change

namespace Guard

variable {Item : Type uItem} {View : Type uView}
  {observer : Observer (List Item) View} {Receipt : Type uReceipt}

/-- Every sound guard rejects a transformation known to change its
observation. -/
theorem rejects_of_not_lawful (guard : Guard observer Receipt)
    (change : Change Item Receipt) (changesObservation :
      Not (LawfulAt observer change)) : Not (guard.accepts change) := by
  intro accepted
  exact changesObservation (guard.sound change accepted)

end Guard

/-- Lawfulness for a finer observation implies lawfulness after any
postcomposition.  The converse is intentionally false in the canaries. -/
theorem lawfulAt_postcompose
    {Item : Type uItem} {Fine : Type uView} {Coarse : Type*}
    (observer : Observer (List Item) Fine) (summarize : Fine -> Coarse)
    {Receipt : Type uReceipt} {change : Change Item Receipt}
    (lawful : LawfulAt observer change) :
    LawfulAt (observer.postcompose summarize) change := by
  exact congrArg summarize lawful

/-! ## Occurrence accounting -/

/-- A pruning proposal additionally names the removed occurrence bag and
proves that it accounts for the source bag exactly. -/
structure PruningChange (Item : Type uItem) (Receipt : Type uReceipt)
    extends Change Item Receipt where
  removed : Multiset Item
  accounting : (source : Multiset Item) = (target : Multiset Item) + removed

/-- The three disjoint accounting classes relevant to a finite control
prefix. -/
structure Account (Item : Type uItem) where
  emitted : Multiset Item
  latent : Multiset Item
  pruned : Multiset Item

namespace Account

variable {Item : Type uItem}

/-- Total accounted occurrence mass. -/
def total (account : Account Item) : Multiset Item :=
  account.emitted + account.latent + account.pruned

/-- Before a certified prune, removed work is still latent. -/
def before (emitted kept removed alreadyPruned : Multiset Item) :
    Account Item where
  emitted := emitted
  latent := kept + removed
  pruned := alreadyPruned

/-- After a certified prune, the same work is explicitly classified as
pruned rather than silently erased. -/
def after (emitted kept removed alreadyPruned : Multiset Item) :
    Account Item where
  emitted := emitted
  latent := kept
  pruned := alreadyPruned + removed

/-- Reclassification from latent to receipted-pruned conserves total
occurrence mass. -/
theorem prune_reclassification_conserves
    (emitted kept removed alreadyPruned : Multiset Item) :
    (after emitted kept removed alreadyPruned).total =
      (before emitted kept removed alreadyPruned).total := by
  simp [total, before, after]
  ac_rfl

end Account

/-! ## Revision-current asynchronous advice

An external or threaded watcher may construct a proposal, but a proposal is
not pruning authority.  Admission separately requires that the proposal was
formed at the current revision, describes the current live occurrence list,
and preserves the declared observation.  Thread identity and arrival order
are deliberately absent from the semantics.
-/

/-- A watcher proposes one exactly accounted change at the revision it
observed.  Its receipt is evidence for a checker, not authority by itself. -/
structure Proposal (Revision : Type uRevision) (Item : Type uItem)
    (Receipt : Type uReceipt) extends PruningChange Item Receipt where
  observedRevision : Revision

/-- Runtime state relevant to revisioned pruning.  Removed occurrences remain
in the accounting ledger, and accepted receipts remain inspectable. -/
structure Snapshot (Revision : Type uRevision) (Item : Type uItem)
    (Receipt : Type uReceipt) where
  revision : Revision
  live : List Item
  pruned : Multiset Item
  receipts : List Receipt

/-- The proof object separating asynchronous advice from pruning authority. -/
structure Admission {Revision : Type uRevision} {Item : Type uItem}
    {View : Type uView} {Receipt : Type uReceipt}
    (observer : Observer (List Item) View)
    (snapshot : Snapshot Revision Item Receipt)
    (proposal : Proposal Revision Item Receipt) : Prop where
  revisionCurrent : proposal.observedRevision = snapshot.revision
  sourceCurrent : proposal.source = snapshot.live
  lawful : LawfulAt observer proposal.toPruningChange.toChange

/-- A partial checker may conservatively decline.  Every accepted proposal is
revision-current, source-current, and observationally lawful. -/
structure Checker {Revision : Type uRevision} {Item : Type uItem}
    {View : Type uView} {Receipt : Type uReceipt}
    (observer : Observer (List Item) View) where
  accepts : Snapshot Revision Item Receipt ->
    Proposal Revision Item Receipt -> Prop
  revisionCurrent : forall {snapshot proposal},
    accepts snapshot proposal ->
      proposal.observedRevision = snapshot.revision
  sourceCurrent : forall {snapshot proposal},
    accepts snapshot proposal -> proposal.source = snapshot.live
  sound : forall {snapshot proposal}, accepts snapshot proposal ->
    LawfulAt observer proposal.toPruningChange.toChange

namespace Checker

variable {Revision : Type uRevision} {Item : Type uItem}
  {View : Type uView} {Receipt : Type uReceipt}
  {observer : Observer (List Item) View}

/-- Successful checking constructs the only object accepted by the pruning
transition. -/
def admission
    (checker : @Checker Revision Item View Receipt observer)
    {snapshot : Snapshot Revision Item Receipt}
    {proposal : Proposal Revision Item Receipt}
    (accepted : checker.accepts snapshot proposal) :
    Admission observer snapshot proposal where
  revisionCurrent := checker.revisionCurrent accepted
  sourceCurrent := checker.sourceCurrent accepted
  lawful := checker.sound accepted

/-- A checker satisfying the revision law cannot accept stale advice. -/
theorem rejectsStale
    (checker : @Checker Revision Item View Receipt observer)
    {snapshot : Snapshot Revision Item Receipt}
    {proposal : Proposal Revision Item Receipt}
    (stale : proposal.observedRevision ≠ snapshot.revision) :
    Not (checker.accepts snapshot proposal) := by
  intro accepted
  exact stale (checker.revisionCurrent accepted)

end Checker

/-- Apply an admitted proposal.  The live list changes, while removed
occurrences and the evidence receipt move into explicit ledgers. -/
def applyProposal {Revision : Type uRevision} {Item : Type uItem}
    {View : Type uView} {Receipt : Type uReceipt}
    (observer : Observer (List Item) View)
    (snapshot : Snapshot Revision Item Receipt)
    (proposal : Proposal Revision Item Receipt)
    (_ : Admission observer snapshot proposal) :
    Snapshot Revision Item Receipt where
  revision := snapshot.revision
  live := proposal.target
  pruned := snapshot.pruned + proposal.removed
  receipts := snapshot.receipts ++ [proposal.receipt]

/-- Accepted pruning reclassifies occurrence mass; it never erases it. -/
theorem applyProposal_conserves
    {Revision : Type uRevision} {Item : Type uItem}
    {View : Type uView} {Receipt : Type uReceipt}
    (observer : Observer (List Item) View)
    (snapshot : Snapshot Revision Item Receipt)
    (proposal : Proposal Revision Item Receipt)
    (admission : Admission observer snapshot proposal) :
    ((applyProposal observer snapshot proposal admission).live :
        Multiset Item) +
      (applyProposal observer snapshot proposal admission).pruned =
    (snapshot.live : Multiset Item) + snapshot.pruned := by
  change (proposal.target : Multiset Item) +
      (snapshot.pruned + proposal.removed) =
    (snapshot.live : Multiset Item) + snapshot.pruned
  rw [← admission.sourceCurrent, proposal.accounting]
  ac_rfl

/-- Stale advice has no admission, independently of what evidence it carries. -/
theorem stale_has_no_admission
    {Revision : Type uRevision} {Item : Type uItem}
    {View : Type uView} {Receipt : Type uReceipt}
    {observer : Observer (List Item) View}
    {snapshot : Snapshot Revision Item Receipt}
    {proposal : Proposal Revision Item Receipt}
    (stale : proposal.observedRevision ≠ snapshot.revision) :
    Not (Admission observer snapshot proposal) := by
  intro admission
  exact stale admission.revisionCurrent

/-! ## Weighted aggregation -/

/-- Aggregate weighted occurrences by atom.  This is the algebraic readout
through which weight-preserving merge is observed. -/
noncomputable def aggregateWeights {Atom Weight : Type*} [DecidableEq Atom]
    [AddCommMonoid Weight] : List (Atom × Weight) -> Atom →₀ Weight
  | [] => 0
  | (atom, weight) :: rest =>
      Finsupp.single atom weight + aggregateWeights rest

/-! ## Discriminating observer canaries -/

namespace Canary

def streamObserver : Observer (List Bool) (List Bool) :=
  Observer.identity (List Bool)

def bagObserver : Observer (List Bool) (Multiset Bool) where
  observe := fun occurrences => (occurrences : Multiset Bool)

def setObserver : Observer (List Bool) (Finset Bool) where
  observe := List.toFinset

/-- A pure scheduling change: same occurrences, different order. -/
def reorder : Change Bool Unit where
  source := [true, false]
  target := [false, true]
  receipt := ()

theorem reorder_lawful_at_bag : LawfulAt bagObserver reorder := by
  change (([true, false] : List Bool) : Multiset Bool) =
    (([false, true] : List Bool) : Multiset Bool)
  decide

theorem reorder_not_lawful_at_stream :
    Not (LawfulAt streamObserver reorder) := by
  change Not (([true, false] : List Bool) = [false, true])
  decide

/-- Removing one duplicate is exactly accounted, not silently discarded. -/
def removeDuplicate : PruningChange Bool Unit where
  source := [true, true]
  target := [true]
  receipt := ()
  removed := {true}
  accounting := by decide

theorem duplicate_prune_lawful_at_set :
    LawfulAt setObserver removeDuplicate.toChange := by
  change ([true, true] : List Bool).toFinset = ([true] : List Bool).toFinset
  decide

theorem duplicate_prune_not_lawful_at_bag :
    Not (LawfulAt bagObserver removeDuplicate.toChange) := by
  change Not ((([true, true] : List Bool) : Multiset Bool) =
    (([true] : List Bool) : Multiset Bool))
  decide

/-- The set guard may authorize this exact duplicate prune. -/
def duplicateSetGuard : Guard setObserver Unit where
  accepts := fun change => change = removeDuplicate.toChange
  sound := by
    intro change accepted
    subst change
    exact duplicate_prune_lawful_at_set

/-- No sound bag guard can authorize the same unweighted duplicate prune. -/
theorem every_sound_bag_guard_rejects_duplicate
    (guard : Guard bagObserver Unit) :
    Not (guard.accepts removeDuplicate.toChange) :=
  guard.rejects_of_not_lawful _ duplicate_prune_not_lawful_at_bag

abbrev WeightedOccurrence := Bool × Nat

noncomputable def weightedObserver :
    Observer (List WeightedOccurrence) (Bool →₀ Nat) where
  observe := aggregateWeights

def rawWeightedBagObserver :
    Observer (List WeightedOccurrence) (Multiset WeightedOccurrence) where
  observe := fun occurrences => (occurrences : Multiset WeightedOccurrence)

/-- Two equal atoms are merged by adding their weights. -/
def mergeWeights : Change WeightedOccurrence Unit where
  source := [(true, 2), (true, 3)]
  target := [(true, 5)]
  receipt := ()

theorem merge_lawful_at_aggregated_weight :
    LawfulAt weightedObserver mergeWeights := by
  ext atom
  cases atom <;> simp [weightedObserver, mergeWeights,
    aggregateWeights]

theorem merge_not_lawful_at_raw_occurrence_bag :
    Not (LawfulAt rawWeightedBagObserver mergeWeights) := by
  change Not ((([(true, 2), (true, 3)] : List WeightedOccurrence) :
      Multiset WeightedOccurrence) =
    (([(true, 5)] : List WeightedOccurrence) : Multiset WeightedOccurrence))
  decide

/-- A guard for the aggregate-weight observation can authorize the merge, while
the raw occurrence-bag observer cannot. -/
noncomputable def aggregateWeightGuard : Guard weightedObserver Unit where
  accepts := fun change => change = mergeWeights
  sound := by
    intro change accepted
    subst change
    exact merge_lawful_at_aggregated_weight

theorem every_raw_bag_guard_rejects_weight_merge
    (guard : Guard rawWeightedBagObserver Unit) :
    Not (guard.accepts mergeWeights) :=
  guard.rejects_of_not_lawful _ merge_not_lawful_at_raw_occurrence_bag

end Canary

end Mettapedia.GSLT.Core.ObservationIndexedPruning

#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.Guard.rejects_of_not_lawful
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.Account.prune_reclassification_conserves
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.applyProposal_conserves
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.stale_has_no_admission
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.Canary.reorder_lawful_at_bag
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.Canary.duplicate_prune_not_lawful_at_bag
#print axioms Mettapedia.GSLT.Core.ObservationIndexedPruning.Canary.merge_lawful_at_aggregated_weight
