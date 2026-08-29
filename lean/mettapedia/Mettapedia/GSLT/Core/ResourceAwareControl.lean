import Mathlib.Data.Multiset.UnionInter
import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Dynamics.IndexedEventValuation

/-!
# Resource-aware observation control

Parallel activation needs two independent certificates.

* Semantic serializability says that every ordering of the selected
  occurrences has the same declared observation.
* Linear-resource separation says that the exact occurrence demands fit in
  one source inventory.

Neither certificate implies the other.  A numeric cost or other event
valuation is a third, read-only channel: it accounts for an already selected
history and does not create semantic or resource authority.

This module joins those interfaces without choosing a queue discipline, a
worker representation, or a surface syntax.  An unfunded batch remains
pending with its exact occurrence multiplicity.  It is not converted into an
empty semantic result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ResourceAwareControl

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uItem uGuard uView uAccount uResource uGrade uState uStateView

/-! ## Exact additive-account separation -/

/-! An account may be an occurrence multiset, a vector budget, an energy
quantity, or any other additive resource carrier.  Keeping the account type
abstract is what lets one wave carry several independent accounts without
pretending that they share one scalar order. -/

/-- Total account demand of an occurrence list.  Equal item values at
different list positions contribute separately. -/
def batchDemand {Item : Type uItem} {Account : Type uAccount}
    [AddMonoid Account] (demand : Item -> Account) (batch : List Item) :
    Account :=
  (batch.map demand).sum

@[simp] theorem batchDemand_nil {Item : Type uItem} {Account : Type uAccount}
    [AddMonoid Account] (demand : Item -> Account) :
    batchDemand demand [] = 0 :=
  rfl

@[simp] theorem batchDemand_cons {Item : Type uItem}
    {Account : Type uAccount} [AddMonoid Account] (demand : Item -> Account)
    (item : Item) (batch : List Item) :
    batchDemand demand (item :: batch) =
      demand item + batchDemand demand batch :=
  rfl

/-- One common-source decomposition for an exact list of occurrence demands.
The retained frame is the resource inventory untouched by the batch. -/
structure BatchSeparation {Item : Type uItem} (Account : Type uAccount)
    [AddMonoid Account] (demand : Item -> Account) (source : Account)
    (batch : List Item) : Type (max uItem uAccount) where
  frame : Account
  source_eq : source = batchDemand demand batch + frame

namespace BatchSeparation

variable {Item : Type uItem} {Account : Type uAccount}
variable {OtherAccount : Type*}
section Generic
variable [AddMonoid Account]
variable {demand : Item -> Account} {source : Account} {batch : List Item}

/-- Additive reindexing transports an exact decomposition.  This is the
account-projection law used to expose one declared resource view without
changing the licensed occurrence batch. -/
theorem batchDemand_map [AddMonoid OtherAccount]
    (reindex : Account →+ OtherAccount) :
    batchDemand (fun item => reindex (demand item)) batch =
      reindex (batchDemand demand batch) := by
  induction batch with
  | nil => simp
  | cons item rest inductionHypothesis =>
      simp [batchDemand_cons, inductionHypothesis]

def map [AddMonoid OtherAccount]
    (separation : BatchSeparation Account demand source batch)
    (reindex : Account →+ OtherAccount) :
    BatchSeparation OtherAccount (fun item => reindex (demand item))
      (reindex source) batch where
  frame := reindex separation.frame
  source_eq := by
    calc
      reindex source =
          reindex (batchDemand demand batch + separation.frame) :=
        congrArg reindex separation.source_eq
      _ = reindex (batchDemand demand batch) + reindex separation.frame :=
        reindex.map_add _ _
      _ = batchDemand (fun item => reindex (demand item)) batch +
          reindex separation.frame := by
        rw [batchDemand_map]

theorem batchDemand_pair {Left : Type*} {Right : Type*}
    [AddMonoid Left] [AddMonoid Right]
    (leftDemand : Item -> Left) (rightDemand : Item -> Right)
    (items : List Item) :
    batchDemand (fun item => (leftDemand item, rightDemand item)) items =
      (batchDemand leftDemand items, batchDemand rightDemand items) := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
      rw [batchDemand_cons, batchDemand_cons, batchDemand_cons,
        inductionHypothesis]
      rfl

/-- Two independent exact accounts combine pointwise over the same
occurrence positions. -/
def pair {Left : Type*} {Right : Type*} [AddMonoid Left] [AddMonoid Right]
    {leftDemand : Item -> Left} {rightDemand : Item -> Right}
    {leftSource : Left} {rightSource : Right}
    (left : BatchSeparation Left leftDemand leftSource batch)
    (right : BatchSeparation Right rightDemand rightSource batch) :
    BatchSeparation (Left × Right)
      (fun item => (leftDemand item, rightDemand item))
      (leftSource, rightSource) batch where
  frame := (left.frame, right.frame)
  source_eq := by
    rw [batchDemand_pair]
    apply Prod.ext
    · exact left.source_eq
    · exact right.source_eq

end Generic

variable {Resource : Type uResource}
variable [DecidableEq Resource]
variable {demand : Item -> Multiset Resource}
variable {source : Multiset Resource} {batch : List Item}

/-- Construct the canonical retained frame from a successful affordability
check. -/
def of_le (funded : batchDemand demand batch <= source) :
    BatchSeparation (Multiset Resource) demand source batch where
  frame := source - batchDemand demand batch
  source_eq := by
    rw [add_comm]
    exact (Multiset.sub_add_cancel funded).symm

/-- Executable exact-resource admission.  Failure has no semantic meaning. -/
def analyze? (demand : Item -> Multiset Resource)
    (source : Multiset Resource) (batch : List Item) :
    Option (BatchSeparation (Multiset Resource) demand source batch) :=
  if funded : batchDemand demand batch <= source then
    some (of_le funded)
  else
    none

/-- Analysis succeeds exactly when the complete positional demand fits the
source inventory. -/
theorem analyze?_isSome_iff :
    (analyze? demand source batch).isSome = true <->
      batchDemand demand batch <= source := by
  by_cases funded : batchDemand demand batch <= source
  · simp [analyze?, funded]
  · simp [analyze?, funded]

/-- A supplied decomposition is never rejected by the executable analysis. -/
theorem analyze?_complete
    (separation : BatchSeparation (Multiset Resource) demand source batch) :
    (analyze? demand source batch).isSome = true := by
  rw [analyze?_isSome_iff]
  apply Multiset.le_iff_exists_add.mpr
  exact ⟨separation.frame, separation.source_eq⟩

end BatchSeparation

/-! ## Funding decisions retain residual work -/

/-- Account admission either returns an exact residual decomposition or
retains the same batch as pending work together with proof that no such
decomposition exists. -/
inductive FundingDecision {Item : Type uItem} (Account : Type uAccount)
    [AddMonoid Account] (demand : Item -> Account) (source : Account)
    (batch : List Item) : Type (max uItem uAccount) where
  | admitted (separation : BatchSeparation Account demand source batch)
  | deferred
      (insufficient : Not (Nonempty
        (BatchSeparation Account demand source batch)))

namespace FundingDecision

variable {Item : Type uItem} {Account : Type uAccount} [AddMonoid Account]
variable (demand : Item -> Account)
variable (source : Account) (batch : List Item)

/-- Turn any exact, complete analyzer into a funding decision without
changing the candidate batch. -/
def ofOption
    (analysis : Option (BatchSeparation Account demand source batch))
    (complete : analysis = none ->
      Not (Nonempty (BatchSeparation Account demand source batch))) :
    FundingDecision Account demand source batch :=
  match analysis with
  | some separation => .admitted separation
  | none => .deferred (complete rfl)

/-- Executable admission for exact linear-occurrence multisets. -/
def decideMultiset {Resource : Type uResource} [DecidableEq Resource]
    (demand : Item -> Multiset Resource) (source : Multiset Resource)
    (batch : List Item) :
    FundingDecision (Multiset Resource) demand source batch :=
  if funded : batchDemand demand batch <= source then
    .admitted (BatchSeparation.of_le funded)
  else
    .deferred (by
      rintro ⟨separation⟩
      apply funded
      apply Multiset.le_iff_exists_add.mpr
      exact ⟨separation.frame, separation.source_eq⟩)

/-- Occurrence ledger at the activation boundary. -/
structure Ledger (Item : Type uItem) where
  executed : Multiset Item
  pending : Multiset Item

/-- Admission moves the whole batch to `executed`; deferral leaves it wholly
pending.  More refined partial admission can be expressed by applying this
construction to each selected sub-batch. -/
def ledger : FundingDecision Account demand source batch -> Ledger Item
  | .admitted _ => ⟨(batch : Multiset Item), 0⟩
  | .deferred _ => ⟨0, (batch : Multiset Item)⟩

/-- Funding decisions conserve exact occurrence multiplicity. -/
theorem ledger_accounts
    (decision : FundingDecision Account demand source batch) :
    (ledger demand source batch decision).executed +
        (ledger demand source batch decision).pending =
      (batch : Multiset Item) := by
  cases decision <;> simp [ledger]

/-- An insufficient batch remains pending verbatim; resource refusal is not
semantic emptiness. -/
theorem deferred_pending
    (insufficient : Not (Nonempty
      (BatchSeparation Account demand source batch))) :
    (ledger demand source batch
      (FundingDecision.deferred insufficient)).pending =
        (batch : Multiset Item) :=
  rfl

end FundingDecision

/-! ## Joining candidate, execution, and resource authority -/

/-- The candidate view itself is insensitive to every permutation of one
exact occurrence batch.  This is separate from agreement of the states
reached by executing those permutations. -/
def PermutationInvariantAt {Item : Type uItem} {View : Type uView}
    (observe : List Item -> View) (batch : List Item) : Prop :=
  ∀ ordering, ordering.Perm batch -> observe ordering = observe batch

/-- Relational execution semantics for an ordered occurrence batch.  The
state observer is deliberately independent of the candidate observer. -/
structure ExecutionSemantics (Item : Type uItem) (State : Type uState)
    (View : Type uStateView) where
  run : State -> List Item -> State -> Prop
  observe : State -> View

namespace ExecutionSemantics

/-- Every permutation of the exact occurrence batch has a run whose terminal
state agrees with the reference target at the declared state observer. -/
def SerializesTo {Item : Type uItem} {State : Type uState}
    {View : Type uStateView} (semantics : ExecutionSemantics Item State View)
    (source : State) (batch : List Item) (referenceTarget : State) : Prop :=
  semantics.run source batch referenceTarget ∧
    ∀ ordering, ordering.Perm batch ->
      ∃ target,
        semantics.run source ordering target ∧
          semantics.observe target = semantics.observe referenceTarget

end ExecutionSemantics

/-- A wave license retains four independent facts:

* the exact occurrence batch is nonempty;
* its candidate observation is permutation-invariant;
* all operational schedules agree at the declared result observer; and
* its additive account has an exact common-source decomposition.

No scalar score, cost projection, or queue discipline can construct one of
these fields from the others. -/
structure CertifiedBatch
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {State : Type uState} {StateView : Type uStateView}
    (contract : Contract Item Guard View)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (Account : Type uAccount) [AddMonoid Account]
    (demand : Item -> Account) (source : Account) (batch : List Item) :
    Type (max uItem uView uState uStateView uAccount) where
  nonempty : batch ≠ []
  candidateInvariant :
    PermutationInvariantAt contract.observer.observe batch
  executionSerializable :
    semantics.SerializesTo initial batch referenceTarget
  resources : BatchSeparation Account demand source batch

namespace CertifiedBatch

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {contract : Contract Item Guard View}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {demand : Item -> Account}
variable {source : Account} {batch : List Item}

/-- Observation-directed activation plan for a fully certified wave. -/
def plan
    (_certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (branchAuthority : BranchAuthority) : Plan :=
  dispatch contract.demand branchAuthority .serializable

/-- The joined plan never exercises authority absent from the observation
contract or the retained certificates. -/
theorem plan_lawful
    (certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (branchAuthority : BranchAuthority) :
    PlanLawful contract.demand branchAuthority .serializable
      (certified.plan branchAuthority) :=
  dispatch_lawful contract.demand branchAuthority .serializable

/-- Complete-bag demand plus all four certificates licenses bulk activation. -/
theorem completeBag_dispatches_bulk
    (certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (complete : contract.demand.completion = .completeBag) :
    (certified.plan .general).activation = .bulk := by
  rcases contract with ⟨contractObserver, observationDemand⟩
  rcases observationDemand with ⟨completion, guard⟩
  simp only at complete
  subst completion
  rfl

/-- First-witness demand remains controlled even when a whole batch is
resource-separated and serializable at both observers.  The certificates do
not change the consumer's requested observation. -/
theorem first_remains_controlled
    (certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (first : contract.demand.completion = .first) :
    (certified.plan .general).activation = .controlled := by
  rcases contract with ⟨observer, observationDemand⟩
  rcases observationDemand with ⟨completion, guard⟩
  simp only at first
  subst completion
  rfl

/-- Structural unit-cost work/span of one certified nonempty wave.  This is a
readout of the occurrence schedule, not its linear-resource inventory. -/
def unitWorkSpan
    (_certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch) :
    WorkSpan :=
  ⟨batch.length, 1⟩

/-- Serial occurrence-by-occurrence baseline for the same batch. -/
def serialUnitWorkSpan
    (_certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch) :
    WorkSpan :=
  ⟨batch.length, batch.length⟩

/-- One certified wave preserves structural work and cannot increase span
relative to serial activation. -/
theorem unitWorkSpan_le_serial
    (certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch) :
    certified.unitWorkSpan <= certified.serialUnitWorkSpan := by
  constructor
  · exact le_rfl
  · exact List.length_pos_of_ne_nil certified.nonempty

/-- A genuinely wide certified wave strictly improves structural span while
retaining the same work coordinate. -/
theorem unitWorkSpan_strict_of_wide
    (certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (wide : 1 < batch.length) :
    certified.unitWorkSpan.work = certified.serialUnitWorkSpan.work ∧
      certified.unitWorkSpan.span < certified.serialUnitWorkSpan.span :=
  ⟨rfl, wide⟩

/-- Any event valuation remains a readout of the exact selected occurrence
history.  It is not an input to `plan`. -/
def valuation
    (_certified : CertifiedBatch contract semantics initial referenceTarget
      Account demand source batch)
    (reading : Valuation.{uItem, uGrade} Item) : Option reading.Grade :=
  reading.historyGrade batch

end CertifiedBatch

/-! ## Discriminating controls -/

namespace Canary

inductive Job where
  | left
  | right
  | contested
deriving DecidableEq, Repr

inductive Token where
  | first
  | second
deriving DecidableEq, Repr

def demand : Job -> Multiset Token
  | .left => {.first}
  | .right => {.second}
  | .contested => {.first}

def inventory : Multiset Token := {.first, .second}

def bagObserver : Mettapedia.Cybernetics.Observer
    (List Job) (Multiset Job) where
  observe := fun jobs => (jobs : Multiset Job)

def streamObserver : Mettapedia.Cybernetics.Observer
    (List Job) (List Job) :=
  Mettapedia.Cybernetics.Observer.identity (List Job)

def completeBag : Contract Job Unit (Multiset Job) where
  observer := bagObserver
  demand := { completion := .completeBag }

def orderedStream : Contract Job Unit (List Job) where
  observer := streamObserver
  demand := { completion := .orderedStream }

def firstWitness : Contract Job Unit (Multiset Job) where
  observer := bagObserver
  demand := { completion := .first }

theorem bag_permutationInvariant (batch : List Job) :
    PermutationInvariantAt bagObserver.observe batch := by
  intro ordering permutation
  exact Quot.sound permutation

/-- Ordered candidate observation really detects a nontrivial permutation. -/
theorem stream_not_permutationInvariant :
    Not (PermutationInvariantAt streamObserver.observe [.left, .right]) := by
  intro invariant
  have swapped := invariant [.right, .left] (by decide)
  change [Job.right, Job.left] = [Job.left, Job.right] at swapped
  simp at swapped

def appendBagSemantics :
    ExecutionSemantics Job (List Job) (Multiset Job) where
  run source schedule target := target = source ++ schedule
  observe := fun state => (state : Multiset Job)

def appendStreamSemantics :
    ExecutionSemantics Job (List Job) (List Job) where
  run source schedule target := target = source ++ schedule
  observe := id

theorem append_serializes_to_bag (initial batch : List Job) :
    appendBagSemantics.SerializesTo initial batch (initial ++ batch) := by
  constructor
  · rfl
  · intro ordering permutation
    refine ⟨initial ++ ordering, rfl, ?_⟩
    have suffixEquality :
        (ordering : Multiset Job) = (batch : Multiset Job) :=
      Quot.sound permutation
    exact congrArg (fun suffix : Multiset Job =>
      (initial : Multiset Job) + suffix) suffixEquality

theorem append_not_serializes_to_stream :
    Not (appendStreamSemantics.SerializesTo [] [.left, .right]
      [.left, .right]) := by
  rintro ⟨_reference, serializable⟩
  obtain ⟨target, targetRun, sameView⟩ :=
    serializable [.right, .left] (by decide)
  change target = [Job.right, Job.left] at targetRun
  change target = [Job.left, Job.right] at sameView
  subst target
  simp at sameView

/-- Distinct exact resources admit the two occurrences. -/
theorem disjoint_resources_accepted :
    (BatchSeparation.analyze? demand inventory [.left, .right]).isSome = true := by
  decide

/-- Equal structural work does not imply resource compatibility: the second
batch contests the sole first token. -/
theorem equal_work_contested_resources_rejected :
    ([Job.left, Job.right] : List Job).length =
        ([Job.left, Job.contested] : List Job).length ∧
      (BatchSeparation.analyze? demand inventory
        [.left, .contested]).isSome = false := by
  decide

/-- Resource separation alone does not make append activation serializable at
an ordered-stream observer. -/
theorem resources_do_not_grant_stream_serializability :
    (BatchSeparation.analyze? demand inventory [.left, .right]).isSome = true ∧
      Not (appendStreamSemantics.SerializesTo [] [.left, .right]
        [.left, .right]) :=
  ⟨disjoint_resources_accepted, append_not_serializes_to_stream⟩

/-- Bag serializability alone does not manufacture a missing linear token. -/
theorem bag_serializability_does_not_grant_resources :
    appendBagSemantics.SerializesTo [] [.left, .contested]
        [.left, .contested] ∧
      (BatchSeparation.analyze? demand inventory
        [.left, .contested]).isSome = false := by
  constructor
  · exact append_serializes_to_bag [] [.left, .contested]
  · exact equal_work_contested_resources_rejected.2

def disjointSeparation :
    BatchSeparation (Multiset Token) demand inventory [.left, .right] where
  frame := 0
  source_eq := rfl

def energyDemand : Job -> Nat
  | .left => 1
  | .right => 1
  | .contested => 2

def energySeparation :
    BatchSeparation Nat energyDemand 2 [.left, .right] where
  frame := 0
  source_eq := rfl

/-- Exact linear ownership and fungible energy combine without collapsing
their distinct account types. -/
def jointResourceEnergySeparation :
    BatchSeparation (Multiset Token × Nat)
      (fun job => (demand job, energyDemand job)) (inventory, 2)
      [.left, .right] :=
  BatchSeparation.pair disjointSeparation energySeparation

/-- Linear compatibility cannot manufacture a missing energy unit. -/
theorem linear_resources_do_not_grant_energy_budget :
    Nonempty
        (BatchSeparation (Multiset Token) demand inventory [.left, .right]) ∧
      Not (Nonempty
        (BatchSeparation Nat energyDemand 1 [.left, .right])) := by
  constructor
  · exact ⟨disjointSeparation⟩
  · rintro ⟨separation⟩
    have impossible := separation.source_eq
    change 1 = 2 + separation.frame at impossible
    omega

def completeCertified :
    CertifiedBatch completeBag appendBagSemantics [] [.left, .right]
      (Multiset Token) demand inventory
      [.left, .right] where
  nonempty := by decide
  candidateInvariant := bag_permutationInvariant [.left, .right]
  executionSerializable := append_serializes_to_bag [] [.left, .right]
  resources := disjointSeparation

def firstCertified :
    CertifiedBatch firstWitness appendBagSemantics [] [.left, .right]
      (Multiset Token) demand inventory
      [.left, .right] where
  nonempty := by decide
  candidateInvariant := bag_permutationInvariant [.left, .right]
  executionSerializable := append_serializes_to_bag [] [.left, .right]
  resources := disjointSeparation

/-- Both certificates plus complete-bag demand activate the exact batch in one
wave. -/
theorem joined_complete_batch_uses_bulk :
    (completeCertified.plan .general).activation = .bulk :=
  completeCertified.completeBag_dispatches_bulk rfl

/-- The same batch under first-witness demand keeps a controlled frontier. -/
theorem joined_first_batch_remains_controlled :
    (firstCertified.plan .general).activation = .controlled :=
  firstCertified.first_remains_controlled rfl

/-- The two-occurrence wave keeps work two and reduces structural span from
two to one. -/
theorem joined_batch_work_span :
    completeCertified.unitWorkSpan = ⟨2, 1⟩ ∧
      completeCertified.serialUnitWorkSpan = ⟨2, 2⟩ :=
  ⟨rfl, rfl⟩

/-- Insufficient resources retain both exact occurrence positions as pending
work. -/
theorem contested_batch_is_pending :
    let decision := FundingDecision.decideMultiset demand inventory
      [.left, .contested]
    (FundingDecision.ledger demand inventory [.left, .contested]
      decision).pending =
        ({.left, .contested} : Multiset Job) := by
  decide

end Canary

/-! ## Axiom audit -/

#print axioms BatchSeparation.analyze?_isSome_iff
#print axioms BatchSeparation.analyze?_complete
#print axioms BatchSeparation.batchDemand_map
#print axioms BatchSeparation.batchDemand_pair
#print axioms FundingDecision.ledger_accounts
#print axioms FundingDecision.deferred_pending
#print axioms CertifiedBatch.plan_lawful
#print axioms CertifiedBatch.completeBag_dispatches_bulk
#print axioms CertifiedBatch.first_remains_controlled
#print axioms CertifiedBatch.unitWorkSpan_le_serial
#print axioms CertifiedBatch.unitWorkSpan_strict_of_wide
#print axioms Canary.resources_do_not_grant_stream_serializability
#print axioms Canary.bag_serializability_does_not_grant_resources
#print axioms Canary.linear_resources_do_not_grant_energy_budget
#print axioms Canary.joined_complete_batch_uses_bulk
#print axioms Canary.contested_batch_is_pending

end Mettapedia.GSLT.Core.ResourceAwareControl
