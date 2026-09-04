import Mettapedia.GSLT.Dynamics.ReusableRevisionViewAuthority
import Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex

/-!
# Product law for revision-view realizations

An immutable revision view has three independent physical coordinates:

* an encoding of the ordered occurrence snapshot;
* a candidate index which observes one head without changing order or
  multiplicity;
* a lease policy which retains the encoded value for the lifetime of one
  observation.

The product theorem proves that exactness of these three coordinates composes.
It deliberately does not identify reference counting, epoch reclamation, or
owned copying with a payload encoding.  Those are alternative lifetime
policies for the same immutable value law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RevisionViewRealizationProduct

universe uRevision uId uHead uRow uPhysical uIndex uLease uValue

/-- One authored equation occurrence.  Equal payloads do not identify equal
occurrences. -/
structure Occurrence
    (Id : Type uId) (Head : Type uHead) (Row : Type uRow) where
  id : Id
  /-- `none` is the variable/wildcard-head pattern. -/
  head : Option Head
  payload : Row
deriving DecidableEq, Repr

/-- The semantic value retained by a revision lease. -/
structure Snapshot
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) where
  revision : Revision
  occurrences : List (Occurrence Id Head Row)
deriving DecidableEq, Repr

/-- Observe one head in authored order, retaining exact multiplicity. -/
def observe
    {Id : Type uId} {Head : Type uHead} {Row : Type uRow}
    [DecidableEq Head]
    (head : Head) (occurrences : List (Occurrence Id Head Row)) :
    List (Occurrence Id Head Row) :=
  occurrences.filter fun occurrence =>
    match occurrence.head with
    | none => true
    | some storedHead => decide (storedHead = head)

/-- A physical encoding is exact when decoding a freshly encoded snapshot
returns that complete snapshot, including its revision and ordered occurrence
family. -/
structure ExactEncoding
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow)
    (Physical : Type uPhysical) where
  encode : Snapshot Revision Id Head Row → Physical
  decode : Physical → Snapshot Revision Id Head Row
  decode_encode : ∀ snapshot, decode (encode snapshot) = snapshot

/-- A candidate index is exact when it returns the independent semantic
observation for every snapshot and head. -/
structure ExactCandidateIndex
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow)
    (IndexState : Type uIndex) [DecidableEq Head] where
  build : Snapshot Revision Id Head Row → IndexState
  query : IndexState → Head → List (Occurrence Id Head Row)
  query_exact : ∀ snapshot head,
    query (build snapshot) head = observe head snapshot.occurrences

/-- A value lease may add ownership metadata, but acquisition cannot retag the
revision or replace the physical value. -/
structure ExactLeasePolicy
    (Revision : Type uRevision) (Physical : Type uPhysical)
    (LeaseState : Type uLease) where
  acquire : Revision → Physical → LeaseState
  leaseRevision : LeaseState → Revision
  leaseValue : LeaseState → Physical
  revision_acquire : ∀ revision value,
    leaseRevision (acquire revision value) = revision
  value_acquire : ∀ revision value,
    leaseValue (acquire revision value) = value

/-- Observe a snapshot through the product of its encoding, candidate index,
and lease policy. -/
def observeAcquired
    {Revision : Type uRevision} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {Physical : Type uPhysical} {IndexState : Type uIndex}
    {LeaseState : Type uLease} [DecidableEq Head]
    (encoding : ExactEncoding Revision Id Head Row Physical)
    (index : ExactCandidateIndex Revision Id Head Row IndexState)
    (leases : ExactLeasePolicy Revision Physical LeaseState)
    (snapshot : Snapshot Revision Id Head Row) (head : Head) :
    List (Occurrence Id Head Row) :=
  let lease := leases.acquire snapshot.revision (encoding.encode snapshot)
  index.query (index.build (encoding.decode (leases.leaseValue lease))) head

/-- Exact physical encoding, exact candidate selection, and value-preserving
lease acquisition compose to the exact semantic head observation. -/
theorem observeAcquired_exact
    {Revision : Type uRevision} {Id : Type uId}
    {Head : Type uHead} {Row : Type uRow}
    {Physical : Type uPhysical} {IndexState : Type uIndex}
    {LeaseState : Type uLease} [DecidableEq Head]
    (encoding : ExactEncoding Revision Id Head Row Physical)
    (index : ExactCandidateIndex Revision Id Head Row IndexState)
    (leases : ExactLeasePolicy Revision Physical LeaseState)
    (snapshot : Snapshot Revision Id Head Row) (head : Head) :
    observeAcquired encoding index leases snapshot head =
      observe head snapshot.occurrences := by
  simp only [observeAcquired, leases.value_acquire]
  rw [encoding.decode_encode]
  exact index.query_exact snapshot head

/-! ## Concrete positive realizations -/

/-- The identity encoding is the owned-flat baseline. -/
def ownedFlatEncoding
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) :
    ExactEncoding Revision Id Head Row (Snapshot Revision Id Head Row) where
  encode := id
  decode := id
  decode_encode := fun _ => rfl

/-- Split a list into ordered chunks of at most two elements. -/
def pairChunks {α : Type uValue} : List α → List (List α)
  | [] => []
  | [first] => [[first]]
  | first :: second :: rest =>
      [first, second] :: pairChunks rest

/-- Chunking followed by flattening is a lossless, order-preserving physical
encoding. -/
theorem flatten_pairChunks {α : Type uValue} :
    ∀ values : List α, (pairChunks values).flatten = values
  | [] => rfl
  | [first] => rfl
  | first :: second :: rest => by
      simp [pairChunks, flatten_pairChunks rest]

/-- A non-identity concrete carrier: the revision is retained separately and
the occurrence family is stored in ordered two-element chunks. -/
def pairChunkEncoding
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) :
    ExactEncoding Revision Id Head Row
      (Revision × List (List (Occurrence Id Head Row))) where
  encode := fun snapshot =>
    (snapshot.revision, pairChunks snapshot.occurrences)
  decode := fun physical => {
    revision := physical.1
    occurrences := physical.2.flatten
  }
  decode_encode := by
    intro snapshot
    cases snapshot with
    | mk revision occurrences =>
        simp only [flatten_pairChunks]

/-- The scan index is the independent semantic baseline for physical indexes. -/
def scanIndex
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) [DecidableEq Head] :
    ExactCandidateIndex Revision Id Head Row
      (Snapshot Revision Id Head Row) where
  build := id
  query := fun snapshot head => observe head snapshot.occurrences
  query_exact := fun _ _ => rfl

/-- An extensional head partition specifies the result a materialized
per-head index must realize.  Concrete finite maps remain a representation
choice. -/
def extensionalHeadIndex
    (Revision : Type uRevision) (Id : Type uId)
    (Head : Type uHead) (Row : Type uRow) [DecidableEq Head] :
    ExactCandidateIndex Revision Id Head Row
      (Head → List (Occurrence Id Head Row)) where
  build := fun snapshot head => observe head snapshot.occurrences
  query := fun indexed head => indexed head
  query_exact := fun _ _ => rfl

/-- An owned immutable lease pairs the authority revision with the retained
physical value. -/
structure OwnedLease (Revision : Type uRevision) (Physical : Type uPhysical)
    where
  revision : Revision
  value : Physical
deriving DecidableEq, Repr

def ownedLeasePolicy
    (Revision : Type uRevision) (Physical : Type uPhysical) :
    ExactLeasePolicy Revision Physical (OwnedLease Revision Physical) where
  acquire := fun revision value => ⟨revision, value⟩
  leaseRevision := OwnedLease.revision
  leaseValue := OwnedLease.value
  revision_acquire := fun _ _ => rfl
  value_acquire := fun _ _ => rfl

/-! ## Lifetime policy and reclamation boundary -/

/-- Abstract reference-count state for one immutable carrier value. -/
structure RefCountState where
  cacheOwned : Bool
  leaseCount : Nat
  retired : Bool
deriving DecidableEq, Repr

def acquireReference (state : RefCountState) : RefCountState :=
  { state with leaseCount := state.leaseCount + 1 }

def retireCacheReference (state : RefCountState) : RefCountState :=
  { state with cacheOwned := false, retired := true }

def releaseReference (state : RefCountState) : RefCountState :=
  { state with leaseCount := state.leaseCount - 1 }

/-- Reclamation is allowed only after the cache reference and every acquired
lease reference are gone. -/
def reclaimable (state : RefCountState) : Bool :=
  state.retired && !state.cacheOwned && state.leaseCount == 0

/-- Retiring the cache after any acquisition cannot reclaim the value while
that acquired lease is outstanding. -/
theorem retire_after_acquire_not_reclaimable (state : RefCountState) :
    reclaimable (retireCacheReference (acquireReference state)) = false := by
  simp [reclaimable, retireCacheReference, acquireReference]

/-- Positive release boundary: the last outstanding lease makes a retired,
cache-detached value reclaimable. -/
example :
    reclaimable (releaseReference ⟨false, 1, true⟩) = true := by
  decide

/-- Negative release boundary: one of two outstanding leases is not enough. -/
example :
    reclaimable (releaseReference ⟨false, 2, true⟩) = false := by
  decide

/-! ## Revision-log visibility -/

structure VersionedOccurrence
    (Id : Type uId) (Head : Type uHead) (Row : Type uRow) where
  occurrence : Occurrence Id Head Row
  born : Nat
  dead : Option Nat
deriving DecidableEq, Repr

def visibleAt
    {Id : Type uId} {Head : Type uHead} {Row : Type uRow}
    (entry : VersionedOccurrence Id Head Row) (revision : Nat) : Prop :=
  entry.born ≤ revision ∧
    match entry.dead with
    | none => True
    | some dead => revision < dead

/-- A later retirement does not alter an older revision lease. -/
example :
    let entry : VersionedOccurrence Nat Nat String :=
      ⟨⟨10, some 0, "same"⟩, 0, some 1⟩
    visibleAt entry 0 ∧ ¬ visibleAt entry 1 := by
  simp [visibleAt]

/-! ## Role-exact allocation receipts -/

structure AllocationReceipt where
  carrierBytes : Nat
  observerBytes : Nat
  totalBytes : Nat
deriving DecidableEq, Repr

def RoleExact (receipt : AllocationReceipt) : Prop :=
  receipt.totalBytes = receipt.carrierBytes + receipt.observerBytes

theorem combine_roleExact
    (left right : AllocationReceipt)
    (leftExact : RoleExact left) (rightExact : RoleExact right) :
    RoleExact {
      carrierBytes := left.carrierBytes + right.carrierBytes
      observerBytes := left.observerBytes + right.observerBytes
      totalBytes := left.totalBytes + right.totalBytes
    } := by
  simp only [RoleExact] at leftExact rightExact ⊢
  omega

/-- Positive accounting control. -/
example : RoleExact ⟨10, 20, 30⟩ := by norm_num [RoleExact]

/-- Negative accounting control: an unclassified byte breaks the receipt. -/
example : ¬ RoleExact ⟨10, 20, 31⟩ := by norm_num [RoleExact]

/-! ## Multiplicity and order negative controls -/

def duplicateSnapshot : Snapshot Nat Nat Nat String := {
  revision := 0
  occurrences := [
    ⟨10, some 0, "same"⟩,
    ⟨11, none, "same"⟩,
    ⟨12, some 1, "tail"⟩
  ]
}

/-- Equal payloads with distinct occurrence identities remain distinct. -/
example :
    (observe 0 duplicateSnapshot.occurrences).map Occurrence.id = [10, 11] := by
  decide

/-- The same wildcard occurrence participates in every concrete-head
observation without being duplicated within one observation. -/
example :
    (observe 1 duplicateSnapshot.occurrences).map Occurrence.id = [11, 12] := by
  decide

/-- Deduplicating by payload is not an exact candidate index. -/
example :
    [duplicateSnapshot.occurrences[0]] ≠
      observe 0 duplicateSnapshot.occurrences := by
  decide

/-- Reversing candidates is not exact even when support and multiplicity are
unchanged. -/
example :
    (observe 0 duplicateSnapshot.occurrences).reverse ≠
      observe 0 duplicateSnapshot.occurrences := by
  decide

#print axioms observeAcquired_exact
#print axioms flatten_pairChunks
#print axioms retire_after_acquire_not_reclaimable
#print axioms combine_roleExact

end Mettapedia.GSLT.Dynamics.RevisionViewRealizationProduct
