import Mettapedia.GSLT.Dynamics.RevisionBoundProgramView

/-!
# Reusable authority for immutable revision views

A revision-derived program view may be shared across observations only under
its complete authority key.  The cache owns one immutable view; acquisition
returns a value lease which remains unchanged if the cache is later detached
or replaced.  A key mismatch and explicit invalidation both rebuild from the
authoritative snapshot family.

This module specifies the semantic and work-accounting boundary.  It does not
choose a physical reclamation mechanism: reference counts, epochs, and owned
copies are alternative realizations of the same value-level lease law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ReusableRevisionViewAuthority

open RevisionBoundProgramView

universe uStore uRevision uId uRow uCode

variable {Store : Type uStore} {Revision : Type uRevision}
variable {Id : Type uId} {Row : Type uRow} {Code : Type uCode}
variable [DecidableEq Store] [DecidableEq Revision]

/-- The authoritative occurrence snapshot at every complete revision key. -/
structure SnapshotFamily
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) where
  snapshotAt : RevisionKey Store Revision → Snapshot Store Revision Id Row
  key_snapshotAt : ∀ key, (snapshotAt key).key = key

/-- One cached immutable view and the exact authority key that produced it. -/
structure CacheEntry
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) (Code : Type uCode) where
  key : RevisionKey Store Revision
  view : ProgramView Store Revision Id Row Code

/-- A cache slot is representation state only; absence never removes the
authoritative snapshot family. -/
structure Authority
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) (Code : Type uCode) where
  cached : Option (CacheEntry Store Revision Id Row Code)

/-- The cache is sound when its stored view is exactly the view derived from
the authoritative snapshot at its stored complete key. -/
def Sound
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code) : Prop :=
  ∀ entry, authority.cached = some entry →
    entry.view = build compile (family.snapshotAt entry.key)

inductive AcquisitionKind where
  | built
  | reused
deriving DecidableEq, Repr

/-- An acquisition returns a value lease and the updated cache authority.
`buildCount` is semantic-work evidence, not elapsed time. -/
structure Acquisition
    (Store : Type uStore) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) (Code : Type uCode) where
  authority : Authority Store Revision Id Row Code
  lease : ProgramView Store Revision Id Row Code
  kind : AcquisitionKind
  buildCount : Nat

/-- Construct and publish a view for one exact key. -/
def buildAndPublish
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (key : RevisionKey Store Revision) :
    Acquisition Store Revision Id Row Code :=
  let view := build compile (family.snapshotAt key)
  {
    authority := { cached := some { key := key, view := view } }
    lease := view
    kind := .built
    buildCount := 1
  }

/-- Reuse exactly one matching immutable view.  Every mismatch rebuilds from
the authoritative snapshot family and atomically replaces the cache value at
this abstract level. -/
def acquire
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (key : RevisionKey Store Revision) :
    Acquisition Store Revision Id Row Code :=
  match authority.cached with
  | some entry =>
      if entry.key = key then
        {
          authority := authority
          lease := entry.view
          kind := .reused
          buildCount := 0
        }
      else
        buildAndPublish family compile key
  | none => buildAndPublish family compile key

/-- Detach the cached representation.  Previously returned value leases are
not fields of the resulting authority and therefore remain immutable values. -/
def invalidate
    (_authority : Authority Store Revision Id Row Code) :
    Authority Store Revision Id Row Code :=
  { cached := none }

/-- Every acquisition from a sound cache returns the exact derived view for
the requested complete authority key. -/
theorem acquire_exact
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (key : RevisionKey Store Revision)
    (sound : Sound family compile authority) :
    (acquire family compile authority key).lease =
      build compile (family.snapshotAt key) := by
  cases hCached : authority.cached with
  | none =>
      simp [acquire, hCached, buildAndPublish]
  | some entry =>
      by_cases hKey : entry.key = key
      · have hView := sound entry hCached
        simpa [acquire, hCached, hKey, hKey] using hView
      · simp [acquire, hCached, hKey, buildAndPublish]

/-- Acquisition preserves the cache-soundness invariant. -/
theorem acquire_sound
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (key : RevisionKey Store Revision)
    (sound : Sound family compile authority) :
    Sound family compile (acquire family compile authority key).authority := by
  cases hCached : authority.cached with
  | none =>
      intro entry hEntry
      simp [acquire, hCached, buildAndPublish] at hEntry
      subst entry
      rfl
  | some cached =>
      by_cases hKey : cached.key = key
      · simpa [acquire, hCached, hKey] using sound
      · intro entry hEntry
        simp [acquire, hCached, hKey, buildAndPublish] at hEntry
        subst entry
        rfl

omit [DecidableEq Store] [DecidableEq Revision] in
/-- Invalidation preserves cache soundness because it removes only derived
state. -/
theorem invalidate_sound
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code) :
    Sound family compile (invalidate authority) := by
  intro entry hEntry
  simp [invalidate] at hEntry

/-- Repeating an acquisition at the same complete key performs no second
build and returns the identical immutable value. -/
theorem acquire_twice_reuses
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (key : RevisionKey Store Revision) :
    let first := acquire family compile authority key
    let second := acquire family compile first.authority key
    second.kind = .reused ∧
      second.buildCount = 0 ∧
      second.lease = first.lease := by
  dsimp
  cases hCached : authority.cached with
  | none =>
      simp [acquire, hCached, buildAndPublish]
  | some entry =>
      by_cases hKey : entry.key = key
      · simp [acquire, hCached, hKey]
      · simp [acquire, hCached, hKey, buildAndPublish]

/-- A distinct complete key cannot reuse the view installed by the preceding
acquisition. -/
theorem changed_key_builds
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (firstKey secondKey : RevisionKey Store Revision)
    (changed : firstKey ≠ secondKey) :
    let first := acquire family compile authority firstKey
    let second := acquire family compile first.authority secondKey
    second.kind = .built ∧ second.buildCount = 1 := by
  dsimp
  cases hCached : authority.cached with
  | none =>
      simp [acquire, hCached, buildAndPublish, changed]
  | some entry =>
      by_cases hKey : entry.key = firstKey
      · simp [acquire, hCached, hKey, buildAndPublish, changed]
      · simp [acquire, hCached, hKey, buildAndPublish, changed]

/-- Explicit invalidation forces one rebuild even when the next request uses
the same key. -/
theorem acquire_after_invalidate_builds
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (key : RevisionKey Store Revision) :
    let next := acquire family compile (invalidate authority) key
    next.kind = .built ∧ next.buildCount = 1 := by
  simp [acquire, invalidate, buildAndPublish]

/-- Cache replacement cannot retag an already acquired lease.  The old and
new leases remain exact at their independently requested keys. -/
theorem acquired_lease_survives_replacement
    (family : SnapshotFamily Store Revision Id Row)
    (compile : Row → Option Code)
    (authority : Authority Store Revision Id Row Code)
    (firstKey secondKey : RevisionKey Store Revision)
    (sound : Sound family compile authority) :
    let first := acquire family compile authority firstKey
    let second := acquire family compile first.authority secondKey
    first.lease = build compile (family.snapshotAt firstKey) ∧
      second.lease = build compile (family.snapshotAt secondKey) := by
  dsimp
  constructor
  · exact acquire_exact family compile authority firstKey sound
  · exact acquire_exact family compile
      (acquire family compile authority firstKey).authority secondKey
      (acquire_sound family compile authority firstKey sound)

namespace Canaries

def snapshotFamily : SnapshotFamily Bool Nat Nat Nat where
  snapshotAt := fun key => {
    key := key
    occurrences :=
      if key.store then
        [⟨20, 200 + key.revision⟩]
      else
        [⟨10, 100 + key.revision⟩]
  }
  key_snapshotAt := fun _ => rfl

def compileRow (row : Nat) : Option Nat := some (row + 1)

def emptyAuthority : Authority Bool Nat Nat Nat Nat := { cached := none }

def keyA0 : RevisionKey Bool Nat := ⟨false, 0⟩
def keyA1 : RevisionKey Bool Nat := ⟨false, 1⟩
def keyB0 : RevisionKey Bool Nat := ⟨true, 0⟩

def first := acquire snapshotFamily compileRow emptyAuthority keyA0
def repeated := acquire snapshotFamily compileRow first.authority keyA0
def revised := acquire snapshotFamily compileRow first.authority keyA1
def foreign := acquire snapshotFamily compileRow first.authority keyB0
def rebuilt := acquire snapshotFamily compileRow
  (invalidate first.authority) keyA0

/-- Positive: the first request builds one view. -/
example : first.kind = .built ∧ first.buildCount = 1 := by decide

/-- Positive: an exact-key repeat reuses the value without rebuilding. -/
example : repeated.kind = .reused ∧ repeated.buildCount = 0 := by decide

/-- Negative revision control: a later revision cannot reuse the old view. -/
example : revised.kind = .built ∧ revised.buildCount = 1 := by decide

/-- Negative authority control: equal revision numbers in distinct stores do
not authorize reuse. -/
example : foreign.kind = .built ∧ foreign.buildCount = 1 := by decide

/-- Negative invalidation control: removing the cache forces reconstruction. -/
example : rebuilt.kind = .built ∧ rebuilt.buildCount = 1 := by decide

/-- An acquired old view retains its original occurrence after a new revision
is installed. -/
example :
    first.lease.entries.map eraseEntry = [⟨10, 100⟩] ∧
      revised.lease.entries.map eraseEntry = [⟨10, 101⟩] := by
  decide

end Canaries

#print axioms acquire_exact
#print axioms acquire_sound
#print axioms invalidate_sound
#print axioms acquire_twice_reuses
#print axioms changed_key_builds
#print axioms acquire_after_invalidate_builds
#print axioms acquired_lease_survives_replacement

end Mettapedia.GSLT.Dynamics.ReusableRevisionViewAuthority
