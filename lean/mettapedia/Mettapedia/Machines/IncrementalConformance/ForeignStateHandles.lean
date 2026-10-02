import Mettapedia.Machines.IncrementalConformance.ForeignState

/-!
# Mutable foreign handles realizing branch-owned sessions

An owner map and a foreign heap are distinct structures. Injective mutable
ownership prevents an update through one owner's handle from changing a sibling.
The view/read, update, cancellation and fresh allocation theorems connect this
addressed representation to `ForeignState.Sessions`. Snapshot values can share
immutable substructure; live mutable handle aliases are excluded explicitly.

This is a finite-action semantic adapter, not a model of physical allocation,
foreign frame lifetimes, thread affinity, SWI query nesting or concurrent access.
No exported raw handle is modeled: all access goes through the live owner map.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignStateHandles

open Mettapedia.Machines.IncrementalConformance.ForeignState

universe u v w

structure Host (Owner : Type u) (Handle : Type v) (State : Type w) where
  owners : Owner → Option Handle
  heap : Handle → Option (Frame State)

variable {Owner : Type u} {Handle : Type v} {State : Type w}
  [DecidableEq Owner] [DecidableEq Handle]

def Host.view (host : Host Owner Handle State) : Sessions Owner State :=
  fun owner => (host.owners owner).bind host.heap

/-- Every mutable handle has at most one live owning branch. -/
def Host.Unique (host : Host Owner Handle State) : Prop :=
  ∀ owner sibling handle,
    host.owners owner = some handle → host.owners sibling = some handle → owner = sibling

/-- Every retained foreign slot has a registered owner. This is separate from
absence of dangling registrations: safety alone does not prevent retention. -/
def Host.NoOrphans (host : Host Owner Handle State) : Prop :=
  ∀ handle frame, host.heap handle = some frame → ∃ owner, host.owners owner = some handle

/-- Every registered handle designates an existing foreign state. -/
def Host.NoDangling (host : Host Owner Handle State) : Prop :=
  ∀ owner handle, host.owners owner = some handle → ∃ frame, host.heap handle = some frame

def Host.modify (host : Host Owner Handle State) (owner : Owner)
    (operation : Frame State → Frame State) : Host Owner Handle State :=
  match host.owners owner with
  | none => host
  | some handle =>
      { host with heap := Function.update host.heap handle ((host.heap handle).map operation) }

omit [DecidableEq Owner] in
theorem modify_view_self (host : Host Owner Handle State) (owner : Owner)
    (operation : Frame State → Frame State) :
    (host.modify owner operation).view owner = (host.view owner).map operation := by
  cases found : host.owners owner <;> simp [Host.modify, Host.view, found]

omit [DecidableEq Owner] in
theorem modify_view_other (host : Host Owner Handle State) (unique : host.Unique)
    (owner sibling : Owner) (different : sibling ≠ owner)
    (operation : Frame State → Frame State) :
    (host.modify owner operation).view sibling = host.view sibling := by
  cases found : host.owners owner with
  | none => simp [Host.modify, found]
  | some handle =>
    cases other : host.owners sibling with
    | none => simp [Host.modify, Host.view, found, other]
    | some otherHandle =>
      have handlesDiffer : otherHandle ≠ handle := by
        intro same
        subst otherHandle
        exact different (unique sibling owner handle other found)
      simp [Host.modify, Host.view, found, other, handlesDiffer]

/-- Addressed mutation realizes one branch-local semantic update. -/
theorem modify_realizes (host : Host Owner Handle State) (unique : host.Unique)
    (owner : Owner) (operation : Frame State → Frame State) :
    (host.modify owner operation).view =
      ForeignState.modify host.view owner operation := by
  funext sibling
  by_cases same : sibling = owner
  · subst sibling
    simpa [ForeignState.modify] using modify_view_self host owner operation
  · simpa [ForeignState.modify, same] using
      modify_view_other host unique owner sibling same operation

omit [DecidableEq Owner] in
theorem modify_unique (host : Host Owner Handle State) (unique : host.Unique)
    (owner : Owner) (operation : Frame State → Frame State) :
    (host.modify owner operation).Unique := by
  cases found : host.owners owner <;> simpa [Host.modify, found, Host.Unique] using unique

omit [DecidableEq Owner] in
theorem modify_noDangling (host : Host Owner Handle State) (live : host.NoDangling)
    (owner : Owner) (operation : Frame State → Frame State) :
    (host.modify owner operation).NoDangling := by
  cases found : host.owners owner with
  | none => simpa [Host.modify, found] using live
  | some handle =>
    intro sibling otherHandle registered
    have original : host.owners sibling = some otherHandle := by
      simpa [Host.modify, found] using registered
    obtain ⟨frame, value⟩ := live sibling otherHandle original
    by_cases same : otherHandle = handle
    · subst otherHandle
      exact ⟨operation frame, by simp [Host.modify, found, value]⟩
    · exact ⟨frame, by simp [Host.modify, found, value, same]⟩

/-- A cancelled owner loses both its registration and its exclusively owned slot. -/
def Host.cancel (host : Host Owner Handle State) (owner : Owner) : Host Owner Handle State :=
  { owners := Function.update host.owners owner none
    heap := match host.owners owner with
      | none => host.heap
      | some handle => Function.update host.heap handle none }

theorem cancel_view_self (host : Host Owner Handle State) (owner : Owner) :
    (host.cancel owner).view owner = none := by simp [Host.cancel, Host.view]

theorem cancel_view_other (host : Host Owner Handle State) (unique : host.Unique)
    (owner sibling : Owner) (different : sibling ≠ owner) :
    (host.cancel owner).view sibling = host.view sibling := by
  cases found : host.owners owner with
  | none => simp [Host.cancel, Host.view, found, different]
  | some handle =>
    cases other : host.owners sibling with
    | none => simp [Host.cancel, Host.view, found, other, different]
    | some otherHandle =>
      have handlesDiffer : otherHandle ≠ handle := by
        intro same
        subst otherHandle
        exact different (unique sibling owner handle other found)
      simp [Host.cancel, Host.view, found, other, different, handlesDiffer]

theorem cancel_realizes (host : Host Owner Handle State) (unique : host.Unique)
    (owner : Owner) :
    (host.cancel owner).view = ForeignState.cancel host.view owner := by
  funext sibling
  by_cases same : sibling = owner
  · subst sibling
    simp [ForeignState.cancel, cancel_view_self]
  · simpa [ForeignState.cancel, same] using cancel_view_other host unique owner sibling same

theorem cancel_unique (host : Host Owner Handle State) (unique : host.Unique) (owner : Owner) :
    (host.cancel owner).Unique := by
  intro left right handle hl hr
  by_cases leftSame : left = owner
  · subst left
    simp [Host.cancel] at hl
  by_cases rightSame : right = owner
  · subst right
    simp [Host.cancel] at hr
  exact unique left right handle
    (by simpa [Host.cancel, leftSame] using hl)
    (by simpa [Host.cancel, rightSame] using hr)

theorem cancel_noDangling (host : Host Owner Handle State) (unique : host.Unique)
    (live : host.NoDangling) (owner : Owner) : (host.cancel owner).NoDangling := by
  intro sibling handle registered
  have different : sibling ≠ owner := by
    intro same
    subst sibling
    simp [Host.cancel] at registered
  have original : host.owners sibling = some handle := by
    simpa [Host.cancel, different] using registered
  obtain ⟨frame, value⟩ := live sibling handle original
  refine ⟨frame, ?_⟩
  cases found : host.owners owner with
  | none => simpa [Host.cancel, found] using value
  | some deadHandle =>
      have handlesDiffer : handle ≠ deadHandle := by
        intro same
        subst deadHandle
        exact different (unique sibling owner handle original found)
      simpa [Host.cancel, found, handlesDiffer] using value

/-- Fresh allocation copies the semantic snapshot into a distinct mutable slot. -/
def Host.allocate (host : Host Owner Handle State) (owner : Owner) (handle : Handle)
    (frame : Frame State) : Host Owner Handle State :=
  { owners := Function.update host.owners owner (some handle)
    heap := Function.update host.heap handle (some frame) }

omit [DecidableEq Owner] [DecidableEq Handle] in
theorem unallocated_not_owned (host : Host Owner Handle State) (live : host.NoDangling)
    (handle : Handle) (unused : host.heap handle = none) (owner : Owner) :
    host.owners owner ≠ some handle := by
  intro registered
  obtain ⟨frame, value⟩ := live owner handle registered
  rw [unused] at value
  cases value

theorem allocate_realizes (host : Host Owner Handle State) (live : host.NoDangling)
    (owner : Owner) (handle : Handle) (frame : Frame State) (unused : host.heap handle = none) :
    (host.allocate owner handle frame).view = Function.update host.view owner (some frame) := by
  funext sibling
  by_cases same : sibling = owner
  · subst sibling
    simp [Host.allocate, Host.view]
  · cases found : host.owners sibling with
    | none => simp [Host.allocate, Host.view, same, found]
    | some otherHandle =>
      have handlesDiffer : otherHandle ≠ handle := by
        intro equal
        subst otherHandle
        exact unallocated_not_owned host live handle unused sibling found
      simp [Host.allocate, Host.view, same, found, handlesDiffer]

theorem allocate_unique (host : Host Owner Handle State) (unique : host.Unique)
    (live : host.NoDangling) (owner : Owner) (handle : Handle) (frame : Frame State)
    (unused : host.heap handle = none) : (host.allocate owner handle frame).Unique := by
  intro left right address hl hr
  by_cases leftSame : left = owner
  · subst left
    have addressSame : handle = address := by simpa [Host.allocate] using hl
    subst address
    by_cases rightSame : right = owner
    · exact rightSame.symm
    · have old : host.owners right = some handle := by simpa [Host.allocate, rightSame] using hr
      exact (unallocated_not_owned host live handle unused right old).elim
  · by_cases rightSame : right = owner
    · subst right
      have addressSame : handle = address := by simpa [Host.allocate] using hr
      subst address
      have old : host.owners left = some handle := by simpa [Host.allocate, leftSame] using hl
      exact (unallocated_not_owned host live handle unused left old).elim
    · exact unique left right address
        (by simpa [Host.allocate, leftSame] using hl)
        (by simpa [Host.allocate, rightSame] using hr)

theorem allocate_noDangling (host : Host Owner Handle State) (live : host.NoDangling)
    (owner : Owner) (handle : Handle) (frame : Frame State) :
    (host.allocate owner handle frame).NoDangling := by
  intro sibling address registered
  by_cases same : sibling = owner
  · subst sibling
    have addressSame : handle = address := by simpa [Host.allocate] using registered
    subst address
    exact ⟨frame, by simp [Host.allocate]⟩
  · have old : host.owners sibling = some address := by
      simpa [Host.allocate, same] using registered
    by_cases addressSame : address = handle
    · subst address
      exact ⟨frame, by simp [Host.allocate]⟩
    · obtain ⟨oldFrame, value⟩ := live sibling address old
      exact ⟨oldFrame, by simpa [Host.allocate, addressSame] using value⟩

/-- Creating a branch by allocating a fresh mutable handle realizes value-level
fork, provided the target branch has not already been registered. -/
theorem allocate_realizes_fork (host : Host Owner Handle State) (live : host.NoDangling)
    (source target : Owner) (handle : Handle) (frame : Frame State)
    (sourceState : host.view source = some frame)
    (freshOwner : host.owners target = none) (freshHandle : host.heap handle = none) :
    (host.allocate target handle frame).view = ForeignState.fork host.view source target := by
  rw [allocate_realizes host live target handle frame freshHandle]
  have absent : host.view target = none := by simp [Host.view, freshOwner]
  simp [ForeignState.fork, absent, sourceState]

/-- Cleanup invalidates all registrations and all foreign slots in this model. -/
def Host.cleanup : Host Owner Handle State := ⟨fun _ => none, fun _ => none⟩

omit [DecidableEq Owner] [DecidableEq Handle] in
theorem cleanup_realizes : (Host.cleanup : Host Owner Handle State).view = ForeignState.cleanup := rfl

omit [DecidableEq Owner] [DecidableEq Handle] in
theorem cleanup_noDangling : (Host.cleanup : Host Owner Handle State).NoDangling := by
  intro owner handle registered
  cases registered

omit [DecidableEq Owner] in
theorem modify_noOrphans (host : Host Owner Handle State) (owned : host.NoOrphans)
    (owner : Owner) (operation : Frame State → Frame State) :
    (host.modify owner operation).NoOrphans := by
  cases found : host.owners owner with
  | none => simpa [Host.modify, found] using owned
  | some handle =>
    intro address frame value
    by_cases same : address = handle
    · subst address
      exact ⟨owner, by simp [Host.modify, found]⟩
    · have old : host.heap address = some frame := by
        simpa [Host.modify, found, same] using value
      obtain ⟨sibling, registered⟩ := owned address frame old
      exact ⟨sibling, by simpa [Host.modify, found] using registered⟩

theorem cancel_noOrphans (host : Host Owner Handle State) (owned : host.NoOrphans)
    (owner : Owner) : (host.cancel owner).NoOrphans := by
  intro address frame value
  have old : host.heap address = some frame := by
    cases found : host.owners owner with
    | none => simpa [Host.cancel, found] using value
    | some handle =>
      by_cases same : address = handle
      · subst address
        simp [Host.cancel, found] at value
      · simpa [Host.cancel, found, same] using value
  obtain ⟨sibling, registered⟩ := owned address frame old
  have different : sibling ≠ owner := by
    intro same
    subst sibling
    simp [Host.cancel, registered] at value
  exact ⟨sibling, by simpa [Host.cancel, different] using registered⟩

/-- Fresh owner admission is essential for the no-retention conclusion.
Reassigning an already registered owner can strand its previous slot. -/
theorem allocate_noOrphans (host : Host Owner Handle State) (owned : host.NoOrphans)
    (owner : Owner) (handle : Handle) (frame : Frame State)
    (freshOwner : host.owners owner = none) :
    (host.allocate owner handle frame).NoOrphans := by
  intro address retained value
  by_cases same : address = handle
  · subst address
    exact ⟨owner, by simp [Host.allocate]⟩
  · have old : host.heap address = some retained := by
      simpa [Host.allocate, same] using value
    obtain ⟨sibling, registered⟩ := owned address retained old
    have different : sibling ≠ owner := by
      intro equal
      subst sibling
      rw [freshOwner] at registered
      cases registered
    exact ⟨sibling, by simpa [Host.allocate, different] using registered⟩

omit [DecidableEq Owner] [DecidableEq Handle] in
theorem cleanup_noOrphans : (Host.cleanup : Host Owner Handle State).NoOrphans := by
  intro handle frame value
  cases value

theorem modify_after_cancel_is_noop (host : Host Owner Handle State) (owner : Owner)
    (operation : Frame State → Frame State) :
    (host.cancel owner).modify owner operation = host.cancel owner := by
  simp [Host.modify, Host.cancel]

theorem cancel_releases_slot (host : Host Owner Handle State) (owner : Owner) (handle : Handle)
    (owned : host.owners owner = some handle) : (host.cancel owner).heap handle = none := by
  simp [Host.cancel, owned]

section ForeignSimulation

variable {Var Val Attr : Type} [DecidableEq Var] [DecidableEq Val]
  [Fintype Var] [Fintype Val]

/-- The independently specified reconstructing call is simulated by updating the
exclusively owned foreign slot. The ownership premise is checked separately from
solver correctness; it is not a simulation premise in disguise. -/
theorem handle_call_simulates
    (host : Host Owner Handle (Retained Var Val Attr)) (unique : host.Unique)
    (reference : Sessions Owner (List (Event Var Val Attr)))
    (related : SessionsRelated reference host.view) (owner : Owner) (event : Event Var Val Attr) :
    SessionsRelated (sessionStep referenceCall (.call owner event) reference)
      (host.modify owner (fun frame => (frame.call (retainedCall event)).2)).view := by
  rw [modify_realizes host unique owner]
  exact sessionStep_related (.call owner event) related

theorem handle_rollback_simulates
    (host : Host Owner Handle (Retained Var Val Attr)) (unique : host.Unique)
    (reference : Sessions Owner (List (Event Var Val Attr)))
    (related : SessionsRelated reference host.view) (owner : Owner) :
    SessionsRelated (sessionStep referenceCall (.rollback owner) reference)
      (host.modify owner Frame.rollback).view := by
  rw [modify_realizes host unique owner]
  exact sessionStep_related (.rollback owner) related

theorem handle_cancel_simulates
    (host : Host Owner Handle (Retained Var Val Attr)) (unique : host.Unique)
    (reference : Sessions Owner (List (Event Var Val Attr)))
    (related : SessionsRelated reference host.view) (owner : Owner) :
    SessionsRelated (sessionStep referenceCall (.cancel owner) reference) (host.cancel owner).view := by
  rw [cancel_realizes host unique owner]
  exact sessionStep_related (.cancel owner) related

end ForeignSimulation

namespace Controls

def aliased : Host Bool Unit (Retained Bool Bool Nat) :=
  ⟨fun _ => some (), fun _ => some ⟨initial, []⟩⟩

theorem shared_mutable_handles_violate_ownership : ¬ aliased.Unique := by
  intro unique
  have impossible : false = true := unique false true () rfl rfl
  cases impossible

theorem alias_mutation_changes_other_owner :
    ((aliased.modify false (fun frame =>
      (frame.call (retainedCall (.post (.bind false true)))).2)).view true).map
      (fun frame => frame.current.solutions) ≠
    (aliased.view true).map (fun frame => frame.current.solutions) := by decide

def singleOwner : Host Bool Bool (Retained Bool Bool Nat) :=
  ⟨fun owner => if owner then none else some false,
    fun handle => if handle then none else some ⟨initial, []⟩⟩

theorem single_owner_noOrphans : singleOwner.NoOrphans := by
  intro handle frame value
  cases handle with
  | false => exact ⟨false, rfl⟩
  | true => cases value

/-- Re-registering the same owner can look correct through every live owner,
yet leave the old foreign slot retained forever. -/
theorem reregister_orphans_old_slot :
    ¬ (singleOwner.allocate false true ⟨initial, []⟩).NoOrphans := by
  intro owned
  obtain ⟨owner, registered⟩ := owned false ⟨initial, []⟩ (by rfl)
  cases owner <;> simp [Host.allocate, singleOwner] at registered

end Controls

end Mettapedia.Machines.IncrementalConformance.ForeignStateHandles
