import Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation

/-!
# Delayed values in an authoritative rollback store

`DelayedSourceBindingCompilation` proves that a retained source view denotes
an ordinary open term and supports exact layerwise observation.  This module
connects that value representation to the existing authoritative dense-slot
store and value-restoring undo trail.

The logical authority remains a dense environment of fully denoted open
terms.  The physical store may retain eager terms or delayed source views.
Every write, finite write sequence, direct layer observation, and rollback to
a valid mark commutes with that denotation.

Ownership is tracked independently of meaning.  A physically admissible state
must retain every delayed view reachable from both its current slots and its
undo trail, because rollback may resurrect an overwritten value.  This is the
smallest store-level lifetime obligation needed before a runtime may keep
source views across matcher observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DelayedBindingStoreRefinement

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open CompiledPlanOpenActivationViewCompilation
open FiniteEnvironmentCompilation
open AuthoritativeSlotTrailCompilation
open DelayedSourceBindingCompilation
open SupportRestrictedSourceViewCompilation
open TermObservationCoalgebra

universe uKey uOwner uRevision

variable {Key : Type uKey} {Owner : Type uOwner} {Revision : Type uRevision}
  {inventory : Inventory Key}

abbrev Value := BindingValue Owner Revision

abbrev PhysicalState (inventory : Inventory Key) :=
  State inventory (Value (Owner := Owner) (Revision := Revision))

abbrev LogicalState (inventory : Inventory Key) :=
  DenseEnvironment inventory OpenTerm

abbrev Update (inventory : Inventory Key) :=
  DenseWrite inventory (Value (Owner := Owner) (Revision := Revision))

/-! ## Denotational refinement -/

def denoteSlots (environment : DenseEnvironment inventory
    (Value (Owner := Owner) (Revision := Revision))) :
    LogicalState inventory :=
  fun slot => (environment slot).map BindingValue.denote

def denoteState (state : PhysicalState
    (Owner := Owner) (Revision := Revision) inventory) :
    LogicalState inventory :=
  denoteSlots state.slots

def logicalWrite [DecidableEq Key] (inventory : Inventory Key)
    (state : LogicalState inventory)
    (update : Update (Owner := Owner) (Revision := Revision) inventory) :
    LogicalState inventory :=
  writeDense inventory state (update.1, update.2.denote)

theorem denoteState_write [DecidableEq Key] (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (update : Update (Owner := Owner) (Revision := Revision) inventory) :
    denoteState (write inventory state update) =
      logicalWrite inventory (denoteState state) update := by
  funext slot
  by_cases same : slot = update.1
  · subst slot
    simp [denoteState, denoteSlots, logicalWrite, write, writeDense]
  · simp [denoteState, denoteSlots, logicalWrite, write, writeDense, same]

/-- The generic binding-store interface instantiated by authoritative dense
slots whose physical values may be delayed source views. -/
def bindingStore [DecidableEq Key] (inventory : Inventory Key) :
    BindingStore
      (LogicalState inventory)
      (PhysicalState (Owner := Owner) (Revision := Revision) inventory)
      (Update (Owner := Owner) (Revision := Revision) inventory) where
  denote := denoteState
  logicalWrite := logicalWrite inventory
  write := write inventory
  write_exact := denoteState_write inventory

theorem writeMany_eq_run [DecidableEq Key] (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (updates : List
      (Update (Owner := Owner) (Revision := Revision) inventory)) :
    (bindingStore (Owner := Owner) (Revision := Revision) inventory).writeMany
        state updates =
      run inventory state updates := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      simp only [BindingStore.writeMany,
        AuthoritativeSlotTrailCompilation.run]
      exact inductionHypothesis (write inventory state update)

/-- Every finite physical update path denotes the corresponding sequence of
ordinary open-term writes. -/
theorem run_exact [DecidableEq Key] (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (updates : List
      (Update (Owner := Owner) (Revision := Revision) inventory)) :
    denoteState (run inventory state updates) =
      BindingStore.logicalWriteMany
        (bindingStore (Owner := Owner) (Revision := Revision) inventory)
        (denoteState state) updates := by
  rw [← writeMany_eq_run]
  exact BindingStore.writeMany_exact
    (bindingStore (Owner := Owner) (Revision := Revision) inventory)
    state updates

/-- Delayed and eager storage of the same source view have identical logical
meaning, including when an older value is retained by the undo trail. -/
theorem delayed_write_eq_eager_write [DecidableEq Key]
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (slot : inventory.Slot) (view : SourceView Owner Revision) :
    denoteState (write inventory state (slot, .delayed view)) =
      denoteState (write inventory state (slot, .eager view.force)) := by
  rw [denoteState_write, denoteState_write]
  rfl

/-- An owned support snapshot may be stored lazily with exactly the meaning of
the original full source view.  This is the store-level bridge needed by a
runtime that captures source support before leaving a mutable matcher region. -/
theorem captured_write_eq_eager_write [DecidableEq Key]
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (slot : inventory.Slot) (view : SourceView Owner Revision) :
    denoteState
        (write inventory state
          (slot, .delayed (SupportSnapshot.capture view).toSourceView)) =
      denoteState (write inventory state (slot, .eager view.force)) := by
  rw [delayed_write_eq_eager_write]
  rw [SupportSnapshot.capture_force_exact]

/-! ## Total valid-mark rollback instance -/

/-- Invalid marks fail closed at the concrete interface.  The total
capability interface returns the unchanged state for that unreachable case;
all laws below are stated only for valid marks. -/
def rollbackOrCurrent [DecidableEq Key] (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (savedMark : Nat) :
    PhysicalState (Owner := Owner) (Revision := Revision) inventory :=
  (rollbackTo? inventory savedMark state).getD state

theorem rollbackTo?_write_of_valid [DecidableEq Key]
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (savedMark : Nat)
    (update : Update (Owner := Owner) (Revision := Revision) inventory)
    (valid : savedMark ≤ state.trail.length) :
    rollbackTo? inventory savedMark (write inventory state update) =
      rollbackTo? inventory savedMark state := by
  unfold rollbackTo?
  have validAfter : savedMark ≤ (write inventory state update).trail.length := by
    simp only [write, List.length_cons]
    omega
  simp only [valid, validAfter, ↓reduceIte]
  have steps :
      (write inventory state update).trail.length - savedMark =
        1 + (state.trail.length - savedMark) := by
    simp only [write, List.length_cons]
    omega
  rw [steps, rollbackN_add]
  simp [rollbackN, undoOne?_write]

theorem rollbackOrCurrent_write_of_valid [DecidableEq Key]
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (savedMark : Nat)
    (update : Update (Owner := Owner) (Revision := Revision) inventory)
    (valid : savedMark ≤ state.trail.length) :
    rollbackOrCurrent inventory (write inventory state update) savedMark =
      rollbackOrCurrent inventory state savedMark := by
  obtain ⟨restored, restoredEq⟩ :=
    rollbackTo?_available inventory savedMark state valid
  simp [rollbackOrCurrent,
    rollbackTo?_write_of_valid inventory state savedMark update valid,
    restoredEq]

def linearRollbackStore [DecidableEq Key] (inventory : Inventory Key) :
    LinearRollbackStore
      (LogicalState inventory)
      (PhysicalState (Owner := Owner) (Revision := Revision) inventory)
      Nat
      (Update (Owner := Owner) (Revision := Revision) inventory) where
  toBindingStore := bindingStore inventory
  save := mark
  valid state savedMark := savedMark ≤ state.trail.length
  savedMeaning state savedMark :=
    denoteState (rollbackOrCurrent inventory state savedMark)
  save_valid state := Nat.le_refl state.trail.length
  save_exact state := by
    unfold rollbackOrCurrent mark
    rw [show rollbackTo? inventory state.trail.length state = some state by
      simpa [mark, AuthoritativeSlotTrailCompilation.run] using
        (rollbackTo?_run inventory state [])]
    rfl
  valid_write state savedMark update valid := by
    change savedMark ≤ state.trail.length + 1
    omega
  savedMeaning_write state savedMark update valid := by
    exact congrArg denoteState
      (rollbackOrCurrent_write_of_valid inventory state savedMark update valid)
  rollback := rollbackOrCurrent inventory
  rollback_exact _ _ _ := rfl

/-- A finite transaction followed by rollback through the capability
interface restores exactly the entrance logical substitution. -/
theorem rollback_after_run_exact [DecidableEq Key] (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (updates : List
      (Update (Owner := Owner) (Revision := Revision) inventory)) :
    denoteState
        (rollbackOrCurrent inventory (run inventory state updates) (mark state)) =
      denoteState state := by
  unfold rollbackOrCurrent
  rw [rollbackTo?_run]
  rfl

/-! ## Lifetime and rollback-root discipline -/

def ValueAdmitted (registry : SnapshotRegistry Owner Revision) :
    Value (Owner := Owner) (Revision := Revision) -> Prop
  | .eager _ => True
  | .delayed view => registry.Admitted view

def OptionAdmitted (registry : SnapshotRegistry Owner Revision) :
    Option (Value (Owner := Owner) (Revision := Revision)) -> Prop
  | none => True
  | some value => ValueAdmitted registry value

/-- Both current values and overwritten values retained by the undo trail are
GC roots.  Omitting either conjunct permits a live delayed view to dangle. -/
def StateAdmitted (registry : SnapshotRegistry Owner Revision)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory) :
    Prop :=
  (∀ slot, OptionAdmitted registry (state.slots slot)) ∧
  (∀ entry ∈ state.trail, OptionAdmitted registry entry.previous)

theorem write_preserves_admission [DecidableEq Key]
    (registry : SnapshotRegistry Owner Revision)
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (update : Update (Owner := Owner) (Revision := Revision) inventory)
    (stateAdmitted : StateAdmitted registry state)
    (valueAdmitted : ValueAdmitted registry update.2) :
    StateAdmitted registry (write inventory state update) := by
  constructor
  · intro slot
    by_cases same : slot = update.1
    · subst slot
      simpa [write, writeDense, OptionAdmitted] using valueAdmitted
    · simpa [write, writeDense, same] using stateAdmitted.1 slot
  · intro entry membership
    rcases List.mem_cons.mp membership with head | tail
    · subst entry
      simpa [write] using stateAdmitted.1 update.1
    · exact stateAdmitted.2 entry tail

theorem run_preserves_admission [DecidableEq Key]
    (registry : SnapshotRegistry Owner Revision)
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (updates : List
      (Update (Owner := Owner) (Revision := Revision) inventory))
    (stateAdmitted : StateAdmitted registry state)
    (updatesAdmitted : ∀ update ∈ updates,
      ValueAdmitted registry update.2) :
    StateAdmitted registry (run inventory state updates) := by
  induction updates generalizing state with
  | nil => exact stateAdmitted
  | cons update updates inductionHypothesis =>
      apply inductionHypothesis (write inventory state update)
      · exact write_preserves_admission registry inventory state update
          stateAdmitted (updatesAdmitted update (by simp))
      · intro candidate membership
        exact updatesAdmitted candidate (by simp [membership])

/-- Rollback retains admission because the complete physical entrance state,
including its older trail prefix, is restored exactly. -/
theorem rollback_run_preserves_admission [DecidableEq Key]
    (registry : SnapshotRegistry Owner Revision)
    (inventory : Inventory Key)
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (updates : List
      (Update (Owner := Owner) (Revision := Revision) inventory))
    (stateAdmitted : StateAdmitted registry state) :
    rollbackTo? inventory (mark state) (run inventory state updates) =
        some state ∧
      StateAdmitted registry state := by
  exact ⟨rollbackTo?_run inventory state updates, stateAdmitted⟩

/-! ## Direct slot observation -/

def observePhysicalLayer
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (slot : inventory.Slot) :
    Option (TermLayer (Value (Owner := Owner) (Revision := Revision))) :=
  (state.slots slot).map outBinding

def observeLogicalLayer (state : LogicalState inventory)
    (slot : inventory.Slot) : Option (TermLayer OpenTerm) :=
  (state slot).map outOpen

/-- Looking through a stored delayed value one layer at a time is exactly
ordinary observation of the fully denoted logical binding. -/
theorem observePhysicalLayer_exact
    (state : PhysicalState (Owner := Owner) (Revision := Revision) inventory)
    (slot : inventory.Slot) :
    (observePhysicalLayer state slot).map
        (TermLayer.map BindingValue.denote) =
      observeLogicalLayer (denoteState state) slot := by
  cases selected : state.slots slot with
  | none => simp [observePhysicalLayer, observeLogicalLayer,
      denoteState, denoteSlots, selected]
  | some value =>
      simp only [observePhysicalLayer, observeLogicalLayer,
        denoteState, denoteSlots, selected, Option.map_some]
      exact congrArg some (outBinding_exact value)

/-! ## Positive and negative controls -/

namespace Canaries

private def oneKey : Inventory Unit where
  keys := [()]
  nodup := by decide

private def slot : oneKey.Slot := ⟨0, by decide⟩

private def environment : OpenEnvironment
  | 0 => some (.symbol [9])
  | _ => none

private def view (revision : Nat) : SourceView Unit Nat :=
  { owner := (), revision, generation := 7, environment
    source := .application [1]
      (.cons (.variable 0) (.cons (.symbol [2]) .nil)) }

private def registry : SnapshotRegistry Unit Nat where
  retains _ revision _ := revision = 5

private def empty : PhysicalState (Owner := Unit) (Revision := Nat) oneKey :=
  { slots := emptyDenseEnvironment oneKey, trail := [] }

/-- A retained delayed view may be written, observed, and rolled back through
the generic capability instance without changing its open-term meaning. -/
example :
    let update : Update (Owner := Unit) (Revision := Nat) oneKey :=
      (slot, .delayed (view 5))
    let written := write oneKey empty update
    observePhysicalLayer written slot =
        some (.application [1]
          [.delayed { view 5 with source := .variable 0 },
           .delayed { view 5 with source := .symbol [2] }]) ∧
      denoteState (rollbackOrCurrent oneKey written (mark empty)) =
        denoteState empty := by
  constructor
  · rfl
  · exact rollback_after_run_exact oneKey empty [(slot, .delayed (view 5))]

/-- A stale delayed view still has a mathematical denotation but is rejected
as physical state because its owner/revision passport is not retained. -/
example :
    ¬ StateAdmitted registry
      (write oneKey empty (slot, .delayed (view 4))) := by
  intro admitted
  have selected := admitted.1 slot
  simp [write, writeDense, OptionAdmitted, ValueAdmitted,
    SnapshotRegistry.Admitted, registry] at selected
  norm_num [view] at selected

/-- The undo trail is an ownership root: overwriting an admitted delayed view
with an eager value still requires the old delayed view to remain retained. -/
example :
    let first := write oneKey empty (slot, .delayed (view 5))
    let second := write oneKey first (slot, .eager (.symbol [3]))
    StateAdmitted registry second := by
  have emptyAdmitted : StateAdmitted registry empty := by
    constructor
    · intro candidate
      trivial
    · intro entry membership
      simp [empty] at membership
  have firstAdmitted : StateAdmitted registry
      (write oneKey empty (slot, .delayed (view 5))) :=
    write_preserves_admission registry oneKey empty
      (slot, .delayed (view 5)) emptyAdmitted (by rfl)
  exact write_preserves_admission registry oneKey
    (write oneKey empty (slot, .delayed (view 5)))
    (slot, .eager (.symbol [3])) firstAdmitted (by trivial)

/-- Without a retained revision passport, the overwritten delayed value makes
the whole state inadmissible even though the current slot is eager. -/
example :
    let first := write oneKey empty (slot, .delayed (view 4))
    let second := write oneKey first (slot, .eager (.symbol [3]))
    ¬ StateAdmitted registry second := by
  dsimp only
  intro stateAdmitted
  have oldRoot := stateAdmitted.2
    { slot := slot, previous := some (.delayed (view 4)) }
    (by simp [write, writeDense, empty])
  simp [OptionAdmitted, ValueAdmitted, SnapshotRegistry.Admitted, registry, view]
    at oldRoot

end Canaries

#print axioms denoteState_write
#print axioms run_exact
#print axioms delayed_write_eq_eager_write
#print axioms captured_write_eq_eager_write
#print axioms rollbackTo?_write_of_valid
#print axioms linearRollbackStore
#print axioms rollback_after_run_exact
#print axioms write_preserves_admission
#print axioms run_preserves_admission
#print axioms rollback_run_preserves_admission
#print axioms observePhysicalLayer_exact

end Mettapedia.GSLT.LanguageDef.DelayedBindingStoreRefinement
