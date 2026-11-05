import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.ControlComposition

/-!
# Fresh-only source insertion and its progress observation

The already-present branch emits no answer, while the fresh branch inserts
one row and emits true. Failure to access the space remains distinct from
both cases. This is the insertion guard used by frontier-style phases, not
the always-successful materialization operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces

def source (spaceName rowName : String) : Atom :=
  .expression [.symbol "if", GuardedInsertionSource.absent spaceName rowName,
    .expression [.symbol "add-atom", .var spaceName, .var rowName], .expression [.symbol "empty"]]

def answers (changed : Bool) : List Atom := if changed then [Effects.boolean true] else []

def update (before : Effects.State) (handle : Handle) (row : Atom) : Option (Effects.State × Bool) := do
  let rows ← before.read handle
  if row ∈ rows then some (before, false)
  else (Effects.insert before handle row).map (fun after => (after, true))

theorem forget_progress (before : Effects.State) (handle : Handle) (row : Atom) :
    (update before handle row).map Prod.fst = GuardedInsertionSource.update before handle row := by
  unfold update GuardedInsertionSource.update
  cases snapshot : before.read handle with
  | none => rfl
  | some rows =>
      by_cases present : row ∈ rows <;> simp [present, Option.map_map, Function.comp_def]

theorem unchanged_update {before after : Effects.State} {handle : Handle} {row : Atom} {changed : Bool}
    (completed : update before handle row = some (after, changed)) :
    GuardedInsertionSource.update before handle row = some after := by
  rw [← forget_progress, completed]
  rfl

theorem update_reads_back {before after : Effects.State} {handle : Handle} {row : Atom} {changed : Bool}
    (completed : update before handle row = some (after, changed)) :
    ∃ rows, before.read handle = some rows ∧
      after.read handle = some (if row ∈ rows then rows else rows ++ [row]) ∧
      changed = decide (row ∉ rows) := by
  obtain ⟨rows, snapshot, afterRead⟩ := GuardedInsertionSource.update_reads_back (unchanged_update completed)
  refine ⟨rows, snapshot, afterRead, ?_⟩
  unfold update at completed
  simp only [snapshot] at completed
  by_cases present : row ∈ rows
  · have same : (before, false) = (after, changed) := by simpa [present] using completed
    simpa [present] using (Prod.mk.inj same).2.symm
  · have mapped : (Effects.insert before handle row).map (fun next => (next, true)) = some (after, changed) := by
      simpa [present] using completed
    obtain ⟨middle, _, same⟩ := Option.map_eq_some_iff.mp mapped
    simpa [present] using (Prod.mk.inj same).2.symm

theorem source_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (spaceName rowName : String) (handle : Handle) (row : Atom) (changed : Bool)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (completed : update before handle row = some (after, changed)) :
    Returns program bindings before (source spaceName rowName) after (answers changed) := by
  obtain ⟨rows, snapshot, _, progress⟩ := update_reads_back completed
  have tested := GuardedInsertionSource.absent_returns program bindings before spaceName rowName handle row rows
    location bound snapshot
  have plain := unchanged_update completed
  by_cases present : row ∈ rows
  · have flag : changed = false := by simpa [present] using progress
    have same : before = after := by simpa [GuardedInsertionSource.update, snapshot, present] using plain
    subst after
    rw [flag]
    change Returns program bindings before (source spaceName rowName) before []
    apply if_answers program bindings before before before _ (Effects.boolean false) _ _ []
      (by simpa [present] using tested)
    simpa [Effects.boolean] using empty_returns program bindings before
  · have flag : changed = true := by simpa [present] using progress
    have inserted : Effects.insert before handle row = some after := by
      simpa [GuardedInsertionSource.update, snapshot, present] using plain
    rw [flag]
    change Returns program bindings before (source spaceName rowName) after [Effects.boolean true]
    apply if_answers program bindings before before after _ (Effects.boolean true) _ _ [Effects.boolean true]
      (by simpa [present] using tested)
    simpa using GuardedInsertionSource.insert_returns program bindings before after spaceName rowName handle row
      location bound inserted

theorem missing_is_not_zero_progress (before : Effects.State) (handle : Handle) (row : Atom)
    (missing : before.read handle = none) : update before handle row = none := by simp [update, missing]

theorem update_exists {before : Effects.State} {handle : Handle} {rows : List Atom}
    (snapshot : before.read handle = some rows) (row : Atom) :
    ∃ after changed, update before handle row = some (after, changed) := by
  obtain ⟨after, computed⟩ := GuardedInsertionSource.update_exists snapshot row
  have projected : (update before handle row).map Prod.fst = some after :=
    (forget_progress before handle row).trans computed
  obtain ⟨receipt, updated, _⟩ := Option.map_eq_some_iff.mp projected
  exact ⟨receipt.1, receipt.2, updated⟩

theorem update_growth {before after : Effects.State} {handle : Handle} {row : Atom} {changed : Bool}
    (completed : update before handle row = some (after, changed)) :
    ∃ rows result, before.read handle = some rows ∧ after.read handle = some result ∧
      result.length = rows.length + (answers changed).length := by
  obtain ⟨rows, snapshot, afterRead, flag⟩ := update_reads_back completed
  refine ⟨rows, _, snapshot, afterRead, ?_⟩
  rw [flag]
  by_cases present : row ∈ rows <;> simp [present, answers]

theorem zero_progress_preserves_state {before after : Effects.State} {handle : Handle} {row : Atom}
    (completed : update before handle row = some (after, false)) : before = after := by
  obtain ⟨rows, snapshot, _, flag⟩ := update_reads_back completed
  have present : row ∈ rows := by
    by_contra absent
    simp [absent] at flag
  have plain := unchanged_update completed
  simpa [GuardedInsertionSource.update, snapshot, present] using plain

namespace Controls

open GuardedInsertionSource.Controls (row emptyState heldState caller program)

theorem fresh_step_emits_one :
    update emptyState .self row = some (heldState, true) ∧ answers true = [Effects.boolean true] := ⟨rfl, rfl⟩

theorem held_step_is_empty_not_false :
    update heldState .self row = some (heldState, false) ∧ answers false = [] ∧ answers false ≠ [Effects.boolean false] := by
  exact ⟨rfl, rfl, by decide⟩

theorem held_source_has_no_answer : Returns program caller heldState (source "space" "row") heldState [] :=
  source_returns program caller heldState heldState "space" "row" .self row false rfl rfl rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionSource
