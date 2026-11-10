import Mettapedia.Languages.MeTTa.ContextualTransform.StoreOperations
import Mettapedia.Languages.MeTTa.StoreAndDemand.PeTTaSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison

/-!
# Scoped PeTTa removal selects a transform publication

Each stored row is renamed apart at its own source use, and its unifier is
discarded after selection. The target preparation retains occurrence identities,
not a shared substitution. The independent source survivor computation and the
target's occurrence contraction agree in both directions on completion.

Exhaustion remains a failed preparation, never a negative match. Return-value
conventions of complete remove-atom adapters are above this store operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open PeTTa.Unifying (unify rename)

abbrev atomFrames := Frames.ofSubstitution MetaMeTTaComparison.atomAction

variable {O : Type} (label : O → Atom)

/-- Independent indexed source selection: every occurrence has its own
renaming use and its own success or clash evidence. -/
inductive Removal (pattern : Atom) : Nat → List O → List O → List O → Prop where
  | nil (use : Nat) : Removal pattern use [] [] []
  | take {use row rest kept taken bindings} :
      unify [] pattern (rename use (label row)) = .ok bindings →
      Removal pattern (use + 1) rest kept taken →
      Removal pattern use (row :: rest) kept (row :: taken)
  | keep {use row rest kept taken} :
      unify [] pattern (rename use (label row)) = .clash →
      Removal pattern (use + 1) rest kept taken →
      Removal pattern use (row :: rest) (row :: kept) taken

/-- The prepared target keeps just the selected identities. It does not
construct the source survivor list or combine different rows' bindings. -/
def selectedRows (pattern : Atom) : Nat → List O → Option (List O)
  | _, [] => some []
  | use, row :: rest => do
      let later ← selectedRows pattern (use + 1) rest
      match unify [] pattern (rename use (label row)) with
      | .ok _ => some (row :: later)
      | .clash => some later
      | .exhausted => none

theorem Removal.prepared {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) :
    selectedRows label pattern use rows = some taken := by
  induction selected with
  | nil => rfl
  | take matched _ ih => simp [selectedRows, ih, matched]
  | keep clashed _ ih => simp [selectedRows, ih, clashed]

theorem Removal.source {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) :
    PeTTa.Unifying.survivors pattern use (rows.map label) = some (kept.map label) := by
  induction selected with
  | nil => rfl
  | take matched _ ih => simp [PeTTa.Unifying.survivors, ih, matched]
  | keep clashed _ ih => simp [PeTTa.Unifying.survivors, ih, clashed]

theorem Removal.taken_sublist {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) : taken.Sublist rows := by
  induction selected with
  | nil => exact .slnil
  | take _ _ ih => exact ih.cons_cons _
  | keep _ _ ih => exact ih.cons _

theorem Removal.kept_sublist {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) : kept.Sublist rows := by
  induction selected with
  | nil => exact .slnil
  | take _ _ ih => exact ih.cons _
  | keep _ _ ih => exact ih.cons_cons _

theorem prepared_selection {pattern : Atom} {use : Nat} {rows taken : List O}
    (prepared : selectedRows label pattern use rows = some taken) :
    ∃ kept, Removal label pattern use rows kept taken := by
  induction rows generalizing use taken with
  | nil =>
      simp only [selectedRows, Option.some.injEq] at prepared
      subst taken
      exact ⟨[], .nil _⟩
  | cons row rest ih =>
      cases tail : selectedRows label pattern (use + 1) rest with
      | none => simp [selectedRows, tail] at prepared
      | some later =>
          obtain ⟨kept, selected⟩ := ih tail
          cases matched : unify [] pattern (rename use (label row)) with
          | ok bindings =>
              simp [selectedRows, tail, matched] at prepared
              subst taken
              exact ⟨kept, .take matched selected⟩
          | clash =>
              simp [selectedRows, tail, matched] at prepared
              subst taken
              exact ⟨row :: kept, .keep matched selected⟩
          | exhausted => simp [selectedRows, tail, matched] at prepared

theorem source_selection {pattern : Atom} {use : Nat} {rows : List O} {kept : List Atom}
    (completed : PeTTa.Unifying.survivors pattern use (rows.map label) = some kept) :
    ∃ keptIds taken, Removal label pattern use rows keptIds taken ∧ keptIds.map label = kept := by
  induction rows generalizing use kept with
  | nil =>
      simp only [List.map_nil, PeTTa.Unifying.survivors, Option.some.injEq] at completed
      subst kept
      exact ⟨[], [], .nil _, rfl⟩
  | cons row rest ih =>
      cases tail : PeTTa.Unifying.survivors pattern (use + 1) (rest.map label) with
      | none => simp [PeTTa.Unifying.survivors, tail] at completed
      | some later =>
          obtain ⟨keptIds, taken, selected, rfl⟩ := ih tail
          cases matched : unify [] pattern (rename use (label row)) with
          | ok bindings =>
              simp [PeTTa.Unifying.survivors, tail, matched] at completed
              subst kept
              exact ⟨keptIds, row :: taken, .take matched selected, rfl⟩
          | clash =>
              simp [PeTTa.Unifying.survivors, tail, matched] at completed
              subst kept
              exact ⟨row :: keptIds, taken, .keep matched selected, rfl⟩
          | exhausted => simp [PeTTa.Unifying.survivors, tail, matched] at completed

variable [DecidableEq O]

theorem Removal.contracts {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) (unique : rows.Nodup) :
    OrderedStore.survivors rows taken = kept := by
  induction selected with
  | nil => rfl
  | @take use row rest kept taken bindings matched tail ih =>
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      have noRow : ∀ occurrence ∈ rest, occurrence ≠ row := by
        intro occurrence member same
        subst occurrence
        exact absent member
      have eraseHead : OrderedStore.survivors rest (row :: taken) =
          OrderedStore.survivors rest taken := by
        apply List.filter_congr
        intro occurrence member
        simp [noRow occurrence member]
      calc
        OrderedStore.survivors (row :: rest) (row :: taken) =
            OrderedStore.survivors rest (row :: taken) := by simp [OrderedStore.survivors]
        _ = OrderedStore.survivors rest taken := eraseHead
        _ = kept := ih uniqueRest
  | @keep use row rest kept taken clashed tail ih =>
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      have notTaken : row ∉ taken := fun member => absent (tail.taken_sublist label |>.subset member)
      simpa [OrderedStore.survivors, notTaken] using congrArg (List.cons row) (ih uniqueRest)

def request (taken : List O) : OrderedStore.Publication Atom O := ⟨⟨taken, [], []⟩, []⟩

theorem Removal.admitted {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) (unique : rows.Nodup)
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows)) (request taken) := by
  refine ⟨⟨unique, (selected.taken_sublist label).nodup unique, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨?_, by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr ((selected.taken_sublist label).subset
      (List.mem_toFinset.mp member))
  · intro query member
    simp [request, OrderedStore.Publication.commit] at member

/-- Source completion is equivalent to a prepared identity selection and
an admitted target effect with precisely the source's ordered survivor values. -/
theorem removal_iff_target (pattern : Atom) (use : Nat) (rows : List O)
    (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) (kept : List Atom) :
    PeTTa.Unifying.survivors pattern use (rows.map label) = some kept ↔
      ∃ taken, selectedRows label pattern use rows = some taken ∧
        ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
            (s := (knowledge, rows)) (request taken),
          (((OrderedStore.step atomFrames PUnit.unit label).result (request taken) admitted).2.map label) = kept := by
  constructor
  · intro completed
    obtain ⟨keptIds, taken, selected, rfl⟩ := source_selection label completed
    refine ⟨taken, selected.prepared label, selected.admitted label unique knowledge consistent, ?_⟩
    rw [OrderedStore.result_rows]
    simp only [request, OrderedStore.publish, List.append_nil]
    rw [selected.contracts label unique]
  · rintro ⟨taken, prepared, admitted, result⟩
    obtain ⟨keptIds, selected⟩ := prepared_selection label prepared
    rw [OrderedStore.result_rows] at result
    simp only [request, OrderedStore.publish, List.append_nil] at result
    rw [selected.contracts label unique] at result
    rw [← result]
    exact selected.source label

omit [DecidableEq O] in
/-- The selected store is also the store written by the existing source
removeRows adapter. Its historical return convention is retained explicitly;
it is not silently identified with CeTTa's changed-store Boolean policy. -/
theorem source_remove_rows (state after : PeTTa.Effects.State) (location head : Atom)
    (tail : List Atom) (handle : PeTTa.NamedSpaces.Handle) (use : Nat)
    (rows kept taken : List O)
    (resolved : PeTTa.Effects.readHandle location = some handle)
    (opened : state.read handle = some (rows.map label))
    (selected : Removal label (.expression (head :: tail)) use rows kept taken)
    (written : state.write handle (kept.map label) = some after) :
    PeTTa.Unifying.removeRows state location (.expression (head :: tail)) use =
      some (.ok (after,
        [PeTTa.Effects.boolean (if PeTTa.Unifying.equationRow (.expression (head :: tail))
          then decide (kept.length < rows.length) else true)], rows.length)) := by
  simp [PeTTa.Unifying.removeRows, resolved, opened, selected.source label, written]

omit [DecidableEq O] in
theorem exhaustion_prevents_preparation (pattern : Atom) (use : Nat) (row : O) (rest : List O)
    (exhausted : unify [] pattern (rename use (label row)) = .exhausted) :
    selectedRows label pattern use (row :: rest) = none := by
  cases tail : selectedRows label pattern (use + 1) rest <;> simp [selectedRows, tail, exhausted]

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
