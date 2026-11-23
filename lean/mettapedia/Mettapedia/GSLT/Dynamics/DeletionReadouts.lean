import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mathlib.Tactic

/-!
# Demands after scoped deletion

Occurrences, not equal values, are counted. For an exposed key, a maintained
count needs its total and the presence of each occurrence that can be deleted.
For existence alone the answer is different: if an occurrence cannot be
deleted by this consumer, all deletable occurrences can be forgotten.

The observation classes below are exact for the declared family of future
deletions, not for an arbitrary future extension of that family. This does
not prescribe how a store should build or represent its indexes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.DeletionReadouts

open Mettapedia.GSLT.Core (PolicyFamily)

section Count

variable {Id Key : Type*} [DecidableEq Id] [DecidableEq Key]

abbrev Rows (Id Key : Type*) := Finset (Id × Key)

def keyed (rows : Rows Id Key) (key : Key) : Rows Id Key :=
  rows.filter fun pair => pair.2 = key

def erase (rows : Rows Id Key) (id : Id) : Rows Id Key :=
  rows.filter fun pair => pair.1 ≠ id

def count (rows : Rows Id Key) (key : Key) : Nat := (keyed rows key).card

theorem erase_at_key (rows : Rows Id Key) (id : Id) (key : Key) :
    keyed (erase rows id) key = (keyed rows key).erase (id, key) := by
  ext pair
  obtain ⟨a, k⟩ := pair
  simp only [keyed, erase, Finset.mem_filter, Finset.mem_erase, ne_eq, Prod.mk.injEq]
  tauto

theorem count_erased (rows : Rows Id Key) (id : Id) (key : Key) :
    count (erase rows id) key = count rows key - if (id, key) ∈ rows then 1 else 0 := by
  have present : (id, key) ∈ keyed rows key ↔ (id, key) ∈ rows := by simp [keyed]
  unfold count
  rw [erase_at_key]
  by_cases hit : (id, key) ∈ rows
  · rw [if_pos hit, Finset.card_erase_of_mem (present.mpr hit)]
  · rw [if_neg hit, Finset.erase_eq_of_notMem (present.not.mpr hit), Nat.sub_zero]

variable (deletable : Set Id) (visible : Set Key)

@[ext] structure Summary where
  totals : visible → Nat
  held : deletable → visible → Bool

def readout (rows : Rows Id Key) : Summary deletable visible where
  totals key := count rows key
  held id key := decide ((id.val, key.val) ∈ rows)

def Summary.erase (state : Summary deletable visible) (id : deletable) : Summary deletable visible where
  totals key := state.totals key - if state.held id key then 1 else 0
  held other key := if other.val = id.val then false else state.held other key

theorem readout_erase (rows : Rows Id Key) (id : deletable) :
    readout deletable visible (erase rows id) =
      (readout deletable visible rows).erase deletable visible id := by
  apply Summary.ext
  · funext key
    simp [readout, Summary.erase, count_erased]
  · funext other key
    by_cases equal : other.val = id.val <;> simp [readout, Summary.erase, erase, equal]

abbrev Delete := List deletable

def run (rows : Rows Id Key) (edits : Delete deletable) : Rows Id Key :=
  edits.foldl (fun state (id : deletable) => erase state id.val) rows

def summarizeRun (state : Summary deletable visible) (edits : Delete deletable) : Summary deletable visible :=
  edits.foldl (Summary.erase deletable visible) state

theorem summarize_after_run (rows : Rows Id Key) (edits : Delete deletable) :
    readout deletable visible (run deletable rows edits) =
      summarizeRun deletable visible (readout deletable visible rows) edits := by
  induction edits generalizing rows with
  | nil => rfl
  | cons head rest ih =>
      simp only [run, summarizeRun, List.foldl_cons] at ih ⊢
      rw [ih, readout_erase]

def countFamily : PolicyFamily (Rows Id Key) where
  Policy := Delete deletable × visible
  Result := fun _ => Nat
  decide p rows := count (run deletable rows p.1) p.2

/-- The executable readout maintains every permitted sequence, without the
payloads or identities hidden from all of those operations. -/
def countReadout : (countFamily deletable visible).ReadoutRealization (readout deletable visible) where
  run p state := (summarizeRun deletable visible state p.1).totals p.2
  agrees p rows := by
    change (summarizeRun deletable visible (readout deletable visible rows) p.1).totals p.2 = _
    rw [← summarize_after_run]
    rfl

/-- A single deletion is enough to recover every bit the totals forgot.
Together with the realization this characterizes the least information
needed for the whole declared future family. -/
theorem count_equivalent_iff (left right : Rows Id Key) :
    (countFamily deletable visible).PolicyEquivalent left right ↔
      readout deletable visible left = readout deletable visible right := by
  constructor
  · intro same
    apply Summary.ext
    · funext key
      exact same ([], key)
    · funext id key
      have before : count left key = count right key := same ([], key)
      have after : count (erase left id) key = count (erase right id) key := same ([id], key)
      have lc := count_erased left id key
      have rc := count_erased right id key
      have existsRow (rows : Rows Id Key) (inRows : (id.val, key.val) ∈ rows) : 0 < count rows key := by
        apply Finset.card_pos.mpr
        exact ⟨(id.val, key.val), by simp [keyed, inRows]⟩
      by_cases one : (id.val, key.val) ∈ left <;> by_cases two : (id.val, key.val) ∈ right
      · simp [readout, one, two]
      · have some := existsRow left one
        simp only [one, two, if_true, if_false] at lc rc
        omega
      · have some := existsRow right two
        simp only [one, two, if_true, if_false] at lc rc
        omega
      · simp [readout, one, two]
  · intro same p
    let realization := countReadout deletable visible
    calc
      _ = realization.run p (readout deletable visible left) := (realization.agrees p left).symm
      _ = realization.run p (readout deletable visible right) := congrArg _ same
      _ = _ := realization.agrees p right

end Count

section Any

variable {Id : Type*} [DecidableEq Id]

/-- Readiness after deleting a finite set of identified occurrences.
Batch deletions model exactly their sequential effect at one key. -/
def anyAfter (held removed : Finset Id) : Bool := decide (held \ removed).Nonempty

/-- None represents a permanent witness at the specified deletion scope.
Which deletable occurrences also exist then has no effect on this observer. -/
def anyView (deletable held : Finset Id) : Option (Finset Id) :=
  if held ⊆ deletable then some held else none

private theorem any_true_of_external (held editable removed : Finset Id)
    (permanent : ¬ held ⊆ editable) (allowed : removed ⊆ editable) :
    anyAfter held removed = true := by
  obtain ⟨id, here, outside⟩ := Finset.not_subset.mp permanent
  exact decide_eq_true ⟨id, Finset.mem_sdiff.mpr ⟨here, fun gone => outside (allowed gone)⟩⟩

def answerFromAnyView (view : Option (Finset Id)) (removed : Finset Id) : Bool :=
  match view with
  | none => true
  | some held => anyAfter held removed

theorem any_view_exact (editable held removed : Finset Id) (allowed : removed ⊆ editable) :
    answerFromAnyView (anyView editable held) removed = anyAfter held removed := by
  by_cases all : held ⊆ editable
  · simp [anyView, all, answerFromAnyView]
  · simp [anyView, all, answerFromAnyView, any_true_of_external held editable removed all allowed]

private theorem any_delete_all (held editable : Finset Id) (all : held ⊆ editable) :
    anyAfter held editable = false := by
  simp [anyAfter, Finset.sdiff_eq_empty_iff_subset.mpr all]

private theorem singleton_test (held editable : Finset Id)
    (all : held ⊆ editable) (id : Id) :
    anyAfter held (editable.erase id) = decide (id ∈ held) := by
  have test : (held \ editable.erase id).Nonempty ↔ id ∈ held := by
    constructor
    · rintro ⟨witness, membership⟩
      obtain ⟨inHeld, notRemoved⟩ := Finset.mem_sdiff.mp membership
      by_cases same : witness = id
      · simpa only [same] using inHeld
      · exact (notRemoved (Finset.mem_erase.mpr ⟨same, all inHeld⟩)).elim
    · intro kept
      exact ⟨id, Finset.mem_sdiff.mpr ⟨kept, by simp⟩⟩
  simp only [anyAfter, test]

/-- Exact characterization of the reusable witness-only view. It can be
strictly smaller than the support for an exact count on the same store. -/
theorem any_equivalent_iff (editable left right : Finset Id) :
    (∀ removed ⊆ editable, anyAfter left removed = anyAfter right removed) ↔
      anyView editable left = anyView editable right := by
  by_cases leftAll : left ⊆ editable <;> by_cases rightAll : right ⊆ editable
  · simp only [anyView, if_pos leftAll, if_pos rightAll, Option.some.injEq]
    constructor
    · intro same
      ext id
      have check := same (editable.erase id) (Finset.erase_subset _ _)
      rw [singleton_test left editable leftAll id, singleton_test right editable rightAll id] at check
      exact decide_eq_decide.mp check
    · rintro rfl _ _
      rfl
  · simp only [anyView, if_pos leftAll, if_neg rightAll, reduceCtorEq, iff_false]
    intro bad
    have impossible := bad editable le_rfl
    rw [any_delete_all left editable leftAll,
      any_true_of_external right editable editable rightAll le_rfl] at impossible
    contradiction
  · simp only [anyView, if_neg leftAll, if_pos rightAll, reduceCtorEq, iff_false]
    intro bad
    have impossible := bad editable le_rfl
    rw [any_true_of_external left editable editable leftAll le_rfl,
      any_delete_all right editable rightAll] at impossible
    contradiction
  · simp only [anyView, if_neg leftAll, if_neg rightAll, iff_true]
    intro removed allowed
    rw [any_true_of_external left editable removed leftAll allowed,
      any_true_of_external right editable removed rightAll allowed]

/-- Restricting the future operations can only identify more states.
The converse would require information the smaller scope may discard. -/
theorem narrowing_deletion_scope (narrow wide left right : Finset Id)
    (included : narrow ⊆ wide) (same : anyView wide left = anyView wide right) :
    anyView narrow left = anyView narrow right := by
  apply (any_equivalent_iff narrow left right).mp
  intro removed allowed
  exact (any_equivalent_iff wide left right).mpr same removed (allowed.trans included)

namespace Controls

theorem permanent_witness_hides_editable_rows :
    ∀ removed ⊆ ({0} : Finset Nat),
      anyAfter {0, 1} removed = anyAfter {1} removed := by
  apply (any_equivalent_iff _ _ _).mpr
  decide

theorem expanding_scope_exposes_forgotten_rows :
    anyAfter ({0, 1} : Finset Nat) {1} = true ∧ anyAfter ({1} : Finset Nat) {1} = false := by decide

/-- In general no upgrade can recover a wider deletion view from the
narrow view alone. This is about the representation, not checking a key. -/
theorem no_upgrade_from_narrow_view_alone :
    ¬ ∃ upgrade : Option (Finset Nat) → Option (Finset Nat),
      ∀ held, upgrade (anyView {0} held) = anyView {0, 1} held := by
  rintro ⟨upgrade, works⟩
  have same : anyView ({0} : Finset Nat) {0, 1} = anyView {0} {1} := by decide
  have impossible := (works {0, 1}).symm.trans ((congrArg upgrade same).trans (works {1}))
  exact (by decide : anyView ({0, 1} : Finset Nat) {0, 1} ≠ anyView {0, 1} {1}) impossible

theorem equality_of_present_counts_does_not_survive_one_erase :
    count ({(0, 7)} : Rows Nat Nat) 7 = count {(1, 7)} 7 ∧
      count (erase ({(0, 7)} : Rows Nat Nat) 0) 7 ≠ count (erase {(1, 7)} 0) 7 := by decide

end Controls
end Any
end Mettapedia.GSLT.Dynamics.DeletionReadouts
