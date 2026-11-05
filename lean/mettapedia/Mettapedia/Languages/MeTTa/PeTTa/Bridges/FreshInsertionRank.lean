import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

/-!
# Finite fresh-entry budgets from actual insertion receipts

Only heads in the declared finite catalogue are charged. Unrelated rows and
duplicate occurrences are allowed. A continuation must retain previously
present support before another fresh entry can use the same budget.

The resulting bound counts fresh entries, not returned answers, attempted
calls, evaluator instructions, or arbitrary callback execution. Finite
branching and source-to-agenda correspondence are additional obligations for
a complete recursive driver's termination theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionRank

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NamedSpaces

def remaining (catalogue : Finset Atom) (rows : List Atom) : Nat :=
  (catalogue \ rows.toFinset).card

theorem remaining_mono (catalogue : Finset Atom) {before after : List Atom}
    (retained : before.toFinset ⊆ after.toFinset) : remaining catalogue after ≤ remaining catalogue before := by
  apply Finset.card_le_card
  intro row member
  obtain ⟨inside, absent⟩ := Finset.mem_sdiff.mp member
  exact Finset.mem_sdiff.mpr ⟨inside, fun present => absent (retained present)⟩

theorem fresh_entry_decreases (catalogue : Finset Atom) (target : Handle) (row : Atom)
    (before after : Effects.State) (old result : List Atom)
    (inside : row ∈ catalogue) (beforeRead : before.read target = some old)
    (afterRead : after.read target = some result)
    (updated : FreshInsertionSource.update before target row = some (after, true)) :
    remaining catalogue result + 1 = remaining catalogue old := by
  obtain ⟨rows, snapshot, reading, flag⟩ := FreshInsertionSource.update_reads_back updated
  have same : rows = old := Option.some.inj (snapshot.symm.trans beforeRead)
  subst rows
  have absent : row ∉ old := by
    intro present
    simp [present] at flag
  have resultEq : result = old ++ [row] := by
    exact Option.some.inj (afterRead.symm.trans (by simpa [absent] using reading))
  rw [resultEq]
  have support : (old ++ [row]).toFinset = insert row old.toFinset := by
    ext item
    simp
  rw [remaining, support, Finset.sdiff_insert]
  exact Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨inside, by simpa using absent⟩)

/-- One fresh entry and its intervening support-preserving continuation.
The insertion receipt is executable; no conclusion about counts or descent
is supplied as an assumption. -/
structure Entry (catalogue : Finset Atom) (target : Handle) (before after : Effects.State) where
  row : Atom
  inside : row ∈ catalogue
  middle : Effects.State
  inserted : FreshInsertionSource.update before target row = some (middle, true)
  middleRows : List Atom
  afterRows : List Atom
  middleRead : middle.read target = some middleRows
  afterRead : after.read target = some afterRows
  retained : middleRows.toFinset ⊆ afterRows.toFinset

theorem Entry.decreases {catalogue : Finset Atom} {target : Handle} {before after : Effects.State}
    (entry : Entry catalogue target before after) (old result : List Atom)
    (beforeRead : before.read target = some old) (afterRead : after.read target = some result) :
    remaining catalogue result + 1 ≤ remaining catalogue old := by
  have resultEq : entry.afterRows = result := Option.some.inj (entry.afterRead.symm.trans afterRead)
  have decrease := fresh_entry_decreases catalogue target entry.row before entry.middle old entry.middleRows
    entry.inside beforeRead entry.middleRead entry.inserted
  have preserved := remaining_mono catalogue entry.retained
  rw [resultEq] at preserved
  omega

theorem Entry.before_read {catalogue : Finset Atom} {target : Handle} {before after : Effects.State}
    (entry : Entry catalogue target before after) : ∃ rows, before.read target = some rows := by
  obtain ⟨rows, snapshot, _, _⟩ := FreshInsertionSource.update_reads_back entry.inserted
  exact ⟨rows, snapshot⟩

inductive Entries (catalogue : Finset Atom) (target : Handle) : Nat → Effects.State → Effects.State → Prop
  | nil (state) : Entries catalogue target 0 state state
  | cons {count before middle after} : Entry catalogue target before middle →
      Entries catalogue target count middle after → Entries catalogue target (count + 1) before after

theorem Entries.budget {catalogue : Finset Atom} {target : Handle} {count : Nat} {before after : Effects.State}
    (entries : Entries catalogue target count before after) (old result : List Atom)
    (beforeRead : before.read target = some old) (afterRead : after.read target = some result) :
    remaining catalogue result + count ≤ remaining catalogue old := by
  induction entries generalizing old result with
  | nil state =>
      have same : old = result := Option.some.inj (beforeRead.symm.trans afterRead)
      simp [same]
  | cons entry later ih =>
      have first := entry.decreases old entry.afterRows beforeRead entry.afterRead
      have rest := ih entry.afterRows result entry.afterRead afterRead
      omega

theorem Entries.count_le {catalogue : Finset Atom} {target : Handle} {count : Nat} {before after : Effects.State}
    (entries : Entries catalogue target count before after) (old result : List Atom)
    (beforeRead : before.read target = some old) (afterRead : after.read target = some result) :
    count ≤ catalogue.card := by
  have bound := entries.budget old result beforeRead afterRead
  have size : remaining catalogue old ≤ catalogue.card := Finset.card_le_card Finset.sdiff_subset
  omega

theorem Entries.of_sequence {catalogue : Finset Atom} {target : Handle} (states : Nat → Effects.State)
    (steps : ∀ index, Nonempty (Entry catalogue target (states index) (states (index + 1))))
    (count start : Nat) : Entries catalogue target count (states start) (states (start + count)) := by
  induction count generalizing start with
  | zero => simpa using Entries.nil (states start)
  | succ count ih =>
      obtain ⟨entry⟩ := steps start
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using
        Entries.cons entry (ih (start + 1))

/-- There is no infinite sequence of catalogue-fresh entries whose intervening
continuations retain support. An infinite computation with no further fresh
entries is not ruled out by this statement. -/
theorem no_infinite_fresh_entries (catalogue : Finset Atom) (target : Handle) (states : Nat → Effects.State) :
    ¬ (∀ index, Nonempty (Entry catalogue target (states index) (states (index + 1)))) := by
  intro all
  obtain ⟨first⟩ := all 0
  obtain ⟨last⟩ := all (catalogue.card + 1)
  obtain ⟨old, beforeRead⟩ := first.before_read
  obtain ⟨result, afterRead⟩ := last.before_read
  have path := Entries.of_sequence states all (catalogue.card + 1) 0
  have bound := path.count_le old result beforeRead (by simpa only [Nat.zero_add] using afterRead)
  omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionRank
