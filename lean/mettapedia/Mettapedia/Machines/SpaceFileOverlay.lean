import Mathlib.Tactic

/-!
# A space over a file: the live layer, tombstones and compaction

A space attached to a read-only file keeps its writes in a live layer above
the file: facts added since the file was made, and tombstones for file
facts removed since.  A removal of a ground fact takes every copy of it
(`Mettapedia.Machines.RemoveAtomUnifies`), so a tombstone hides every copy
in the file; a fact added again after its removal lives in the live layer,
which tombstones do not touch.  Compaction writes a new file holding what
the space holds and empties the live layer; facts in the new file are
numbered afresh, in order.

This file proves, over facts with decidable equality:
* `lookup_overlay`: a lookup on the space answers the file's facts the
  tombstones leave and the live layer's facts, each filtered by the lookup;
* `remove_then_add`: removing a fact and adding it again leaves exactly the
  added copy;
* `compact_same_bag`, `compact_lookup`: compaction keeps the space's facts
  and every lookup's answers, with an empty live layer;
* `renumber_reads_back`, `renumber_keeps_order`: numbering the surviving
  file facts afresh reads back exactly the surviving facts, and their old
  numbers increase, so the fresh numbering keeps their order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SpaceFileOverlay

variable {Fact : Type} [DecidableEq Fact]

/-- A space over a file. -/
structure Overlay (Fact : Type) where
  file : List Fact
  added : List Fact
  tombstones : List Fact

/-- The facts the space holds: the file's facts no tombstone hides, then
the live layer's. -/
def facts (s : Overlay Fact) : List Fact :=
  s.file.filter (fun f => decide (f ∉ s.tombstones)) ++ s.added

/-- A lookup through the space, by any decidable selection. -/
def lookup (s : Overlay Fact) (sel : Fact → Bool) : List Fact :=
  (facts s).filter sel

/-- The lookup the layers answer separately. -/
def layeredLookup (s : Overlay Fact) (sel : Fact → Bool) : List Fact :=
  (s.file.filter (fun f => decide (f ∉ s.tombstones))).filter sel ++
    s.added.filter sel

theorem lookup_overlay (s : Overlay Fact) (sel : Fact → Bool) :
    lookup s sel = layeredLookup s sel := by
  simp [lookup, layeredLookup, facts, List.filter_append]

/-- Removing a ground fact: every copy in the live layer goes, and a
tombstone hides every copy in the file. -/
def remove (s : Overlay Fact) (f : Fact) : Overlay Fact :=
  { s with added := s.added.filter (fun g => decide (g ≠ f)),
           tombstones := f :: s.tombstones }

def add (s : Overlay Fact) (f : Fact) : Overlay Fact :=
  { s with added := s.added ++ [f] }

/-- Counting an element a filter rejects finds none. -/
theorem count_filter_rejected (p : Fact → Bool) (l : List Fact) (a : Fact)
    (h : p a = false) : (l.filter p).count a = 0 := by
  rw [List.count_eq_zero]
  intro hm
  have := (List.mem_filter.mp hm).2
  rw [h] at this
  exact Bool.false_ne_true this

/-- After a removal and an addition of the same fact, the space holds that
fact exactly once. -/
theorem remove_then_add (s : Overlay Fact) (f : Fact) :
    (facts (add (remove s f) f)).count f = 1 := by
  simp [facts, add, remove, List.count_append, count_filter_rejected]

/-- Compaction: a new file holding the space's facts, no live layer. -/
def compact (s : Overlay Fact) : Overlay Fact :=
  { file := facts s, added := [], tombstones := [] }

theorem compact_same_bag (s : Overlay Fact) : facts (compact s) = facts s := by
  simp [compact, facts]

theorem compact_lookup (s : Overlay Fact) (sel : Fact → Bool) :
    lookup (compact s) sel = lookup s sel := by
  simp [lookup, compact_same_bag]

/-! ## Numbering the surviving facts afresh -/

omit [DecidableEq Fact] in
theorem zipIdx_fst (l : List Fact) (n : Nat) : (l.zipIdx n).map Prod.fst = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [List.zipIdx_cons, ih]

omit [DecidableEq Fact] in
theorem zipIdx_snd_ge (l : List Fact) (n : Nat) :
    ∀ p ∈ l.zipIdx n, n ≤ p.2 := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      intro p hp
      simp only [List.zipIdx_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact le_refl _
      · exact Nat.le_of_succ_le (ih (n + 1) p hp)

omit [DecidableEq Fact] in
theorem zipIdx_increasing (l : List Fact) (n : Nat) :
    (l.zipIdx n).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      simp only [List.zipIdx_cons, List.pairwise_cons]
      exact ⟨fun p hp => Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (zipIdx_snd_ge xs (n + 1) p hp),
        ih (n + 1)⟩

/-- The surviving file facts, each with its old number, in order. -/
def survivors (file : List Fact) (keep : Fact → Bool) : List (Fact × Nat) :=
  (file.zipIdx).filter (fun p => keep p.1)

omit [DecidableEq Fact] in
/-- The new file, numbered 0, 1, 2, ... in the survivors' order, reads back
exactly the surviving facts, in the file's order. -/
theorem renumber_reads_back (file : List Fact) (keep : Fact → Bool) :
    (survivors file keep).map Prod.fst = file.filter keep := by
  unfold survivors
  show List.map Prod.fst (List.filter (keep ∘ Prod.fst) file.zipIdx) = List.filter keep file
  rw [← List.filter_map, zipIdx_fst]

omit [DecidableEq Fact] in
/-- The survivors' old numbers strictly increase, so the fresh numbering
keeps their order. -/
theorem renumber_keeps_order (file : List Fact) (keep : Fact → Bool) :
    ((survivors file keep).map Prod.snd).Pairwise (· < ·) := by
  unfold survivors
  rw [List.pairwise_map]
  exact (zipIdx_increasing file 0).filter _

end Mettapedia.Machines.SpaceFileOverlay
