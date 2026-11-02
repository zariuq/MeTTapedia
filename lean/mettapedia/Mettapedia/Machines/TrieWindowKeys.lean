import Mathlib.Tactic

/-!
# A lookup's key past the match trie's window gets an index

The match trie reads a row only within a window (its first 511 elements
and 8 levels); every row agreeing there lands in one leaf.  A lookup whose
distinguishing key lies past the window was offered the whole leaf:
522-column rows asked by their last bound column took 0.36 / 1.47 / 5.79 s
for 500 / 1,000 / 2,000 lookups.  The repair indexes the key past the
window.

The model: a row is what the trie sees of it and the key past the window;
a lookup asks for both.  This file proves:
* `trie_complete` and `keyed_complete`: both selections offer every row the
  lookup matches, so the lookup's answers are the same either way;
* `trie_offers_all`: rows that agree within the window are all offered to
  each lookup by the trie;
* `keyed_offers_one`: with distinct keys the index offers each lookup one
  row;
* `lookups_quadratic` and `lookups_linear`: asking each of `n` such rows once
  costs `n * n` offered rows through the trie and `n` through the index.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TrieWindowKeys

/-- A row: what the trie's window sees of it, and its key past the window. -/
structure Row where
  seen : ℕ
  key : ℕ
  deriving DecidableEq

/-- A lookup matches a row agreeing on both. -/
def Row.matches (row ask : Row) : Bool := row.seen == ask.seen && row.key == ask.key

/-- The trie offers the rows agreeing within its window. -/
def trieOffer (rows : List Row) (ask : Row) : List Row :=
  rows.filter (fun row => row.seen == ask.seen)

/-- The index past the window offers the rows agreeing on the key. -/
def keyedOffer (rows : List Row) (ask : Row) : List Row :=
  rows.filter (fun row => row.key == ask.key)

theorem trie_complete (rows : List Row) (ask row : Row) (hrow : row ∈ rows)
    (hmatch : row.matches ask = true) : row ∈ trieOffer rows ask := by
  simp only [Row.matches, Bool.and_eq_true] at hmatch
  exact List.mem_filter.mpr ⟨hrow, hmatch.1⟩

theorem keyed_complete (rows : List Row) (ask row : Row) (hrow : row ∈ rows)
    (hmatch : row.matches ask = true) : row ∈ keyedOffer rows ask := by
  simp only [Row.matches, Bool.and_eq_true] at hmatch
  exact List.mem_filter.mpr ⟨hrow, hmatch.2⟩

/-- `n` rows agreeing within the window, keyed `0 … n-1` past it. -/
def wide (n : ℕ) : List Row := (List.range n).map (fun i => ⟨0, i⟩)

theorem trie_offers_all (n i : ℕ) :
    (trieOffer (wide n) ⟨0, i⟩).length = n := by
  simp [trieOffer, wide, List.filter_map, Function.comp_def]

theorem keyed_offers_one (n i : ℕ) (hi : i < n) :
    (keyedOffer (wide n) ⟨0, i⟩).length = 1 := by
  simp only [keyedOffer, wide, List.filter_map, Function.comp_def,
    List.length_map]
  rw [← List.countP_eq_length_filter]
  have h := List.count_eq_one_of_mem (List.nodup_range) (List.mem_range.mpr hi)
  simpa [List.count] using h

/-- Asking each row once: the rows offered in all. -/
def offered (offer : List Row → Row → List Row) (n : ℕ) : ℕ :=
  ((List.range n).map (fun i => (offer (wide n) ⟨0, i⟩).length)).sum

theorem lookups_quadratic (n : ℕ) : offered trieOffer n = n * n := by
  simp only [offered, trie_offers_all, List.map_const', List.sum_replicate,
    List.length_range, smul_eq_mul]

theorem lookups_linear (n : ℕ) : offered keyedOffer n = n := by
  unfold offered
  have : (List.range n).map (fun i => (keyedOffer (wide n) ⟨0, i⟩).length) =
      List.replicate n 1 := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact keyed_offers_one n j (by simpa using h1)
  rw [this, List.sum_replicate, smul_eq_mul, mul_one]

end Mettapedia.Machines.TrieWindowKeys
