import Mettapedia.GSLT.Equations.RecipeMatching
import Mettapedia.GSLT.Equations.OccurrenceRuns
import Mettapedia.GSLT.Contracts.OccurrenceObservers

/-! # Selective occurrence cursors

First compute the possible constructor classes. Then drive the occurrence
read from whichever coordinate is bound, rather than expanding quotient
representatives or inspecting every outer row. The cursor here exposes
the mathematical access pattern, so a hash lookup, trie projection, or
rank/select implementation can supply the postings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.SelectiveCursor

open UniversalAlgebra RecipeMatching OccurrenceRuns

variable {Key Pos : Type*} [DecidableEq Key] [LinearOrder Pos]

def read (get : Key → List Pos) (keys : List Key) : List Pos :=
  merge (keys.map get)

theorem read_exact (keyOf : Pos → Key) (store : List Pos)
    (ordered : store.SortedLE) (unique : store.Nodup) (get : Key → List Pos)
    (keys : List Key) (distinct : keys.Nodup) (test : Key → Bool)
    (exactKeys : ∀ r ∈ store, keyOf r ∈ keys ↔ test (keyOf r) = true)
    (post : ∀ k ∈ keys, get k = posting keyOf store k) :
    read get keys = store.filter (test ∘ keyOf) := by
  let active := fun k => keys.contains k
  have source : merge (keys.map get) = merge ((keys.filter active).map (posting keyOf store)) := by
    rw [List.filter_eq_self.mpr (by intro k member; simpa [active] using member)]
    exact congrArg merge (List.map_congr_left post)
  rw [read, source, selected_postings_eq keyOf store ordered unique keys distinct active
    (by intro r _ found; simpa [active] using found)]
  apply List.filter_congr
  intro r belongs
  apply Bool.eq_iff_iff.mpr
  simpa [active] using exactKeys r belongs

/-- Results of a compound recipe query can drive an ordered occurrence
cursor. The same theorem applies to a child coordinate of another recipe
relation: store its tuple occurrences and use that coordinate for `keyOf`. -/
theorem recipe_read_exact {S : Signature} (g : Catalogue S Key) (p : Term S)
    (ρ : Nat → Key) (keyOf : Pos → Key) (store : List Pos) (ordered : store.SortedLE)
    (unique : store.Nodup) (get : Key → List Pos) (keys : List Key) (distinct : keys.Nodup)
    (support : ∀ r ∈ store, keyOf r ∈ keys ↔ g.Matches ρ p (keyOf r))
    (post : ∀ k ∈ keys, get k = posting keyOf store k) :
    read get keys =
      store.filter (fun r => decide (keyOf r ∈ g.roots ρ p)) := by
  apply read_exact keyOf store ordered unique get keys distinct
    (fun k => decide (k ∈ g.roots ρ p)) _ post
  intro r belongs
  simpa only [decide_eq_true_eq, g.mem_roots_iff] using support r belongs

/-- Number of posting requests in the reverse plan, counted separately
from index-navigation cost and result materialization. -/
def requests (keys : List Key) : Nat := keys.length

/-- This returns an exact completed count without comparing or emitting
any occurrence ID. The input header must count the already-eligible
posting, with no missing row predicates or residual filters. -/
def count (size : Key → Nat) (keys : List Key) : Nat := (keys.map size).sum

omit [DecidableEq Key] in
theorem count_eq_read (get : Key → List Pos) (size : Key → Nat)
    (keys : List Key) (valid : ∀ k ∈ keys, size k = (get k).length) :
    count size keys = (read get keys).length := by
  rw [count, read, merge_count, List.map_map]
  exact congrArg List.sum (List.map_congr_left valid)

omit [DecidableEq Key] in
theorem count_observation {Row : Type} [LinearOrder Row]
    (get : Key → List Row) (size : Key → Nat) (keys : List Key)
    (valid : ∀ k ∈ keys, size k = (get k).length) :
    count size keys = Contracts.OccurrenceObservers.observe .count [read get keys] := by
  simpa [Contracts.OccurrenceObservers.observe] using count_eq_read get size keys valid

/-- Minimum among the nonempty posting heads. Posting order is the actual
source occurrence order, not order of class IDs or preference rank. -/
def first (head : Key → Option Pos) (keys : List Key) : Option Pos :=
  (keys.filterMap head).min?

private theorem head_min (xs : List Pos) (h : xs.SortedLE) : xs.min? = xs.head? :=
  List.min?_eq_head? (h.pairwise.imp fun le => min_eq_left le)

omit [DecidableEq Key] in
theorem first_eq_read (get : Key → List Pos) (keys : List Key)
    (ordered : ∀ k ∈ keys, (get k).SortedLE) :
    first (fun k => (get k).head?) keys = (read get keys).head? := by
  have readsOrdered : (read get keys).SortedLE := by
    apply merge_sorted
    intro run belongs
    obtain ⟨k, mem, rfl⟩ := List.mem_map.mp belongs
    exact ordered k mem
  rw [first, ← head_min _ readsOrdered]
  cases out : (keys.filterMap fun k => (get k).head?).min? with
  | none =>
    symm
    apply List.min?_eq_none_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p belongs
    obtain ⟨run, used, hit⟩ := (mem_merge _ _).1 belongs
    obtain ⟨k, mem, rfl⟩ := List.mem_map.mp used
    have noHeads := List.min?_eq_none_iff.mp out
    cases h : get k with
    | nil => simp [h] at hit
    | cons x xs =>
      have hx : x ∈ keys.filterMap (fun k => (get k).head?) :=
        List.mem_filterMap.mpr ⟨k, mem, by simp [h]⟩
      simp [noHeads] at hx
  | some p =>
    symm
    obtain ⟨belongs, least⟩ := List.min?_eq_some_iff.mp out
    obtain ⟨k, mem, hk⟩ := List.mem_filterMap.mp belongs
    apply List.min?_eq_some_iff.mpr
    refine ⟨(mem_merge _ _).2 ⟨get k, List.mem_map.mpr ⟨k, mem, rfl⟩,
      List.mem_of_head? hk⟩, ?_⟩
    intro q hit
    obtain ⟨run, used, hq⟩ := (mem_merge _ _).1 hit
    obtain ⟨j, hasKey, rfl⟩ := List.mem_map.mp used
    cases h : get j with
    | nil => simp [h] at hq
    | cons x xs =>
      have hx : (get j).min? = some x := by rw [head_min _ (ordered j hasKey), h]; rfl
      exact (least x (List.mem_filterMap.mpr ⟨j, hasKey, by simp [h]⟩)).trans
        ((List.min?_eq_some_iff.mp hx).2 q hq)

/-- Metadata-only read lower bound: if a live bucket is not among the
inspected ones, two compatible tables differ in their answer. This is
about independent headers, not a ban on maintained aggregate indices. -/
theorem unknown_bucket_changes_count (keys inspected : List Key) (k : Key)
    (included : k ∈ keys) (notInspected : k ∉ inspected) :
    ∃ a b : Key → Nat, (∀ i ∈ inspected, a i = b i) ∧ count a keys ≠ count b keys := by
  refine ⟨fun _ => 0, fun i => if i = k then 1 else 0, ?_, ?_⟩
  · intro i seen
    have ne : i ≠ k := fun h => notInspected (h ▸ seen)
    simp [ne]
  · have mem : 1 ∈ keys.map (fun i => if i = k then 1 else 0) :=
      List.mem_map.mpr ⟨k, included, by simp⟩
    have gt := List.le_sum_of_mem mem
    simp [count]
    omega

end Mettapedia.GSLT.Equations.SelectiveCursor
