import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic

/-! # Ordered occurrence runs and selective cursors

The order key is a position in the source observation, not a representative
of a term class. Distinct positions can store equal payloads. Raw postings
are partitioned by a stable key; a particular quotient, or an inner join
constraint, selects which postings to read. A materialized index and a merge
cursor are two evaluations of the same read.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.OccurrenceRuns

variable {I K : Type*} [LinearOrder I]

/-- Specification of a raw posting. It need not be computed by scanning the
store: an index can maintain exactly this list at each stable key. -/
def posting [DecidableEq K] (key : I → K) (store : List I) (k : K) : List I :=
  store.filter (fun i => decide (key i = k))

/-- Reference merge. A priority queue over current heads can implement the
same merge without this reference's repeated pairwise work. -/
def merge (runs : List (List I)) : List I :=
  runs.foldr (fun a b => a.merge b (fun i j => decide (i ≤ j))) []

theorem merge_perm (runs : List (List I)) : (merge runs).Perm runs.flatten := by
  induction runs with
  | nil => exact .nil
  | cons run runs ih =>
    exact (List.merge_perm_append (fun i j : I => decide (i ≤ j))).trans
      (List.Perm.append_left run ih)

theorem mem_merge (runs : List (List I)) (i : I) :
    i ∈ merge runs ↔ ∃ run ∈ runs, i ∈ run := by
  rw [(merge_perm runs).mem_iff, List.mem_flatten]

theorem merge_sorted (runs : List (List I))
    (sorted : ∀ run ∈ runs, run.SortedLE) : (merge runs).SortedLE := by
  induction runs with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons run more ih =>
    apply List.sortedLE_iff_pairwise.mpr
    have h₁ := (sorted run (by simp)).pairwise
    have h₂ := (ih (fun xs mem => sorted xs (List.mem_cons_of_mem _ mem))).pairwise
    simpa only [merge, List.foldr_cons, decide_eq_true_eq] using
      List.pairwise_merge
        (le := fun i j : I => decide (i ≤ j))
        (fun a b c h k => decide_eq_true (le_trans (of_decide_eq_true h) (of_decide_eq_true k)))
        (fun a b => by simpa using le_total a b)
        run (merge more) (by simpa using h₁) (by simpa using h₂)

omit [LinearOrder I] in
private theorem postings_nodup [DecidableEq K] (key : I → K) (store : List I)
    (unique : store.Nodup) (keys : List K) (nodup : keys.Nodup) :
    ((keys.map (posting key store)).flatten).Nodup := by
  induction keys with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨outside, distinct⟩ := List.nodup_cons.mp nodup
    simp only [List.map_cons, List.flatten_cons, List.nodup_append]
    refine ⟨unique.filter _, ih distinct, ?_⟩
    intro a mem b mem' eq
    subst b
    simp only [posting, List.mem_filter, decide_eq_true_eq] at mem
    obtain ⟨run, used, present⟩ := List.mem_flatten.mp mem'
    obtain ⟨k', belongs, rfl⟩ := List.mem_map.mp used
    simp only [posting, List.mem_filter, decide_eq_true_eq] at present
    exact outside (mem.2.symm.trans present.2 ▸ belongs)

/-- The ordered class bucket equals a merge of stable postings. It suffices
to name keys occurring in the answer. Extra empty postings are harmless.
Repeating an active key, in contrast, repeats its occurrences. -/
theorem selected_postings_eq [DecidableEq K] (key : I → K) (store : List I)
    (sorted : store.SortedLE) (unique : store.Nodup)
    (keys : List K) (nodup : keys.Nodup) (select : K → Bool)
    (covered : ∀ i ∈ store, select (key i) = true → key i ∈ keys) :
    merge ((keys.filter select).map (posting key store)) =
      store.filter (select ∘ key) := by
  let runs := (keys.filter select).map (posting key store)
  have sortedMerge : (merge runs).SortedLE := by
    apply merge_sorted
    intro run mem
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp mem
    exact (sorted.pairwise.filter _).sortedLE
  have sortedRef : (store.filter (select ∘ key)).SortedLE :=
    (sorted.pairwise.filter _).sortedLE
  apply List.Perm.eq_of_sortedLE sortedMerge sortedRef
  apply (List.perm_ext_iff_of_nodup
    ((merge_perm runs).nodup_iff.mpr (postings_nodup key store unique _ (nodup.filter select)))
    (unique.filter _)).2
  intro i
  rw [mem_merge]
  constructor
  · rintro ⟨run, used, present⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp used
    obtain ⟨hi, eq⟩ := List.mem_filter.mp present
    have equal : key i = k := of_decide_eq_true eq
    exact List.mem_filter.mpr ⟨hi, by simpa [Function.comp_apply, equal] using
      (List.mem_filter.mp hk).2⟩
  · intro mem
    obtain ⟨hi, yes⟩ := List.mem_filter.mp mem
    refine ⟨posting key store (key i), List.mem_map.mpr ⟨key i, ?_, rfl⟩, ?_⟩
    · exact List.mem_filter.mpr ⟨covered i hi yes, yes⟩
    · simp [posting, hi]

theorem merge_count (runs : List (List I)) :
    (merge runs).length = (runs.map List.length).sum :=
  (merge_perm runs).length_eq.trans List.length_flatten

/-- A cursor seek drops exactly the prefix strictly below the requested key.
It may be implemented by binary/galloping search, rank/select or a trie seek;
none of those costs follow from the list specification alone. -/
def seek (bound : I) (run : List I) : List I :=
  run.dropWhile (fun i => decide (i < bound))

theorem seek_eq_filter (bound : I) (run : List I) (ordered : run.SortedLE) :
    seek bound run = run.filter (fun i => decide (bound ≤ i)) := by
  induction run with
  | nil => rfl
  | cons i run ih =>
    have rest := ordered.pairwise.tail.sortedLE
    by_cases h : i < bound
    · simpa [seek, h, not_le_of_gt h] using ih rest
    · have first := le_of_not_gt h
      have keep : ∀ x ∈ run, (decide (bound ≤ x) : Bool) := fun x mem =>
        decide_eq_true (first.trans ((List.pairwise_cons.mp ordered.pairwise).1 x mem))
      have all := List.filter_eq_self.mpr keep
      simp [seek, h, first, all]

/-- A filter on positions can be pushed to every run without disrupting
source order or multiplicity. -/
theorem merge_filter (runs : List (List I)) (keep : I → Bool)
    (ordered : ∀ run ∈ runs, run.SortedLE) :
    (merge runs).filter keep = merge (runs.map (List.filter keep)) := by
  apply List.Perm.eq_of_sortedLE
  · exact ((merge_sorted runs ordered).pairwise.filter _).sortedLE
  · apply merge_sorted
    intro run mem
    obtain ⟨old, belongs, rfl⟩ := List.mem_map.mp mem
    exact ((ordered old belongs).pairwise.filter _).sortedLE
  · refine ((merge_perm runs).filter keep).trans ?_
    rw [List.filter_flatten]
    exact (merge_perm _).symm

theorem seek_merge (bound : I) (runs : List (List I))
    (ordered : ∀ run ∈ runs, run.SortedLE) :
    seek bound (merge runs) = merge (runs.map (seek bound)) := by
  rw [seek_eq_filter _ _ (merge_sorted runs ordered), merge_filter _ _ ordered]
  congr 1
  exact List.map_congr_left fun run mem => (seek_eq_filter bound run (ordered run mem)).symm

end Mettapedia.GSLT.Equations.OccurrenceRuns
