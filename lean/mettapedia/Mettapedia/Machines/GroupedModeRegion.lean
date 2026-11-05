import Mettapedia.Machines.SortedRunMode
import Mettapedia.Machines.AdditiveFoldInference

/-!
# From the sorted source fold to an inferred grouped counter region

The inferred finite histogram program supplies the counters; an independently
specified mode readout supplies smallest-label tie-breaking. Grouping reuses
the existing join aggregation carrier. The finite label-domain admission is
explicit, and duplicate solutions remain counted.

This boundary concerns pure vote collection and readout. Publishing the next
label generation, source answer counts and concurrent readers are separate
parts of the enclosing label-propagation program.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModeAggregation.Grouped

open AdditiveFoldInference
open Mettapedia.Algebra.Collections

def extendCounts (n : Nat) (counts : Fin n → Nat) (label : Nat) : Nat :=
  if bound : label < n then counts ⟨label, bound⟩ else 0

def finiteReadout (n : Nat) (counts : Fin n → Nat) : Option Nat :=
  readout (extendCounts n counts) ((List.range n).filter fun label => 0 < extendCounts n counts label)

theorem inferred_counts_full (n : Nat) (labels : List Nat)
    (bounded : ∀ label ∈ labels, label < n) :
    extendCounts n (sourceRun (histogramProgram n) labels 0) = histogram labels := by
  funext label
  by_cases bound : label < n
  · simp [extendCounts, bound, inferred_histogram_counts, histogram]
  · have absent : label ∉ labels := fun member => bound (bounded label member)
    simp [extendCounts, bound, histogram, List.count_eq_zero.mpr absent]

theorem finite_readout_exact (n : Nat) (labels : List Nat)
    (bounded : ∀ label ∈ labels, label < n) :
    finiteReadout n (sourceRun (histogramProgram n) labels 0) = mode labels := by
  unfold finiteReadout mode
  rw [inferred_counts_full n labels bounded]
  apply readout_membership
  intro label
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, histogram, List.count_pos_iff]
  exact ⟨fun both => both.2, fun member => ⟨bounded label member, member⟩⟩

/-- The actual sorted-run model, not a declared target equality, meets the
counter program accepted by the proof-producing inference algorithm. -/
theorem sorted_source_to_inferred (n : Nat) (labels : List Nat)
    (bounded : ∀ label ∈ labels, label < n) :
    SortedRun.sourceMode (labels.mergeSort (· ≤ ·)) =
      finiteReadout n (sourceRun (histogramProgram n) labels 0) := by
  rw [SortedRun.sorted_source_is_histogram_readout, sparse_readout_exact, finite_readout_exact n labels bounded]

def generator (n label : Nat) : Multiplicative (Fin n → Nat) :=
  Multiplicative.ofAdd (fun i => if label = i.val then 1 else 0)

theorem fold_generator_counts (n : Nat) (labels : List Nat) :
    Multiplicative.toAdd (foldList (generator n) labels) = sourceRun (histogramProgram n) labels 0 := by
  funext i
  rw [inferred_histogram_counts]
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    by_cases same : label = i.val
    · simp [foldList, generator, same] at ih ⊢
      omega
    · simpa [foldList, generator, same] using ih

variable {Key : Type} [DecidableEq Key]

def groupedCounts (n : Nat) (rows : List (Key × Nat)) : Key → Multiplicative (Fin n → Nat) :=
  JoinAggregation.groupFold Prod.fst (fun row => generator n row.2) rows

def votes (rows : List (Key × Nat)) (key : Key) : List Nat :=
  (rows.filter fun row => row.1 = key).map Prod.snd

theorem grouped_counts_exact (n : Nat) (rows : List (Key × Nat)) (key : Key) :
    Multiplicative.toAdd (groupedCounts n rows key) = sourceRun (histogramProgram n) (votes rows key) 0 := by
  rw [groupedCounts, JoinAggregation.groupFold_apply]
  have same : foldList (fun row : Key × Nat => generator n row.2) (rows.filter fun row => row.1 = key) =
      foldList (generator n) (votes rows key) := by simp [foldList, votes, List.map_map, Function.comp_def]
  rw [same, fold_generator_counts]

theorem grouped_mode_exact (n : Nat) (rows : List (Key × Nat)) (key : Key)
    (bounded : ∀ row ∈ rows, row.2 < n) :
    finiteReadout n (Multiplicative.toAdd (groupedCounts n rows key)) =
      SortedRun.sourceMode ((votes rows key).mergeSort (· ≤ ·)) := by
  rw [grouped_counts_exact]
  symm
  apply sorted_source_to_inferred
  intro label member
  obtain ⟨row, present, equality⟩ := List.mem_map.mp member
  subst label
  exact bounded row (List.mem_filter.mp present).1

theorem grouped_merge (n : Nat) (left right : List (Key × Nat)) :
    groupedCounts n (left ++ right) = groupedCounts n left * groupedCounts n right :=
  JoinAggregation.groupFold_append _ _ _ _

/-- The enclosing source keeps the old label when there are no votes. -/
def nextLabel (old : Nat) (result : Option Nat) : Nat := result.getD old

theorem isolated_keeps_old (n old : Nat) :
    nextLabel old (finiteReadout n (sourceRun (histogramProgram n) [] 0)) = old := by
  rw [finite_readout_exact n [] (by simp)]
  rfl

namespace Controls

theorem duplicate_votes_are_not_set_votes :
    finiteReadout 3 (sourceRun (histogramProgram 3) [1, 2, 2] 0) = some 2 ∧
    finiteReadout 3 (sourceRun (histogramProgram 3) [1, 2] 0) = some 1 := by decide

theorem out_of_domain_loses_answer :
    finiteReadout 2 (sourceRun (histogramProgram 2) [3] 0) = none ∧ mode [3] = some 3 := by decide

theorem answer_equivalence_does_not_erase_effect_order :
    mode [1, 2] = mode [2, 1] ∧ ([1, 2] : List Nat) ≠ [2, 1] := by decide

end Controls
end Mettapedia.Machines.ModeAggregation.Grouped
