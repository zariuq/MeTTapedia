import Mettapedia.Machines.JoinAggregation
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finsupp.Multiset

/-!
# Histogram aggregation with a smallest-label mode readout

The count loop is executable and independent of the list-count specification.
Histograms compose by pointwise addition. The winner is only a readout: it is
not asserted to compose on its own. Lexicographic scores make the tie rule
explicit, independently of the order used to enumerate candidate labels.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModeAggregation

abbrev Counts := Nat → Nat

def histogram (labels : List Nat) : Counts := fun label => labels.count label

def countStep (counts : Counts) (label : Nat) : Counts :=
  Function.update counts label (counts label + 1)

def countLoop (labels : List Nat) (counts : Counts) : Counts := labels.foldl countStep counts

theorem countLoop_exact (labels : List Nat) (counts : Counts) :
    countLoop labels counts = counts + histogram labels := by
  induction labels generalizing counts with
  | nil => funext label; simp [countLoop, histogram]
  | cons head rest ih =>
    rw [countLoop, List.foldl_cons]
    change countLoop rest (countStep counts head) = _
    rw [ih]
    funext label
    by_cases same : label = head
    · subst label; simp [countStep, histogram, Nat.add_comm, Nat.add_left_comm]
    · simp [countStep, histogram, same, Ne.symm same]

theorem histogram_append (left right : List Nat) :
    histogram (left ++ right) = histogram left + histogram right := by
  funext label
  simp [histogram]

theorem histogram_perm {left right : List Nat} (permutation : left.Perm right) :
    histogram left = histogram right := by
  funext label
  exact permutation.count_eq label

/-- Full counts support one-occurrence deletion with truncated subtraction.
This is extra structure beyond the additive merge law; a compressed readout
need not retain the data required to execute it. -/
theorem histogram_erase (labels : List Nat) (removed : Nat) :
    histogram (labels.erase removed) =
      Function.update (histogram labels) removed (histogram labels removed - 1) := by
  funext label
  by_cases same : label = removed
  · subst label; simp [histogram]
  · simp [histogram, same, List.count_erase_of_ne same]

abbrev Score := Nat ×ₗ OrderDual Nat

def score (counts : Counts) (label : Nat) : Score := toLex (counts label, label)

theorem score_le_iff (counts : Counts) (a b : Nat) :
    score counts a ≤ score counts b ↔ counts a ≤ counts b ∧ (counts a = counts b → b ≤ a) := by
  exact Prod.Lex.toLex_le_toLex'

theorem score_injective (counts : Counts) : Function.Injective (score counts) := by
  intro a b same
  exact congrArg (fun p : Score => (ofLex p).2) same

def readout (counts : Counts) (candidates : List Nat) : Option Nat := candidates.argmax (score counts)

/-- Independent count and smallest-tie specification for a nonempty answer. -/
def IsMode (labels : List Nat) (winner : Nat) : Prop :=
  winner ∈ labels ∧ ∀ label ∈ labels,
    labels.count label ≤ labels.count winner ∧ (labels.count label = labels.count winner → winner ≤ label)

theorem readout_some_iff (counts : Counts) (candidates : List Nat) (winner : Nat) :
    readout counts candidates = some winner ↔
      winner ∈ candidates ∧ ∀ label ∈ candidates, score counts label ≤ score counts winner := by
  constructor
  · intro answer
    exact ⟨List.argmax_mem answer, fun _ member => List.le_of_mem_argmax member answer⟩
  · rintro ⟨member, maximal⟩
    apply List.argmax_eq_some_iff.mpr
    refine ⟨member, maximal, ?_⟩
    intro label present dominates
    have same := score_injective counts (le_antisymm dominates (maximal label present))
    subst label
    rfl

theorem readout_membership (counts : Counts) {left right : List Nat}
    (same : ∀ label, label ∈ left ↔ label ∈ right) : readout counts left = readout counts right := by
  cases answer : readout counts left with
  | none =>
    have empty : left = [] := List.argmax_eq_none.mp answer
    have rightEmpty : right = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro label present
      simpa [empty] using (same label).mpr present)
    simp [rightEmpty, readout]
  | some winner =>
    have result := (readout_some_iff counts left winner).mp answer
    symm
    apply (readout_some_iff counts right winner).mpr
    exact ⟨(same winner).mp result.1, fun label member => result.2 label ((same label).mpr member)⟩

def mode (labels : List Nat) : Option Nat := readout (histogram labels) labels

theorem mode_spec (labels : List Nat) (winner : Nat) : mode labels = some winner ↔ IsMode labels winner := by
  simp only [mode, readout_some_iff, score_le_iff, histogram, IsMode]

theorem mode_none_iff (labels : List Nat) : mode labels = none ↔ labels = [] := List.argmax_eq_none

theorem mode_perm {left right : List Nat} (permutation : left.Perm right) : mode left = mode right := by
  unfold mode
  rw [histogram_perm permutation]
  exact readout_membership _ (fun _ => permutation.mem_iff)

theorem countLoop_mode (labels : List Nat) :
    readout (countLoop labels 0) labels = mode labels := by
  rw [countLoop_exact, zero_add]
  rfl

/-- A sparse histogram, interpreted independently through finite support. -/
noncomputable def sparseHistogram (labels : List Nat) : Nat →₀ Nat :=
  Multiset.toFinsupp (labels : Multiset Nat)

noncomputable def sparseReadout (counts : Nat →₀ Nat) : Option Nat :=
  readout counts counts.support.toList

theorem sparseHistogram_add (left right : List Nat) :
    sparseHistogram (left ++ right) = sparseHistogram left + sparseHistogram right := by
  exact Multiset.toFinsupp_add (left : Multiset Nat) (right : Multiset Nat)

theorem sparse_readout_exact (labels : List Nat) : sparseReadout (sparseHistogram labels) = mode labels := by
  unfold sparseReadout mode
  have counts : (sparseHistogram labels : Counts) = histogram labels := by
    funext label
    simp [sparseHistogram, histogram]
  rw [counts]
  apply readout_membership
  intro label
  simp [sparseHistogram]

/-- Partial summaries merge; partial winners need not. -/
theorem merged_readout_exact (left right : List Nat) :
    sparseReadout (sparseHistogram left + sparseHistogram right) = mode (left ++ right) := by
  rw [← sparseHistogram_add, sparse_readout_exact]

namespace Controls

theorem smallest_tie : mode [2, 1, 2, 1] = some 1 := by decide
theorem multiplicity_matters : mode [1, 2, 2] = some 2 ∧ mode [1, 2] = some 1 := by decide

theorem winner_is_not_a_summary :
    mode [1, 1, 2] = mode [1, 1, 1] ∧
    mode ([1, 1, 2] ++ [2, 2]) ≠ mode ([1, 1, 1] ++ [2, 2]) := by decide

theorem no_winner_merge : ¬ ∃ combine : Option Nat → Option Nat → Option Nat,
    ∀ left right, mode (left ++ right) = combine (mode left) (mode right) := by
  rintro ⟨combine, correct⟩
  have a := correct [1, 1, 2] [2, 2]
  have b := correct [1, 1, 1] [2, 2]
  have equal : mode [1, 1, 2] = mode [1, 1, 1] := by decide
  rw [equal] at a
  exact winner_is_not_a_summary.2 (a.trans b.symm)

end Controls
end Mettapedia.Machines.ModeAggregation
