import Mettapedia.Machines.ModeAggregation

/-!
# The sorted run fold used by label propagation

The source stores a current label/count and a completed best label/count.
It replaces the best only on a strict count increase. The invariant exposes
the already completed runs and the current repeated suffix; sortedness makes
every completed label smaller than the current one. This derives the tie rule
instead of assuming that the source implements the histogram readout.

`Option Nat` encodes the source's sentinel label versus a natural label; its
`none` is not an evaluator empty-answer event. The enclosing source bypasses
mode on an empty vote list and keeps the old vertex label instead.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModeAggregation.SortedRun

structure Choice where
  label : Option Nat
  count : Nat
  deriving DecidableEq

def BestOf (labels : List Nat) (choice : Choice) : Prop :=
  match choice.label with
  | none => labels = [] ∧ choice.count = 0
  | some label => IsMode labels label ∧ choice.count = labels.count label

structure State where
  current : Option Nat
  runCount : Nat
  best : Choice
  deriving DecidableEq

def initial : State := ⟨none, 0, ⟨none, 0⟩⟩

def finish (state : State) : Choice :=
  if state.best.count < state.runCount then ⟨state.current, state.runCount⟩ else state.best

def step (state : State) (label : Nat) : State :=
  if state.current = some label then {state with runCount := state.runCount + 1}
  else ⟨some label, 1, finish state⟩

def sourceMode (labels : List Nat) : Option Nat := (finish (labels.foldl step initial)).label

def Invariant (labels : List Nat) (state : State) : Prop :=
  match state.current with
  | none => labels = [] ∧ state.runCount = 0 ∧ BestOf [] state.best
  | some current => ∃ completed : List Nat,
      labels = completed ++ List.replicate state.runCount current ∧
      0 < state.runCount ∧ (∀ label ∈ completed, label < current) ∧ BestOf completed state.best

private theorem count_current (completed : List Nat) (current n : Nat)
    (earlier : ∀ label ∈ completed, label < current) :
    (completed ++ List.replicate n current).count current = n := by
  have absent : current ∉ completed := fun member => (Nat.lt_irrefl _ (earlier current member))
  simp [List.count_eq_zero.mpr absent]

private theorem count_other (completed : List Nat) (current n label : Nat) (different : label ≠ current) :
    (completed ++ List.replicate n current).count label = completed.count label := by
  have absent : label ∉ List.replicate n current := fun member => different (List.eq_of_mem_replicate member)
  simp [List.count_append, List.count_eq_zero.mpr absent]

theorem append_run_best (completed : List Nat) (current n : Nat) (positive : 0 < n)
    (earlier : ∀ label ∈ completed, label < current) (best : Choice) (valid : BestOf completed best) :
    BestOf (completed ++ List.replicate n current)
      (if best.count < n then ⟨some current, n⟩ else best) := by
  have currentCount := count_current completed current n earlier
  have currentMember : current ∈ completed ++ List.replicate n current := by simp [positive.ne']
  cases held : best.label with
  | none =>
    obtain ⟨empty, zero⟩ := (show completed = [] ∧ best.count = 0 by simpa [BestOf, held] using valid)
    subst completed
    simp only [zero, positive, ↓reduceIte, BestOf]
    refine ⟨⟨currentMember, ?_⟩, currentCount.symm⟩
    intro label member
    have same : label = current := List.eq_of_mem_replicate (by simpa using member)
    subst label
    exact ⟨le_rfl, fun _ => le_rfl⟩
  | some winner =>
    obtain ⟨winning, weight⟩ := (show IsMode completed winner ∧ best.count = completed.count winner by
      simpa [BestOf, held] using valid)
    have winnerEarlier := earlier winner winning.1
    have winnerCount := count_other completed current n winner (Nat.ne_of_lt winnerEarlier)
    by_cases larger : best.count < n
    · simp only [larger, ↓reduceIte, BestOf]
      refine ⟨⟨currentMember, ?_⟩, currentCount.symm⟩
      intro label member
      by_cases same : label = current
      · subst label; exact ⟨le_rfl, fun _ => le_rfl⟩
      · have oldMember : label ∈ completed := by
          rcases List.mem_append.mp member with old | repeated
          · exact old
          · exact False.elim (same (List.eq_of_mem_replicate repeated))
        rw [count_other completed current n label same, currentCount]
        have bounded := (winning.2 label oldMember).1
        constructor <;> omega
    · simp only [larger, ↓reduceIte, BestOf, held]
      refine ⟨⟨List.mem_append_left _ winning.1, ?_⟩, weight.trans winnerCount.symm⟩
      intro label member
      by_cases same : label = current
      · subst label
        rw [currentCount, winnerCount]
        constructor
        · omega
        · intro _; exact Nat.le_of_lt winnerEarlier
      · have oldMember : label ∈ completed := by
          rcases List.mem_append.mp member with old | repeated
          · exact old
          · exact False.elim (same (List.eq_of_mem_replicate repeated))
        rw [count_other completed current n label same, winnerCount]
        exact winning.2 label oldMember

theorem finish_correct (labels : List Nat) (state : State) (valid : Invariant labels state) :
    BestOf labels (finish state) := by
  cases current : state.current with
  | none =>
    obtain ⟨empty, zero, best⟩ := (show labels = [] ∧ state.runCount = 0 ∧ BestOf [] state.best by
      simpa [Invariant, current] using valid)
    simpa [finish, zero, empty] using best
  | some label =>
    obtain ⟨completed, shape, positive, earlier, best⟩ :=
      (show ∃ completed : List Nat, labels = completed ++ List.replicate state.runCount label ∧
        0 < state.runCount ∧ (∀ x ∈ completed, x < label) ∧ BestOf completed state.best by
          simpa [Invariant, current] using valid)
    rw [shape]
    simpa [finish, current] using append_run_best completed label state.runCount positive earlier state.best best

theorem initial_valid : Invariant [] initial := by simp [Invariant, initial, BestOf]

theorem step_valid (labels : List Nat) (state : State) (next : Nat) (valid : Invariant labels state)
    (ordered : ∀ label ∈ labels, label ≤ next) : Invariant (labels ++ [next]) (step state next) := by
  have finished := finish_correct labels state valid
  cases current : state.current with
  | none =>
    have empty : labels = [] := (show labels = [] ∧ state.runCount = 0 ∧ BestOf [] state.best by
      simpa [Invariant, current] using valid).1
    simp only [step, current, reduceCtorEq, ↓reduceIte, Invariant]
    refine ⟨[], by simp [empty], by omega, by simp, ?_⟩
    simpa [empty] using finished
  | some label =>
    obtain ⟨completed, shape, positive, earlier, best⟩ :=
      (show ∃ completed : List Nat, labels = completed ++ List.replicate state.runCount label ∧
        0 < state.runCount ∧ (∀ x ∈ completed, x < label) ∧ BestOf completed state.best by
          simpa [Invariant, current] using valid)
    by_cases same : label = next
    · subst next
      simp only [step, current, ↓reduceIte, Invariant]
      refine ⟨completed, ?_, by omega, earlier, best⟩
      rw [shape, List.replicate_add]
      simp [List.append_assoc]
    · have lastMember : label ∈ labels := by rw [shape]; simp [positive.ne']
      have less : label < next := lt_of_le_of_ne (ordered label lastMember) same
      simp only [step, current, Option.some.injEq, same, ↓reduceIte, Invariant]
      refine ⟨labels, by simp, by omega, ?_, finished⟩
      intro old member
      rw [shape] at member
      rcases List.mem_append.mp member with prior | repeated
      · exact (earlier old prior).trans less
      · exact (List.eq_of_mem_replicate repeated) ▸ less

theorem scan_valid (labels : List Nat) (sorted : labels.Pairwise (· ≤ ·)) :
    Invariant labels (labels.foldl step initial) := by
  induction labels using List.reverseRecOn with
  | nil => exact initial_valid
  | append_singleton labels next ih =>
    have parts := List.pairwise_append.mp sorted
    have oldSorted := parts.1
    have ordered : ∀ label ∈ labels, label ≤ next := by
      intro label member
      exact parts.2.2 label member next (by simp)
    rw [List.foldl_append]
    exact step_valid labels (labels.foldl step initial) next (ih oldSorted) ordered

theorem source_equals_mode (labels : List Nat) (sorted : labels.Pairwise (· ≤ ·)) :
    sourceMode labels = mode labels := by
  have valid := finish_correct labels (labels.foldl step initial) (scan_valid labels sorted)
  cases answer : (finish (labels.foldl step initial)).label with
  | none =>
    have empty := (show labels = [] ∧ (finish (labels.foldl step initial)).count = 0 by
      simpa [BestOf, answer] using valid).1
    unfold sourceMode
    rw [answer]
    exact ((mode_none_iff labels).mpr empty).symm
  | some winner =>
    have winning := (show IsMode labels winner ∧ _ by simpa [BestOf, answer] using valid).1
    simpa [sourceMode, answer] using ((mode_spec labels winner).mpr winning).symm

theorem sorted_source_is_histogram_readout (labels : List Nat) :
    sourceMode (labels.mergeSort (· ≤ ·)) = sparseReadout (sparseHistogram labels) := by
  rw [source_equals_mode _ (List.pairwise_mergeSort' _ _), sparse_readout_exact]
  exact mode_perm (List.mergeSort_perm _ _)

namespace Controls

theorem source_smallest_tie : sourceMode [1, 1, 2, 2] = some 1 := by decide
theorem unsorted_counterexample :
    sourceMode [1, 2, 2, 1, 1] = some 2 ∧ mode [1, 2, 2, 1, 1] = some 1 := by decide

def finishNonStrict (state : State) : Choice :=
  if state.best.count ≤ state.runCount then ⟨state.current, state.runCount⟩ else state.best

theorem nonstrict_tie_is_wrong :
    (finishNonStrict ([1, 1, 2, 2].foldl step initial)).label = some 2 ∧
    sourceMode [1, 1, 2, 2] = some 1 := by decide

end Controls
end Mettapedia.Machines.ModeAggregation.SortedRun
