import Mettapedia.Machines.BoundedSearchPortfolio
import Mettapedia.Machines.RuntimePlumbing.SuccessPriority
import Mettapedia.Machines.ObserverLicence.Presentations

/-!
# Bounded witnesses under success-priority value selection

Errors here are ordinary replies classified by a pure predicate, not raised
control. The operational stack expands the existing search space and retains
its actual frontier. Successes can fill a demand before exhaustion; errors
can be published only after uncut exhaustion establishes that no success was
hidden. A cut-off error-only batch remains private.

This is an observer-boundary model. It does not identify every nested HE
selection boundary, classify native arithmetic or establish C correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open BoundedSearchPortfolio (Cursor Status Iteration)
open RuntimePlumbing

universe u
variable {S : Type u} {Reply : Type}

def status (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply) : Status :=
  if demand ≤ (SuccessPriority.successes isError cursor.answers).length then .full
  else if cursor.frontier.isEmpty then
    if cursor.cut then .cutoff else .exhausted
  else .paused

def tick (space : Space S Reply) (isError : Reply → Bool) (demand : Nat)
    (cursor : Cursor S Reply) : Cursor S Reply :=
  if status isError demand cursor = .paused then
    BoundedSearchPortfolio.expandOne space cursor else cursor

def advance (space : Space S Reply) (isError : Reply → Bool) (demand : Nat) :
    Nat → Cursor S Reply → Cursor S Reply
  | 0, cursor => cursor
  | fuel + 1, cursor => advance space isError demand fuel (tick space isError demand cursor)

def run (space : Space S Reply) (isError : Reply → Bool) (demand fuel depth : Nat)
    (root : S) : Cursor S Reply :=
  advance space isError demand fuel (BoundedSearchPortfolio.start root depth)

def batch (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply) : List Reply :=
  (SuccessPriority.select isError cursor.answers).take demand

theorem advance_add (space : Space S Reply) (isError : Reply → Bool)
    (demand first second : Nat) (cursor : Cursor S Reply) :
    advance space isError demand (first + second) cursor =
      advance space isError demand second (advance space isError demand first cursor) := by
  induction first generalizing cursor with
  | zero => simp [advance]
  | succ first ih =>
      simp only [Nat.succ_add, advance]
      exact ih (tick space isError demand cursor)

theorem advance_occurrences (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel : Nat) (cursor : Cursor S Reply) :
    (advance space isError demand fuel cursor).answers ++
        BoundedSearchPortfolio.pendingAnswers space (advance space isError demand fuel cursor).frontier =
      cursor.answers ++ BoundedSearchPortfolio.pendingAnswers space cursor.frontier := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      rw [advance, ih]
      unfold tick
      split
      · exact BoundedSearchPortfolio.expandOne_answers space cursor
      · rfl

theorem advance_cut (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel : Nat) (cursor : Cursor S Reply) :
    ((advance space isError demand fuel cursor).cut ||
      BoundedSearchPortfolio.pendingCut space (advance space isError demand fuel cursor).frontier) =
      (cursor.cut || BoundedSearchPortfolio.pendingCut space cursor.frontier) := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      rw [advance, ih]
      unfold tick
      split
      · exact BoundedSearchPortfolio.expandOne_cut space cursor
      · rfl

theorem run_occurrences (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel depth : Nat) (root : S) :
    (run space isError demand fuel depth root).answers ++
      BoundedSearchPortfolio.pendingAnswers space (run space isError demand fuel depth root).frontier =
        (bounded space depth root).1 := by
  simpa [run, BoundedSearchPortfolio.start, Cursor.answers,
    BoundedSearchPortfolio.pendingAnswers] using
      advance_occurrences space isError demand fuel (BoundedSearchPortfolio.start root depth)

theorem run_cut (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel depth : Nat) (root : S) :
    ((run space isError demand fuel depth root).cut ||
      BoundedSearchPortfolio.pendingCut space (run space isError demand fuel depth root).frontier) =
        (bounded space depth root).2 := by
  simpa [run, BoundedSearchPortfolio.start, BoundedSearchPortfolio.pendingCut] using
    advance_cut space isError demand fuel (BoundedSearchPortfolio.start root depth)

theorem full_has_enough (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply)
    (full : status isError demand cursor = .full) :
    demand ≤ (SuccessPriority.successes isError cursor.answers).length := by
  by_contra notEnough
  simp only [status, notEnough, ↓reduceIte] at full
  split at full <;> simp_all
  split at full <;> contradiction

theorem exhausted_shape (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply)
    (exhausted : status isError demand cursor = .exhausted) :
    cursor.frontier = [] ∧ cursor.cut = false := by
  unfold status at exhausted
  split at exhausted
  · contradiction
  · split at exhausted
    · split at exhausted <;> simp_all [List.isEmpty_iff]
    · contradiction

theorem run_exhausted_exact (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel depth : Nat) (root : S)
    (exhausted : status isError demand (run space isError demand fuel depth root) = .exhausted) :
    (run space isError demand fuel depth root).answers = (bounded space depth root).1 ∧
      (bounded space depth root).2 = false := by
  obtain ⟨empty, uncut⟩ := exhausted_shape isError demand _ exhausted
  have occurrences := run_occurrences space isError demand fuel depth root
  have cuts := run_cut space isError demand fuel depth root
  exact ⟨by simpa [empty, BoundedSearchPortfolio.pendingAnswers] using occurrences,
    by simpa [empty, uncut, BoundedSearchPortfolio.pendingCut] using cuts.symm⟩

theorem full_batch_has_no_error (isError : Reply → Bool) (demand : Nat)
    (cursor : Cursor S Reply) (positive : 0 < demand)
    (full : status isError demand cursor = .full) :
    (batch isError demand cursor).length = demand ∧
      ∀ value ∈ batch isError demand cursor, isError value = false := by
  have enough := full_has_enough isError demand cursor full
  have nonempty : SuccessPriority.successes isError cursor.answers ≠ [] := by
    intro empty
    simp [empty] at enough
    omega
  rw [batch, SuccessPriority.select_of_success isError cursor.answers nonempty]
  constructor
  · simp [List.length_take, Nat.min_eq_left enough]
  · intro value member
    have inSuccess := List.mem_of_mem_take member
    simpa [SuccessPriority.successes] using (List.mem_filter.mp inSuccess).2

def BatchMeaning (space : Space S Reply) (root : S) (isError : Reply → Bool)
    (demand : Nat) (answers : List Reply) : Prop :=
  ∃ depth, answers = (SuccessPriority.select isError (bounded space depth root).1).take demand ∧
    (demand ≤ (SuccessPriority.successes isError (bounded space depth root).1).length ∨
      (bounded space depth root).2 = false)

theorem cursor_ready_meaning (space : Space S Reply) (isError : Reply → Bool)
    (demand depth : Nat) (root : S) (cursor : Cursor S Reply)
    (occurrences : cursor.answers ++ BoundedSearchPortfolio.pendingAnswers space cursor.frontier =
      (bounded space depth root).1)
    (cuts : (cursor.cut || BoundedSearchPortfolio.pendingCut space cursor.frontier) =
      (bounded space depth root).2)
    (ready : BoundedSearchPortfolio.ready (status isError demand cursor) = true) :
    BatchMeaning space root isError demand (batch isError demand cursor) := by
  cases outcome : status isError demand cursor with
  | paused | cutoff => simp [outcome, BoundedSearchPortfolio.ready] at ready
  | exhausted =>
      obtain ⟨empty, uncutCursor⟩ := exhausted_shape isError demand cursor outcome
      have exactAnswers : cursor.answers = (bounded space depth root).1 := by
        simpa [empty, BoundedSearchPortfolio.pendingAnswers] using occurrences
      have uncut : (bounded space depth root).2 = false := by
        simpa [empty, uncutCursor, BoundedSearchPortfolio.pendingCut] using cuts.symm
      exact ⟨depth, by simp only [batch, exactAnswers], Or.inr uncut⟩
  | full =>
      have enough := full_has_enough isError demand cursor outcome
      have successes := congrArg (SuccessPriority.successes isError) occurrences
      rw [SuccessPriority.successes_append] at successes
      have totalEnough : demand ≤ (SuccessPriority.successes isError (bounded space depth root).1).length := by
        rw [← successes, List.length_append]
        omega
      refine ⟨depth, ?_, Or.inl totalEnough⟩
      by_cases zero : demand = 0
      · simp [batch, zero]
      have nonempty : SuccessPriority.successes isError cursor.answers ≠ [] := by
        intro empty
        simp [empty] at enough
        omega
      have wholeNonempty : SuccessPriority.successes isError (bounded space depth root).1 ≠ [] := by
        intro empty
        simp [empty] at totalEnough
        omega
      rw [batch, SuccessPriority.select_of_success _ _ nonempty,
        SuccessPriority.select_of_success _ _ wholeNonempty, ← successes]
      exact (List.take_append_of_le_length enough).symm

theorem run_ready_meaning (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel depth : Nat) (root : S)
    (ready : BoundedSearchPortfolio.ready (status isError demand
      (run space isError demand fuel depth root)) = true) :
    BatchMeaning space root isError demand (batch isError demand (run space isError demand fuel depth root)) :=
  cursor_ready_meaning space isError demand depth root _
    (run_occurrences space isError demand fuel depth root)
    (run_cut space isError demand fuel depth root) ready

theorem error_publication_proves_no_success (space : Space S Reply) (root : S)
    (isError : Reply → Bool) (demand : Nat) (answers : List Reply)
    (meaning : BatchMeaning space root isError demand answers)
    {value : Reply} (member : value ∈ answers) (error : isError value = true) :
    ∀ other, IsAnswer space root other → isError other = true := by
  obtain ⟨depth, exactAnswers, enoughOrUncut⟩ := meaning
  rw [exactAnswers] at member
  have selected := List.mem_of_mem_take member
  have none : SuccessPriority.successes isError (bounded space depth root).1 = [] := by
    by_contra nonempty
    rw [SuccessPriority.select_of_success _ _ nonempty] at selected
    have notError := (List.mem_filter.mp selected).2
    simp [error] at notError
  have positive : 0 < demand := by
    by_contra nonpositive
    have zero : demand = 0 := by omega
    simp [zero] at member
  have uncut : (bounded space depth root).2 = false := by
    rcases enoughOrUncut with enough | uncut
    · simp [none] at enough
      omega
    · exact uncut
  intro other answer
  obtain ⟨_distance, reaches⟩ := answer
  have present := bounded_exhaustive space reaches uncut
  by_contra notError
  have errorFalse : isError other = false := Bool.eq_false_iff.mpr notError
  have inSuccess : other ∈ SuccessPriority.successes isError (bounded space depth root).1 := by
    simp [SuccessPriority.successes, present, errorFalse]
  rw [none] at inSuccess
  contradiction

namespace Controls

abbrev Sample := Except Nat Nat

def isError : Sample → Bool
  | .error _ => true
  | .ok _ => false

def fan (values : List Sample) : Space (Option Sample) Sample where
  expand
    | none => .branch (values.map some)
    | some value => .answer value

theorem raw_first_error_is_not_a_preferred_witness :
    (BoundedSearchPortfolio.run (fan [.error 3, .ok 7]) 1 10 1 none).answers = [.error 3] ∧
      SuccessPriority.select isError [.error 3, .ok 7] = [.ok 7] ∧
      batch isError 1 (run (fan [.error 3, .ok 7]) isError 1 10 1 none) = [.ok 7] := by decide

theorem a_provisional_error_remains_private :
    (run (fan [.error 3, .ok 7]) isError 1 2 1 none).answers = [.error 3] ∧
      status isError 1 (run (fan [.error 3, .ok 7]) isError 1 2 1 none) = .paused := by decide

theorem all_errors_wait_for_uncut_exhaustion :
    status isError 2 (run (fan [.error 3, .error 4]) isError 2 10 1 none) = .exhausted ∧
      batch isError 2 (run (fan [.error 3, .error 4]) isError 2 10 1 none) = [.error 3, .error 4] := by decide

theorem successful_duplicates_survive :
    batch isError 2 (run (fan [.error 3, .ok 7, .ok 7]) isError 2 10 1 none) = [.ok 7, .ok 7] := by decide

theorem an_empty_cutoff_is_not_an_error_only_completion :
    status isError 1 (run (fan [.error 3, .ok 7]) isError 1 10 0 none) = .cutoff := by decide

theorem zero_demand_performs_no_expansion :
    (run (fan [.error 3]) isError 0 10 1 none).work = 0 ∧
      batch isError 0 (run (fan [.error 3]) isError 0 10 1 none) = [] := by decide

end Controls

end Mettapedia.Machines.ObserverLicence.HEWitness
