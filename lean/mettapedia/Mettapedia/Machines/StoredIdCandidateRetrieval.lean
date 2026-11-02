import Mettapedia.Machines.StoredIdUnification
import Mathlib.Data.List.Basic

/-!
# Complete candidate filtering before stored-ID unification

The structural screen reads actual stored-view heads, including lazy
substitutions. Variables remain possible matches; rigid constructor clashes
can be rejected. Every retained occurrence is then checked by the existing
stored-ID unifier, with its own view and variable frame unchanged.

The observable sweep retains solved bindings and paused equation/binding
states, in source occurrence order. Zero fuel must retain the unscreened
pending work. A pause is not a negative answer. These are finite-term
correctness and resumption laws, not a transfer of ground-key join costs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoredIdCandidateRetrieval

open StoredIdViews StoredIdUnification ShapeScopedUnification
open Mettapedia.Logic.LP

variable {α Var Id Token : Type} [DecidableEq α] [DecidableEq Var]

def possible (reader : Reader α Var Id) (pattern value : View Var Id) : Bool :=
  match head reader pattern, head reader value with
  | .cell _, _ | _, .cell _ => true
  | .atom a, .atom b => decide (a = b)
  | .node _ _, .node _ _ => true
  | _, _ => false

theorem rejected_inspection (reader : Reader α Var Id) (pattern value : View Var Id)
    (rejected : possible reader pattern value = false) (rest : Equations Var Id) :
    inspectPair reader pattern value rest = .conflict := by
  cases first : head reader pattern <;> cases second : head reader value <;>
    simp only [possible, first, second, Bool.true_eq_false, decide_eq_false_iff_not] at rejected
  all_goals simp [inspectPair, first, second, rejected]

theorem rejected_run (reader : Reader α Var Id) (pattern value : View Var Id)
    (rejected : possible reader pattern value = false) (fuel : Nat) :
    run reader (fuel + 1) [(pattern, value)] = .conflict := by
  rw [run, rejected_inspection reader pattern value rejected]

theorem candidate_complete (reader : Reader α Var Id) (pattern value : View Var Id)
    (solvable : ∃ substitution, Unifies substitution (readEquations reader [(pattern, value)])) :
    possible reader pattern value = true := by
  cases answer : possible reader pattern value with
  | true => rfl
  | false =>
      exact False.elim (conflict_sound reader 1 _ (rejected_run reader pattern value answer 0) solvable)

structure Occurrence (Token Var Id : Type) where
  token : Token
  value : View Var Id
  deriving DecidableEq

structure Retained (Token Var Id : Type) where
  occurrence : Occurrence Token Var Id
  state : Result Var Id
  deriving DecidableEq

def retain (occurrence : Occurrence Token Var Id) : Result Var Id → Option (Retained Token Var Id)
  | .conflict => none
  | state => some ⟨occurrence, state⟩

omit [DecidableEq α] [DecidableEq Var] in
theorem retain_none_iff (occurrence : Occurrence Token Var Id) (state : Result Var Id) :
    retain occurrence state = none ↔ state = .conflict := by
  cases state <;> simp [retain]

def sweep (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) : List (Retained Token Var Id) :=
  rows.filterMap (fun row => retain row (run reader fuel [(pattern, row.value)]))

def screened (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) : List (Retained Token Var Id) :=
  if fuel = 0 then sweep reader fuel pattern rows
  else sweep reader fuel pattern (rows.filter (fun row => possible reader pattern row.value))

theorem positive_screen_exact (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) :
    sweep reader (fuel + 1) pattern (rows.filter (fun row => possible reader pattern row.value)) =
      sweep reader (fuel + 1) pattern rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases accepted : possible reader pattern row.value with
      | true =>
          have lifted := congrArg
            (fun remaining => (retain row (run reader (fuel + 1) [(pattern, row.value)])).toList ++ remaining) ih
          cases kept : retain row (run reader (fuel + 1) [(pattern, row.value)]) <;>
            simpa [sweep, accepted, List.filterMap_cons, kept] using lifted
      | false =>
          have failed := rejected_run reader pattern row.value accepted fuel
          simpa [sweep, accepted, failed, retain] using ih

theorem screened_exact (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) : screened reader fuel pattern rows = sweep reader fuel pattern rows := by
  cases fuel with
  | zero => rfl
  | succ fuel => simpa only [screened, Nat.succ_ne_zero, ↓reduceIte] using positive_screen_exact reader fuel pattern rows

def resumeRows (reader : Reader α Var Id) (fuel : Nat)
    (rows : List (Retained Token Var Id)) : List (Retained Token Var Id) :=
  rows.filterMap (fun row => retain row.occurrence (resume reader fuel row.state))

theorem retain_resume (reader : Reader α Var Id) (fuel : Nat) (row : Occurrence Token Var Id)
    (state : Result Var Id) :
    (retain row state).bind (fun kept => retain kept.occurrence (resume reader fuel kept.state)) =
      retain row (resume reader fuel state) := by
  cases state <;> rfl

theorem resume_sweep (reader : Reader α Var Id) (first later : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) :
    resumeRows reader later (sweep reader first pattern rows) = sweep reader (first + later) pattern rows := by
  simp only [resumeRows, sweep, List.filterMap_filterMap, retain_resume, ← run_add]

theorem resume_screened (reader : Reader α Var Id) (first later : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) :
    resumeRows reader later (screened reader first pattern rows) = screened reader (first + later) pattern rows := by
  rw [screened_exact, screened_exact, resume_sweep]

theorem empty_sweep_proves_no_match (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) (empty : screened reader fuel pattern rows = []) :
    ∀ row ∈ rows, ¬∃ substitution, Unifies substitution (readEquations reader [(pattern, row.value)]) := by
  rw [screened_exact] at empty
  have all := List.filterMap_eq_nil_iff.mp empty
  intro row member
  have conflict := (retain_none_iff row _).mp (all row member)
  exact conflict_sound reader fuel _ conflict

theorem solved_occurrence_sound (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) (row : Occurrence Token Var Id) (bindings : List (Binding Var Id))
    (member : (⟨row, .solved bindings⟩ : Retained Token Var Id) ∈ screened reader fuel pattern rows) :
    row ∈ rows ∧ Unifies (bindingsMeaning reader bindings) (readEquations reader [(pattern, row.value)]) := by
  rw [screened_exact] at member
  obtain ⟨source, present, accepted⟩ := List.mem_filterMap.mp member
  cases outcome : run reader fuel [(pattern, source.value)] with
  | conflict => simp [outcome, retain] at accepted
  | paused pending saved => simp [outcome, retain] at accepted
  | solved saved =>
      have same : (⟨source, .solved saved⟩ : Retained Token Var Id) = ⟨row, .solved bindings⟩ := by
        simpa only [outcome, retain, Option.some.injEq] using accepted
      cases same
      exact ⟨present, solved_sound reader fuel _ bindings outcome⟩

theorem solvable_occurrence_eventually_returned (reader : Reader α Var Id) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) (row : Occurrence Token Var Id) (member : row ∈ rows)
    (solvable : ∃ substitution, Unifies substitution (readEquations reader [(pattern, row.value)])) :
    ∃ fuel bindings, (⟨row, .solved bindings⟩ : Retained Token Var Id) ∈ screened reader fuel pattern rows := by
  obtain ⟨fuel, bindings, completed⟩ := finite_completeness reader _ solvable
  refine ⟨fuel, bindings, ?_⟩
  rw [screened_exact]
  exact List.mem_filterMap.mpr ⟨row, member, by simp only [completed, retain]⟩

def completed (row : Occurrence Token Var Id) : Result Var Id → Option (Token × List (Binding Var Id))
  | .solved bindings => some (row.token, bindings)
  | _ => none

def completedSweep (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) : List (Token × List (Binding Var Id)) :=
  rows.filterMap (fun row => completed row (run reader fuel [(pattern, row.value)]))

/-- A semantically complete filter preserves completed answers at any fuel.
This weaker observation does not promise equality of retained pending work. -/
theorem complete_filter_preserves_completed (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (possibleRow : Occurrence Token Var Id → Bool)
    (complete : ∀ row, (∃ substitution, Unifies substitution (readEquations reader [(pattern, row.value)])) →
      possibleRow row = true)
    (rows : List (Occurrence Token Var Id)) :
    completedSweep reader fuel pattern (rows.filter possibleRow) = completedSweep reader fuel pattern rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases admitted : possibleRow row with
      | true =>
          have lifted := congrArg
            (fun remaining => (completed row (run reader fuel [(pattern, row.value)])).toList ++ remaining) ih
          cases kept : completed row (run reader fuel [(pattern, row.value)]) <;>
            simpa [completedSweep, admitted, List.filterMap_cons, kept] using lifted
      | false =>
          have omitted : completed row (run reader fuel [(pattern, row.value)]) = none := by
            cases result : run reader fuel [(pattern, row.value)] with
            | conflict => rfl
            | paused pending saved => rfl
            | solved bindings =>
                have admitted' := complete row ⟨bindingsMeaning reader bindings, solved_sound reader fuel _ bindings result⟩
                rw [admitted] at admitted'
                cases admitted'
          simpa [completedSweep, admitted, omitted] using ih

theorem completed_root_screen (reader : Reader α Var Id) (fuel : Nat) (pattern : View Var Id)
    (rows : List (Occurrence Token Var Id)) :
    completedSweep reader fuel pattern (rows.filter (fun row => possible reader pattern row.value)) =
      completedSweep reader fuel pattern rows :=
  complete_filter_preserves_completed reader fuel pattern _
    (fun row solvable => candidate_complete reader pattern row.value solvable) rows

namespace Controls

open StoredIdViews.Controls (reader)

def rigidRow : Occurrence Nat Nat Nat := ⟨10, .stored 2 0⟩
def openRow : Occurrence Nat Nat Nat := ⟨11, .stored 0 1⟩

theorem rigid_constructor_clash_is_filtered : possible reader (.stored 1 0) rigidRow.value = false := by decide +kernel
theorem stored_variables_are_candidates : possible reader (.stored 1 0) openRow.value = true := by decide +kernel

theorem zero_budget_keeps_even_rigid_pending_work :
    screened reader 0 (.stored 1 0) [rigidRow] =
      [⟨rigidRow, .paused [(.stored 1 0, rigidRow.value)] []⟩] := rfl

theorem filtering_zero_budget_changes_residuals :
    sweep reader 0 (.stored 1 0) ([rigidRow].filter (fun row => possible reader (.stored 1 0) row.value)) ≠
      sweep reader 0 (.stored 1 0) [rigidRow] := by decide +kernel

theorem same_filter_preserves_completed_observer :
    completedSweep reader 0 (.stored 1 0) ([rigidRow].filter (fun row => possible reader (.stored 1 0) row.value)) =
      completedSweep reader 0 (.stored 1 0) [rigidRow] := completed_root_screen reader 0 _ _

theorem equal_occurrences_remain_two :
    (screened reader 2 (.stored 1 0) [openRow, openRow]).length = 2 := by
  rw [screened_exact]
  decide +kernel

theorem same_frame_occurs_conflict : run reader 3 [(.stored 0 0, .stored 2 0)] = .conflict := by
  rw [run]
  simp only [inspectPair, head, StoredIdViews.Controls.reader, StoredIdViews.Controls.inspect]
  rw [bindAction, occurs_correct]
  decide +kernel

theorem cross_frame_not_filtered : possible reader (.stored 0 0) (.stored 2 1) = true := rfl

theorem duplicate_resumptions_preserve_order :
    resumeRows reader 4 (screened reader 1 (.stored 1 0) [openRow, rigidRow, openRow]) =
      screened reader 5 (.stored 1 0) [openRow, rigidRow, openRow] :=
  resume_screened reader 1 4 _ _

end Controls

end Mettapedia.Machines.StoredIdCandidateRetrieval
