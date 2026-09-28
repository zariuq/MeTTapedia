import Mettapedia.GSLT.Dynamics.GuardedWork
import Mettapedia.GSLT.Core.WeightedOccurrenceControl
import Mathlib.Data.List.Sort

/-!
# Choice over valued work occurrences

An agenda transports occurrences. Valuation annotates them; a supplied policy
uses those values to rank them. The value carrier is unrestricted. Numerical
weights, estimated costs, Boolean preferences, and structured records all use
the same plumbing without a built-in probability or priority interpretation.

The reference realization sorts an already valued view. It does not require
rescoring pending work at each selection. Selection returns one occurrence AND
the retained alternatives. This differs from a maximum-only answer observer,
which can deliberately discard nonmaximal answers. The conservation law holds
even for a comparator that is not a total order; a claim of optimal ranking
would require further laws on that comparator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ValuedAgenda

open ContextualCandidateValuation
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

variable {Occurrence Value : Type}

def rank (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    List (ValuedOccurrence Occurrence Value) :=
  rows.mergeSort fun first second => before first.value second.value

theorem rank_perm (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    (rank before rows).Perm rows :=
  List.mergeSort_perm _ _

/-- Only the ranking view changes; every annotated occurrence is retained. -/
def discipline (before : Value → Value → Bool) :
    QueueDiscipline (ValuedOccurrence Occurrence Value) where
  integrate pending generated := rank before (pending ++ generated)
  integrate_complete pending generated := rank_perm before (pending ++ generated)

def select (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    Option (ValuedOccurrence Occurrence Value × List (ValuedOccurrence Occurrence Value)) :=
  match rank before rows with
  | [] => none
  | chosen :: rest => some (chosen, rest)

/-- One selected occurrence plus the residual agenda has exactly the original
multiplicity. Equal atom payloads need not have equal occurrence identities. -/
theorem select_conserves (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value))
    (chosen : ValuedOccurrence Occurrence Value)
    (rest : List (ValuedOccurrence Occurrence Value))
    (selected : select before rows = some (chosen, rest)) :
    (chosen :: rest).Perm rows := by
  cases ranked : rank before rows with
  | nil => simp [select, ranked] at selected
  | cons first tail =>
      have pair : (first, tail) = (chosen, rest) := by
        simpa [select, ranked] using selected
      cases pair
      simpa [ranked] using rank_perm before rows

theorem selected_was_present (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value))
    (chosen : ValuedOccurrence Occurrence Value)
    (rest : List (ValuedOccurrence Occurrence Value))
    (selected : select before rows = some (chosen, rest)) : chosen ∈ rows := by
  exact (select_conserves before rows chosen rest selected).mem_iff.mp (by simp)

theorem select_none_iff (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    select before rows = none ↔ rows = [] := by
  constructor
  · intro none
    cases ranked : rank before rows with
    | nil =>
        have length := (rank_perm before rows).length_eq
        simp [ranked] at length
        exact List.length_eq_zero_iff.mp length.symm
    | cons first rest => simp [select, ranked] at none
  · rintro rfl
    simp [select, rank]

/-- Values attached by the existing contextual valuation layer feed the same
agenda. Erasing the value view recovers a permutation of the original work. -/
theorem ranked_valuation_preserves_occurrences (before : Value → Value → Bool)
    (value : Occurrence → Value) (occurrences : List Occurrence) :
    ((rank before (attachValues value occurrences)).map ValuedOccurrence.occurrence).Perm
      occurrences := by
  have mapped := (rank_perm before (attachValues value occurrences)).map
    ValuedOccurrence.occurrence
  simpa using mapped

/-- The early pure guard optimization remains exact even when its output feeds
a global choice. This does not turn global choice into a local operation. -/
theorem hoist_before_selection (before : Value → Value → Bool)
    (guard : Occurrence → Bool) (value : Occurrence → Value)
    (occurrences : List Occurrence) :
    select before (GuardedWork.valueThenGuard guard value occurrences) =
      select before (GuardedWork.guardThenValue guard value occurrences) := by
  rw [GuardedWork.hoist_guard]

/-! ## One-pass choice without sorting the retained alternatives -/

/-- Comparison count and selection result. The counter advances precisely
where the comparator is invoked. No charge is assigned to list management. -/
def tournament (before : Value → Value → Bool) :
    List (ValuedOccurrence Occurrence Value) →
      Nat × Option (ValuedOccurrence Occurrence Value × List (ValuedOccurrence Occurrence Value))
  | [] => (0, none)
  | row :: rows =>
      let result := tournament before rows
      match result.2 with
      | none => (result.1, some (row, []))
      | some (chosen, rest) =>
          (result.1 + 1, some (if before row.value chosen.value
            then (row, chosen :: rest) else (chosen, row :: rest)))

/-- This realization needs no ordering laws to conserve work. The laws of a
comparator determine what being a preferred candidate means. -/
theorem tournament_conserves (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    match (tournament before rows).2 with
    | none => rows = []
    | some (chosen, rest) => (chosen :: rest).Perm rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases selected : (tournament before rows).2 with
      | none =>
          simp only [selected] at ih
          subst rows
          simp [tournament]
      | some result =>
          rcases result with ⟨chosen, rest⟩
          simp only [selected] at ih
          cases preferred : before row.value chosen.value with
          | false =>
              simp only [tournament, selected, preferred, Bool.false_eq_true, ↓reduceIte]
              exact (List.Perm.swap row chosen rest).trans (List.Perm.cons row ih)
          | true =>
              simpa [tournament, selected, preferred] using List.Perm.cons row ih

/-- Exactly n-1 comparisons for nonempty input. The residual need not be sorted
when the observer asks for only one preferred work item. -/
theorem tournament_comparisons (before : Value → Value → Bool)
    (rows : List (ValuedOccurrence Occurrence Value)) :
    (tournament before rows).1 = rows.length - 1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases selected : (tournament before rows).2 with
      | none =>
          have empty := tournament_conserves before rows
          simp only [selected] at empty
          subst rows
          rfl
      | some result =>
          rcases result with ⟨chosen, rest⟩
          have conserved := tournament_conserves before rows
          simp only [selected] at conserved
          have length := conserved.length_eq
          simp only [tournament, selected, ih, List.length_cons]
          simp only [List.length_cons] at length
          omega

/-- Under the declared numerical/ordered interpretation, the one-pass selector
really chooses a minimum. Reversing the order gives maximum selection. -/
theorem tournament_minimum [LinearOrder Value]
    (rows : List (ValuedOccurrence Occurrence Value)) :
    match (tournament (fun a b => decide (a ≤ b)) rows).2 with
    | none => rows = []
    | some (chosen, _) => ∀ row ∈ rows, chosen.value ≤ row.value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases selected : (tournament (fun a b => decide (a ≤ b)) rows).2 with
      | none =>
          simp only [selected] at ih
          subst rows
          simp [tournament]
      | some result =>
          rcases result with ⟨chosen, rest⟩
          simp only [selected] at ih
          by_cases preferred : row.value ≤ chosen.value
          · have minimal : ∀ candidate ∈ row :: rows, row.value ≤ candidate.value := by
              intro candidate member
              rcases List.mem_cons.mp member with equal | member
              · subst candidate
                exact le_rfl
              · exact preferred.trans (ih candidate member)
            simpa [tournament, selected, preferred] using minimal
          · have minimal : ∀ candidate ∈ row :: rows, chosen.value ≤ candidate.value := by
              intro candidate member
              rcases List.mem_cons.mp member with equal | member
              · subst candidate
                exact le_of_lt (lt_of_not_ge preferred)
              · exact ih candidate member
            simpa [tournament, selected, preferred] using minimal

namespace Controls

def rows : List (ValuedOccurrence Nat Nat) :=
  [⟨10, 2⟩, ⟨11, 9⟩, ⟨12, 2⟩]

theorem policy_changes_choice_without_losing_work :
    (select (· ≤ ·) rows).map (fun selected => selected.1.occurrence) = some 10 ∧
    (select (· ≥ ·) rows).map (fun selected => selected.1.occurrence) = some 11 := by
  simp [select, rank, rows, List.mergeSort]

theorem same_value_is_not_same_occurrence :
    (rank (· ≤ ·) rows).map ValuedOccurrence.occurrence = [10, 12, 11] := by
  simp [rank, rows, List.mergeSort]

/-- Dropping the alternatives is not an occurrence-preserving agenda update. -/
theorem winner_only_loses_work :
    ¬ ([⟨11, 9⟩] : List (ValuedOccurrence Nat Nat)).Perm rows := by
  intro permutation
  have length := permutation.length_eq
  change 1 = 3 at length
  omega

theorem one_pass_selects_with_two_comparisons :
    tournament (· ≥ ·) rows =
      (2, some (⟨11, 9⟩, [⟨10, 2⟩, ⟨12, 2⟩])) := rfl

end Controls

#print axioms select_conserves
#print axioms select_none_iff
#print axioms ranked_valuation_preserves_occurrences
#print axioms hoist_before_selection
#print axioms tournament_conserves
#print axioms tournament_comparisons
#print axioms tournament_minimum

end Mettapedia.GSLT.Dynamics.ValuedAgenda
