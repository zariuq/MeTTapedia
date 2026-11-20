import Mettapedia.Machines.ObserverLicence.HEPublication

/-!
# Preferred witnesses for potentially infinite producers

A normal reply is a preferred witness as soon as it is reached. An error
reply additionally requires that every answer is an error. The bounded
implementation obtains that negative fact from uncut exhaustion; another
implementation could supply an independent sound certificate.

When any success exists, the mixed portfolio has an actual successful
publication without assuming finite exhaustive search.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open RuntimePlumbing

universe u w
variable {S : Type u} {Reply : Type}

def PreferredAnswer (space : Space S Reply) (root : S) (isError : Reply → Bool) (value : Reply) : Prop :=
  IsAnswer space root value ∧
    (isError value = false ∨ ∀ other, IsAnswer space root other → isError other = true)

theorem selected_member_is_raw (isError : Reply → Bool) (values : List Reply)
    {value : Reply} (member : value ∈ SuccessPriority.select isError values) : value ∈ values := by
  cases successes : SuccessPriority.successes isError values with
  | nil => simpa [SuccessPriority.select, successes] using member
  | cons first rest =>
      have successful : value ∈ SuccessPriority.successes isError values := by
        simpa [SuccessPriority.select, successes] using member
      exact (List.mem_filter.mp successful).1

theorem batch_members_preferred (space : Space S Reply) (root : S) (isError : Reply → Bool)
    (demand : Nat) (answers : List Reply) (meaning : BatchMeaning space root isError demand answers)
    {value : Reply} (member : value ∈ answers) : PreferredAnswer space root isError value := by
  have saved := meaning
  obtain ⟨depth, exactAnswers, _⟩ := meaning
  have selected := member
  rw [exactAnswers] at selected
  have raw := selected_member_is_raw isError _ (List.mem_of_mem_take selected)
  obtain ⟨distance, _, reaches⟩ := bounded_sound space depth raw
  refine ⟨⟨distance, reaches⟩, ?_⟩
  cases error : isError value with
  | false => exact Or.inl rfl
  | true => exact Or.inr (error_publication_proves_no_success space root isError demand answers saved member error)

theorem answer_forces_nonempty_once (space : Space S Reply) (root : S) (isError : Reply → Bool)
    (answers : List Reply) (meaning : BatchMeaning space root isError 1 answers)
    {witness : Reply} (answer : IsAnswer space root witness) : answers ≠ [] := by
  intro empty
  obtain ⟨depth, exactAnswers, decides⟩ := meaning
  have noPreferred : SuccessPriority.select isError (bounded space depth root).1 = [] := by
    cases selected : SuccessPriority.select isError (bounded space depth root).1 with
    | nil => rfl
    | cons value rest => simp [selected, empty] at exactAnswers
  have rawEmpty : (bounded space depth root).1 = [] := by
    cases selected : SuccessPriority.successes isError (bounded space depth root).1 with
    | nil => simpa [SuccessPriority.select, selected] using noPreferred
    | cons value rest => simp [SuccessPriority.select, selected] at noPreferred
  rcases decides with enough | uncut
  · simp [rawEmpty, SuccessPriority.successes] at enough
  · exact no_answer_of_uncut_empty space uncut rawEmpty witness answer

theorem success_produces_a_successful_publication (space : Space S Reply) (root : S)
    (isError : Reply → Bool) {witness : Reply} (answer : IsAnswer space root witness)
    (success : isError witness = false) (E : Type w) :
    ∃ budget schedule origin value,
      (BoundedSearchPortfolio.execute (strategyEngine space isError root 1 E)
        (strategyEngine space isError root 1 E) schedule
          (initialPortfolio space root E budget)).published = some (origin, [value]) ∧
      IsAnswer space root value ∧ isError value = false := by
  obtain ⟨target, settles⟩ := a_success_has_a_settling_bound space isError root answer success
  obtain ⟨budget, schedule, origin, answers, published, meaning⟩ :=
    mixed_portfolio_has_a_lawful_publication space isError root 1 target E settles
  have nonempty := answer_forces_nonempty_once space root isError answers meaning answer
  have length : answers.length ≤ 1 := by
    obtain ⟨_, exactAnswers, _⟩ := meaning
    rw [exactAnswers, List.length_take]
    exact Nat.min_le_left _ _
  cases answers with
  | nil => contradiction
  | cons value rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
      subst rest
      obtain ⟨isAnswer, normalOrNone⟩ := batch_members_preferred space root isError 1 [value] meaning List.mem_cons_self
      have normal : isError value = false := by
        rcases normalOrNone with normal | allErrors
        · exact normal
        · have impossible := allErrors witness answer
          rw [success] at impossible
          contradiction
      exact ⟨budget, schedule, origin, value, published, isAnswer, normal⟩

theorem preferred_nonempty_iff_raw (isError : Reply → Bool) (values : List Reply) :
    SuccessPriority.select isError values = [] ↔ values = [] := by
  cases successes : SuccessPriority.successes isError values with
  | nil => simp [SuccessPriority.select, successes]
  | cons first rest =>
      have nonempty : values ≠ [] := by intro empty; simp [empty, SuccessPriority.successes] at successes
      simp [SuccessPriority.select, successes, nonempty]

/-- Boolean existence can forget which witness survives preference. This is
not a procedure that computes the preferred witness itself. -/
theorem preferred_existence_iff_raw (space : Space S Reply) (root : S) (isError : Reply → Bool) :
    (∃ value, PreferredAnswer space root isError value) ↔ ∃ value, IsAnswer space root value := by
  classical
  constructor
  · rintro ⟨value, reached, _⟩
    exact ⟨value, reached⟩
  · rintro ⟨value, reached⟩
    by_cases normal : ∃ other, IsAnswer space root other ∧ isError other = false
    · obtain ⟨other, arrived, success⟩ := normal
      exact ⟨other, arrived, Or.inl success⟩
    · refine ⟨value, reached, Or.inr ?_⟩
      intro other arrived
      cases classified : isError other with
      | true => rfl
      | false => exact False.elim (normal ⟨other, arrived, classified⟩)

end Mettapedia.Machines.ObserverLicence.HEWitness
