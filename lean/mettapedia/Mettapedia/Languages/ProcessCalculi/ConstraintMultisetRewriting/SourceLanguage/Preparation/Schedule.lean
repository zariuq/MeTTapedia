import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Continuations

/-! # Checking schedulable moves in agenda order -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Machine

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open Evaluation (Evaluator)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage : Type} {D : Discipline S Γ star}
  (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)

theorem advanceAt_none_iff (state : State κ Γ star D.Ty Storage) (position : Fin state.agenda.length) :
    advanceAt machine strategy state position = none ↔
      ¬ (Solvable (state.agenda.get position).store ∧
        ∃ next replies, Move D machine.program machine.supply (state.world.source machine.spaces)
          (state.agenda.get position) next replies) := by
  by_cases live : Solvable (state.agenda.get position).store
  · have confirmed := (machine.solver.satisfiable_iff _).mpr live
    simp only [advanceAt, confirmed, if_true, Option.map_eq_none_iff, Evaluation.reduce_none_iff, live, true_and]
  · have rejected := Bool.eq_false_iff.mpr fun accepted => live ((machine.solver.satisfiable_iff _).mp accepted)
    simp only [advanceAt, rejected, Bool.false_eq_true, if_false, live, false_and, not_false_eq_true]

variable (decides : (state : State κ Γ star D.Ty Storage) → (position : Fin state.agenda.length) →
  Decidable (strategy.chooses (state.source machine.spaces) (state.agenda.get position)))

private def attempt (state : State κ Γ star D.Ty Storage) (position : Fin state.agenda.length) :
    Option (Transition κ Γ star D.Ty Storage) :=
  match decides state position with
  | .isTrue _ => advanceAt machine strategy state position
  | .isFalse _ => none

/-- A failed candidate contributes no new world. The first available,
permitted reply is the only one reinserted into the agenda. -/
def firstReady (state : State κ Γ star D.Ty Storage) : Option (Transition κ Γ star D.Ty Storage) :=
  (List.finRange state.agenda.length).findSome? (attempt machine strategy decides state)

theorem firstReady_source {state : State κ Γ star D.Ty Storage}
    {transition : Transition κ Γ star D.Ty Storage}
    (taken : firstReady machine strategy decides state = some transition) :
    ChargedStep D machine.program machine.supply strategy
      (state.source machine.spaces) transition.work (transition.next.source machine.spaces) := by
  obtain ⟨position, _, tried⟩ := List.exists_of_findSome?_eq_some taken
  unfold attempt at tried
  cases decision : decides state position with
  | isTrue permitted =>
    rw [decision] at tried
    exact advanceAt_source machine strategy permitted tried
  | isFalse =>
    rw [decision] at tried
    cases tried

theorem firstReady_none_iff (state : State κ Γ star D.Ty Storage) :
    firstReady machine strategy decides state = none ↔
      ∀ position : Fin state.agenda.length,
        strategy.chooses (state.source machine.spaces) (state.agenda.get position) →
        Solvable (state.agenda.get position).store →
        ∀ next replies, ¬ Move D machine.program machine.supply (state.world.source machine.spaces)
          (state.agenda.get position) next replies := by
  unfold firstReady
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro tries position permitted live next replies moved
    have attempted := tries position (List.mem_finRange _)
    unfold attempt at attempted
    cases decision : decides state position with
    | isFalse refused => exact refused permitted
    | isTrue =>
      rw [decision] at attempted
      exact (advanceAt_none_iff machine strategy state position).mp attempted ⟨live, next, replies, moved⟩
  · intro noMove position _
    unfold attempt
    cases decision : decides state position with
    | isFalse => rfl
    | isTrue allowed =>
      apply (advanceAt_none_iff machine strategy state position).mpr
      rintro ⟨live, next, replies, moved⟩
      exact noMove position allowed live next replies moved

theorem quiescent_of_firstReady_none (state : State κ Γ star D.Ty Storage)
    (permits : ∀ branch ∈ state.agenda, strategy.chooses (state.source machine.spaces) branch)
    (stopped : firstReady machine strategy decides state = none) :
    Config.Quiescent (D := D) machine.program machine.supply (state.source machine.spaces) := by
  intro branch present live next replies moved
  change branch ∈ state.agenda at present
  obtain ⟨ordinal, rfl⟩ := List.mem_iff_get.mp present
  exact (firstReady_none_iff machine strategy decides state).mp stopped ordinal
    (permits _ present) live next replies moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Machine
