import Mettapedia.Logic.HMLFundedObservationCodes

/-!
# The observational ceiling of affordable modal tests

Agreement is defined by executing the emitted programs. Its earned finite
code kernel determines how increasing a purse refines the observation.
Every independently supplied maximal prefix has that same observation,
including prefixes stopped by exhaustion. Arbitrary early interruption
does not enter this equivalence.

Across all budgets even the public answers recover the exact eager work
price. Consequently ordinary modal agreement suffices for paid agreement
only when the occurrence-sensitive work accounts also agree.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation

open Inspection Funded

universe u v

theorem affordable_classification_injective (budget : Nat) (first second : Bool × Nat)
    (before : first.2 ≤ budget) (after : second.2 ≤ budget)
    (same : classify budget first = classify budget second) : first = second := by
  have decoded := congrArg (meaning budget) same
  rw [meaning_classifies, meaning_classifies, if_pos before, if_pos after,
    Nat.min_eq_right before, Nat.min_eq_right after] at decoded
  have answer : first.1 = second.1 := Option.some.inj (congrArg Prod.fst decoded)
  have price : first.2 = second.2 := congrArg (fun payload : Option Bool × Nat => payload.2) decoded
  exact Prod.ext answer price

theorem all_budget_classifications_iff (first second : Bool × Nat) :
    (∀ budget, classify budget first = classify budget second) ↔ first = second := by
  constructor
  · intro same
    exact affordable_classification_injective (max first.2 second.2) first second
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) (same _)
  · rintro rfl budget
    rfl

theorem all_budget_answers_iff (first second : Bool × Nat) :
    (∀ budget, (if first.2 ≤ budget then some first.1 else none) =
      (if second.2 ≤ budget then some second.1 else none)) ↔ first = second := by
  constructor
  · intro same
    have after : second.2 ≤ first.2 := by
      by_contra unaffordable
      have observation := same first.2
      rw [if_pos (le_refl _), if_neg unaffordable] at observation
      cases observation
    have before : first.2 ≤ second.2 := by
      by_contra unaffordable
      have observation := same second.2
      rw [if_neg unaffordable, if_pos (le_refl _)] at observation
      cases observation
    have answer := same first.2
    rw [if_pos (le_refl _), if_pos after] at answer
    exact Prod.ext (Option.some.inj answer) (Nat.le_antisymm before after)
  · rintro rfl budget
    rfl

variable {State : Type u} {Action : Type v} {n : Nat}

def Agree (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (first second : State) : Prop :=
  ∀ question : Question Action n,
    observation presentation environment budget question first =
      observation presentation environment budget question second

def MaximalAgree (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (first second : State) : Prop :=
  ∀ (question : Question Action n) (before after : List Bool)
    (left : Prefix presentation question.formula question.admitted environment first before budget)
    (right : Prefix presentation question.formula question.admitted environment second after budget),
    Maximal environment left.endpoint → Maximal environment right.endpoint →
    (publicAnswer left.endpoint, left.endpoint.spent) =
      (publicAnswer right.endpoint, right.endpoint.spent)

theorem maximal_agreement_iff (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (first second : State) :
    MaximalAgree presentation environment budget first second ↔
      Agree presentation environment budget first second := by
  constructor
  · intro same question
    exact same question [] []
      (attempt presentation question.formula question.admitted environment first [] budget)
      (attempt presentation question.formula question.admitted environment second [] budget)
      (run_maximal environment _ _ _ _) (run_maximal environment _ _ _ _)
  · intro same question before after left right leftMaximal rightMaximal
    rw [maximal_prefix_observation presentation environment budget question first before left leftMaximal,
      maximal_prefix_observation presentation environment budget question second after right rightMaximal]
    exact same question

theorem agreement_classified (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (first second : State) :
    Agree presentation environment budget first second ↔
      ∀ question : Question Action n,
        classify budget (row presentation environment question first) =
          classify budget (row presentation environment question second) := by
  constructor
  · intro same question
    exact (observation_equality_iff presentation environment budget question first second).1
      (same question)
  · intro same question
    exact (observation_equality_iff presentation environment budget question first second).2
      (same question)

theorem agreement_refl (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (state : State) :
    Agree presentation environment budget state state := fun _ => rfl

theorem agreement_symm (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) {first second : State}
    (same : Agree presentation environment budget first second) :
    Agree presentation environment budget second first := fun question => (same question).symm

theorem agreement_trans (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) {first middle last : State}
    (before : Agree presentation environment budget first middle)
    (after : Agree presentation environment budget middle last) :
    Agree presentation environment budget first last :=
  fun question => (before question).trans (after question)

theorem agreement_restriction (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) {small large : Nat} (included : small ≤ large)
    {first second : State} (same : Agree presentation environment large first second) :
    Agree presentation environment small first second := by
  apply (agreement_classified presentation environment small first second).2
  intro question
  have largeSame := (agreement_classified presentation environment large first second).1 same question
  simpa only [restrict_classifies] using congrArg (restrict included) largeSame

theorem no_resource_agreement (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) :
    Agree presentation environment 0 first second := by
  intro question
  rw [observation_classified, observation_classified, meaning_classifies, meaning_classifies]
  have before := inspection_positive presentation question.formula question.admitted environment first
  have after := inspection_positive presentation question.formula question.admitted environment second
  change 0 < (row presentation environment question first).2 at before
  change 0 < (row presentation environment question second).2 at after
  rw [if_neg (by omega : ¬ (row presentation environment question first).2 ≤ 0),
    if_neg (by omega : ¬ (row presentation environment question second).2 ≤ 0)]
  rfl

theorem all_budgets_agreement_iff (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) :
    (∀ budget, Agree presentation environment budget first second) ↔
      ∀ question : Question Action n,
        row presentation environment question first = row presentation environment question second := by
  constructor
  · intro same question
    exact (all_budget_classifications_iff _ _).1 (fun budget =>
      (agreement_classified presentation environment budget first second).1 (same budget) question)
  · intro same budget
    apply (agreement_classified presentation environment budget first second).2
    intro question
    rw [same question]

theorem all_public_answers_iff (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) :
    (∀ budget (question : Question Action n),
      (observation presentation environment budget question first).1 =
        (observation presentation environment budget question second).1) ↔
      ∀ question : Question Action n,
        row presentation environment question first = row presentation environment question second := by
  constructor
  · intro same question
    apply (all_budget_answers_iff _ _).1
    intro budget
    have answer := same budget question
    simpa only [observation_classified, meaning_classifies] using answer
  · intro same budget question
    rw [observation_classified, observation_classified, same question]

def ModalAgreement (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) : Prop :=
  ∀ question : Question Action n,
    satisfies presentation.toLTS environment.toEnv question.formula first ↔
      satisfies presentation.toLTS environment.toEnv question.formula second

def WorkAgreement (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) : Prop :=
  ∀ question : Question Action n,
    (row presentation environment question first).2 = (row presentation environment question second).2

theorem all_budgets_modal_and_work (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (first second : State) :
    (∀ budget, Agree presentation environment budget first second) ↔
      ModalAgreement presentation environment first second ∧
        WorkAgreement presentation environment first second := by
  rw [all_budgets_agreement_iff]
  constructor
  · intro same
    constructor
    · intro question
      rw [← inspect_truth presentation question.formula question.admitted environment first,
        ← inspect_truth presentation question.formula question.admitted environment second]
      exact congrArg Prod.fst (same question) ▸ Iff.rfl
    · intro question
      exact congrArg Prod.snd (same question)
  · rintro ⟨truth, work⟩ question
    apply Prod.ext
    · have sameTruth := truth question
      rw [← inspect_truth presentation question.formula question.admitted environment first,
        ← inspect_truth presentation question.formula question.admitted environment second] at sameTruth
      change (row presentation environment question first).1 = _
      cases before : (row presentation environment question first).1 <;>
        cases after : (row presentation environment question second).1 <;>
        simp_all only [row, Bool.false_eq_true, iff_true]
    · exact work question

end Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation
