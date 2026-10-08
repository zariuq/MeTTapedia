import Mettapedia.Logic.HMLObservationQuotient

/-!
# Positive and negative controls for funded modal equivalence

One state supplies the same successor twice while another supplies it once.
Their closed modal truth agrees for every admitted formula; the independent
occurrence presentation has different eager work. Actual compiled programs
separate them by affordability and, when both complete, by exact spending.

The observation quotient admits compatible consumers and rejects an
unobservable state decoder. All maximal supplied runs, including exhausted
runs with unfinished code, obey the same earned readout contract.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation.Controls

open Inspection Funded

def repeated : SuccessorPresentation Bool Unit where
  successors state _ := if state then [true, true] else [true]

def closedEnvironment : BooleanEnv Bool 0 := fun index => Fin.elim0 index

theorem same_modal_truth {n : Nat} (formula : Formula Unit n) (admitted : formula.isHML = true)
    (environment : BooleanEnv Bool n)
    (constant : ∀ index first second, environment index first = environment index second)
    (first second : Bool) :
    (inspect repeated formula admitted environment first).1 =
      (inspect repeated formula admitted environment second).1 := by
  induction formula with
  | tt => rfl
  | ff => rfl
  | var index => exact constant index first second
  | neg body inductionHypothesis =>
      exact congrArg Bool.not (inductionHypothesis admitted environment constant)
  | conj before after firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact congrArg₂ Bool.and (firstHypothesis parts.1 environment constant)
        (secondHypothesis parts.2 environment constant)
  | disj before after firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact congrArg₂ Bool.or (firstHypothesis parts.1 environment constant)
        (secondHypothesis parts.2 environment constant)
  | diamond action body _ =>
      cases first <;> cases second <;>
        simp only [inspect, repeated, Bool.false_eq_true, if_false, if_true, List.map_cons,
          List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_self]
  | box action body _ =>
      cases first <;> cases second <;>
        simp only [inspect, repeated, Bool.false_eq_true, if_false, if_true, List.map_cons,
          List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_self]
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem closed_modal_agreement : ModalAgreement repeated closedEnvironment false true := by
  intro question
  rw [← inspect_truth repeated question.formula question.admitted closedEnvironment false,
    ← inspect_truth repeated question.formula question.admitted closedEnvironment true,
    same_modal_truth question.formula question.admitted closedEnvironment
      (fun index => Fin.elim0 index) false true]

def oneSuccessor : Question Unit 0 := ⟨.diamond () .tt, rfl⟩

theorem independent_prices :
    row repeated closedEnvironment oneSuccessor false = (true, 2) ∧
      row repeated closedEnvironment oneSuccessor true = (true, 3) := ⟨rfl, rfl⟩

theorem no_work_agreement : ¬ WorkAgreement repeated closedEnvironment false true := by
  intro same
  have prices := same oneSuccessor
  change 2 = 3 at prices
  omega

theorem same_relation_support (first second target : Bool) (action : Unit) :
    repeated.toLTS.trans first action target ↔ repeated.toLTS.trans second action target := by
  cases first <;> cases second <;> simp [SuccessorPresentation.toLTS, repeated]

theorem exhausted_profiles :
    observation repeated closedEnvironment 1 oneSuccessor false = (none, 1) ∧
      observation repeated closedEnvironment 1 oneSuccessor true = (none, 1) := ⟨rfl, rfl⟩

theorem affordability_separates :
    observation repeated closedEnvironment 2 oneSuccessor false = (some true, 2) ∧
      observation repeated closedEnvironment 2 oneSuccessor true = (none, 2) := ⟨rfl, rfl⟩

theorem full_answers_same_prices_different :
    observation repeated closedEnvironment 3 oneSuccessor false = (some true, 2) ∧
      observation repeated closedEnvironment 3 oneSuccessor true = (some true, 3) := ⟨rfl, rfl⟩

theorem budget_two_disagrees : ¬ Agree repeated closedEnvironment 2 false true := by
  intro same
  have compared := congrArg Prod.fst (same oneSuccessor)
  change (some true : Option Bool) = none at compared
  cases compared

theorem no_all_budget_modal_implication :
    ModalAgreement repeated closedEnvironment false true ∧
      ¬ (∀ budget, Agree repeated closedEnvironment budget false true) :=
  ⟨closed_modal_agreement, fun same => budget_two_disagrees (same 2)⟩

theorem quotient_resource_refinement_strict :
    classifyState repeated closedEnvironment 0 false = classifyState repeated closedEnvironment 0 true ∧
      classifyState repeated closedEnvironment 2 false ≠ classifyState repeated closedEnvironment 2 true := by
  exact ⟨(class_equality_iff repeated closedEnvironment 0 false true).2
    (no_resource_agreement repeated closedEnvironment false true),
    fun same => budget_two_disagrees ((class_equality_iff repeated closedEnvironment 2 false true).1 same)⟩

theorem no_zero_resource_decoder :
    ¬ ∃ decoder : ObservationClass repeated closedEnvironment 0 → Bool,
      ∀ state, decoder (classifyState repeated closedEnvironment 0 state) = state := by
  rintro ⟨decoder, exactState⟩
  have classes := quotient_resource_refinement_strict.1
  have impossible := (exactState false).symm.trans ((congrArg decoder classes).trans (exactState true))
  cases impossible

def paidAnswer : ObservationClass repeated closedEnvironment 2 → Option Bool :=
  fun code => (classProfile repeated closedEnvironment 2 code oneSuccessor).1

theorem compatible_paid_consumer :
    paidAnswer (classifyState repeated closedEnvironment 2 false) = some true ∧
      paidAnswer (classifyState repeated closedEnvironment 2 true) = none := ⟨rfl, rfl⟩

theorem every_exhausted_maximal_prefix (stack : List Bool)
    (receipt : Prefix repeated oneSuccessor.formula oneSuccessor.admitted closedEnvironment true stack 2)
    (maximal : Maximal closedEnvironment receipt.endpoint) :
    publicAnswer receipt.endpoint = none ∧ receipt.endpoint.spent = 2 ∧
      receipt.endpoint.pending ≠ [] := by
  have observation := maximal_prefix_observation repeated closedEnvironment 2 oneSuccessor true stack receipt maximal
  have answer := congrArg Prod.fst observation
  have price := congrArg Prod.snd observation
  change publicAnswer receipt.endpoint = none at answer
  change receipt.endpoint.spent = 2 at price
  refine ⟨answer, price, ?_⟩
  intro complete
  have readout := compiled_completed_readout repeated oneSuccessor.formula oneSuccessor.admitted
    closedEnvironment true stack 2 0 receipt.path complete
  have completed := publicAnswer_completed receipt.endpoint complete true stack readout
  rw [answer] at completed
  cases completed

theorem actual_exhaustion_is_maximal :
    Maximal closedEnvironment
      (attempt repeated oneSuccessor.formula oneSuccessor.admitted closedEnvironment true [] 2).endpoint :=
  run_maximal closedEnvironment _ _ _ _

theorem zero_price_code_unrealized (budget : Nat) (state : Bool) :
    classify budget (row repeated closedEnvironment oneSuccessor state) ≠ some (true, ⟨0, by omega⟩) := by
  intro same
  have observed := congrArg (meaning budget) same
  rw [meaning_classifies] at observed
  cases state <;> simp [row, oneSuccessor, inspect, repeated, meaning] at observed <;> omega

end Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation.Controls
