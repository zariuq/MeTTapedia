import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Executable guard controls for open bindings and duplicate occurrences

The checks distinguish certain equality from mere unifiability. Open absence
and counts remain unaccepted; a genuine incompatibility establishes absence.
An ordinary consumption retains its binding equation and leaves the second
equal-valued occurrence. An inconsistent store never licenses a firing check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature zero)

def label (_ : Nat) : Term signature := .var 0
def boundZero : EquationStore (Term signature) := [(.var 0, .const 0)]
def boundOne : EquationStore (Term signature) := [(.var 0, .const 1)]

theorem equality_is_not_unifiability :
    acceptsCertainCheck (signature := signature) [] label {1} (.equal (.var 0) (.var 1)) = false ∧
      compatible (signature := signature) [] (Term.var (σ := signature) 0) (.var 1) = true := by cbv

theorem declared_equality_is_accepted :
    acceptsCertainCheck (signature := signature) [(Term.var 0, .var 1)] label {1} (.equal (.var 0) (.var 1)) = true := by cbv

theorem two_equal_values_count_as_two_occurrences :
    acceptsCertainCheck (signature := signature) boundZero label {1, 4} (.count (.const 0) 2) = true ∧
      acceptsCertainCheck (signature := signature) boundZero label {1, 4} (.count (.const 0) 1) = false := by cbv

theorem an_open_count_is_not_generalized_from_one_answer :
    acceptsCertainCheck (signature := signature) [] label {1, 4} (.count (.const 0) 0) = false ∧
      acceptsCertainCheck (signature := signature) [] label {1, 4} (.count (.const 0) 2) = false := by cbv

theorem open_absence_remains_unaccepted :
    acceptsCertainCheck (signature := signature) [] label {1, 4} (.absent (.const 0)) = false := by cbv

theorem genuine_incompatibility_establishes_absence_and_zero_count :
    acceptsCertainCheck (signature := signature) boundOne label {1, 4} (.absent (.const 0)) = true ∧
      acceptsCertainCheck (signature := signature) boundOne label {1, 4} (.count (.const 0) 0) = true := by cbv

def consume : RuleInstance (Term signature) := ⟨[.const 0], [], [], [], []⟩
def selection : Selection Nat := ⟨[1], [], []⟩
def before : Configuration (Term signature) Nat := ⟨[], {1, 4}⟩
def after := selection.result label consume before

theorem the_consuming_step_is_valid : selection.Valid (FirstOrder.action signature) label consume before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zero, ?_⟩, ?_⟩
  · intro equation member
    have only : equation = (Term.const (σ := signature) 0, Term.var (σ := signature) 0) := by
      simpa [Selection.problem, Selection.equations, selection, consume, before, label] using member
    subst equation
    rfl
  · intro check member
    cases member

theorem an_ordinary_consuming_step_fires :
    Step (FirstOrder.action signature) label consume before after :=
  ⟨selection, the_consuming_step_is_valid, rfl⟩

theorem after_consumption_the_remaining_occurrence_and_binding_are_retained :
    after.present = {4} ∧ after.equations = [(Term.const (σ := signature) 0, .var 0)] := by
  with_unfolding_all decide

theorem consuming_one_of_two_does_not_establish_absence :
    acceptsCertainCheck (signature := signature) after.equations label after.present (.absent (.const 0)) = false ∧
      acceptsCertainCheck (signature := signature) after.equations label after.present (.count (.const 0) 1) = true ∧
        acceptsCertainCheck (signature := signature) after.equations label after.present (.count (.const 0) 0) = false := by cbv

def singletonBefore : Configuration (Term signature) Nat := ⟨[], {1}⟩
def singletonAfter := selection.result label consume singletonBefore

theorem consuming_the_only_occurrence_does_establish_absence :
    acceptsCertainCheck (signature := signature) singletonAfter.equations label singletonAfter.present (.absent (.const 0)) = true ∧
      acceptsCertainCheck (signature := signature) singletonAfter.equations label singletonAfter.present (.count (.const 0) 1) = false := by cbv

theorem an_inconsistent_store_cannot_license_a_check :
    acceptsCertainCheck (signature := signature) [(Term.const 0, .const 1)] label {1} (.equal (.const 0) (.const 0)) = false := by cbv

theorem structural_equality_preserves_variable_identity :
    (Term.app (σ := signature) () (fun _ => Term.var 0)).structuralEqual
      (.app () (fun _ => .var 1)) = false := by cbv

theorem the_computed_count_is_a_universal_judgment :
    (FirstOrder.action signature).Entails after.equations
      (fun assignment => (Check.count (.const 0) 1).Holds (FirstOrder.action signature)
        assignment label after.present) :=
  (accepts_iff after.equations label after.present (.count (.const 0) 1)).mp
    consuming_one_of_two_does_not_establish_absence.2.1 |>.2

namespace OpenAbsence

open ConstraintMultisetRewriting.Controls (f one)

/-- Row 0 is cancel(0); rows 1 and 2 are distinct request occurrences. -/
def rows : Nat → Term signature
  | 0 => f (.const 0)
  | 1 => .const 10
  | 2 => .const 11
  | 3 => f (f (.var 0))
  | 4 => f (.const 1)
  | _ => f (.const 2)

def query : Term signature := f (.var 0)
def initial : Configuration (Term signature) Nat := ⟨[], {0, 1, 2}⟩
def askRule : RuleInstance (Term signature) :=
  ⟨[.const 10], [], [], [.absent query], [rows 3]⟩
def askSelection : Selection Nat := ⟨[1], [], [3]⟩
def bindRule (value : Nat) : RuleInstance (Term signature) :=
  ⟨[.const 11], [], [(.var 0, .const value)], [], []⟩
def bindSelection : Selection Nat := ⟨[2], [], []⟩
def afterBind (value : Nat) := bindSelection.result rows (bindRule value) initial

theorem the_three_guard_verdicts :
    acceptsCertainCheck (signature := signature) [] rows initial.present (.absent query) = false ∧
    acceptsCertainCheck (signature := signature) boundOne rows initial.present (.absent query) = true ∧
    acceptsCertainCheck (signature := signature) boundZero rows initial.present (.absent query) = false := by cbv

theorem a_partial_empty_scan_would_give_the_wrong_verdict :
    acceptsCertainCheck (signature := signature) boundZero rows ∅ (.absent query) = true ∧
    acceptsCertainCheck (signature := signature) boundZero rows initial.present (.absent query) = false := by cbv

theorem the_partial_scan_lacks_coverage :
    ¬ Check.CoversMatches (FirstOrder.action signature) boundZero rows ∅ initial.present query := by
  intro covered
  have impossible := covered zero (by
    intro equation member
    have only : equation = (Term.var (σ := signature) 0, .const 0) := by simpa [boundZero] using member
    subst equation
    rfl) 0 (by decide) rfl
  exact Finset.notMem_empty 0 impossible

theorem relevant_and_unrelated_insertions_differ :
    acceptsCertainCheck (signature := signature) boundOne rows {0, 1, 2, 4} (.absent query) = false ∧
    acceptsCertainCheck (signature := signature) boundOne rows {0, 1, 2, 5} (.absent query) = true := by cbv

theorem either_binding_step_is_available (value : Nat) :
    bindSelection.Valid (FirstOrder.action signature) rows (bindRule value) initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.single 0 (.const value), ?_⟩, ?_⟩
  · intro equation member
    simp [Selection.problem, Selection.equations, bindSelection, bindRule, initial, rows] at member
    rcases member with rfl | rfl <;> rfl
  · simp [bindRule]

theorem the_unbound_guard_does_not_admit_the_step :
    ¬ askSelection.Valid (FirstOrder.action signature) rows askRule initial := by
  intro admitted
  have absent := admitted.checks (.absent query) (by simp [askRule]) zero (by
    intro equation member
    have only : equation = (Term.const (σ := signature) 10, .const 10) := by
      simpa [Selection.problem, Selection.equations, askSelection, askRule, initial, rows] using member
    subst equation
    rfl)
  exact absent 0 (by decide) rfl

theorem binding_to_one_enables_the_step :
    askSelection.Valid (FirstOrder.action signature) rows askRule (afterBind 1) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨one, ?_⟩, ?_⟩
  · intro equation member
    simp [afterBind, Selection.result, Selection.problem, Selection.equations,
      askSelection, askRule, bindSelection, bindRule, initial, rows] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member assignment model
    have only : check = Check.absent query := by simpa [askRule] using member
    subst check
    have bound : assignment 0 = Term.const (σ := signature) 1 := model (.var 0, .const 1) (by
      simp [afterBind, Selection.result, Selection.problem, Selection.equations,
        askSelection, askRule, bindSelection, bindRule, initial, rows])
    intro occurrence present same
    have choices : occurrence = 0 ∨ occurrence = 1 := by
      simp [afterBind, Selection.result, fire, Selection.commit, bindSelection, initial] at present
      tauto
    rcases choices with rfl | rfl
    · change f (assignment 0) = f (.const 0) at same
      rw [bound] at same
      have children := eq_of_heq (Term.app.inj same).2
      have impossible := congrFun children 0
      cases impossible
    · change f (assignment 0) = Term.const (σ := signature) 10 at same
      cases same

theorem binding_to_zero_refuses_the_step :
    ¬ askSelection.Valid (FirstOrder.action signature) rows askRule (afterBind 0) := by
  intro admitted
  have absent := admitted.checks (.absent query) (by simp [askRule]) zero (by
    intro equation member
    simp [afterBind, Selection.result, Selection.problem, Selection.equations,
      askSelection, askRule, bindSelection, bindRule, initial, rows] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  exact absent 0 (by decide) rfl

theorem a_later_equation_enables_an_actual_interaction :
    Step (FirstOrder.action signature) rows (bindRule 1) initial (afterBind 1) ∧
    Step (FirstOrder.action signature) rows askRule (afterBind 1)
      (askSelection.result rows askRule (afterBind 1)) ∧
    ¬ askSelection.Valid (FirstOrder.action signature) rows askRule initial :=
  ⟨⟨bindSelection, either_binding_step_is_available 1, rfl⟩,
    ⟨askSelection, binding_to_one_enables_the_step, rfl⟩,
    the_unbound_guard_does_not_admit_the_step⟩

end OpenAbsence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks.Controls
