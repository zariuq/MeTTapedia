import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Guards that depend on their own explicit tells

The existing atomic selection asks under its entire equation problem, including
its own explicit tells. Asking before those tells is a stronger requirement.
The two requirements agree when the tells already follow from the incoming
and selected-port equations. A concrete original step separates them otherwise.

This comparison adds no alternative transition relation and changes no default.
It concerns tells in the same atomic event; later events still cannot discharge
an earlier event's guard. A check contributes no equation in either comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TellDependentGuards

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

def inputProblem (selection : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) : EquationStore T :=
  before.equations ++ Selection.equations label rule.take selection.taken ++
    Selection.equations label rule.read selection.read

theorem problem_eq_inputs_append_tell (selection : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) :
    selection.problem label rule before = inputProblem selection label rule before ++ rule.tell := rfl

theorem input_ask_implies_joint_ask [DecidableEq O] (A : SubstitutionAction T S)
    (selection : Selection O) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (check : Check T)
    (asked : A.Entails (inputProblem selection label rule before)
      (fun assignment => check.Holds A assignment label before.present)) :
    A.Entails (selection.problem label rule before)
      (fun assignment => check.Holds A assignment label before.present) :=
  A.entails_of_refines (A.append_refines _ _) asked

theorem equivalent_when_tells_already_follow (A : SubstitutionAction T S)
    (selection : Selection O) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O)
    (redundant : ∀ assignment, A.Models assignment (inputProblem selection label rule before) →
      A.Models assignment rule.tell) :
    A.Equivalent (inputProblem selection label rule before) (selection.problem label rule before) := by
  intro assignment
  rw [problem_eq_inputs_append_tell, A.models_append]
  exact ⟨fun solved => ⟨solved, redundant assignment solved⟩, And.left⟩

theorem asks_agree_when_tells_already_follow [DecidableEq O] (A : SubstitutionAction T S)
    (selection : Selection O) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (check : Check T)
    (redundant : ∀ assignment, A.Models assignment (inputProblem selection label rule before) →
      A.Models assignment rule.tell) :
    A.Entails (inputProblem selection label rule before)
        (fun assignment => check.Holds A assignment label before.present) ↔
      A.Entails (selection.problem label rule before)
        (fun assignment => check.Holds A assignment label before.present) := by
  have equivalent := equivalent_when_tells_already_follow A selection label rule before redundant
  exact ⟨fun asked assignment solved => asked assignment ((equivalent assignment).mpr solved),
    fun asked assignment solved => asked assignment ((equivalent assignment).mp solved)⟩

namespace Controls

open Mettapedia.Logic.LP

abbrev signature := ConstraintMultisetRewriting.Controls.signature
abbrev A := FirstOrder.action signature

def x : Term signature := .var 0
def zeroTerm : Term signature := .const 0
def oneTerm : Term signature := .const 1
def label (occurrence : Nat) : Term signature := if occurrence = 0 then zeroTerm else .const 2
def before : Configuration (Term signature) Nat := ⟨[], {0}⟩
def rule : RuleInstance (Term signature) :=
  ⟨[], [], [(x, oneTerm)], [.absent x], [.const 2]⟩
def selection : Selection Nat := ⟨[], [], [1]⟩

theorem original_joint_selection_is_valid : selection.Valid A label rule before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨ConstraintMultisetRewriting.Controls.one, ?_⟩
    intro equation member
    have same : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, rule, selection, before] using member
    subst equation
    rfl
  · intro check member assignment solved
    have same : check = .absent x := by simpa [rule] using member
    subst check
    have value := solved (x, oneTerm) (by
      simp [Selection.problem, Selection.equations, rule, selection, before])
    change assignment 0 = Term.const (σ := signature) 1 at value
    intro occurrence present equal
    have atZero : occurrence = 0 := by simpa [before] using present
    subst occurrence
    change assignment 0 = zeroTerm at equal
    rw [value] at equal
    cases equal

theorem pre_tell_guard_is_unresolved :
    Check.Unresolved A (inputProblem selection label rule before) label before.present (.absent x) := by
  constructor
  · intro certain
    have absent := certain ConstraintMultisetRewriting.Controls.zero (A.models_nil _)
    exact absent 0 (by simp [before]) rfl
  · intro refuted
    apply refuted ConstraintMultisetRewriting.Controls.one (A.models_nil _)
    intro occurrence present same
    have atZero : occurrence = 0 := by simpa [before] using present
    subst occurrence
    change Term.const (σ := signature) 1 = .const 0 at same
    cases same

theorem the_choice_has_a_real_separator :
    selection.Valid A label rule before ∧
      ¬ A.Entails (inputProblem selection label rule before)
        (fun assignment => (Check.absent x).Holds A assignment label before.present) :=
  ⟨original_joint_selection_is_valid, pre_tell_guard_is_unresolved.1⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TellDependentGuards
