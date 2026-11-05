import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecksControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateReuse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSourceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeGuardBoundaryControls

/-!
# Nontrivial shared constraints in the guarded transform diamond

One request imposes X = f(Y); another imposes Y = 1. They consume distinct
occurrences, share a persistent read, retain equality and absence guards,
and publish distinct output occurrences. Both orders are admitted and all
fixed continuation schedules see the same joint solutions and resources.

The open-absence control shows why physical independence alone is weaker:
an equation-only change can enable a previously unresolved guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A f)
open GuardFreeProcessOrders

def rows : Nat → Term signature
  | 0 | 2 => f (.var 0)
  | 1 | 3 => f (.var 1)
  | _ => .const 9

def initial : Configuration (Term signature) Nat := ⟨[], {0, 1, 4}⟩
def firstRule : RuleInstance (Term signature) :=
  ⟨[f (f (.var 1))], [.const 9, .const 9], [],
    [.equal (.var 0) (f (.var 1)), .absent (.const 3)], [rows 2]⟩
def secondRule : RuleInstance (Term signature) :=
  ⟨[f (.const 1)], [.const 9], [],
    [.equal (.var 1) (.const 1), .absent (.const 3)], [rows 3]⟩
def firstSelection : Selection Nat := ⟨[0], [4, 4], [2]⟩
def secondSelection : Selection Nat := ⟨[1], [4], [3]⟩
def first : ConditionalSchedule.Firing (Term signature) Nat := (firstRule, firstSelection)
def second : ConditionalSchedule.Firing (Term signature) Nat := (secondRule, secondSelection)

def firstProblem := firstSelection.problem rows firstRule initial
def secondProblem := secondSelection.problem rows secondRule initial
def jointProblem := (initial.equations ++ added rows firstRule firstSelection) ++ added rows secondRule secondSelection

private theorem consistent_of_accepted {problem : EquationStore (Term signature)}
    (accepted : (unifyTotal problem).isSome = true) : A.Consistent problem :=
  (FirstOrder.accepted_iff_consistent problem).mp (Option.isSome_iff_exists.mp accepted)

theorem first_ready : firstSelection.Valid A rows firstRule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_accepted (by cbv), ?_⟩
  intro check member
  have options : check = Check.equal (.var 0) (f (.var 1)) ∨ check = Check.absent (.const 3) := by
    simpa [firstRule] using member
  rcases options with rfl | rfl
  all_goals apply ((FirstOrderChecks.accepts_iff firstProblem rows initial.present _).mp (by cbv)).2

theorem second_ready : secondSelection.Valid A rows secondRule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_accepted (by cbv), ?_⟩
  intro check member
  have options : check = Check.equal (.var 1) (.const 1) ∨ check = Check.absent (.const 3) := by
    simpa [secondRule] using member
  rcases options with rfl | rfl
  all_goals apply ((FirstOrderChecks.accepts_iff secondProblem rows initial.present _).mp (by cbv)).2

theorem joint_consistent : A.Consistent jointProblem := consistent_of_accepted (by cbv)

theorem resources_independent : Independent rows firstSelection.commit secondSelection.commit := by
  simp [Independent, Clash, Spoils, WritesInto, Selection.commit, firstSelection, secondSelection]

theorem first_guards_ignore_second_writes : ∀ check ∈ firstRule.checks,
    Check.IgnoresWrites A jointProblem rows secondSelection check := by
  intro check member
  simp only [firstRule, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · trivial
  · intro occurrence written
    have choices : occurrence = 1 ∨ occurrence = 3 := by simpa [secondSelection] using written
    rcases choices with rfl | rfl
    all_goals exact (FirstOrder.refused_iff_inconsistent (signature := signature) _).mp (by cbv)

theorem second_guards_ignore_first_writes : ∀ check ∈ secondRule.checks,
    Check.IgnoresWrites A jointProblem rows firstSelection check := by
  intro check member
  simp only [secondRule, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · trivial
  · intro occurrence written
    have choices : occurrence = 0 ∨ occurrence = 2 := by simpa [firstSelection] using written
    rcases choices with rfl | rfl
    all_goals exact (FirstOrder.refused_iff_inconsistent (signature := signature) _).mp (by cbv)

theorem nontrivial_guarded_interactions_commute :
    secondSelection.Valid A rows secondRule (firstSelection.result rows firstRule initial) ∧
    firstSelection.Valid A rows firstRule (secondSelection.result rows secondRule initial) ∧
    SameUpTo A (secondSelection.result rows secondRule (firstSelection.result rows firstRule initial))
      (firstSelection.result rows firstRule (secondSelection.result rows secondRule initial)) :=
  independently_ready_commute A rows first second initial first_ready second_ready resources_independent
    joint_consistent first_guards_ignore_second_writes second_guards_ignore_first_writes

theorem all_fixed_continuations_agree (rest : List (ConditionalSchedule.Firing (Term signature) Nat)) :
    ConditionalSchedule.Executable A rows
        (secondSelection.result rows secondRule (firstSelection.result rows firstRule initial)) rest ↔
      ConditionalSchedule.Executable A rows
        (firstSelection.result rows firstRule (secondSelection.result rows secondRule initial)) rest :=
  continuation_after_commuting A rows first second initial nontrivial_guarded_interactions_commute.2.2 rest

theorem the_joint_caller_values_are_fixed (assignment : Subst signature) (model : A.Models assignment jointProblem) :
    assignment 0 = f (.const 1) ∧ assignment 1 = .const 1 := by
  have firstEquation := model (f (f (.var 1)), f (.var 0)) (by
    simp [jointProblem, added, Selection.equations, initial, firstRule, secondRule,
      firstSelection, secondSelection, rows])
  have secondEquation := model (f (.const 1), f (.var 1)) (by
    simp [jointProblem, added, Selection.equations, initial, firstRule, secondRule,
      firstSelection, secondSelection, rows])
  change f (f (assignment 1)) = f (assignment 0) at firstEquation
  change f (.const 1) = f (assignment 1) at secondEquation
  have secondBound := (congrFun (eq_of_heq (Term.app.inj secondEquation).2) 0).symm
  have firstBound := (congrFun (eq_of_heq (Term.app.inj firstEquation).2) 0).symm
  exact ⟨firstBound.trans (congrArg f secondBound), secondBound⟩

theorem shared_read_and_duplicate_values_keep_physical_identity :
    (secondSelection.result rows secondRule (firstSelection.result rows firstRule initial)).present = {2, 3, 4} ∧
    firstSelection.read = [4, 4] := by decide

theorem physical_independence_does_not_imply_guard_readiness :
    let rows := FirstOrderChecks.Controls.OpenAbsence.rows
    let ask := FirstOrderChecks.Controls.OpenAbsence.askSelection
    let bind := FirstOrderChecks.Controls.OpenAbsence.bindSelection
    Independent rows ask.commit bind.commit ∧
      ¬ ask.Valid A rows FirstOrderChecks.Controls.OpenAbsence.askRule
        FirstOrderChecks.Controls.OpenAbsence.initial ∧
      ask.Valid A rows FirstOrderChecks.Controls.OpenAbsence.askRule
        (FirstOrderChecks.Controls.OpenAbsence.afterBind 1) :=
  ⟨by simp [Independent, Clash, Spoils, WritesInto, Selection.commit,
      FirstOrderChecks.Controls.OpenAbsence.askSelection, FirstOrderChecks.Controls.OpenAbsence.bindSelection],
    FirstOrderChecks.Controls.OpenAbsence.the_unbound_guard_does_not_admit_the_step,
    FirstOrderChecks.Controls.OpenAbsence.binding_to_one_enables_the_step⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core.Controls
