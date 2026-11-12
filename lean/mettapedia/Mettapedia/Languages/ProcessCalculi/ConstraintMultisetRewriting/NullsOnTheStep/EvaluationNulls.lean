import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullSeparations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventControls

/-!
# The nulls of evaluation beside the nulls of the step

The step's evaluation interface (`Interface.Step.Evaluation`) already keeps three outcomes apart: a
refusal refutes one candidate, unresolved work makes no negative claim, and an exhausted budget says
nothing about the state (`unresolved_is_not_refusal`, `budget_is_not_refusal`,
`zero_budget_is_not_a_refutation`, `unresolved_does_not_refute_valid_work`). They are three of the
nulls, and each is separated here from the step's empty answer set, on the four-rule theory of
`NullSeparations`:

* `budget_is_not_empty_answer_set`: with no budget, every strategy stops with an exhausted budget at
  the empty store, which has a successor.
* `unresolved_is_not_empty_answer_set`: a strategy that leaves its work unresolved stops there too.
* `refusal_halt_is_not_empty_answer_set`: a strategy that proposes `consume` there is refused, and
  the state still has a successor: the refusal of one candidate is not the empty answer set.

No verdict of a guard is unresolved work (`SchemaGuards.ThreeValued.attempt`).

The publication controls' base refusal is a refusal of permission (`published_refusal_is_forbidden`):
the firing is prepared, so its payload exists, and it is not admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Evaluation

open Interface.Step.Evaluation (Attempt evaluate)
open NamesOnTheStep NamesOnTheStep.IssuingControls Separations

/-- **An exhausted budget is not the empty answer set.** -/
theorem budget_is_not_empty_answer_set (strategy : (s : Conf × Set ℕ) → Attempt sp s) :
    (evaluate sp strategy 0 emptyS).halt = .budgetExhausted ∧ ¬ NoSuccessor sp emptyS :=
  ⟨rfl, emptyStore_has_successor.2⟩

/-- **Unresolved work is not the empty answer set.** -/
theorem unresolved_is_not_empty_answer_set :
    (evaluate sp (fun _ => .unresolved none) 1 emptyS).halt = .unresolved none ∧
      (evaluate sp (fun _ => .unresolved none) 1 emptyS).run.word = [] ∧ ¬ NoSuccessor sp emptyS :=
  ⟨rfl, rfl, emptyStore_has_successor.2⟩

def consumeAt : Fir × List ℕ := (⟨consume, [], ⟨[(factT, 0)], [], [(factU, 0)]⟩⟩, [])

theorem consume_refused : ¬ sp.Admits (s := emptyS) consumeAt :=
  refusal_without_absence.2 consumeAt rfl

/-- **The refusal of one candidate is not the empty answer set.** -/
theorem refusal_halt_is_not_empty_answer_set (strategy : (s : Conf × Set ℕ) → Attempt sp s)
    (selected : strategy emptyS = .refused consumeAt consume_refused) (fuel : ℕ) :
    (evaluate sp strategy (fuel + 1) emptyS).run = .nil emptyS ∧ ¬ NoSuccessor sp emptyS :=
  ⟨Interface.Step.Evaluation.selected_refusal_keeps_state sp strategy fuel emptyS consumeAt
      consume_refused selected,
    emptyStore_has_successor.2⟩

/-- **The publication controls' base refusal is a refusal of permission.** -/
theorem published_refusal_is_forbidden :
    Forbidden PreparedStep.Controls.guarded.step.toStep (s := ()) () :=
  ⟨Interface.EventControls.prepared, PreparedStep.Controls.guarded_refused⟩

#print axioms budget_is_not_empty_answer_set
#print axioms unresolved_is_not_empty_answer_set
#print axioms refusal_halt_is_not_empty_answer_set
#print axioms published_refusal_is_forbidden

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Evaluation
