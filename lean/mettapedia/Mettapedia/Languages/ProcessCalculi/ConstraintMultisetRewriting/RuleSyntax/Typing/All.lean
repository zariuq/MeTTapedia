import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Judgment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Programs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Check
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Limits

/-!
# Typing as a property of programs, at the dependent frames of the step of a program

* `Judgment`: at the typed βη frames with helper telescopes, rows, made rows, equations and openings
  are typed by construction, and the dependent full step's check of made rows holds for every program.
  The judgment `WellTypedRule` asks that every answer have the type of the take pattern it answers at
  every solution of the rule's own tells; `WellTypedProgram` asks it of every rule; a state is well
  typed for a typing of its occurrences when every present row has its expected type at every
  solution of the knowledge (`WellTypedState`). Subject reduction for one firing (`result_wellTyped`)
  and over whole runs (`reach_wellTyped`, `dependent_reach_wellTyped`); canonical openings are fresh
  (`canonical_fresh`).
* `Programs`: one program with real takes, `append zero k nil ys = ys` and `cons n x xs ↦ x`, over the
  rigid package and over the package where addition computes; a run of length two that reaches its
  answer in both (`run`, `answer_reads_two`, `dependent_run`); well typed where addition computes
  (`declared_wellTyped`, `declared_run_typed`), not in the rigid package (`rigid_not_wellTyped`,
  `rigid_result_not_wellTyped`).
* `Check`: the step restricted by the answer check (`checked`); checking only refuses (`checked_le`);
  the check is exact (`answerCheck_iff_result_wellTyped`) and keeps every program typed
  (`checked_reach_wellTyped`); for a well-typed program the checked step and the step have the same
  runs (`checked_reach_iff`); the control (`rigid_check_refuses`).
* `Limits`: deciding the judgment at an initial solution of the tells
  (`wellTypedRule_iff_of_initial`); the knowledge holds equations between terms of different types
  (`heterogeneous_take`); typing does not give termination (`spin_runs_forever`), uniqueness of
  answers (`answers_not_unique`) or absences beside another program (`absence_not_compositional`,
  with locality: `locality_outside`, `locality_inside`).
-/
