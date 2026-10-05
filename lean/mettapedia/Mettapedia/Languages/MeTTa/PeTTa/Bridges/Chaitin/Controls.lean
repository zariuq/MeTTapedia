import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.IterationBisimulation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.TablePrograms
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Controls
import Mettapedia.Languages.Chaitin.GSLT.Controls

/-!
# Positive and negative controls for the Lisp/PeTTa comparison

Complete tape contents, missing rows, nonterminating machines and the
first-match boundary are observed separately. The examples consume the
general comparison rather than unfolding an entire Lisp execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls

open Mettapedia.Languages
open Mettapedia.Languages.TuringMachine
open Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.HennessyMilner
open IterationBisimulation
open TuringMachine.Controls (oneRow twoChoices)

def written : Configuration := ⟨1, [1], 0, []⟩
def otherWrite : Configuration := ⟨1, [2], 0, []⟩

theorem blank_iteration : IterationStep oneRow Configuration.blank written :=
  (iterationStep_iff _ _ _).mpr (by decide)

theorem wrong_write_rejected : ¬ IterationStep oneRow Configuration.blank otherWrite := by
  rw [iterationStep_iff]
  decide

/-- A generated return-observing formula sees the written cell. -/
theorem written_formula :
    (sourceSystem oneRow).sat (.dia () (.atom written)) Configuration.blank ∧
      (targetSystem oneRow).sat (.dia () (.atom written)) Configuration.blank.term := by
  have source : (sourceSystem oneRow).sat (.dia () (.atom written)) Configuration.blank := by
    change ∃ next, IterationStep oneRow Configuration.blank next ∧
      next = written ∧ (sourceIterations oneRow).IsNormalForm next
    exact ⟨written, blank_iteration, rfl, (iterationNormal_iff _ _).mpr (by decide)⟩
  exact ⟨source, (formula_iff oneRow (by decide) _ _).mp source⟩

theorem wrong_write_formula_rejected :
    ¬ (targetSystem oneRow).sat (.dia () (.atom otherWrite)) Configuration.blank.term := by
  intro target
  have source := (formula_iff oneRow (by decide) _ _).mpr target
  change ∃ next, IterationStep oneRow Configuration.blank next ∧
    next = otherWrite ∧ (sourceIterations oneRow).IsNormalForm next at source
  obtain ⟨next, step, rfl, _⟩ := source
  exact wrong_write_rejected step

/-- Missing rows produce the explicit absent-successor result. -/
theorem missing_row_returns_none :
    Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program oneRow written))
      (Chaitin.GSLT.result Chaitin.SExpr.nil) ∧
      TuringMachine.Tables.EquationNormal oneRow written.term := by
  refine ⟨?_, (normal_iff _ _).mp ((iterationNormal_iff _ _).mpr (by decide))⟩
  exact (Chaitin.GSLT.TableIteration.returns_iff _ _ _).mpr (by decide)

theorem busy_beaver_returns_same_tape :
    Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram busyBeaver2 Configuration.blank))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration busyBeaver2Final)) ∧
      TuringMachine.Execution.Returns busyBeaver2 Configuration.blank busyBeaver2Final := by
  exact ⟨Chaitin.GSLT.busyBeaver2_returns,
    (TablePrograms.returns_iff _ busyBeaver2_deterministic _ _).mp Chaitin.GSLT.busyBeaver2_returns⟩

theorem nonterminating_machine_still_has_a_total_iteration :
    ∃ value, Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program alternating Configuration.blank))
      (Chaitin.GSLT.result value) :=
  ⟨_, Chaitin.GSLT.pureEval_generated (Chaitin.GSLT.TableIteration.program_evaluates _ _)⟩

theorem nonterminating_recursive_program_has_no_target_return :
    ¬ TuringMachine.Tables.EquationHalts alternating Configuration.blank.term :=
  TuringMachine.Controls.alternating_does_not_halt

/-- The historical first-match policy really discards the second choice. -/
theorem first_match_rejects_second_choice :
    IterationStep twoChoices Configuration.blank written ∧
      ¬ IterationStep twoChoices Configuration.blank otherWrite ∧
      TuringMachine.Tables.EquationStep twoChoices Configuration.blank.term otherWrite.term := by
  refine ⟨(iterationStep_iff _ _ _).mpr (by decide), ?_,
    TuringMachine.Controls.two_answers_are_distinct.2.1⟩
  rw [iterationStep_iff]
  decide

/-- Without determinism, the target's extra choice obstructs a bisimulation
through this configuration translation. -/
theorem nondeterministic_table_not_covered :
    ¬ Nonempty (StepCover (sourceIterations twoChoices)
      (targetEquations twoChoices) Configuration.term) := by
  rintro ⟨cover⟩
  obtain ⟨next, step, same⟩ := cover.liftStep first_match_rejects_second_choice.2.2
  have identical := Configuration.term_injective same
  subst next
  exact first_match_rejects_second_choice.2.1 step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls
