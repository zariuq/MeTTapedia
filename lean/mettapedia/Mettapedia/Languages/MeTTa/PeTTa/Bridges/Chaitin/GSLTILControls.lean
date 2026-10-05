import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.GSLTIL
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls
import Mettapedia.Languages.TuringMachine.Bridges.GSLTILControls

/-!
# Controls for historical Lisp blocks in GSLT-IL

Concrete returned tapes agree in all three execution views. A modal readout
rejects a different written cell, and the extra answer of a nondeterministic
table obstructs local coverage of the historical first-match interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.GSLTIL.Controls

open Mettapedia.Languages
open TuringMachine
open Mettapedia.GSLT.Ultrainfinite
open Chaitin.Controls (written otherWrite)
open TuringMachine.Controls (oneRow twoChoices)

theorem busy_beaver_returns_all_views :
    Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram busyBeaver2 Configuration.blank))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration busyBeaver2Final)) ∧
    TuringMachine.Execution.Returns busyBeaver2 Configuration.blank busyBeaver2Final ∧
    TuringMachine.Bridges.GSLTIL.Returns busyBeaver2 Configuration.blank busyBeaver2Final :=
  ⟨Chaitin.Controls.busy_beaver_returns_same_tape.1,
    Chaitin.Controls.busy_beaver_returns_same_tape.2,
    (returns_iff _ busyBeaver2_deterministic _ _).mp Chaitin.GSLT.busyBeaver2_returns⟩

theorem formula_reads_written_tape :
    (targetSystem oneRow).sat (.dia () (.atom written))
      (TuringMachine.Bridges.GSLTIL.command Configuration.blank.term) :=
  (formula_iff oneRow (by decide) _ _).mp Chaitin.Controls.written_formula.1

theorem formula_rejects_wrong_write :
    ¬ (targetSystem oneRow).sat (.dia () (.atom otherWrite))
      (TuringMachine.Bridges.GSLTIL.command Configuration.blank.term) := by
  intro observed
  have source := (formula_iff oneRow (by decide) _ _).mpr observed
  change ∃ next, IterationBisimulation.IterationStep oneRow Configuration.blank next ∧
    next = otherWrite ∧ (IterationBisimulation.sourceIterations oneRow).IsNormalForm next at source
  obtain ⟨next, step, rfl, _⟩ := source
  exact Chaitin.Controls.wrong_write_rejected step

theorem nondeterministic_table_not_covered :
    ¬ Nonempty (StepCover (IterationBisimulation.sourceIterations twoChoices)
      (TuringMachine.Bridges.GSLTIL.theory twoChoices)
      (fun state : Configuration => TuringMachine.Bridges.GSLTIL.command state.term)) := by
  rintro ⟨cover⟩
  have authored := (TuringMachine.Tables.equationStep_iff Configuration.blank otherWrite.term).mp
    Chaitin.Controls.first_match_rejects_second_choice.2.2
  have target := (TuringMachine.Bridges.GSLTIL.step_command_iff twoChoices _ _).mpr authored
  obtain ⟨next, step, same⟩ := cover.liftStep target
  have identical := Configuration.term_injective
    (Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.at_injective _ same)
  subst next
  exact Chaitin.Controls.first_match_rejects_second_choice.2.1 step

theorem total_iteration_does_not_imply_halting :
    (∃ value, Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program alternating Configuration.blank))
      (Chaitin.GSLT.result value)) ∧
    ¬ TuringMachine.Bridges.GSLTIL.Halts alternating Configuration.blank.term :=
  ⟨Chaitin.Controls.nonterminating_machine_still_has_a_total_iteration,
    TuringMachine.Bridges.GSLTIL.Controls.alternating_has_no_return⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.GSLTIL.Controls
