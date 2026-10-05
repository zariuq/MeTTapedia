import Mettapedia.Languages.Chaitin.GSLT.TuringAdequacy
import Mettapedia.Languages.Chaitin.GSLT.TableIteration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.UniversalOutputs

/-!
# Historical Lisp table programs execute through the existing rho controller

The table and initial tape prepare both programs before either executes. A
successful run of the authored historical Lisp evaluator is transported to
actual canonical rho reductions, retaining the source's complete final tape.
The same fixed universal controller realizes the universal Lisp interpreter's
defined outputs. This is computation preservation, not reflection of
arbitrary target schedules or compilation of arbitrary Lisp expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.Chaitin.TablePrograms

open Mettapedia.Languages
open Mettapedia.Languages.TuringMachine
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- A complete Lisp iteration is implemented by fifteen canonical COMM
reductions, with the persistent controller and complete tape restored. -/
theorem iteration_preserved (machine : Machine) (initial next : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program machine initial))
      (Chaitin.GSLT.result (Chaitin.GSLT.TableIteration.outcome (some next)))) :
    Nonempty (ReducesN 15 (TuringMachine.Persistent.encoding machine initial)
      (TuringMachine.Persistent.encoding machine next)) := by
  have same := (Chaitin.GSLT.TableIteration.returns_iff machine initial _).mp source
  have stepped : machine.next? initial = some next :=
    (Chaitin.GSLT.TableIteration.outcome_injective same).symm
  obtain ⟨entry, member, applies, sameTarget⟩ :=
    step_term_term_iff.mp (Machine.step_of_next? stepped)
  subst next
  exact TuringMachine.Persistent.transition_preserved machine initial entry member applies

/-- An absent row is observed after dispatch as a genuine rho normal form;
the source returns the empty optional result, rather than a successor. -/
theorem iteration_stopped_quiescent (machine : Machine) (initial : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program machine initial))
      (Chaitin.GSLT.result Chaitin.SExpr.nil)) :
    Nonempty (ReducesN 5 (TuringMachine.Persistent.encoding machine initial)
      (TuringMachine.Persistent.awaiting machine initial)) ∧
      Reduction.NormalForm (TuringMachine.Persistent.awaiting machine initial) := by
  have same := (Chaitin.GSLT.TableIteration.returns_iff machine initial _).mp source
  have encoded : Chaitin.GSLT.TableIteration.outcome none =
      Chaitin.GSLT.TableIteration.outcome (machine.next? initial) := same
  have stopped : machine.next? initial = none :=
    (Chaitin.GSLT.TableIteration.outcome_injective encoded).symm
  exact ⟨TuringMachine.Persistent.dispatch_reduces machine initial,
    (TuringMachine.Halting.awaiting_normal_iff machine initial).mpr
      (Machine.halted_of_next?_eq_none stopped)⟩

/-- Every source return has an actual target execution with its full tape. -/
theorem returns_preserved (machine : Machine) (initial final : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final))) :
    Nonempty (ReducesStar (TuringMachine.Persistent.encoding machine initial)
      (TuringMachine.Persistent.encoding machine final)) :=
  TuringMachine.UniversalOutputs.execution_preserved
    ((Chaitin.GSLT.machine_returns_iff machine initial final).mp source)

/-- Source return reaches a genuine target normal form, after dispatch. -/
theorem returns_quiescent (machine : Machine) (initial final : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final))) :
    Nonempty (ReducesStar (TuringMachine.Persistent.encoding machine initial)
      (TuringMachine.Persistent.awaiting machine final)) ∧
      Reduction.NormalForm (TuringMachine.Persistent.awaiting machine final) :=
  TuringMachine.UniversalOutputs.execution_quiescent
    ((Chaitin.GSLT.machine_returns_iff machine initial final).mp source)

/-- The universal Lisp interpreter reuses the already compiled rho table. -/
theorem universal_returns_quiescent (index argument : Nat) (final : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringInterpreter.universalProgram index argument))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final))) :
    Nonempty (ReducesStar (TuringMachine.UniversalOutputs.withInput index argument)
      (TuringMachine.Persistent.awaiting UniversalTable.machine final)) ∧
      Reduction.NormalForm (TuringMachine.Persistent.awaiting UniversalTable.machine final) :=
  returns_quiescent UniversalTable.machine _ final source

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.Chaitin.TablePrograms
