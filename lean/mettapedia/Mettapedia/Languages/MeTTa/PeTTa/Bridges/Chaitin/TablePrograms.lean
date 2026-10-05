import Mettapedia.Languages.Chaitin.GSLT.TuringAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Universal

/-!
# Historical Lisp table programs in the PeTTa equation kernel

The source is the ordinary historical Lisp table interpreter, executing in
its authored evaluator GSLT. The target is the existing finite equation
program for the same table. Both retain the complete terminal configuration.
The compilation inputs are the table and initial configuration, not a
terminal answer. This specializes the language comparison to table programs;
it does not implement an interpreter for arbitrary Lisp expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.TablePrograms

open Mettapedia.Languages
open TuringMachine

/-- The existing source interpreter and target equation executor return the
same configuration, in both directions, with no common fuel bound. -/
theorem returns_iff (machine : Machine) (deterministic : machine.Deterministic)
    (initial final : Configuration) :
    Chaitin.GSLT.theory.MultiStep
        (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
        (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final)) ↔
      TuringMachine.Execution.Returns machine initial final := by
  rw [Chaitin.GSLT.machine_returns_iff,
    TuringMachine.Execution.returns_iff deterministic]

/-- Successful source and target executions have the same halting domain. -/
theorem halts_iff (machine : Machine) (deterministic : machine.Deterministic)
    (initial : Configuration) :
    (∃ value, Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
      (Chaitin.GSLT.result value)) ↔
      TuringMachine.Tables.EquationHalts machine initial.term :=
  (Chaitin.GSLT.machine_halts_iff machine deterministic initial).symm.trans
    (TuringMachine.Tables.equationHalts_iff initial).symm

/-- Source success cannot be translated to an unrelated target tape. -/
theorem returned_configuration_unique (machine : Machine)
    (deterministic : machine.Deterministic) (initial first second : Configuration)
    (source : Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration first)))
    (target : TuringMachine.Execution.Returns machine initial second) :
    first = second :=
  TuringMachine.Execution.returns_unique deterministic
    ((returns_iff machine deterministic initial first).mp source) target

/-- The same fixed universal table works on both sides of the comparison. -/
theorem universal_returns_iff (index argument : Nat) (final : Configuration) :
    Chaitin.GSLT.theory.MultiStep
        (Chaitin.GSLT.start (Chaitin.TuringInterpreter.universalProgram index argument))
        (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final)) ↔
      TuringMachine.Execution.Returns UniversalTable.machine
        (UniversalTable.inputConfiguration index argument) final :=
  returns_iff UniversalTable.machine UniversalTable.deterministic _ final

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.TablePrograms
