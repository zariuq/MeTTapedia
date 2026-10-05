import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Persistent
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Halting
import Mettapedia.Languages.TuringMachine.UniversalTable

/-!
# The fixed universal table's computations execute in canonical rho

One finite persistent controller, obtained from the existing universal table,
has an execution to the represented output of every defined partial-recursive
computation. Tape and program data change between inputs; the table controller
does not. The proof uses the table's checked Mathlib compilation and the
fifteen-COMM source-step simulation, without an execution fuel bound.

These are preservation theorems, including actual quiescence for terminal
source computations. They do not assert reflection of arbitrary target
executions or target divergence, and do not compile the historical Chaitin
Lisp interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.UniversalOutputs

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.TuringMachine

theorem execution_preserved {machine : Machine} {initial final : Configuration}
    (computed : final ∈ StateTransition.eval machine.next? initial) :
    Nonempty (ReducesStar (Persistent.encoding machine initial) (Persistent.encoding machine final)) := by
  obtain ⟨path, _⟩ := StateTransition.mem_eval.mp computed
  obtain ⟨returned, same, run⟩ := Persistent.reaches_preserved machine
    (MathlibBridge.reaches_next_forward machine path)
  cases Configuration.term_injective same
  exact run

/-- A terminal source computation retains its full configuration in a
quiescent target query, after completing the dispatch protocol. -/
theorem execution_quiescent {machine : Machine} {initial final : Configuration}
    (computed : final ∈ StateTransition.eval machine.next? initial) :
    Nonempty (ReducesStar (Persistent.encoding machine initial) (Persistent.awaiting machine final)) ∧
      Reduction.NormalForm (Persistent.awaiting machine final) := by
  obtain ⟨_, stopped⟩ := StateTransition.mem_eval.mp computed
  obtain ⟨⟨finish⟩, quiet⟩ := Halting.halted_dispatch (Machine.halted_of_next?_eq_none stopped)
  obtain ⟨run⟩ := execution_preserved computed
  exact ⟨⟨run.trans (reducesN_to_star finish)⟩, quiet⟩

noncomputable def withInput (index argument : Nat) : Pattern :=
  Persistent.encoding UniversalTable.machine (UniversalTable.inputConfiguration index argument)

/-- Every defined output has a concrete canonical-rho execution, for one
fixed finite controller. This is the forward computation claim. -/
theorem partrec_outputs (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index : Nat, ∀ argument output, output ∈ function argument →
      ∃ final : Configuration,
        Nonempty (ReducesStar (withInput index argument)
          (Persistent.encoding UniversalTable.machine final)) ∧
        PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
          (Turing.PartrecToTM2.halt [output]) final := by
  obtain ⟨index, specification⟩ := UniversalTable.universal_for_partrec function effective
  refine ⟨index, fun argument output computed => ?_⟩
  obtain ⟨final, sourceRun, represented⟩ := (specification argument).2 output computed
  exact ⟨final, execution_preserved sourceRun, represented⟩

theorem zero_output (argument : Nat) :
    ∃ final : Configuration,
      Nonempty (ReducesStar
        (withInput (Encodable.encode Nat.Partrec.Code.zero) argument)
        (Persistent.encoding UniversalTable.machine final)) ∧
      PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [0]) final := by
  obtain ⟨final, sourceRun, represented⟩ := UniversalTable.zero_output argument
  exact ⟨final, execution_preserved sourceRun, represented⟩

/-- Every defined partial-recursive output has a halting canonical-rho
execution with the same represented terminal tape result. -/
theorem partrec_quiescent_outputs (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index : Nat, ∀ argument output, output ∈ function argument →
      ∃ final : Configuration,
        Nonempty (ReducesStar (withInput index argument)
          (Persistent.awaiting UniversalTable.machine final)) ∧
        Reduction.NormalForm (Persistent.awaiting UniversalTable.machine final) ∧
        PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
          (Turing.PartrecToTM2.halt [output]) final := by
  obtain ⟨index, specification⟩ := UniversalTable.universal_for_partrec function effective
  refine ⟨index, fun argument output computed => ?_⟩
  obtain ⟨final, sourceRun, represented⟩ := (specification argument).2 output computed
  obtain ⟨run, quiet⟩ := execution_quiescent sourceRun
  exact ⟨final, run, quiet, represented⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.UniversalOutputs
