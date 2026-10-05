import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Execution
import Mettapedia.Languages.TuringMachine.UniversalTable
import Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix

/-!
# A universal finite equation program and prefix machines

The already compiled universal table supplies one fixed finite atomspace
program. Each partial-recursive function has an index in its prepared input;
the equation kernel preserves termination and reflects all terminal results.
Effective conditional prefix machines use the same bridge, preserving their
binary-program halting domains. This does not supply a historical Lisp
interpreter or a streaming protocol inside a target runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Universal

open Mettapedia.Languages.TuringMachine
open Tables Execution

theorem halts_iff (index argument : Nat) :
    EquationHalts UniversalTable.machine (UniversalTable.inputConfiguration index argument).term ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom :=
  (equationHalts_iff _).trans (UniversalTable.halts_iff index argument)

/-- One fixed finite equation program computes every partial-recursive
function, preserving the source's represented output. -/
theorem universal_for_partrec (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index : Nat, ∀ argument,
      (EquationHalts UniversalTable.machine
        (UniversalTable.inputConfiguration index argument).term ↔ (function argument).Dom) ∧
      (∀ output, output ∈ function argument →
        ∃ final, Returns UniversalTable.machine
          (UniversalTable.inputConfiguration index argument) final ∧
          PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
            (Turing.PartrecToTM2.halt [output]) final) := by
  obtain ⟨index, specification⟩ := UniversalTable.universal_for_partrec function effective
  refine ⟨index, fun argument => ⟨?_, ?_⟩⟩
  · exact (equationHalts_iff _).trans (specification argument).1
  · intro output computed
    obtain ⟨final, run, represented⟩ := (specification argument).2 output computed
    exact ⟨final, (returns_iff UniversalTable.deterministic _ _).mpr run, represented⟩

/-- The equation program cannot invent a terminal result absent from the
decoded source program. -/
theorem returns_reflected (index argument : Nat) {final : Configuration}
    (returned : Returns UniversalTable.machine
      (UniversalTable.inputConfiguration index argument) final) :
    ∃ output, output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument ∧
      PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [output]) final :=
  UniversalTable.output_reflected index argument
    ((returns_iff UniversalTable.deterministic _ _).mp returned)

theorem halting_family_not_computable :
    ¬ ComputablePred fun index : Nat =>
      EquationHalts UniversalTable.machine (UniversalTable.inputConfiguration index 0).term :=
  fun decision => UniversalTable.halting_family_not_computable
    (decision.of_eq fun index => equationHalts_iff (UniversalTable.inputConfiguration index 0))

theorem zero_returns (argument : Nat) :
    ∃ final, Returns UniversalTable.machine
      (UniversalTable.inputConfiguration (Encodable.encode Nat.Partrec.Code.zero) argument) final ∧
      PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [0]) final := by
  obtain ⟨final, computed, represented⟩ := UniversalTable.zero_output argument
  exact ⟨final, (returns_iff UniversalTable.deterministic _ _).mpr computed, represented⟩

theorem silent_does_not_halt (argument : Nat) :
    ¬ EquationHalts UniversalTable.machine
      (UniversalTable.inputConfiguration
        (Encodable.encode Mettapedia.Computability.silentCode) argument).term := by
  rw [equationHalts_iff]
  exact UniversalTable.silent_does_not_halt argument

/-- Prefix-freeness belongs to the selected input language, not to arbitrary
Turing computation. The MeTTa equation bridge preserves that language. -/
theorem conditional_prefix_free
    (source : KolmogorovComplexity.ConditionalPrefixFreeMachine)
    (effective : Partrec₂ fun program condition => Part.ofOption (source.compute program condition))
    (condition : KolmogorovComplexity.BinString) :
    KolmogorovComplexity.PrefixFree {program |
      EquationHalts (Bridges.Computability.ConditionalPrefix.machine source effective)
        (Bridges.Computability.ConditionalPrefix.inputConfiguration
          source effective program condition).term} := by
  have same : {program | EquationHalts
      (Bridges.Computability.ConditionalPrefix.machine source effective)
      (Bridges.Computability.ConditionalPrefix.inputConfiguration
        source effective program condition).term} =
      Bridges.Computability.ConditionalPrefix.HaltingPrograms source effective condition := by
    ext program
    exact equationHalts_iff _
  rw [same]
  exact Bridges.Computability.ConditionalPrefix.prefix_free source effective condition

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Universal
