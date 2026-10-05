import Mettapedia.Languages.Chaitin.GSLT.Correspondence
import Mettapedia.Languages.Chaitin.TuringInterpreter.NaturalAdequacy

/-!
# Turing completeness through the authored historical Lisp language

The ordinary recursive interpreter runs through the generated evaluator
rewrites. Termination and the complete returned configuration are preserved
and reflected. The program is assembled from the table and its input, with
no access to a terminal configuration. The fixed universal table is reused.

Successful return is distinguished from a blocked configuration: the pure
core deliberately has no rule that performs streaming input or output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.Computability.StreamingInput

/-- The generated rewrite relation computes exactly the terminal
configurations of the first-match table interpreter. -/
theorem machine_returns_iff (source : TuringMachine.Machine)
    (configuration final : TuringMachine.Configuration) :
    theory.MultiStep (start (TuringPrograms.machineProgram source configuration))
      (result (TuringPrograms.encodeConfiguration final)) ↔
        final ∈ StateTransition.eval source.next? configuration := by
  constructor
  · intro path
    exact (TuringInterpreter.returns_iff source configuration final []).mp
      (generated_observed path [])
  · intro computed
    exact pureEval_generated (TuringInterpreter.eval_pure source computed)

/-- Exact correspondence with the generated Turing LanguageDef, including
the final configuration, rather than just its first-match interpreter. -/
theorem authored_machine_returns_iff (source : TuringMachine.Machine)
    (deterministic : source.Deterministic) (configuration final : TuringMachine.Configuration) :
    theory.MultiStep (start (TuringPrograms.machineProgram source configuration))
      (result (TuringPrograms.encodeConfiguration final)) ↔
        TuringMachine.Reaches source configuration.term final.term ∧
          TuringMachine.Halted source final.term := by
  rw [machine_returns_iff, StateTransition.mem_eval]
  constructor
  · rintro ⟨path, stopped⟩
    exact ⟨TuringMachine.MathlibBridge.reaches_next_forward source path,
      TuringMachine.Machine.halted_of_next?_eq_none stopped⟩
  · rintro ⟨path, stopped⟩
    obtain ⟨other, same, reflected⟩ :=
      TuringMachine.MathlibBridge.reaches_next_reflect source deterministic path
    have sameConfiguration := TuringMachine.Configuration.term_injective same
    subst other
    exact ⟨reflected, (TuringMachine.MathlibBridge.next_none_iff_halted source final).mpr stopped⟩

/-- No other value can be returned by the compiled table interpreter. -/
theorem machine_value_iff (source : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (value : SExpr) :
    theory.MultiStep (start (TuringPrograms.machineProgram source configuration)) (result value) ↔
      ∃ final, final ∈ StateTransition.eval source.next? configuration ∧
        value = TuringPrograms.encodeConfiguration final := by
  constructor
  · intro path
    obtain ⟨final, computed, same, _⟩ :=
      (TuringInterpreter.evaluates_iff source configuration [] [] _).mp
        (generated_observed path [])
    exact ⟨final, computed, Result.success.inj (congrArg Observation.result same)⟩
  · rintro ⟨final, computed, rfl⟩
    exact (machine_returns_iff source configuration final).mpr computed

/-- Under determinism, the authored Turing language and the authored Lisp
evaluator agree on whether the same input eventually returns. -/
theorem machine_halts_iff (source : TuringMachine.Machine)
    (deterministic : source.Deterministic) (configuration : TuringMachine.Configuration) :
    TuringMachine.HaltsFrom source configuration.term ↔
      ∃ value, theory.MultiStep (start (TuringPrograms.machineProgram source configuration))
        (result value) := by
  rw [← TuringMachine.MathlibBridge.next_eval_dom_iff_halts source deterministic configuration,
    Part.dom_iff_mem]
  constructor
  · rintro ⟨final, computed⟩
    exact ⟨_, (machine_returns_iff source configuration final).mpr computed⟩
  · rintro ⟨value, path⟩
    obtain ⟨final, computed, _⟩ := (machine_value_iff source configuration value).mp path
    exact ⟨final, computed⟩

theorem universal_halts_iff (index argument : Nat) :
    (∃ value, theory.MultiStep (start (TuringInterpreter.universalProgram index argument))
      (result value)) ↔ ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom :=
  (machine_halts_iff _ TuringMachine.UniversalTable.deterministic _).symm.trans
    (TuringMachine.UniversalTable.halts_iff index argument)

theorem universal_output_preserved (index argument output : Nat)
    (computed : output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument) :
    ∃ final, theory.MultiStep (start (TuringInterpreter.universalProgram index argument))
      (result (TuringPrograms.encodeConfiguration final)) ∧
      TuringMachine.PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [output]) final := by
  obtain ⟨final, run, represented⟩ :=
    TuringMachine.UniversalTable.output_preserved index argument output computed
  exact ⟨final, (machine_returns_iff _ _ final).mpr run, represented⟩

theorem universal_output_reflected (index argument : Nat) (final : TuringMachine.Configuration)
    (returned : theory.MultiStep (start (TuringInterpreter.universalProgram index argument))
      (result (TuringPrograms.encodeConfiguration final))) :
    ∃ output, output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument ∧
      TuringMachine.PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [output]) final :=
  TuringMachine.UniversalTable.output_reflected index argument
    ((machine_returns_iff _ _ final).mp returned)

/-- One fixed interpreter and one fixed table realize every partial-recursive
function. The source index is chosen once, before its argument is supplied. -/
theorem universal_for_partrec (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index : Nat, ∀ argument,
      ((∃ value, theory.MultiStep (start (TuringInterpreter.universalProgram index argument))
          (result value)) ↔ (function argument).Dom) ∧
      (∀ output, output ∈ function argument →
        ∃ final, theory.MultiStep (start (TuringInterpreter.universalProgram index argument))
          (result (TuringPrograms.encodeConfiguration final)) ∧
          TuringMachine.PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
            (Turing.PartrecToTM2.halt [output]) final) := by
  obtain ⟨code, implements⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨Encodable.encode code, fun argument => ⟨?_, ?_⟩⟩
  · simpa only [Denumerable.ofNat_encode, implements] using
      universal_halts_iff (Encodable.encode code) argument
  · intro output computed
    apply universal_output_preserved
    simpa only [Denumerable.ofNat_encode, implements] using computed

theorem universal_halting_not_computable :
    ¬ ComputablePred fun index : Nat =>
      ∃ value, theory.MultiStep (start (TuringInterpreter.universalProgram index 0)) (result value) :=
  fun decided => Mettapedia.Languages.PartrecMachine.halting_family_not_computable
    (decided.of_eq (universal_halts_iff · 0))

end Mettapedia.Languages.Chaitin.GSLT
