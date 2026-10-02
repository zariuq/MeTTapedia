import Mettapedia.Languages.TuringMachine.PartrecBridge
import Mettapedia.Languages.TuringMachine.NativeTypes
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalPrefixInterpreter
import Mettapedia.Computability.KolmogorovComplexity.PrefixMass

/-!
# Effective conditional prefix machines as authored Turing languages

Each effective conditional prefix machine is compiled to a finite deterministic
table. Binary program and auxiliary condition are encoded as finite work-tape
input; the halting programs are prefix-free for each condition, and their
length weight is the weight of the table's generated halting type. Completed
outputs carry a discrete mass whose total agrees with this halting weight.

The existing effective trimmed interpreter yields one table that uniformly
hosts all effective conditional prefix machines, preserving outputs with a
fixed compiler prefix per source machine. A one-way streaming input protocol
requires a separate operational model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix

open Turing.ToPartrec KolmogorovComplexity
open scoped Classical ENNReal BigOperators

variable (source : ConditionalPrefixFreeMachine)
variable (effective : Partrec₂ fun program condition => Part.ofOption (source.compute program condition))

include effective in
theorem exists_nativeCode : ∃ code : Nat.Partrec.Code, ∀ program condition,
    code.eval (Encodable.encode (program, condition)) =
      Encodable.encode <$> Part.ofOption (source.compute program condition) := by
  unfold Partrec₂ Partrec at effective
  obtain ⟨code, specification⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨code, fun program condition => ?_⟩
  simpa using congrArg (fun compute => compute (Encodable.encode (program, condition))) specification

noncomputable def nativeCode : Nat.Partrec.Code :=
  Classical.choose (exists_nativeCode source effective)

theorem nativeCode_eval (program condition : BinString) :
    (nativeCode source effective).eval (Encodable.encode (program, condition)) =
      Encodable.encode <$> Part.ofOption (source.compute program condition) :=
  Classical.choose_spec (exists_nativeCode source effective) program condition

noncomputable def programCode : Code := PartrecMachine.compile (nativeCode source effective)

theorem programCode_eval (program condition : BinString) :
    (programCode source effective).eval [Encodable.encode (program, condition)] =
      (fun output => [Encodable.encode output]) <$> Part.ofOption (source.compute program condition) := by
  rw [programCode, PartrecMachine.compile_eval, List.headI_cons, nativeCode_eval]
  simp only [Part.map_eq_map, Part.map_map]
  rfl

noncomputable def machine : Machine := PartrecBridge.machine (programCode source effective)

noncomputable def inputConfiguration (program condition : BinString) : Configuration :=
  PartrecBridge.inputConfiguration (programCode source effective) [Encodable.encode (program, condition)]

theorem deterministic : (machine source effective).Deterministic := PartrecBridge.deterministic _

theorem input_state (program condition : BinString) :
    (inputConfiguration source effective program condition).state = 0 :=
  PartrecBridge.input_state _ _

theorem halts_iff (program condition : BinString) :
    HaltsFrom (machine source effective) (inputConfiguration source effective program condition).term ↔
      source.compute program condition ≠ none := by
  change HaltsFrom (PartrecBridge.machine _) (PartrecBridge.inputConfiguration _ _).term ↔ _
  rw [PartrecBridge.halts_iff, programCode_eval]
  cases result : source.compute program condition <;> simp [Part.ofOption]

def HaltingPrograms (condition : BinString) : Set BinString :=
  {program | HaltsFrom (machine source effective) (inputConfiguration source effective program condition).term}

theorem prefix_free (condition : BinString) : PrefixFree (HaltingPrograms source effective condition) := by
  intro first firstHalts second secondHalts different isPrefix
  have firstActive := (halts_iff source effective first condition).mp firstHalts
  have secondActive := (halts_iff source effective second condition).mp secondHalts
  exact secondActive (source.prefix_free condition first second isPrefix different firstActive)

theorem halting_type_iff (program condition : BinString) :
    Mettapedia.OSLF.Framework.FormulaFixpoint.lfp (haltingTransformer (machine source effective))
      (inputConfiguration source effective program condition).term ↔
      source.compute program condition ≠ none := by
  rw [← haltsFrom_eq_lfp]
  exact halts_iff _ _ _ _

noncomputable def haltingMass (condition : BinString) : ENNReal :=
  prefixProgramMass (HaltingPrograms source effective condition)

theorem haltingMass_le_one (condition : BinString) : haltingMass source effective condition ≤ 1 :=
  prefixProgramMass_le_one _ (prefix_free source effective condition)

/-- Completed output mass agrees with the weight of the actual table's
halting type under its binary program interface. -/
theorem outputMass_total (condition : BinString) :
    (∑' output, prefixOutputMass (source.compute · condition) output) =
      haltingMass source effective condition := by
  rw [prefixOutputMass_total]
  unfold haltingMass
  apply congrArg prefixProgramMass
  ext program
  exact (halts_iff source effective program condition).symm

theorem outputMass_total_le_one (condition : BinString) :
    (∑' output, prefixOutputMass (source.compute · condition) output) ≤ 1 :=
  prefixOutputMass_total_le_one _ (conditionalHaltingPrograms_prefixFree source condition)

/-- A source answer is retained in the terminal table configuration. -/
theorem output_preserved (program condition output : BinString)
    (computed : source.compute program condition = some output) :
    ∃ final, final ∈ _root_.StateTransition.eval (machine source effective).next?
      (inputConfiguration source effective program condition) ∧
      PartrecBridge.Represents (programCode source effective)
        (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  apply PartrecBridge.eval_preserved
  rw [programCode_eval, computed]
  simp [Part.ofOption]

/-- Every terminal table run is certified by a returned source string. -/
theorem output_reflected (program condition : BinString) {final : Configuration}
    (computed : final ∈ _root_.StateTransition.eval (machine source effective).next?
      (inputConfiguration source effective program condition)) :
    ∃ output, source.compute program condition = some output ∧
      PartrecBridge.Represents (programCode source effective)
        (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  obtain ⟨result, sourceComputed, represented⟩ := PartrecBridge.eval_reflected
    (programCode source effective) [Encodable.encode (program, condition)] computed
  rw [programCode_eval] at sourceComputed
  obtain ⟨output, member, rfl⟩ := (Part.mem_map_iff _).mp sourceComputed
  refine ⟨output, ?_, represented⟩
  simpa only [Part.mem_ofOption, Option.mem_def] using member

noncomputable def universalMachine : Machine := machine trimmedIndexedHost trimmedIndexedHost_effective

/-- One fixed table hosts all effective conditional prefix machines, with
one compiler prefix per source machine and the original auxiliary condition. -/
theorem universal_prefix_simulation (other : ConditionalPrefixFreeMachine)
    (otherEffective : Partrec₂ fun program condition => Part.ofOption (other.compute program condition)) :
    ∃ compilerPrefix : BinString, ∀ program condition,
      HaltsFrom universalMachine
        (inputConfiguration trimmedIndexedHost trimmedIndexedHost_effective (compilerPrefix ++ program) condition).term ↔
      HaltsFrom (machine other otherEffective) (inputConfiguration other otherEffective program condition).term := by
  obtain ⟨simulation⟩ := trimmedIndexedHost_simulates_effective other otherEffective
  refine ⟨simulation.compilerPrefix, fun program condition => ?_⟩
  rw [universalMachine, halts_iff, halts_iff, simulation.compute_eq]

/-- Uniform interpretation preserves returned binary strings, with the
same fixed program prefix for every program and auxiliary condition. -/
theorem universal_prefix_outputs (other : ConditionalPrefixFreeMachine)
    (otherEffective : Partrec₂ fun program condition => Part.ofOption (other.compute program condition)) :
    ∃ compilerPrefix : BinString, ∀ program condition output,
      other.compute program condition = some output →
      ∃ final, final ∈ _root_.StateTransition.eval universalMachine.next?
        (inputConfiguration trimmedIndexedHost trimmedIndexedHost_effective
          (compilerPrefix ++ program) condition) ∧
        PartrecBridge.Represents (programCode trimmedIndexedHost trimmedIndexedHost_effective)
          (Turing.PartrecToTM2.halt [Encodable.encode output]) final := by
  obtain ⟨simulation⟩ := trimmedIndexedHost_simulates_effective other otherEffective
  refine ⟨simulation.compilerPrefix, fun program condition output computed => ?_⟩
  apply output_preserved
  rw [simulation.compute_eq, computed]

end Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix
