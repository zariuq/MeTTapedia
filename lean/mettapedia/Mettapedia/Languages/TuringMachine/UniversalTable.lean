import Mettapedia.Languages.TuringMachine.PartrecBridge
import Mettapedia.Languages.TuringMachine.InputEncoding
import Mettapedia.Languages.TuringMachine.NativeTypes
import Mettapedia.Languages.TuringMachine.Universal
import Mettapedia.Languages.PartrecMachine.UndecidableEquivalence

/-!
# A finite universal table and undecidable authored halting

The universal partial-recursive code is compiled through Mathlib's stack and
tape machines, restricted to its finite control, and realized by one finite
deterministic transition table. Prepared inputs start in state zero. Returned
values are retained in terminal configurations. Input preparation is primitive
recursive, both for raw configuration codes and for the shared pattern codes.

Halting is undecidable for this table and for the existing universal bag
language. The latter theorem uses the language's actual generated steps and
normal forms, with a primitive-recursive reduction on structural pattern codes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.UniversalTable

open Turing Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- One finite deterministic table that runs the established universal code. -/
noncomputable def machine : Machine := PartrecBridge.machine PartrecMachine.universal

noncomputable def inputConfiguration (index argument : Nat) : Configuration :=
  PartrecBridge.inputConfiguration PartrecMachine.universal [index, argument]

theorem deterministic : machine.Deterministic :=
  PartrecBridge.deterministic _

theorem input_state (index argument : Nat) :
    (inputConfiguration index argument).state = 0 :=
  PartrecBridge.input_state _ _

theorem halts_iff (index argument : Nat) :
    HaltsFrom machine (inputConfiguration index argument).term ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom := by
  change HaltsFrom (PartrecBridge.machine PartrecMachine.universal)
    (PartrecBridge.inputConfiguration PartrecMachine.universal [index, argument]).term ↔ _
  rw [PartrecBridge.halts_iff, PartrecMachine.universal_eval]
  rfl

theorem output_preserved (index argument output : Nat)
    (computed : output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument) :
    ∃ final, final ∈ StateTransition.eval machine.next? (inputConfiguration index argument) ∧
      PartrecBridge.Represents PartrecMachine.universal
        (PartrecToTM2.halt [output]) final := by
  apply PartrecBridge.eval_preserved
  rw [PartrecMachine.universal_eval]
  exact Part.mem_map _ computed

theorem output_reflected (index argument : Nat) {final : Configuration}
    (computed : final ∈ StateTransition.eval machine.next? (inputConfiguration index argument)) :
    ∃ output, output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument ∧
      PartrecBridge.Represents PartrecMachine.universal
        (PartrecToTM2.halt [output]) final := by
  obtain ⟨result, sourceComputed, represented⟩ := PartrecBridge.eval_reflected
    PartrecMachine.universal [index, argument] computed
  rw [PartrecMachine.universal_eval] at sourceComputed
  obtain ⟨output, member, rfl⟩ := (Part.mem_map_iff _).mp sourceComputed
  exact ⟨output, member, represented⟩

/-- Every partial-recursive function has one program index for this fixed
table. All inputs preserve termination and all returned natural values. -/
theorem universal_for_partrec (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index : Nat, ∀ argument,
      (HaltsFrom machine (inputConfiguration index argument).term ↔ (function argument).Dom) ∧
      (∀ output, output ∈ function argument →
        ∃ final, final ∈ StateTransition.eval machine.next? (inputConfiguration index argument) ∧
          PartrecBridge.Represents PartrecMachine.universal
            (PartrecToTM2.halt [output]) final) := by
  obtain ⟨code, implements⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨Encodable.encode code, fun argument => ⟨?_, ?_⟩⟩
  · simpa only [Denumerable.ofNat_encode, implements] using
      halts_iff (Encodable.encode code) argument
  · intro output computed
    apply output_preserved
    simpa only [Denumerable.ofNat_encode, implements] using computed

/-- A total source program really terminates and returns its value through
the compiler, even though no fixed simulation budget was chosen. -/
theorem zero_output (argument : Nat) :
    ∃ final, final ∈ StateTransition.eval machine.next?
      (inputConfiguration (Encodable.encode Nat.Partrec.Code.zero) argument) ∧
      PartrecBridge.Represents PartrecMachine.universal
        (PartrecToTM2.halt [0]) final := by
  apply output_preserved
  rw [Denumerable.ofNat_encode]
  change 0 ∈ Part.some 0
  exact Part.mem_some 0

/-- Source divergence cannot be mistaken for a terminal target state. -/
theorem silent_does_not_halt (argument : Nat) :
    ¬ HaltsFrom machine
      (inputConfiguration (Encodable.encode Mettapedia.Computability.silentCode) argument).term := by
  rw [halts_iff, Denumerable.ofNat_encode, Mettapedia.Computability.silentCode_eval]
  exact not_false

theorem halting_type_iff (index argument : Nat) :
    Mettapedia.OSLF.Framework.FormulaFixpoint.lfp (haltingTransformer machine) (inputConfiguration index argument).term ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom := by
  rw [← haltsFrom_eq_lfp]
  exact halts_iff _ _

/-- Undecidability on the explicitly numbered family of prepared inputs. -/
theorem halting_family_not_computable :
    ¬ ComputablePred fun index : Nat => HaltsFrom machine (inputConfiguration index 0).term :=
  fun decided => PartrecMachine.halting_family_not_computable (decided.of_eq (halts_iff · 0))

/-- Codes of complete raw configurations, not an abstract source-program index. -/
def HaltingCode (code : Nat) : Prop :=
  ∃ configuration, InputEncoding.configurationCode configuration = code ∧
    HaltsFrom machine configuration.term

theorem haltingCode_configuration (configuration : Configuration) :
    HaltingCode (InputEncoding.configurationCode configuration) ↔
      HaltsFrom machine configuration.term := by
  constructor
  · rintro ⟨other, same, halted⟩
    cases InputEncoding.configurationCode_injective same
    exact halted
  · exact fun halted => ⟨configuration, rfl, halted⟩

theorem input_code_primrec :
    Primrec fun index : Nat => InputEncoding.configurationCode (inputConfiguration index 0) :=
  (InputEncoding.inputConfiguration_code_primrec PartrecMachine.universal).comp
    (Primrec.list_cons.comp Primrec.id (Primrec.const [0]))

/-- The actual halting set of coded configurations of this one table is undecidable. -/
theorem haltingCode_not_computable : ¬ ComputablePred HaltingCode := by
  intro decided
  apply halting_family_not_computable
  obtain ⟨decidable, computable⟩ := decided
  have prepared : ComputablePred fun index : Nat =>
      HaltingCode (InputEncoding.configurationCode (inputConfiguration index 0)) :=
    ⟨fun index => decidable (InputEncoding.configurationCode (inputConfiguration index 0)),
      computable.comp input_code_primrec.to_comp⟩
  exact prepared.of_eq fun index => haltingCode_configuration (inputConfiguration index 0)

theorem universalTheory_halts_iff (index argument : Nat) :
    (∃ final, (langGSLT universalTheory).MultiStep
      (withTable machine (inputConfiguration index argument).term) final ∧
      (langGSLT universalTheory).IsNormalForm final) ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom :=
  (haltsFrom_iff_universal _ _).symm.trans (halts_iff _ _)

theorem universalTheory_halting_family_not_computable :
    ¬ ComputablePred fun index : Nat =>
      ∃ final, (langGSLT universalTheory).MultiStep
        (withTable machine (inputConfiguration index 0).term) final ∧
        (langGSLT universalTheory).IsNormalForm final :=
  fun decided => PartrecMachine.halting_family_not_computable
    (decided.of_eq (universalTheory_halts_iff · 0))

/-- Encode the bag containing a term and this fixed machine description. -/
noncomputable def withTableCode (code : Nat) : Nat :=
  Nat.pair 6 (Nat.pair 1 (Nat.pair
    (Nat.succ (Nat.pair code
      (Mettapedia.OSLF.MeTTaIL.PatternCode.patternListCode (description machine)))) 0))

theorem withTableCode_primrec : Primrec withTableCode :=
  Primrec₂.natPair.comp (Primrec.const 6)
    (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const _)))
        (Primrec.const 0)))

theorem withTableCode_eq (pattern : Pattern) :
    withTableCode (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern) =
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (withTable machine pattern) :=
  rfl

theorem universal_input_code_primrec :
    Primrec fun index : Nat => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
      (withTable machine (inputConfiguration index 0).term) := by
  apply (withTableCode_primrec.comp
    ((InputEncoding.inputConfiguration_patternCode_primrec PartrecMachine.universal).comp
      (Primrec.list_cons.comp Primrec.id (Primrec.const [0])))).of_eq
  intro index
  exact withTableCode_eq _

/-- Structural codes of all terms that can reach a normal form in the
universal bag theory, including terms outside the prepared-input family. -/
def LanguageHaltingCode (code : Nat) : Prop :=
  ∃ pattern, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern = code ∧
    ∃ final, (langGSLT universalTheory).MultiStep pattern final ∧
      (langGSLT universalTheory).IsNormalForm final

theorem languageHaltingCode_pattern (pattern : Pattern) :
    LanguageHaltingCode (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern) ↔
      ∃ final, (langGSLT universalTheory).MultiStep pattern final ∧
        (langGSLT universalTheory).IsNormalForm final := by
  constructor
  · rintro ⟨other, same, halted⟩
    cases Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode_injective same
    exact halted
  · exact fun halted => ⟨pattern, rfl, halted⟩

/-- Halting in the actual authored universal language is undecidable under
the framework's structural numbering of patterns. -/
theorem languageHaltingCode_not_computable : ¬ ComputablePred LanguageHaltingCode := by
  intro decided
  apply universalTheory_halting_family_not_computable
  obtain ⟨decidable, computable⟩ := decided
  have prepared : ComputablePred fun index : Nat =>
      LanguageHaltingCode (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (withTable machine (inputConfiguration index 0).term)) :=
    ⟨fun index => decidable _, computable.comp universal_input_code_primrec.to_comp⟩
  exact prepared.of_eq fun index => languageHaltingCode_pattern _

end Mettapedia.Languages.TuringMachine.UniversalTable
