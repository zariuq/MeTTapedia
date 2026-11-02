import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInput
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectedBaseCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralGeneratedVectorCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralSelectedRuleBounds

/-! All selected generated instruction rows realize their ordinary source
instances as actual root firings. Inferred captures and output-name bounds
come from the actual admission plan, not per-program witness assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem instruction_plan_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {instruction : OCaml.Instruction}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern} {assignment : Bindings}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (formed : compileInstruction? pool reference instruction = some row.authored)
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      source ordinal trace captured captured [] target := by
  let runtime := GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have binding := selected_base_binding position terms types
  have runtimeBinding : GeneralRuleBindingInference.compile? runtime.language row.authored = some row.binding := by
    rw [GeneralRuleBindingInference.compile?_transport grammar (show runtime.language.typeNames = baseLanguage.typeNames from types)]
    exact binding
  obtain ⟨leftShape, rightShape, premiseFree, empty, omitted⟩ := instruction_shapes pool reference instruction row.authored formed
  obtain ⟨hasInput, head⟩ := instruction_input_properties pool reference instruction row.authored formed
  have runtimeHead : GeneralRuleBindingGrammar.headType? runtime.language [] [] row.authored.left = some (.base "MlConfig") := by
    rw [GeneralRuleBindingGrammar.headType?_transport grammar]
    exact head
  exact generated_plan_root_construct position runtimeBinding omitted empty hasInput
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape runtimeHead premiseFree (GeneralExecutionAdmission.selected_premiseFree_bound position premiseFree)
    (state?_closed pool sourceState source sourceEncoded)
    (state?_open runtime.language grammar runtime.free [] pool sourceState source sourceEncoded)
    (state?_open runtime.language grammar runtime.free [] pool targetState target targetEncoded) input output

#print axioms instruction_plan_coverage

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
