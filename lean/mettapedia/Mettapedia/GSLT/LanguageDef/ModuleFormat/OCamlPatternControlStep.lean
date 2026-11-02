import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralRootStep

/-! A positive source pattern instance constructs an actual prepared step at
any retained pool occurrence. Duplicate source patterns need not share their
pool index; source control points supply the exact typed request.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding Match GeneralFirstOrderProjection

theorem prepared_pattern_control_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (authored : RewriteRule)
    {source next : OCaml.MachineState} {config target : Pattern} {rank nextRank : Nat} (assignment : Bindings)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter) (member : authored ∈ patternRules index parameter)
    (point : ControlPoint program source config rank) (nextPoint : ControlPoint program next target nextRank)
    (input : applyBindings assignment authored.left = config) (output : applyBindings assignment authored.right = target) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target := by
  obtain ⟨ordinal, row, position, same⟩ := epoch_pattern_row program prepared table index parameter authored built
    (prepared_plan_complete program prepared built) signatures indexed member
  have rowMember : row.authored ∈ patternRules index parameter := by rw [same]; exact member
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have types : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.typeNames = baseLanguage.typeNames :=
    (prepare_readback program prepared built).2.2.2.1
  have binding := selected_base_binding position grammar types
  have runtimeBinding : GeneralRuleBindingInference.compile? (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      row.authored = some row.binding := by
    rw [GeneralRuleBindingInference.compile?_transport grammar types]
    exact binding
  obtain ⟨leftShape, rightShape, premiseFree⟩ := pattern_rule_shapes parameter index row.authored rowMember
  obtain ⟨omitted, empty, hasInput, head⟩ := pattern_rule_binding_fields parameter index row.authored rowMember
  have actualInput : applyBindings assignment row.authored.left = config := by rw [same]; exact input
  have actualOutput : applyBindings assignment row.authored.right = target := by rw [same]; exact output
  obtain ⟨trace, captured, firing⟩ := generated_plan_root_construct position runtimeBinding omitted empty hasInput
    (base_label_deterministic _ grammar) (base_collection_deterministic _ grammar) leftShape rightShape
    (by rw [GeneralRuleBindingGrammar.headType?_transport grammar]; exact head) premiseFree
    (GeneralExecutionAdmission.selected_premiseFree_bound position premiseFree)
    (control_point_epoch_checked program prepared table built point).1 (point.open _ grammar _) (nextPoint.open _ grammar _)
    actualInput actualOutput
  exact GeneralOccurrenceSemantics.root_firing_semantic_step rfl firing

#print axioms prepared_pattern_control_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
