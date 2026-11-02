import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionShapes
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionSource
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootReadout

/-! Actual shared function-dispatch receipts recover the source closure,
body and captured environment. Administrative dispatch is distinguished
from the source machine step completed by pattern entry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem function_root_readout {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {instruction : OCaml.Instruction}
    {rows : List RewriteRule} {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (compiled : functionRules? program pool reference instruction = some rows)
    (authored : row.authored ∈ rows)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) row.authored.left = source ∧
      applyBindings (ordinary captured) row.authored.right = target := by
  obtain ⟨leftShape, rightShape, premiseFree⟩ := function_row_shapes program pool reference instruction rows row.authored compiled authored
  exact plan_vector_rootFiring_readout position zero leftShape
    (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree firing

theorem function_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {instruction : OCaml.Instruction} {rows : List RewriteRule}
    {actualFunction argument : OCaml.Value} {continuation target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program pool reference instruction = some rows)
    (authored : row.authored ∈ rows)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlApply" [value actualFunction, value argument, continuation]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ parameter body patternCode sourceEnvironment,
      patternReference? pool parameter = some patternCode ∧
      target = node "MlMatchOne" [patternCode, value argument, code body, environment sourceEnvironment, continuation] ∧
      ∀ rest : OCaml.Continuation,
        OCaml.applyClosure program actualFunction argument rest = .ok (OCaml.enterBody parameter argument body sourceEnvironment rest) := by
  obtain ⟨sameCaptures, emptyHistory, input, output⟩ := function_root_readout position compiled authored zero firing
  obtain ⟨parameter, body, patternCode, sourceEnvironment, resolved, targetSame, source⟩ :=
    function_rule_readback program pool reference instruction rows row.authored declared compiled authored actualFunction argument
      continuation (ordinary captured) input
  exact ⟨sameCaptures, emptyHistory, parameter, body, patternCode, sourceEnvironment, resolved, output.symm.trans targetSame, source⟩

#print axioms function_root_readout
#print axioms function_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
