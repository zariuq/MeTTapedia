import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionFiring

/-! Actual variable-lookup receipts select precisely the source environment
entry and return its encoded value, with the full continuation retained.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem variable_firing_source {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {reference index : Nat} {items : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (declared : program.instruction? reference = some (.variable index))
    (formed : compileInstruction? (patterns program) reference (.variable index) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (firing : GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment items, encodedRest]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ actual,
      items[index]? = some actual ∧ OCaml.machineStep program (.evaluate reference items rest) = .ok (some (.returned actual rest)) ∧
      target = node "MlReturn" [value actual, encodedRest] ∧
      state? (patterns program) (.returned actual rest) = some target := by
  obtain ⟨leftShape, rightShape, premiseFree, _, omitted⟩ := instruction_shapes (patterns program) reference (.variable index) row.authored formed
  have binding := selected_base_binding position terms types
  have zero := GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding omitted
    (GeneralRuleBindingInference.vector_binderFree leftShape) (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree binding
  obtain ⟨sameCaptures, emptyHistory, input, output⟩ := plan_vector_rootFiring_readout position zero leftShape
    (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree firing
  obtain ⟨actual, found, result⟩ := variable_rule_readback (patterns program) reference index items encodedRest row.authored (ordinary captured) formed input
  have targetSame := output.symm.trans result
  refine ⟨sameCaptures, emptyHistory, actual, found, ?_, targetSame, ?_⟩
  · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, found, Except.map]
    rfl
  · rw [targetSame]
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms variable_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
