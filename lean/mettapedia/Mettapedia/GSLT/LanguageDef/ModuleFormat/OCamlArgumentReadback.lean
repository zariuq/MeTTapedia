import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlArgumentInstructions
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionFiring

/-! Compiled argument-entry receipts cannot invent a different order,
environment or continuation. The nullary case remains a build request.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem apply_build (assignment : Bindings) (kind : OCaml.Build) :
    applyBindings assignment (build kind) = build kind := by
  cases kind <;> simp only [build, apply_node, List.map_cons, List.map_nil, apply_tag, apply_primitive]

theorem build_instruction_right (pool : List OCaml.MatchPattern) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (row : RewriteRule)
    (formed : compileInstruction? pool reference (buildInstruction kind arguments) = some row) :
    row.right = startArguments (build kind) arguments (hole "environment") (hole "continuation") := by
  cases kind <;>
    simp only [buildInstruction, compileInstruction?, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at formed <;> cases formed <;> rfl

theorem build_instruction_readback (pool : List OCaml.MatchPattern) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (row : RewriteRule) (assignment : Bindings)
    (captured rest : Pattern)
    (formed : compileInstruction? pool reference (buildInstruction kind arguments) = some row)
    (input : applyBindings assignment row.left = node "MlEvaluate" [code reference, captured, rest]) :
    applyBindings assignment row.right = startArguments (build kind) arguments captured rest := by
  rw [build_instruction_left pool reference kind arguments row formed] at input
  simp only [apply_node, List.map_cons, List.map_nil, apply_code] at input
  have fields := List.cons.inj (Pattern.apply.inj input).2
  have environmentSame := (List.cons.inj fields.2).1
  have restSame := (List.cons.inj (List.cons.inj fields.2).2).1
  rw [build_instruction_right pool reference kind arguments row formed, apply_startArguments, apply_build,
    environmentSame, restSame]

theorem build_instruction_firing_readback {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {pool : List OCaml.MatchPattern} {reference : OCaml.Code} {kind : OCaml.Build} {arguments : List OCaml.Code}
    {capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (formed : compileInstruction? pool reference (buildInstruction kind arguments) = some row.authored)
    (firing : GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, capturedEnvironment, rest]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = startArguments (build kind) arguments capturedEnvironment rest := by
  obtain ⟨leftShape, rightShape, premiseFree, _, omitted⟩ := instruction_shapes pool reference (buildInstruction kind arguments) row.authored formed
  have binding := selected_base_binding position terms types
  have zero := GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding omitted
    (GeneralRuleBindingInference.vector_binderFree leftShape) (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree binding
  obtain ⟨same, empty, input, output⟩ := plan_vector_rootFiring_readout position zero leftShape
    (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree firing
  exact ⟨same, empty, output.symm.trans (build_instruction_readback pool reference kind arguments row.authored
    (ordinary captured) capturedEnvironment rest formed input)⟩

#print axioms build_instruction_readback
#print axioms build_instruction_firing_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
