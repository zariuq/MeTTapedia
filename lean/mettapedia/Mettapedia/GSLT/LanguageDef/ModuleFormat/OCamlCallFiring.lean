import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCallComposition

/-! Two actual generated root firings, function dispatch and pattern entry,
complete one independent source call. Pattern identity comes from the
prepared pool; caller continuations and receipt histories remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem patternId_injective : Function.Injective patternId := by
  intro first second same
  exact digits_injective (List.cons.inj (Pattern.apply.inj same).2).1

theorem pattern_reference_at {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {index : Nat}
    (resolved : patternReference? pool parameter = some (patternId index)) : pool[index]? = some parameter := by
  unfold patternReference? at resolved
  obtain ⟨actual, found, same⟩ := Option.map_eq_some_iff.mp resolved
  have equal := patternId_injective same
  subst actual
  exact OCaml.patternIndex?_sound parameter pool index found

theorem call_firings_source {plan : GeneralExecutionAdmission.Plan}
    {functionRow patternRow : GeneralExecutionAdmission.RulePlan} {functionOrdinal patternOrdinal : Nat}
    {program : OCaml.Program} {pool : List OCaml.MatchPattern} {reference : OCaml.Code}
    {instruction : OCaml.Instruction} {rows : List RewriteRule}
    {actualFunction argument : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
    {index : Nat} {parameter : OCaml.MatchPattern} {body : OCaml.Code} {sourceEnvironment : OCaml.Environment}
    {request target : Pattern}
    {functionTrace patternTrace : List GeneralScopedMatchMachine.BagChoice}
    {functionCaptured functionCompleted patternCaptured patternCompleted : ScopedRuleMatching.Assignment}
    {functionHistory patternHistory : List GeneralPremise.Event}
    (functionPosition : plan.rules[functionOrdinal]? = some functionRow)
    (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program pool reference instruction = some rows)
    (functionAuthored : functionRow.authored ∈ rows)
    (functionZero : GeneralPremise.checkZeroDependencies functionRow.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (functionFiring : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlApply" [value actualFunction, value argument, encodedRest]) functionOrdinal
      functionTrace functionCaptured functionCompleted functionHistory request)
    (requestShape : request = node "MlMatchOne" [patternId index, value argument, code body, environment sourceEnvironment, encodedRest])
    (poolEntry : pool[index]? = some parameter)
    (patternPosition : plan.rules[patternOrdinal]? = some patternRow)
    (patternAuthored : patternRow.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (patternZero : GeneralPremise.checkZeroDependencies patternRow.binding.spec = true)
    (patternFiring : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      request patternOrdinal patternTrace patternCaptured patternCompleted patternHistory target) :
    functionCompleted = functionCaptured ∧ functionHistory = [] ∧
      patternCompleted = patternCaptured ∧ patternHistory = [] ∧
      ∃ next, OCaml.machineStep program (.returned actualFunction (.function argument :: rest)) = .ok (some next) ∧
        state? pool next = some target := by
  obtain ⟨functionSame, functionEmpty, actualParameter, actualBody, patternCode, actualEnvironment,
    actualReference, actualRequest, sourceApplication⟩ :=
      function_firing_source functionPosition declared compiled functionAuthored functionZero functionFiring
  have requestSame := actualRequest.symm.trans requestShape
  have arguments := List.cons.inj (Pattern.apply.inj requestSame).2
  have codeSame := (List.cons.inj (List.cons.inj arguments.2).2).1
  have bodySame := code_injective codeSame
  have environmentSame := environment_injective (List.cons.inj (List.cons.inj (List.cons.inj arguments.2).2).2).1
  have referenceSame := arguments.1
  rw [referenceSame] at actualReference
  have parameterAt := pattern_reference_at actualReference
  have parameterSame := Option.some.inj (parameterAt.symm.trans poolEntry)
  subst actualParameter
  subst actualBody
  subst actualEnvironment
  rw [requestShape] at patternFiring
  obtain ⟨patternSame, patternEmpty, boundValues, matched, output⟩ :=
    match_one_firing_source patternPosition patternAuthored patternZero patternFiring
  refine ⟨functionSame, functionEmpty, patternSame, patternEmpty,
    .evaluate body (OCaml.extend sourceEnvironment boundValues) rest, ?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.returnValue, sourceApplication, OCaml.enterBody, matched, Except.map]
  · rw [output]
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms call_firings_source

theorem returned_call_firings_source {plan : GeneralExecutionAdmission.Plan}
    {returnRow functionRow patternRow : GeneralExecutionAdmission.RulePlan}
    {returnOrdinal functionOrdinal patternOrdinal : Nat}
    {program : OCaml.Program} {pool : List OCaml.MatchPattern} {reference : OCaml.Code}
    {instruction : OCaml.Instruction} {rows : List RewriteRule}
    {actualFunction argument : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
    {index : Nat} {parameter : OCaml.MatchPattern} {body : OCaml.Code} {sourceEnvironment : OCaml.Environment}
    {application request target : Pattern}
    {returnTrace functionTrace patternTrace : List GeneralScopedMatchMachine.BagChoice}
    {returnCaptured returnCompleted functionCaptured functionCompleted patternCaptured patternCompleted : ScopedRuleMatching.Assignment}
    {returnHistory functionHistory patternHistory : List GeneralPremise.Event}
    (returnPosition : plan.rules[returnOrdinal]? = some returnRow)
    (returnAuthored : baseLanguage.rewrites[2]? = some returnRow.authored)
    (returnZero : GeneralPremise.checkZeroDependencies returnRow.binding.spec = true)
    (returnFiring : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value actualFunction, node "MlKFunction" [value argument, encodedRest]]) returnOrdinal
      returnTrace returnCaptured returnCompleted returnHistory application)
    (functionPosition : plan.rules[functionOrdinal]? = some functionRow)
    (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program pool reference instruction = some rows)
    (functionAuthored : functionRow.authored ∈ rows)
    (functionZero : GeneralPremise.checkZeroDependencies functionRow.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (functionFiring : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      application functionOrdinal functionTrace functionCaptured functionCompleted functionHistory request)
    (requestShape : request = node "MlMatchOne" [patternId index, value argument, code body, environment sourceEnvironment, encodedRest])
    (poolEntry : pool[index]? = some parameter)
    (patternPosition : plan.rules[patternOrdinal]? = some patternRow)
    (patternAuthored : patternRow.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (patternZero : GeneralPremise.checkZeroDependencies patternRow.binding.spec = true)
    (patternFiring : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      request patternOrdinal patternTrace patternCaptured patternCompleted patternHistory target) :
    returnCompleted = returnCaptured ∧ returnHistory = [] ∧
      functionCompleted = functionCaptured ∧ functionHistory = [] ∧
      patternCompleted = patternCaptured ∧ patternHistory = [] ∧
      ∃ next, OCaml.machineStep program (.returned actualFunction (.function argument :: rest)) = .ok (some next) ∧
        state? pool next = some target := by
  obtain ⟨returnSame, returnEmpty, applicationSame⟩ := return_function_firing returnPosition returnAuthored returnZero returnFiring
  rw [applicationSame] at functionFiring
  exact ⟨returnSame, returnEmpty, call_firings_source functionPosition declared compiled functionAuthored functionZero
    resolved functionFiring requestShape poolEntry patternPosition patternAuthored patternZero patternFiring⟩

#print axioms returned_call_firings_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
