import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralInference

/-! Closure construction infers the environment capture beneath the
authored closure constructor, with its exact source occurrence address.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

def closureOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .right, [0, 1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .right, [1]⟩, [], .base "MlContinuation"⟩]

def closureInference : Inference :=
  let rows := evaluateOccurrences ++ closureOccurrences
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem closure_inspect (reference : Nat) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlReturn" [node "MlClosure" [node "MlLambdaFunction" [code reference], hole "environment"], hole "continuation"]) =
      some closureOccurrences := by
  simp only [inspect, node, addresses, argumentAddresses, code_addresses, hole,
    List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, closureOccurrences]

theorem closure_infer (name : String) (reference : Nat) :
    infer? baseLanguage (rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlReturn" [node "MlClosure" [node "MlLambdaFunction" [code reference], hole "environment"], hole "continuation"])) =
      some closureInference := by
  simp only [infer?, rule, evaluate_head, evaluate_inspect, closure_inspect, Option.bind_eq_bind, Option.bind_some]
  simp [closureInference, evaluateOccurrences, closureOccurrences, implicitTypes, consistent,
    lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
    dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
    occurrenceAt?, occurrenceDepthAt?, node, hole]
  decide +kernel

#print axioms closure_inspect
#print axioms closure_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
