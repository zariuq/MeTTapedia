import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralInference

/-! Applying a nonrecursive closure infers the captured environment,
argument and continuation from the real grammar positions. Its code and
pattern references remain compact closed payloads.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

def lambdaInputOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .left, [0, 1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:argument", .left, [1]⟩, [], .base "MlValue"⟩,
   ⟨⟨"ml:continuation", .left, [2]⟩, [], .base "MlContinuation"⟩]

def lambdaOutputOccurrences : List Occurrence :=
  [⟨⟨"ml:argument", .right, [1]⟩, [], .base "MlValue"⟩,
   ⟨⟨"ml:environment", .right, [3]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .right, [4]⟩, [], .base "MlContinuation"⟩]

def lambdaInference : Inference :=
  let rows := lambdaInputOccurrences ++ lambdaOutputOccurrences
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"),
    ("ml:argument", .base "MlValue"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem lambda_input_head (reference : Nat) :
    headType? baseLanguage [] [] (node "MlApply" [node "MlClosure"
      [node "MlLambdaFunction" [code reference], hole "environment"], hole "argument", hole "continuation"]) =
      some (.base "MlConfig") := by
  simp only [headType?, node]
  decide +kernel

theorem lambda_input_inspect (reference : Nat) :
    inspect baseLanguage [] .left [] (.base "MlConfig") (node "MlApply" [node "MlClosure"
      [node "MlLambdaFunction" [code reference], hole "environment"], hole "argument", hole "continuation"]) =
      some lambdaInputOccurrences := by
  simp only [inspect, node, addresses, argumentAddresses, code_addresses, hole,
    List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, lambdaInputOccurrences]

theorem lambda_output_inspect (index body : Nat) :
    inspect baseLanguage [] .right [] (.base "MlConfig") (node "MlMatchOne"
      [patternId index, hole "argument", code body, hole "environment", hole "continuation"]) =
      some lambdaOutputOccurrences := by
  simp only [inspect, node, addresses, argumentAddresses, patternId_addresses, code_addresses, hole,
    List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, lambdaOutputOccurrences]

theorem lambda_infer (name : String) (reference index body : Nat) :
    infer? baseLanguage (rule name
      (node "MlApply" [node "MlClosure" [node "MlLambdaFunction" [code reference], hole "environment"],
        hole "argument", hole "continuation"])
      (node "MlMatchOne" [patternId index, hole "argument", code body, hole "environment", hole "continuation"])) =
      some lambdaInference := by
  simp only [infer?, rule, lambda_input_head, lambda_input_inspect, lambda_output_inspect,
    Option.bind_eq_bind, Option.bind_some]
  simp [lambdaInference, lambdaInputOccurrences, lambdaOutputOccurrences, implicitTypes, consistent,
    lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
    dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
    occurrenceAt?, occurrenceDepthAt?, node, hole]
  decide +kernel

#print axioms lambda_input_head
#print axioms lambda_input_inspect
#print axioms lambda_output_inspect
#print axioms lambda_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
