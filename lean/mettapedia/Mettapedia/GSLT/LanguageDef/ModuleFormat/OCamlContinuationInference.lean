import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralInference
import Mettapedia.OSLF.MeTTaIL.GeneralEmptyContextInference

/-! The authored argument, cons, Boolean and match continuations share one
capture shape. Their closed source payload never contributes an address.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def singlePayloadFrame (label : String) : Prop := label = "MlKArgument" ∨ label = "MlKConsTail" ∨
  label = "MlKAnd" ∨ label = "MlKOr" ∨ label = "MlKMatch"

def continuationOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .right, [1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:environment", .right, [2, 1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .right, [2, 2]⟩, [], .base "MlContinuation"⟩]

def continuationInference : Inference :=
  let rows := evaluateOccurrences ++ continuationOccurrences
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem continuation_inspect (label : String) (allowed : singlePayloadFrame label) (reference : Nat)
    (payload : Pattern) (shape : VectorFirstOrder payload) (closed : payload.freeFvarNames = []) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, hole "environment", node label [payload, hole "environment", hole "continuation"]]) =
      some continuationOccurrences := by
  have payloadAddresses := vector_addresses_closed shape closed
  rcases allowed with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [inspect, node, addresses, argumentAddresses, code_addresses, payloadAddresses, hole,
      List.nil_append, List.append_nil]
    simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
      matchesParameterRepresentation?, guard, continuationOccurrences]

theorem continuation_infer (label : String) (allowed : singlePayloadFrame label) (name : String)
    (reference target : Nat) (payload : Pattern) (shape : VectorFirstOrder payload) (closed : payload.freeFvarNames = []) :
    infer? baseLanguage (rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlEvaluate" [code target, hole "environment", node label [payload, hole "environment", hole "continuation"]])) =
      some continuationInference := by
  simp only [infer?, rule, evaluate_head, evaluate_inspect, continuation_inspect label allowed target payload shape closed,
    Option.bind_eq_bind, Option.bind_some]
  simp [continuationInference, evaluateOccurrences, continuationOccurrences, implicitTypes, consistent,
    lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
    dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
    occurrenceAt?, occurrenceDepthAt?, node, hole]
  decide +kernel

#print axioms continuation_inspect
#print axioms continuation_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
