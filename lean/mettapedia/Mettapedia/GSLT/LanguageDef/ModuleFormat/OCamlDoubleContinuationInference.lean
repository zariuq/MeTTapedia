import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralInference
import Mettapedia.OSLF.MeTTaIL.GeneralEmptyContextInference

/-! Branch and let continuations retain two closed payloads before their
shared environment/continuation captures. Actual grammar descent fixes
those capture sorts and positions.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def doublePayloadFrame (label : String) : Prop := label = "MlKBranch" ∨ label = "MlKLet"

def doubleContinuationOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .right, [1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:environment", .right, [2, 2]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .right, [2, 3]⟩, [], .base "MlContinuation"⟩]

def doubleContinuationInference : Inference :=
  let rows := evaluateOccurrences ++ doubleContinuationOccurrences
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem double_continuation_inspect (label : String) (allowed : doublePayloadFrame label) (reference : Nat)
    (first second : Pattern) (firstShape : VectorFirstOrder first) (secondShape : VectorFirstOrder second)
    (firstClosed : first.freeFvarNames = []) (secondClosed : second.freeFvarNames = []) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, hole "environment", node label [first, second, hole "environment", hole "continuation"]]) =
      some doubleContinuationOccurrences := by
  have firstAddresses := vector_addresses_closed firstShape firstClosed
  have secondAddresses := vector_addresses_closed secondShape secondClosed
  rcases allowed with rfl | rfl
  all_goals
    simp only [inspect, node, addresses, argumentAddresses, code_addresses, firstAddresses, secondAddresses, hole,
      List.nil_append, List.append_nil]
    simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
      matchesParameterRepresentation?, guard, doubleContinuationOccurrences]

theorem double_continuation_infer (label : String) (allowed : doublePayloadFrame label) (name : String)
    (reference target : Nat) (first second : Pattern) (firstShape : VectorFirstOrder first) (secondShape : VectorFirstOrder second)
    (firstClosed : first.freeFvarNames = []) (secondClosed : second.freeFvarNames = []) :
    infer? baseLanguage (rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlEvaluate" [code target, hole "environment", node label [first, second, hole "environment", hole "continuation"]])) =
      some doubleContinuationInference := by
  simp only [infer?, rule, evaluate_head, evaluate_inspect, double_continuation_inspect label allowed target first second firstShape secondShape firstClosed secondClosed,
    Option.bind_eq_bind, Option.bind_some]
  simp [doubleContinuationInference, evaluateOccurrences, doubleContinuationOccurrences, implicitTypes, consistent,
    lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
    dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
    occurrenceAt?, occurrenceDepthAt?, node, hole]
  decide +kernel

#print axioms double_continuation_inspect
#print axioms double_continuation_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
