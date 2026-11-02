import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralInference
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Literal dispatch receives its actual grammar-inferred binding plan.
The capture sorts and occurrence addresses come from the authored grammar.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar

def literalInference : Inference :=
  let rows := evaluateOccurrences ++ literalReturnOccurrences
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem literal_infer (name : String) (reference : Nat) (datum : OCaml.Literal) :
    infer? baseLanguage (rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlReturn" [literal datum, hole "continuation"])) = some literalInference := by
  simp only [infer?, rule, evaluate_head, evaluate_inspect, literal_return_inspect,
    Option.bind_eq_bind, Option.bind_some]
  simp [literalInference, evaluateOccurrences, literalReturnOccurrences, implicitTypes, consistent,
    lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
    dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
    occurrenceAt?, occurrenceDepthAt?, node, hole]
  decide +kernel

#print axioms literal_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
