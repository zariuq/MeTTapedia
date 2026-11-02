import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnGather
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBranches

/-! Ordinary instances of the remaining terminal, argument and branch rows.
They use the actual authored field projections rather than a parallel rule set.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem return_done_instance (actual : Pattern) :
    BaseRuleInstance 0 (node "MlReturn" [actual, node "MlKDone"]) (node "MlDone" [actual]) := by
  have fields : (baseLanguage.rewrites[0]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [.fvar "value", node "MlKDone"], node "MlDone" [.fvar "value"], []) := by decide +kernel
  simpa [apply_node, applyBindings] using base_instance_of_fields fields [("value", actual)]

theorem return_argument_instance (actual function captured rest : Pattern) :
    BaseRuleInstance 1 (node "MlReturn" [actual, node "MlKArgument" [function, captured, rest]])
      (node "MlEvaluate" [function, captured, node "MlKFunction" [actual, rest]]) := by
  have fields : (baseLanguage.rewrites[1]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [.fvar "argument", node "MlKArgument" [.fvar "function", .fvar "environment", .fvar "rest"]],
       node "MlEvaluate" [.fvar "function", .fvar "environment", node "MlKFunction" [.fvar "argument", .fvar "rest"]], []) := by decide +kernel
  simpa [apply_node, applyBindings] using base_instance_of_fields fields
    [("argument", actual), ("function", function), ("environment", captured), ("rest", rest)]

theorem return_branch_instance (choice : Bool) (yes no captured rest : Pattern) :
    BaseRuleInstance (if choice then 4 else 5)
      (node "MlReturn" [literal (.boolean choice), node "MlKBranch" [yes, no, captured, rest]])
      (node "MlEvaluate" [if choice then yes else no, captured, rest]) := by
  cases choice with
  | false =>
    have fields : (baseLanguage.rewrites[5]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [node "MlFalse", node "MlKBranch" [.fvar "yes", .fvar "no", .fvar "environment", .fvar "rest"]],
       node "MlEvaluate" [.fvar "no", .fvar "environment", .fvar "rest"], []) := by decide +kernel
    simpa [apply_node, applyBindings, literal] using base_instance_of_fields fields
      [("yes", yes), ("no", no), ("environment", captured), ("rest", rest)]
  | true =>
    have fields : (baseLanguage.rewrites[4]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [node "MlTrue", node "MlKBranch" [.fvar "yes", .fvar "no", .fvar "environment", .fvar "rest"]],
       node "MlEvaluate" [.fvar "yes", .fvar "environment", .fvar "rest"], []) := by decide +kernel
    simpa [apply_node, applyBindings, literal] using base_instance_of_fields fields
      [("yes", yes), ("no", no), ("environment", captured), ("rest", rest)]

#print axioms return_done_instance
#print axioms return_argument_instance
#print axioms return_branch_instance

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
