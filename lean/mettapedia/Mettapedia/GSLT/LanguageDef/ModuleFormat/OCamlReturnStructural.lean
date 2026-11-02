import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnReadout

/-! Exact structural return contracts are attached to the authored module
rows. Their witness substitutions also determine any actual scoped firing.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

structure BaseRuleInstance (index : Nat) (source target : Pattern) : Prop where
  realize : ∀ row : RewriteRule, baseLanguage.rewrites[index]? = some row →
    row.premises = [] ∧ ∃ assignment : Bindings,
      applyBindings assignment row.left = source ∧ applyBindings assignment row.right = target

theorem base_instance_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {bound : List TypeExpr} {type : TypeExpr}
    {source expected target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (realization : BaseRuleInstance index source expected)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = expected := by
  obtain ⟨premiseFree, assignment, input, output⟩ := realization.realize row.authored authored
  obtain ⟨sameCaptures, emptyHistory, actualTarget⟩ := pure_base_root_target position authored zero premiseFree input firing
  exact ⟨sameCaptures, emptyHistory, actualTarget.trans output⟩

theorem return_function_instance (function argument rest : Pattern) :
    BaseRuleInstance 2 (node "MlReturn" [function, node "MlKFunction" [argument, rest]])
      (node "MlApply" [function, argument, rest]) := by
  constructor
  intro row authored
  have computed : (baseLanguage.rewrites[2]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlReturn" [.fvar "function", node "MlKFunction" [.fvar "argument", .fvar "rest"]],
        node "MlApply" [.fvar "function", .fvar "argument", .fvar "rest"], []) := by decide +kernel
  rw [authored] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  refine ⟨premiseFree, [("function", function), ("argument", argument), ("rest", rest)], ?_, ?_⟩
  · rw [left]
    simp [apply_node, applyBindings]
  · rw [right]
    simp [apply_node, applyBindings]

theorem return_let_instance (actual parameter body captured rest : Pattern) :
    BaseRuleInstance 3 (node "MlReturn" [actual, node "MlKLet" [parameter, body, captured, rest]])
      (node "MlMatchOne" [parameter, actual, body, captured, rest]) := by
  constructor
  intro row authored
  have computed : (baseLanguage.rewrites[3]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlReturn" [.fvar "value", node "MlKLet" [.fvar "pattern", .fvar "body", .fvar "environment", .fvar "rest"]],
        node "MlMatchOne" [.fvar "pattern", .fvar "value", .fvar "body", .fvar "environment", .fvar "rest"], []) :=
    by decide +kernel
  rw [authored] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  refine ⟨premiseFree,
    [("value", actual), ("pattern", parameter), ("body", body), ("environment", captured), ("rest", rest)], ?_, ?_⟩
  · rw [left]
    simp [apply_node, applyBindings]
  · rw [right]
    simp [apply_node, applyBindings]

theorem return_cons_tail_instance (tail head captured rest : Pattern) :
    BaseRuleInstance 12 (node "MlReturn" [tail, node "MlKConsTail" [head, captured, rest]])
      (node "MlEvaluate" [head, captured, node "MlKConsHead" [tail, rest]]) := by
  constructor
  intro row authored
  have computed : (baseLanguage.rewrites[12]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlReturn" [.fvar "tail", node "MlKConsTail" [.fvar "head", .fvar "environment", .fvar "rest"]],
        node "MlEvaluate" [.fvar "head", .fvar "environment", node "MlKConsHead" [.fvar "tail", .fvar "rest"]], []) :=
    by decide +kernel
  rw [authored] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  refine ⟨premiseFree,
    [("tail", tail), ("head", head), ("environment", captured), ("rest", rest)], ?_, ?_⟩
  · rw [left]
    simp [apply_node, applyBindings]
  · rw [right]
    simp [apply_node, applyBindings]

theorem return_cons_head_instance (head tail rest : Pattern) :
    BaseRuleInstance 13 (node "MlReturn" [head, node "MlKConsHead" [tail, rest]])
      (node "MlReturn" [node "MlCons" [head, tail], rest]) := by
  constructor
  intro row authored
  have computed : (baseLanguage.rewrites[13]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlReturn" [.fvar "head", node "MlKConsHead" [.fvar "tail", .fvar "rest"]],
        node "MlReturn" [node "MlCons" [.fvar "head", .fvar "tail"], .fvar "rest"], []) := by decide +kernel
  rw [authored] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  refine ⟨premiseFree, [("head", head), ("tail", tail), ("rest", rest)], ?_, ?_⟩
  · rw [left]
    simp [apply_node, applyBindings]
  · rw [right]
    simp [apply_node, applyBindings]

#print axioms base_instance_firing
#print axioms return_function_instance
#print axioms return_let_instance
#print axioms return_cons_tail_instance
#print axioms return_cons_head_instance

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
