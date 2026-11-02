import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnReadout

/-! A terminal return receipt is exactly the source machine's successful
halt transition. The result value cannot change during target publication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_done_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {bound : List TypeExpr}
    {result target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[0]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound (.base "MlConfig")
      (node "MlReturn" [result, node "MlKDone"]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlDone" [result] := by
  have fields : (row.authored.left, row.authored.right, row.authored.premises) =
      (node "MlReturn" [.fvar "value", node "MlKDone"], node "MlDone" [.fvar "value"], []) := by
    have computed : (baseLanguage.rewrites[0]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlReturn" [.fvar "value", node "MlKDone"], node "MlDone" [.fvar "value"], []) := by decide +kernel
    rw [authored] at computed
    exact Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  have instantiated : applyBindings [("value", result)] row.authored.left = node "MlReturn" [result, node "MlKDone"] := by
    rw [left]
    simp [apply_node, applyBindings]
  obtain ⟨sameCaptures, emptyHistory, output⟩ := pure_base_root_target position authored zero premiseFree instantiated firing
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  rw [right] at output
  simpa [apply_node, applyBindings] using output

theorem return_done_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {result : OCaml.Value} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[0]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value result, node "MlKDone"]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      OCaml.machineStep program (.returned result []) = .ok (some (.halted (.ok result))) ∧
      state? pool (.halted (.ok result)) = some target := by
  obtain ⟨sameCaptures, emptyHistory, targetSame⟩ := return_done_firing position authored zero firing
  refine ⟨sameCaptures, emptyHistory, rfl, ?_⟩
  rw [targetSame]
  rfl

#print axioms return_done_firing
#print axioms return_done_source_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
