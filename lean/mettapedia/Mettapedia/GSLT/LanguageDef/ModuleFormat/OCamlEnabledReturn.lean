import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledFamilies
import Mettapedia.OSLF.MeTTaIL.GeneralRootSecondConstructor

/-! The continuation constructor selects the actual authored return rows.
The finite index is computed from the module's declarations; no hand-picked
rule family is supplied as an execution assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleMatchingHeads

def returnCandidates (label : String) : List Nat :=
  baseLanguage.rewrites.zipIdx.filterMap fun (row, index) =>
    if secondConstructor? row.left = some ("MlReturn", label) then some index else none

theorem return_candidate_positions :
    ["MlKDone", "MlKArgument", "MlKFunction", "MlKLet", "MlKBranch", "MlKAnd", "MlKOr", "MlKBoolean",
      "MlKConsTail", "MlKConsHead", "MlKBuild", "MlKMatch"].map returnCandidates =
    [[0], [1], [2], [3], [4,5], [6,7], [8,9], [10,11], [12], [13], [14,15], [22]] := by decide +kernel

theorem enabled_return_continuation (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (label : String) (first : Pattern) (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlReturn" [first, node label inputs]) ordinal trace captured completed history target) :
    ∃ index, baseLanguage.rewrites[index]? = some row.authored ∧ index ∈ returnCandidates label := by
  rcases enabled_prepared_row_origin program prepared table "MlReturn" _ built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, member⟩ := kernel
    have allShaped : (kernelCandidates "MlReturn").all (fun i =>
        ((baseLanguage.rewrites[i]?).bind fun rule => secondConstructor? rule.left).isSome) = true := by decide +kernel
    have shaped := List.all_eq_true.mp allShaped index member
    rw [authored] at shaped
    have same := rootFiring_second_constructor_readout
      (GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position) shaped firing
    change secondConstructor? row.authored.left = some ("MlReturn", label) at same
    refine ⟨index, authored, List.mem_filterMap.mpr ?_⟩
    refine ⟨(row.authored, index), List.mk_mem_zipIdx_iff_getElem?.mpr authored, ?_⟩
    simp only [same, if_true]
  · simp at instruction
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms return_candidate_positions
#print axioms enabled_return_continuation

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
