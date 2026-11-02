import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledReturn
import Mettapedia.OSLF.MeTTaIL.GeneralRootFirstReadout

/-! Boolean return rows are selected by the continuation and the actual
Boolean value together. Opposite truth-value branches cannot fire.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleMatchingHeads

def booleanReturnIndex (label : String) (choice : Bool) : Nat :=
  if label = "MlKBranch" then if choice then 4 else 5
  else if label = "MlKAnd" then if choice then 7 else 6
  else if label = "MlKOr" then if choice then 8 else 9
  else if choice then 10 else 11

theorem enabled_boolean_return (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} (label : String) (choice : Bool) (inputs : List Pattern)
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (known : label = "MlKBranch" ∨ label = "MlKAnd" ∨ label = "MlKOr" ∨ label = "MlKBoolean")
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node label inputs]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[booleanReturnIndex label choice]? = some row.authored := by
  obtain ⟨index, authored, member⟩ := enabled_return_continuation program prepared table label _ inputs built position firing
  have allShaped : (returnCandidates label).all (fun i =>
      ((baseLanguage.rewrites[i]?).bind fun rule => firstConstructor? rule.left).isSome) = true := by
    rcases known with rfl | rfl | rfl | rfl <;> decide +kernel
  have shaped := List.all_eq_true.mp allShaped index member
  rw [authored] at shaped
  have observed : firstConstructor? row.authored.left = some ("MlReturn", if choice then "MlTrue" else "MlFalse") := by
    cases choice <;>
      (have read := rootFiring_first_constructor_readout (GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position) shaped firing
       exact read)
  have actual : (baseLanguage.rewrites[index]?.bind fun rule => firstConstructor? rule.left) =
      some ("MlReturn", if choice then "MlTrue" else "MlFalse") := by rw [authored]; exact observed
  have identified : index = booleanReturnIndex label choice := by
    rcases known with rfl | rfl | rfl | rfl
    · have candidates : returnCandidates "MlKBranch" = [4, 5] := by decide +kernel
      rw [candidates] at member
      have alternatives : index = 4 ∨ index = 5 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      rcases alternatives with rfl | rfl
      · have head : (baseLanguage.rewrites[4]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlTrue") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
      · have head : (baseLanguage.rewrites[5]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlFalse") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
    · have candidates : returnCandidates "MlKAnd" = [6, 7] := by decide +kernel
      rw [candidates] at member
      have alternatives : index = 6 ∨ index = 7 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      rcases alternatives with rfl | rfl
      · have head : (baseLanguage.rewrites[6]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlFalse") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
      · have head : (baseLanguage.rewrites[7]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlTrue") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
    · have candidates : returnCandidates "MlKOr" = [8, 9] := by decide +kernel
      rw [candidates] at member
      have alternatives : index = 8 ∨ index = 9 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      rcases alternatives with rfl | rfl
      · have head : (baseLanguage.rewrites[8]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlTrue") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
      · have head : (baseLanguage.rewrites[9]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlFalse") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
    · have candidates : returnCandidates "MlKBoolean" = [10, 11] := by decide +kernel
      rw [candidates] at member
      have alternatives : index = 10 ∨ index = 11 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      rcases alternatives with rfl | rfl
      · have head : (baseLanguage.rewrites[10]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlTrue") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
      · have head : (baseLanguage.rewrites[11]?.bind fun rule => firstConstructor? rule.left) = some ("MlReturn", "MlFalse") := by decide +kernel
        rw [head] at actual
        cases choice <;> simp_all [booleanReturnIndex]
  subst index
  exact authored

#print axioms enabled_boolean_return

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
