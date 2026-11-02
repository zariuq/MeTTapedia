import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledReturn
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowDependencies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnGather

/-! The remaining source code list selects the last versus continuing gather
row. The classifier reads actual matching evidence, preserving argument order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding Match GeneralFirstOrderProjection

private theorem selected_field {α : Type} (field : RewriteRule → α) {index : Nat} {row : RewriteRule}
    {expected : α} (selected : baseLanguage.rewrites[index]? = some row)
    (computed : (baseLanguage.rewrites[index]?).map field = some expected) : field row = expected := by
  rw [selected] at computed
  exact Option.some.inj computed

theorem enabled_gather_row (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} (actual kind captured suffix rest : Pattern)
    (remaining : List OCaml.Code) {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {matched completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlReturn" [actual, node "MlKBuild" [kind, codes (remaining.map code), captured, suffix, rest]])
      ordinal trace matched completed history target) :
    baseLanguage.rewrites[if remaining.isEmpty then 15 else 14]? = some row.authored := by
  obtain ⟨index, authored, member⟩ := enabled_return_continuation program prepared table "MlKBuild" _ _ built position firing
  have candidates : returnCandidates "MlKBuild" = [14,15] := by decide +kernel
  rw [candidates] at member
  have alternatives : index = 14 ∨ index = 15 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have zero := prepared_selected_row_zero program prepared table built position
  cases remaining with
  | nil =>
    rcases alternatives with rfl | rfl
    · have premiseFree : row.authored.premises = [] := selected_field RewriteRule.premises authored (by decide +kernel)
      obtain ⟨_, _, input, _⟩ := pure_base_root_readout position authored zero premiseFree firing
      have left : row.authored.left = node "MlReturn" [.fvar "value", node "MlKBuild" [.fvar "kind",
          node "MlCodeCons" [.fvar "next", .fvar "later"], .fvar "environment", .fvar "suffix", .fvar "rest"]] :=
        selected_field RewriteRule.left authored (by decide +kernel)
      rw [left] at input
      simp only [apply_node, List.map_cons, List.map_nil] at input
      simp [node, codes, linked] at input
    · exact authored
  | cons next later =>
    rcases alternatives with rfl | rfl
    · exact authored
    · have premiseFree : row.authored.premises = [] := selected_field RewriteRule.premises authored (by decide +kernel)
      obtain ⟨_, _, input, _⟩ := pure_base_root_readout position authored zero premiseFree firing
      have left : row.authored.left = node "MlReturn" [.fvar "value", node "MlKBuild" [.fvar "kind",
          node "MlCodeNil", .fvar "environment", .fvar "suffix", .fvar "rest"]] :=
        selected_field RewriteRule.left authored (by decide +kernel)
      rw [left] at input
      simp only [apply_node, List.map_cons, List.map_nil] at input
      simp [node, codes, linked] at input

#print axioms enabled_gather_row

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
