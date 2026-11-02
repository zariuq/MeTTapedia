import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInput

/-! Constructor shapes of the actual instruction, function and pattern
compilers, plus kernel candidate positions computed from the authored rows.
These are inverse compiler facts; the declarations are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem function_row_apply_constructor (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (compiled : functionRules? program pool reference instruction = some rows) (member : row ∈ rows) :
    ∃ arguments, row.left = node "MlApply" arguments := by
  cases instruction with
  | lambda parameter body =>
    cases resolved : patternReference? pool parameter with
    | none => simp [functionRules?, resolved] at compiled
    | some patternCode =>
      rw [function_lambda_rows program reference body resolved] at compiled
      cases Option.some.inj compiled
      have same := List.mem_singleton.mp member
      subst row
      exact ⟨_, rfl⟩
  | letRecursive definitions body =>
    obtain ⟨slot, target, parameter, functionBody, patternCode, _, _, _, same⟩ :=
      recursive_rule_origin program pool reference body definitions rows row compiled member
    rw [same]
    exact ⟨_, rfl⟩
  | _ =>
    simp only [functionRules?] at compiled
    cases Option.some.inj compiled
    cases member

theorem pattern_row_choice (index : Nat) (parameter : OCaml.MatchPattern) (row : RewriteRule)
    (member : row ∈ patternRules index parameter) :
    row = (patternRules index parameter)[0]'(by simp [patternRules]) ∨
      row = (patternRules index parameter)[1]'(by simp [patternRules]) := by
  simpa only [patternRules, List.mem_cons, List.not_mem_nil, or_false, List.getElem_cons_zero, List.getElem_cons_succ] using member

def kernelCandidates (label : String) : List Nat :=
  baseLanguage.rewrites.zipIdx.filterMap fun (row, index) =>
    if GeneralPremise.potentialChild (node label []) row then some index else none

theorem kernel_candidate_origin (label : String) (inputs : List Pattern) (row : RewriteRule)
    (member : row ∈ baseLanguage.rewrites) (compatible : GeneralPremise.potentialChild (node label inputs) row = true) :
    ∃ index, baseLanguage.rewrites[index]? = some row ∧ index ∈ kernelCandidates label := by
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  refine ⟨index, selected, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨(row, index), List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
  have allowed : GeneralPremise.potentialChild (node label []) row = true := by
    simpa only [GeneralPremise.potentialChild, node] using compatible
  simp only [allowed, if_true]

theorem kernel_candidate_positions :
    ["MlEvaluate", "MlReturn", "MlApply", "MlMatchOne", "MlTryClause", "MlSelect", "MlBuildConfig",
      "MlPrimitiveRequest", "MlPrimitiveReturned"].map kernelCandidates =
    [[], [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,22], [], [25], [26], [23,24], [16,17,18], [19], [20,21]] := by
  decide +kernel

#print axioms function_row_apply_constructor
#print axioms pattern_row_choice
#print axioms kernel_candidate_origin
#print axioms kernel_candidate_positions

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
