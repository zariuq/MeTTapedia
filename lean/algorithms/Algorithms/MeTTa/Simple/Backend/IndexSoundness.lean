import Algorithms.MeTTa.Simple.Backend.CompiledBundleContracts
import Algorithms.MeTTa.Simple.Backend.SpaceIndexContracts
import Algorithms.MeTTa.Simple.Backend.RuleIndexContracts

namespace Algorithms.MeTTa.Simple.Backend.IndexSoundness

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend

theorem rewriteCountForHeadArity_sound
    (view : CompiledBundle.View) (ctor : String) (arity : Nat) :
    CompiledBundle.rewriteCountForHeadArity view ctor arity =
      RuleIndex.rewriteCountForHeadArity view.ruleIndex ctor arity := by
  simpa using
    CompiledBundleContracts.rewriteCountForHeadArity_eq_ruleIndex view ctor arity

theorem rewriteAritiesForHead_sound
    (view : CompiledBundle.View) (ctor : String) :
    CompiledBundle.rewriteAritiesForHead view ctor =
      RuleIndex.aritiesForHead view.ruleIndex ctor := by
  simpa using
    CompiledBundleContracts.rewriteAritiesForHead_eq_ruleIndex view ctor

theorem hasRuleHead_sound
    (view : CompiledBundle.View) (ctor : String) :
    CompiledBundle.hasRuleHead view ctor =
      RuleIndex.hasHead view.ruleIndex ctor := by
  simpa using
    CompiledBundleContracts.hasRuleHead_eq_ruleIndex view ctor

theorem hasCompatHeadConstraintRule_sound
    (view : CompiledBundle.View) (ctor : String) (arity : Nat) :
    CompiledBundle.hasCompatHeadConstraintRule view ctor arity =
      RuleIndex.hasCompatHeadConstraintRule view.ruleIndex ctor arity := by
  simpa using
    CompiledBundleContracts.hasCompatHeadConstraintRule_eq_ruleIndex view ctor arity

theorem no_false_negative_self_fvar
    (view : CompiledBundle.View) (x : String) (fact : Pattern)
    (hMem : fact ∈ view.spaceIndex.selfFacts) :
    fact ∈ CompiledBundle.candidateSelfFacts view (.fvar x) := by
  have hSpace : fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex (.fvar x) := by
    exact SpaceIndexContracts.no_false_negative_fvar view.spaceIndex x fact hMem
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_self_comma
    (view : CompiledBundle.View) (lhs rhs fact : Pattern)
    (hMem : fact ∈ view.spaceIndex.selfFacts) :
    fact ∈ CompiledBundle.candidateSelfFacts view (.apply "," [lhs, rhs]) := by
  have hSpace :
      fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex (.apply "," [lhs, rhs]) := by
    exact SpaceIndexContracts.no_false_negative_comma view.spaceIndex lhs rhs fact hMem
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_self_dollar_head
    (view : CompiledBundle.View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = true)
    (hNotComma : ctor ≠ ",")
    (hMem : fact ∈ view.spaceIndex.selfFacts) :
    fact ∈ CompiledBundle.candidateSelfFacts view (.apply ctor args) := by
  have hSpace :
      fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex (.apply ctor args) := by
    exact
      SpaceIndexContracts.no_false_negative_dollar_head
        view.spaceIndex ctor args fact hStarts hNotComma hMem
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_self_nonApply
    (view : CompiledBundle.View) (pat fact : Pattern)
    (hNonApply : ∀ ctor args, pat ≠ .apply ctor args)
    (hMem : fact ∈ view.spaceIndex.selfFacts) :
    fact ∈ CompiledBundle.candidateSelfFacts view pat := by
  have hSpace :
      fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex pat := by
    exact
      SpaceIndexContracts.no_false_negative_nonApply
        view.spaceIndex pat fact hNonApply hMem
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_type_nonApply
    (view : CompiledBundle.View) (x lhs ty : Pattern)
    (hNonApply : ∀ ctor args, x ≠ .apply ctor args)
    (hMem : (lhs, ty) ∈ view.spaceIndex.typeFacts) :
    (lhs, ty) ∈ CompiledBundle.candidateSelfTypeEntries view x := by
  have hSpace :
      (lhs, ty) ∈ SpaceIndex.candidateSelfTypeEntries view.spaceIndex x := by
    exact
      SpaceIndexContracts.no_false_negative_type_nonApply
        view.spaceIndex x lhs ty hNonApply hMem
  simpa [CompiledBundleContracts.candidateSelfTypeEntries_eq_spaceIndex] using hSpace

theorem no_false_negative_self_apply_head_bucket
    (view : CompiledBundle.View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = false)
    (hNotComma : ctor ≠ ",")
    (hHead : fact ∈ SpaceIndex.headFactsFor view.spaceIndex ctor args.length) :
    fact ∈ CompiledBundle.candidateSelfFacts view (.apply ctor args) := by
  have hSpace :
      fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex (.apply ctor args) := by
    exact
      SpaceIndexContracts.no_false_negative_apply_head_bucket
        view.spaceIndex ctor args fact hStarts hNotComma hHead
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_self_apply_fallback
    (view : CompiledBundle.View) (ctor : String) (args : List Pattern) (fact : Pattern)
    (hStarts : ctor.startsWith "$" = false)
    (hNotComma : ctor ≠ ",")
    (hHeadEmpty : SpaceIndex.headFactsFor view.spaceIndex ctor args.length = [])
    (hMem : fact ∈ view.spaceIndex.selfFacts) :
    fact ∈ CompiledBundle.candidateSelfFacts view (.apply ctor args) := by
  have hSpace :
      fact ∈ SpaceIndex.candidateSelfFacts view.spaceIndex (.apply ctor args) := by
    exact
      SpaceIndexContracts.no_false_negative_apply_fallback
        view.spaceIndex ctor args fact hStarts hNotComma hHeadEmpty hMem
  simpa [CompiledBundleContracts.candidateSelfFacts_eq_spaceIndex] using hSpace

theorem no_false_negative_type_apply_head_bucket
    (view : CompiledBundle.View) (ctor : String) (args : List Pattern) (lhs ty : Pattern)
    (hHead : (lhs, ty) ∈ SpaceIndex.typeHeadFactsFor view.spaceIndex ctor args.length) :
    (lhs, ty) ∈ CompiledBundle.candidateSelfTypeEntries view (.apply ctor args) := by
  have hSpace :
      (lhs, ty) ∈ SpaceIndex.candidateSelfTypeEntries view.spaceIndex (.apply ctor args) := by
    exact
      SpaceIndexContracts.no_false_negative_type_apply_head_bucket
        view.spaceIndex ctor args lhs ty hHead
  simpa [CompiledBundleContracts.candidateSelfTypeEntries_eq_spaceIndex] using hSpace

theorem no_false_negative_type_apply_fallback
    (view : CompiledBundle.View) (ctor : String) (args : List Pattern) (lhs ty : Pattern)
    (hHeadEmpty : SpaceIndex.typeHeadFactsFor view.spaceIndex ctor args.length = [])
    (hMem : (lhs, ty) ∈ view.spaceIndex.typeFacts) :
    (lhs, ty) ∈ CompiledBundle.candidateSelfTypeEntries view (.apply ctor args) := by
  have hSpace :
      (lhs, ty) ∈ SpaceIndex.candidateSelfTypeEntries view.spaceIndex (.apply ctor args) := by
    exact
      SpaceIndexContracts.no_false_negative_type_apply_fallback
        view.spaceIndex ctor args lhs ty hHeadEmpty hMem
  simpa [CompiledBundleContracts.candidateSelfTypeEntries_eq_spaceIndex] using hSpace

end Algorithms.MeTTa.Simple.Backend.IndexSoundness
