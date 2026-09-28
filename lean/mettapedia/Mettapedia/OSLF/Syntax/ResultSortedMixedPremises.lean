import Mettapedia.OSLF.Syntax.ResultSortedScopedPremises

/-!
# Result sorts for mixed root and scoped premise lists

A root relation query contributes a selected base event but no recursive
child. The following scoped step contributes one child in its own binder
context and at its declared result sort. This is independent of the selected
query row and recursive firing evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedMixedPremises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise (check)
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ResultSortedScopedPremises

/-- A root query followed by a scoped step has exactly the scoped step's
recursive child. The query's selected root-result ordinal remains in the
premise skeleton but does not become a spurious recursive position. -/
theorem RunSkeleton.relationQuery_then_scopedStep_result_child
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {relation : String} {arguments : List Pattern}
    {step : ScopedStepPremise} {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length index
      [.relationQuery relation arguments, .scopedStep step] initial final)
    (checked : check lang free ambient step = true) :
    ∃ source target,
      RunSkeleton.resultSortedChildren? ambient free run =
        some [⟨step.binders ++ ambient, step.resultType,
          source, target⟩] := by
  cases run with
  | cons query rest =>
      cases query with
      | relationQuery _ _ =>
          cases rest with
          | cons stepHead tail =>
              cases tail with
              | nil =>
                  cases stepHead with
                  | scopedStep _ _ childShape =>
                      exact ⟨childShape.childSource,
                        childShape.childTarget, by
                          simp [RunSkeleton.resultSortedChildren?,
                            PremiseSkeleton.resultSortedChild?, checked]⟩

/-- The same exact-child law applies to any whole authored rule skeleton
with this ordered premise list, irrespective of its capture or firing. -/
theorem RuleSkeleton.relationQuery_then_scopedStep_result_child
    {relEnv : RelationEnv} {lang : LanguageDef}
    {source target : Pattern}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    {relation : String} {arguments : List Pattern}
    {step : ScopedStepPremise}
    (premises : shape.rule.premises =
      [.relationQuery relation arguments, .scopedStep step])
    (checked : check lang free ambient step = true) :
    ∃ childSource childTarget,
      RuleSkeleton.resultSortedChildren? ambient free shape =
        some [⟨step.binders ++ ambient, step.resultType,
          childSource, childTarget⟩] := by
  cases shape with
  | mk rule ruleIndex listed spec declared admitted captured selected
      completed run reduct resultScoped =>
      dsimp only at premises ⊢
      cases rule with
      | mk name typeContext rulePremises left right bindings =>
          dsimp only at premises ⊢
          cases premises
          exact RunSkeleton.relationQuery_then_scopedStep_result_child
            ambient free run checked

#print axioms RunSkeleton.relationQuery_then_scopedStep_result_child
#print axioms RuleSkeleton.relationQuery_then_scopedStep_result_child

end Mettapedia.OSLF.Binding.ResultSortedMixedPremises
