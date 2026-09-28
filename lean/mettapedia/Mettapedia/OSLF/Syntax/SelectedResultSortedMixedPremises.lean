import Mettapedia.OSLF.Syntax.ResultSortedMixedPremises
import Mettapedia.OSLF.Syntax.ScopedOperationalCertification

/-!
# Selected child of a mixed root-query and scoped-step run

The structural result-sort annotation and the actual selected recursive
oracle occurrence must describe the same child. A root query retains its
selected base event but contributes no recursive position. The following
scoped step contributes one child, whose local context, result sort,
endpoints, evidence and oracle ordinal stay together.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SelectedResultSortedMixedPremises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise (check)
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedStepShapes
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ResultSortedScopedPremises

/-- A certified mixed run has exactly one selected recursive oracle
occurrence. Its endpoint judgment is the sole canonically sorted child,
and the child keeps the premise-local binder context and result sort. -/
theorem RunSkeleton.relationQuery_then_scopedStep_selected_child
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {relation : String} {arguments : List Pattern}
    {step : ScopedStepPremise} {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (oracle : StepOracle RuleHistory)
    (run : RunSkeleton RuleHistory relEnv lang rule spec ambient.length index
      [.relationQuery relation arguments, .scopedStep step] initial final)
    (histories : List RuleHistory)
    (selected : RunSkeleton.Selected oracle run histories)
    (checked : check lang free ambient step = true) :
    ∃ childSource childTarget evidence ordinal,
      histories = [evidence] ∧
      run.children =
        [(step.binders.length + ambient.length, childSource, childTarget)] ∧
      RunSkeleton.resultSortedChildren? ambient free run =
        some [⟨step.binders ++ ambient, step.resultType,
          childSource, childTarget⟩] ∧
      ((evidence, childTarget), ordinal) ∈
        (oracle (step.binders.length + ambient.length) childSource).zipIdx := by
  cases run with
  | cons query rest =>
      cases query with
      | relationQuery _ _ =>
          cases rest with
          | cons stepHead tail =>
              cases tail with
              | nil =>
                  cases stepHead with
                  | scopedStep _ ordinal shape =>
                      cases histories with
                      | nil =>
                          simp [RunSkeleton.Selected,
                            PremiseSkeleton.child?] at selected
                      | cons evidence remaining =>
                          have chosen :
                              ((evidence, shape.childTarget), ordinal) ∈
                                (oracle (step.binders.length + ambient.length)
                                  shape.childSource).zipIdx := by
                            simpa [RunSkeleton.Selected,
                              PremiseSkeleton.Selected,
                              PremiseSkeleton.child?,
                              StepShape.childJudgment] using selected.2.1
                          have noRemaining : remaining = [] := by
                            exact selected.2.2
                          subst remaining
                          refine ⟨shape.childSource, shape.childTarget,
                            evidence, ordinal, rfl, ?_, ?_, chosen⟩
                          · simp [RunSkeleton.children,
                              PremiseSkeleton.child?,
                              StepShape.childJudgment]
                          · simp [RunSkeleton.resultSortedChildren?,
                              PremiseSkeleton.resultSortedChild?, checked]

/-- The actual executable constructor frame projects to the same selected,
result-sorted child. Its raw rule shape retains the authored rule index and
the exact oracle-selected recursive occurrence. -/
theorem RuleConstructorFrame.relationQuery_then_scopedStep_selected_child
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {source : Pattern} {firing : RuleFiring RuleHistory}
    {index fuel : Nat} {relation : String} {arguments : List Pattern}
    {step : ScopedStepPremise}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (listed : (rule, index) ∈ lang.rewrites.zipIdx)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient.length rule source firing)
    (premises : rule.premises =
      [.relationQuery relation arguments, .scopedStep step])
    (checked : check lang free ambient step = true) :
    ∃ childSource childTarget evidence ordinal,
      (RuleConstructorFrame.toSkeleton index listed frame).children =
        [(step.binders.length + ambient.length,
          childSource, childTarget)] ∧
      ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?
        ambient free (RuleConstructorFrame.toSkeleton index listed frame) =
          some [⟨step.binders ++ ambient, step.resultType,
            childSource, childTarget⟩] ∧
      ((evidence, childTarget), ordinal) ∈
        (rewriteAt relEnv lang fuel
          (step.binders.length + ambient.length) childSource).zipIdx := by
  cases rule with
  | mk name typeContext rulePremises left right bindings =>
      dsimp only at premises ⊢
      cases premises
      let run := RunFrame.toSkeleton frame.premises
      have selected := selected_projected_run
        (rewriteAt relEnv lang fuel) frame.premises
      obtain ⟨childSource, childTarget, evidence, ordinal,
          _, childrenEq, sortedEq, oracleSelected⟩ :=
        RunSkeleton.relationQuery_then_scopedStep_selected_child
          ambient free (rewriteAt relEnv lang fuel) run
          ((RunFrame.childRequests frame.premises).map
            ChildRequest.evidence) selected checked
      refine ⟨childSource, childTarget, evidence, ordinal, ?_, ?_,
        oracleSelected⟩
      · simpa [run, RuleSkeleton.children,
          RuleConstructorFrame.toSkeleton] using childrenEq
      · simpa [run, ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?,
          RuleConstructorFrame.toSkeleton] using sortedEq

#print axioms RunSkeleton.relationQuery_then_scopedStep_selected_child
#print axioms RuleConstructorFrame.relationQuery_then_scopedStep_selected_child

end Mettapedia.OSLF.Binding.SelectedResultSortedMixedPremises
