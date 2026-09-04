import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

/-!
# Clean-seed plan descent for the rho Cost₁ collapsing slices

Second-generation audit of `scratch/ProbeDescend.lean` (which contains four
`sorry`s and is untrusted).  Same statement, proven branch-by-branch:

* fuel-zero: vacuous by pattern positivity;
* `application`: the productive branch.  Only quote-headed plans collapse; at
  every other head the canonical form is decodable at the plan's own colour
  and the escape premise is refuted;
* `collection`: empty and multi-element/rest bags are vacuous for rho
  (their canonical forms are unit- or parallel-headed at the plan's own
  colour); the singleton bag descends;
* `boundaryCollection`: the plan is the stopped state itself.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem decodeDeclared_drop_of (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      some "PDrop" := by
  cases color <;> decide

theorem decodeDeclared_quote_of (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor =
      some "NQuote" := by
  cases color <;> decide

/-- Near-mechanical lemma: every rho plan constructor application head whose
role is the current colour decodes to its authored label at the plan's own
colour.  This is the engine of every escape-refutation. -/
theorem rhoDescend {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (dropMode : Bool) (target : Pattern),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        (if dropMode then
            .apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor
              [target]
          else target) →
      ((∃ wire arguments, target = .apply wire arguments ∧
            decodeDeclaredCostStaticConstructor rhoCIGSLT color wire = none) ∨
        (∃ collectionType elements rest,
            target = .collection collectionType elements rest ∧
            collectionType ≠
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl).parallelCollection)) →
      ∃ payload, Nonempty
        { state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
            plan.abstractPattern //
          canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
              (state.skeletonContext.fill
                (.fvar (costRegionBoundaryVariableName
                  state.certified.typed.boundary))) =
            (if dropMode then
                .apply
                  rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
                  [.fvar (costRegionBoundaryVariableName
                    state.certified.typed.boundary)]
              else
                .fvar (costRegionBoundaryVariableName
                  state.certified.typed.boundary))
          ∧ Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
              [state.certified.typed] plan.boundaryTable.entries)
          ∧ canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              state.certified.typed.boundary.content = target } := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan dropMode target measure canonical escape
      cases pattern <;> simp_wf at measure
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan dropMode target measure canonical escape
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp only [canonicalize] at canonical
          cases dropMode with
          | true => simp at canonical
          | false =>
              simp only [Bool.false_eq_true, if_false] at canonical
              subst canonical
              rcases escape with ⟨w, a, shape, _⟩ | ⟨t, e, r, shape, _⟩ <;>
                simp at shape
      | fvar lookup =>
          simp only [canonicalize] at canonical
          cases dropMode with
          | true => simp at canonical
          | false =>
              simp only [Bool.false_eq_true, if_false] at canonical
              subst canonical
              rcases escape with ⟨w, a, shape, _⟩ | ⟨t, e, r, shape, _⟩ <;>
                simp at shape

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
