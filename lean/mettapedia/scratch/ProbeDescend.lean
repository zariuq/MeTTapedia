import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem decodeDeclared_drop (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      some "PDrop" := by
  cases color <;> decide

theorem decodeDeclared_quote (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor =
      some "NQuote" := by
  cases color <;> decide

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
      sorry
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
      | boundaryApplication declared rendered outsideCurrent certified certifies =>
          rename_i wireName arguments
          have headNe : wireName ≠
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor := by
            intro headEq
            exact not_collapsingRoot_of_boundaryHead declared rendered
              outsideCurrent (Or.inl ⟨arguments, by rw [headEq]⟩)
          have canonAp := canonicalize_apply_of_ne_quote
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl) headNe arguments
          cases dropMode with
          | true =>
              simp only [if_true] at canonical
              rw [canonAp] at canonical
              have wireEq := (Pattern.apply.inj canonical).1
              have decodedNone := decodeDeclaredCostStaticConstructor_render_of_role_ne
                rhoCIGSLT declared color outsideCurrent
              rw [rendered, wireEq] at decodedNone
              rw [decodeDeclared_drop] at decodedNone
              exact absurd decodedNone (by simp)
          | false =>
              simp only [Bool.false_eq_true, if_false] at canonical
              refine ⟨.apply wireName arguments, ⟨⟨
                { boundarySupport := _, boundaryType := _, content := _
                  certified := certified
                  certifies := certifies
                  residual := .hole
                  content_eq := rfl
                  skeletonContext := .hole
                  abstract_eq := rfl }, ?_, ⟨CostStaticPlanEntryEmbedding.refl _⟩,
                ?_⟩⟩⟩
              · simp [OneHoleContext.fill, canonicalize]
              · show canonicalize _ certified.typed.boundary.content = target
                rw [certified.content_eq]
                exact canonical
      | application declared rendered current preimage notBare children => sorry
      | lambda bodyPlan =>
          simp only [canonicalize] at canonical
          cases dropMode with
          | true => simp at canonical
          | false =>
              simp only [Bool.false_eq_true, if_false] at canonical
              subst canonical
              rcases escape with ⟨w, a, shape, _⟩ | ⟨t, e, r, shape, _⟩ <;>
                simp at shape
      | multiLambda bodyPlan =>
          simp only [canonicalize] at canonical
          cases dropMode with
          | true => simp at canonical
          | false =>
              simp only [Bool.false_eq_true, if_false] at canonical
              subst canonical
              rcases escape with ⟨w, a, shape, _⟩ | ⟨t, e, r, shape, _⟩ <;>
                simp at shape
      | collection choice selected children => sorry
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies => sorry
