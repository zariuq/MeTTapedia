import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyedTyping
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalScopeCollapse

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

theorem canonicalize_binderSafeAt_canary
    (declaration : ReflectivePresentationDecl) (observedQuote : String)
    (safetyDepth : Nat) (pattern : Pattern)
    (safe : binderSafeAt observedQuote safetyDepth pattern = true) :
    binderSafeAt observedQuote safetyDepth
        (canonicalize declaration pattern) = true := by
  have keyed := canonicalizeByDepths_binderSafeAt
    (fun _ _ pattern => PatternCode.patternCode pattern)
    declaration observedQuote 0 0 safetyDepth pattern safe
  rw [canonicalizeByDepths_ignoreScope
      (fun _ pattern => PatternCode.patternCode pattern),
    canonicalizeByAt_const PatternCode.patternCode,
    canonicalizeBy_patternCode] at keyed
  exact keyed

theorem quote_canonicalize_ne_bvar_of_binderSafeAt_canary
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (safetyDepth : Nat) (arguments : List Pattern) (index : Nat)
    (safe : binderSafeAt declaration.quoteConstructor safetyDepth
      (.apply declaration.quoteConstructor arguments) = true) :
    canonicalize declaration (.apply declaration.quoteConstructor arguments) ≠
      .bvar index := by
  intro canonical
  rw [canonicalize_apply_eq_finish] at canonical
  rcases finishNormalizeReflectiveApply_quote_cases declaration
      (arguments.map (canonicalize declaration)) with
    ⟨inner, mappedEq, resultEq⟩ | resultEq
  · rw [resultEq] at canonical
    cases arguments with
    | nil => simp at mappedEq
    | cons argument arguments =>
        cases arguments with
        | nil =>
            have argumentCanonical : canonicalize declaration argument =
                .apply declaration.dropConstructor [inner] := by
              simpa using mappedEq
            have argumentSafe : binderSafeAt declaration.quoteConstructor 0
                argument = true := by
              simpa [binderSafeAt] using safe
            have normalizedSafe := canonicalize_binderSafeAt_canary declaration
              declaration.quoteConstructor 0 argument argumentSafe
            have dropNeQuote : declaration.dropConstructor ≠
                declaration.quoteConstructor := Ne.symm quoteNeDrop
            have dropDecision :
                (declaration.dropConstructor ==
                  declaration.quoteConstructor) = false :=
              beq_eq_false_iff_ne.mpr dropNeQuote
            rw [argumentCanonical, canonical] at normalizedSafe
            simp [binderSafeAt, binderSafeListAt, dropDecision] at normalizedSafe
        | cons second rest => simp at mappedEq
  · rw [resultEq] at canonical
    cases canonical

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostHereditaryLeafDichotomyProbe

theorem rho_boundaryPlan_canonicalize_ne_bvar_canary
    {color declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) (index : Nat) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        pattern ≠ .bvar index := by
  cases plan with
  | bvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | fvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | application =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | lambda => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | multiLambda =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      rename_i wireName arguments
      intro canonical
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
      have collapsing : CollapsingRoot declaration
          (.apply wireName arguments) := by
        rcases eq_bvar_or_collapsingRoot_of_canonicalize_eq_bvar declaration
            canonical with shape | collapsing
        · exact absurd shape (by simp)
        · exact collapsing
      have quoteHead : wireName = declaration.quoteConstructor :=
        eq_quoteConstructor_of_collapsingRoot_apply declaration collapsing
      have scopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
          rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
          (.apply wireName arguments) := by
        simpa only [certified.content_eq, certified.targetSupport_eq] using
          certified.typed.contentReflectiveScopeSafe
      have safe := scopeSafe declaration
        (by
          simpa only [declaration] using
            CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile
              declarationColor)
      rw [quoteHead] at safe canonical
      exact (canonicalize_quote_ne_bvar_of_binderSafeAt declaration
        (Ne.symm
          (CostHereditaryForeignBoundaryWitness.rhoDecl_drop_ne_quote
            declarationColor)) sourceAvailable.length arguments index safe)
        canonical
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact fun _ => absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
