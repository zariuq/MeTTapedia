import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticThinning
import Mettapedia.GSLT.LanguageDef.Cost.FiniteDeclarationInventoryControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SynchronousStaticSourceTerm

/-!
# Actual finite-profile binder insertion controls

These are declaration-aware typing and scope-index controls. They do not
identify arbitrary source programs with the nonprincipal static fragment, or
infer a reflective dependency action from ordinary typing alone.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteStaticThinningControls
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open CostStaticTypeThinning

/-- The lambda static fragment inserts an open variable at its actual second
occurrence. Lambda's principal constructors still require retained frames. -/
theorem lambda_second_variable (color : CostStaticColor) :
    HasType (ContinuationDecorationProfile.ofRetypingPlan
      LambdaContinuedInteraction.lambdaContinuationRetyping).costWholeLanguage
      (FreeTypeContext.map (color.symbolsOf LambdaContinuedInteraction.lambdaIGSLT) (fun _ => none))
      [.base costSignatureSortName,
        mapTypeExpr (color.symbolsOf LambdaContinuedInteraction.lambdaIGSLT) (.base "Term"),
        .base costKeySortName,
        mapTypeExpr (color.symbolsOf LambdaContinuedInteraction.lambdaIGSLT) (.base "Term")]
      (.bvar 3) (mapTypeExpr (color.symbolsOf LambdaContinuedInteraction.lambdaIGSLT) (.base "Term")) := by
  have sourceTyped : HasTypeWithConstructors
      LambdaContinuedInteraction.lambdaIGSLT.presentation.presentation.language
      (· ∈ (ContinuationDecorationProfile.ofRetypingPlan
        LambdaContinuedInteraction.lambdaContinuationRetyping).wrappedLabels)
      (fun _ => none) [.base "Term", .base "Term"] (.bvar 1) (.base "Term") := .bvar rfl
  have inserted := (ContinuationDecorationProfile.ofRetypingPlan
    LambdaContinuedInteraction.lambdaContinuationRetyping).mapStatic_hasType_thinning
      FiniteStaticTypingControls.lambda_nonprincipal color sourceTyped
      (Controls.repeated LambdaContinuedInteraction.lambdaIGSLT color (.base "Term"))
  simpa [mapPattern, ContextSubstitution.renameAmbientBVarsAt,
    Controls.repeated, toTargetIndex] using inserted

/-- Synchronous static code uses a local name and two equal ambient name
types. All three occurrences remain present after foreign binder insertion. -/
def rhoNested : Pattern := .lambda none (.collection .hashBag
  [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 1], .apply "PDrop" [.bvar 2]] none)

theorem rhoNested_supported : HasTypeWithConstructors Synchronous.rhoSyncCalc
    (· ∈ Synchronous.communicationDecoration.wrappedLabels) (fun _ => none)
    [.base "Name", .base "Name"] rhoNested (.arrow (.base "Name") (.base "Proc")) := by
  apply HasType.withConstructors (checkHasType_sound (by decide +kernel))
  · simp only [rhoNested, ConstructorsWithin, ConstructorListWithin, and_true]
    decide +kernel
  · exact CanonicalInventory.synchronous_bareConstructorsAllowed

theorem rhoNested_reindexed_typed (color : CostStaticColor) :
    HasType Synchronous.communicationDecoration.costWholeLanguage
      (FreeTypeContext.map (color.symbolsOf Synchronous.rhoSyncIGSLT) (fun _ => none))
      [.base costSignatureSortName,
        mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Name"),
        .base costKeySortName,
        mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Name")]
      (ContextSubstitution.renameAmbientBVarsAt
        (Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name")).toTargetIndex 0
        (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT) rhoNested))
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT)
        (.arrow (.base "Name") (.base "Proc"))) :=
  Synchronous.communicationDecoration.mapStatic_hasType_thinning
    FiniteStaticTypingControls.synchronous_nonprincipal color rhoNested_supported
    (Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name"))

theorem rhoNested_reindexed (color : CostStaticColor) :
    ContextSubstitution.renameAmbientBVarsAt
      (Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name")).toTargetIndex 0
      (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT) rhoNested) =
      .lambda none (.collection .hashBag
        [.apply ((color.symbolsOf Synchronous.rhoSyncIGSLT).constructor "PDrop") [.bvar 0],
         .apply ((color.symbolsOf Synchronous.rhoSyncIGSLT).constructor "PDrop") [.bvar 2],
         .apply ((color.symbolsOf Synchronous.rhoSyncIGSLT).constructor "PDrop") [.bvar 4]] none) := by
  simp [rhoNested, mapPattern, ContextSubstitution.renameAmbientBVarsAt,
    Controls.repeated, toTargetIndex]

/-- The actual synchronous computed source representative inserts into a
mixed context whenever its exact type-image thinning is supplied. The
normalizer and fragment preservation are the constructed synchronous ones. -/
theorem synchronous_normalized_reinsert_hasType
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort Synchronous.rhoSyncCalc}
    (term : Synchronous.communicationDecoration.StaticSourceTerm
      Synchronous.FiniteWhole.sourceReflection color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning Synchronous.rhoSyncIGSLT color sourceBound targetBound) :
    HasType Synchronous.communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf Synchronous.rhoSyncIGSLT)) targetBound
      (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex 0
        (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT)
          (Synchronous.StaticSource.normalize term).term.1))
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base sort.1)) :=
  (Synchronous.StaticSource.normalize term).reinsert_hasType
    FiniteStaticTypingControls.synchronous_nonprincipal thinning

end Mettapedia.GSLT.LanguageDef.FiniteStaticThinningControls
