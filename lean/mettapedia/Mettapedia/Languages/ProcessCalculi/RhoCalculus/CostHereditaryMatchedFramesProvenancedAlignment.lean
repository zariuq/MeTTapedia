import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesLeafClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProvenancedFVarRestoration
import Mettapedia.GSLT.LanguageDef.CostStaticPlanFVarSelection
import Mettapedia.GSLT.LanguageDef.CostCertifiedBoundaryShape
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryView
import Mettapedia.GSLT.LanguageDef.TwoDepthRestorationApex
import Mettapedia.GSLT.LanguageDef.ColourTagSeparation
import Mettapedia.GSLT.LanguageDef.CostStaticPlanProducers
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostFillDeterminism

/-!
# Provenanced construction of matched rho frame alignment

This module connects the generic plan-stop descent to the matched-frame
restoration interface.  Membership-certified free variables are discharged
by the common source-or-boundary theorem; the caller supplies only the
semantic interpretation of an exact reached-plan stop.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode
open ReflectionExtension

private theorem rhoCost_application_sourceLabel_eq_quote
    (declarationColor color : CostStaticColor)
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    {wireName : String}
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (wireEq : wireName =
      declarationColor.constructorTag ++
        rhoReflectivePresentation.quoteConstructor)
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor) :
    preimage.sourceConstructor.1.label =
      rhoReflectivePresentation.quoteConstructor := by
  have mappedEq :
      (color.symbols rhoCIGSLT).constructor
          preimage.sourceConstructor.1.label =
        (declarationColor.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor := by
    rw [← preimage.labelMap,
      rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered, wireEq]
    cases declarationColor <;> rfl
  cases declarationColor <;> cases color
  · exact CostStaticColor.base.symbols_constructor_injective rhoCIGSLT mappedEq
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq.symm)
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq)
  · exact CostStaticColor.wrapped.symbols_constructor_injective rhoCIGSLT
      mappedEq

private theorem rhoCost_application_declarationColor_eq
    (declarationColor color : CostStaticColor)
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    {wireName : String}
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (wireEq : wireName =
      declarationColor.constructorTag ++
        rhoReflectivePresentation.quoteConstructor)
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor) :
    declarationColor = color := by
  have mappedEq :
      (color.symbols rhoCIGSLT).constructor
          preimage.sourceConstructor.1.label =
        (declarationColor.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor := by
    rw [← preimage.labelMap,
      rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered, wireEq]
    cases declarationColor <;> rfl
  cases declarationColor <;> cases color
  · rfl
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq.symm)
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq)
  · rfl

private theorem rhoCost_boundaryApplication_not_quote
    (color : CostStaticColor)
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    {wireName : String}
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (wireEq : wireName =
      color.constructorTag ++ rhoReflectivePresentation.quoteConstructor)
    (outsideCurrent : rhoCIGSLT.declaredCostConstructorRole constructor ≠
      .static color) : False := by
  have sourceMembership :
      rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoCIGSLT.reflection.1.presentations := by
    change rhoReflectivePresentation.toReflectivePresentationDecl ∈
      ReflectionExtension.rhoReflectionProfile.presentations
    simp [ReflectionExtension.rhoReflectionProfile]
  have wrapped :=
    (rhoCIGSLT.reflectivePresentationsRetypable rhoReflectivePresentation
      sourceMembership).constructorLabels_mem_wrapped.1
  have staticDecoded :=
    decodeDeclaredCostStaticConstructor_symbols_of_wrappedLabel rhoCIGSLT
      color rhoReflectivePresentation.quoteConstructor wrapped
  obtain ⟨staticConstructor, staticConstructorDecoded, staticRole⟩ :=
    exists_declaredCostConstructor_of_static_decode rhoCIGSLT color
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      rhoReflectivePresentation.quoteConstructor staticDecoded
  have boundaryDecoded :
      rhoCIGSLT.decodeDeclaredCostConstructor
        ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor) = some constructor := by
    have wireEq' : wireName =
        (color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor := by
      simpa using wireEq
    rw [← wireEq', ← rendered]
    exact rhoCIGSLT.decodeDeclaredCostConstructor_render constructor
  have constructorEq : constructor = staticConstructor :=
    Option.some.inj (boundaryDecoded.symm.trans staticConstructorDecoded)
  subst staticConstructor
  exact outsideCurrent staticRole

/-- A collapsing raw rho root retained by a reached static plan is a selected
Quote, a selected bare parallel, or an explicit foreign-colour collection
boundary.  Quote cannot cross the colour boundary because its generated wire
name retains the selected constructor tag; rho's raw parallel collection tag
is intentionally shared by both colours. -/
theorem CostStaticPlanReached.rootClass_of_rhoCostCollapsingRoot
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation)
      payload) :
    state.plan.rootClass = .boundaryCollection ∨
      state.plan.rootClass =
          .application rhoReflectivePresentation.quoteConstructor ∨
        state.plan.rootClass =
          .collection rhoReflectivePresentation.parallelCollection := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;>
    rcases collapsing with ⟨arguments, shape⟩ | ⟨elements, shape⟩ <;>
    simp [costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] at shape
  all_goals simp_all [CostStaticRegionPlan.rootClass]
  all_goals rcases shape with ⟨shape, _⟩
  all_goals
    first
    | solve
      | apply rhoCost_application_sourceLabel_eq_quote
        all_goals assumption
    | solve
      | apply rhoCost_boundaryApplication_not_quote
        all_goals assumption

/-- A raw rho collapse selected by either generated declaration has four
possible reached-plan roots: a foreign application boundary, a foreign
collection boundary, a selected Quote, or a selected bare parallel.  This
cross-colour form retains the application-boundary case because a Quote wire
tagged for the other generated declaration is intentionally foreign. -/
theorem CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      payload) :
    state.plan.rootClass = .boundaryApplication ∨
      state.plan.rootClass = .boundaryCollection ∨
        state.plan.rootClass =
            .application rhoReflectivePresentation.quoteConstructor ∨
          state.plan.rootClass =
            .collection rhoReflectivePresentation.parallelCollection := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;>
    rcases collapsing with ⟨arguments, shape⟩ | ⟨elements, shape⟩ <;>
    simp [costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] at shape
  all_goals simp_all [CostStaticRegionPlan.rootClass]
  all_goals rcases shape with ⟨shape, _⟩
  all_goals
    first
    | solve
      | apply rhoCost_application_sourceLabel_eq_quote
        all_goals assumption

/-- A reached source Quote that collapses under a generated rho declaration
belongs to that declaration's colour. -/
theorem CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (sourceQuote : state.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      payload) :
    declarationColor = color := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;>
    rcases collapsing with ⟨arguments, shape⟩ | ⟨elements, shape⟩ <;>
    simp [costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] at shape
  all_goals simp_all [CostStaticRegionPlan.rootClass]
  all_goals rcases shape with ⟨shape, _⟩
  apply rhoCost_application_declarationColor_eq
  all_goals assumption

/-- The payload retained by a reached source-Quote plan is literally Quote
under the generated declaration of the selected colour. -/
theorem CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (sourceQuote : state.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor) :
    ∃ arguments,
      payload = .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).quoteConstructor arguments := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;> simp_all [CostStaticRegionPlan.rootClass]
  case application wireName arguments constructor rendered current preimage
      notBare children =>
    simp only [mapReflectivePresentation]
    rw [← sourceQuote]
    simp only [CostStaticColor.reflectiveSymbols_constructor]
    rw [← preimage.labelMap,
      rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered]

/-- Exact colour split for a reached source-Quote pair.  A delegated stop
whose witness is collapsing is same-colour; a foreign-colour alignment is
rigid descent through the generated Quote argument lists. -/
theorem CanonicalStopAligned.reached_sourceQuotes_cases
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    {stop : Pattern → Pattern → Prop}
    (stopCollapsing : ∀ {left right}, stop left right →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) stop leftPayload rightPayload) :
    (declarationColor = color ∧ stop leftPayload rightPayload) ∨
      (declarationColor = color.flip ∧
        ∃ leftArguments rightArguments,
          leftPayload = .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor leftArguments ∧
          rightPayload = .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor rightArguments ∧
          CanonicalStopAlignedList
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) stop leftArguments rightArguments) := by
  obtain ⟨leftArguments, leftShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      leftReached leftQuote
  obtain ⟨rightArguments, rightShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      rightReached rightQuote
  subst leftPayload
  subst rightPayload
  cases aligned with
  | leaf given =>
      rcases stopCollapsing given with leftCollapsing | rightCollapsing
      · exact Or.inl ⟨
          CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            leftReached leftQuote leftCollapsing,
          given⟩
      · exact Or.inl ⟨
          CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            rightReached rightQuote rightCollapsing,
          given⟩
  | apply ne children =>
      refine Or.inr ⟨CostStaticColor.eq_flip_of_ne ?_, leftArguments,
        rightArguments, rfl, rfl, children⟩
      intro colorEq
      subst declarationColor
      exact ne rfl

/-- The exact fixed-parent semantic result of one reached source-plan pair.

The parent static views determine the semantic-atom cospan.  The two abstract
patterns remain in their reached source plans: they are canonicalized there,
mapped into the selected Cost colour, reinserted under the parent thinning,
and only then compared at the requested restoration depth.  Keeping this
result separate from compact child normalization prevents a later consumer
from trying to reconstruct parent-cospan evidence from an erased pair. -/
def RhoReachedPlanPairCommonApex
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    (leftAbstract rightAbstract : Pattern) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    targetDeclaration callbackRoot
      (cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
              rhoReflectivePresentation callbackAvailable callbackScope
              (leftEnvironment.reify leftAbstract)))))
      (cospan.reifyRight rightEnvironment.lookupAtom?
        (rightView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
              rhoReflectivePresentation callbackAvailable callbackScope
              (rightEnvironment.reify rightAbstract)))))

/-- **The separated-depth variant.**  Identical to
`RhoReachedPlanPairCommonApex` except that the apex is stated over
`TwoDepthApex`, carrying the restoration depth and the canonicalization
key depth independently.  The one-index form is the diagonal of this one
wherever the two quotation disciplines agree; where they do not — at any
foreign-colour quote — only this form is satisfiable.

Both definitions are kept so consumers migrate individually, transporting
existing evidence along `CommonRestorationApex.toTwoDepth`. -/
def RhoReachedPlanPairTwoDepthApex
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope : Nat)
    (restorationDepth keyDepth : Nat)
    (leftAbstract rightAbstract : Pattern) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  CostStaticAtomKeyCospan.TwoDepthApex rhoCIGSLT cospan
    targetDeclaration restorationDepth keyDepth
      (cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
              rhoReflectivePresentation callbackAvailable callbackScope
              (leftEnvironment.reify leftAbstract)))))
      (cospan.reifyRight rightEnvironment.lookupAtom?
        (rightView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
              rhoReflectivePresentation callbackAvailable callbackScope
              (rightEnvironment.reify rightAbstract)))))

/-- **The agreement hypothesis is refuted for rho, at both colours.**

Rho's generated Cost profile carries both colour images of rho's single
authored reflective presentation, and the two spell their quote constructors
differently.  So a foreign quote always exists, and `QuoteStatusAgrees` — the
premise under which the one-index apex embeds into the separated carrier —
has no instance here.

Consequence for the theorem immediately below: it is true and it is
**vacuous over rho**.  It cannot be used to obtain separated evidence, and
nothing in the residual may depend on it.  Terminals must be established
directly over `TwoDepthApex`, at arbitrary independent depths. -/
theorem not_quoteStatusAgrees_rho (color : CostStaticColor) :
    ¬ CostStaticAtomKeyCospan.QuoteStatusAgrees rhoCIGSLT
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) :=
  not_quoteStatusAgrees_costStatic color (by
    show rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoReflectionProfile.presentations
    simp [rhoReflectionProfile])

/-- Migration: an existing one-index apex transports to the separated form
at the diagonal, wherever the two quotation disciplines agree.

**Vacuous over rho** — see `not_quoteStatusAgrees_rho`.  Retained because the
statement is the correct general one for single-colour profiles; it is not a
route to separated evidence in the two-colour setting. -/
theorem RhoReachedPlanPairCommonApex.toTwoDepth
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {callbackAvailable callbackScope depth : Nat}
    {leftAbstract rightAbstract : Pattern}
    (agrees : CostStaticAtomKeyCospan.QuoteStatusAgrees rhoCIGSLT
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation))
    (apex : RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope depth leftAbstract rightAbstract) :
    RhoReachedPlanPairTwoDepthApex leftView rightView callbackAvailable
      callbackScope depth depth leftAbstract rightAbstract :=
  CostStaticAtomKeyCospan.CommonRestorationApex.toTwoDepth agrees apex

namespace RhoReachedPlanPairCommonApex

/-- Turn an actual alignment of reached-plan abstracts into the exact root
cospan apex.  The two callbacks are precisely the recursive plan stops and
rigid variables exposed by that alignment. -/
noncomputable def ofAlignedAbstracts
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftAbstract rightAbstract : Pattern}
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned rhoReflectivePresentation stop
      leftAbstract rightAbstract)
    (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
      stop left right →
        let leftValues := leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let rightValues := rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let leftInventory :=
          (leftView.node.semanticAtomEnvironment leftValues).1
        let rightInventory :=
          (rightView.node.semanticAtomEnvironment rightValues).1
        let leftEnvironment :=
          CostStaticAtomEnvironment.ofInventory leftInventory
        let rightEnvironment :=
          CostStaticAtomEnvironment.ofInventory rightInventory
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color rhoReflectivePresentation
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          targetDeclaration rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (leftEnvironment.reify left)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (rightEnvironment.reify right))))))
    (mapFvar : ∀ availableDepth scopeDepth rootDepth name,
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment :=
        CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl
        rhoCIGSLT color rhoReflectivePresentation
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration rootDepth
        (cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (leftEnvironment.reifyName name))))))
        (cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))))) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  have apex :=
    CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
      leftEnvironment rightEnvironment leftView.node.thinning
      (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
      (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
      rhoReflectivePresentation
      (fun availableDepth scopeDepth rootDepth {left right} stopped => by
        have endpoint := mapStop availableDepth scopeDepth rootDepth stopped
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (rightEnvironment.reify right)))).symm)
      (fun availableDepth scopeDepth rootDepth name => by
        have endpoint := mapFvar availableDepth scopeDepth rootDepth name
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))).symm)
      aligned callbackAvailable callbackScope callbackRoot
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _ apex
  exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
    (thickenEq callbackScope
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))))

end RhoReachedPlanPairCommonApex

namespace RhoReachedPlanPairTwoDepthApex

/-- **The separated-depth producer.**  Exactly `ofAlignedAbstracts`, with the
restoration depth and the canonicalization key depth carried independently
throughout.

This is a *direct* construction, not a transport: it does not assume the two
quotation disciplines agree, and so — unlike `RhoReachedPlanPairCommonApex.toTwoDepth`
— it is usable in rho's two-colour profile, where that assumption is refuted
(`not_quoteStatusAgrees_rho`).  The two callbacks are again the recursive plan
stops and the rigid variables exposed by the alignment, each now stated at an
arbitrary independent pair of depths. -/
noncomputable def ofAlignedAbstracts
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope restorationDepth keyDepth : Nat)
    {leftAbstract rightAbstract : Pattern}
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned rhoReflectivePresentation stop
      leftAbstract rightAbstract)
    (mapStop : ∀ availableDepth scopeDepth stopRestorationDepth stopKeyDepth
        {left right},
      stop left right →
        let leftValues := leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let rightValues := rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let leftInventory :=
          (leftView.node.semanticAtomEnvironment leftValues).1
        let rightInventory :=
          (rightView.node.semanticAtomEnvironment rightValues).1
        let leftEnvironment :=
          CostStaticAtomEnvironment.ofInventory leftInventory
        let rightEnvironment :=
          CostStaticAtomEnvironment.ofInventory rightInventory
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color rhoReflectivePresentation
        CostStaticAtomKeyCospan.TwoDepthApex rhoCIGSLT cospan
          targetDeclaration stopRestorationDepth stopKeyDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (leftEnvironment.reify left)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (rightEnvironment.reify right))))))
    (mapFvar : ∀ availableDepth scopeDepth fvarRestorationDepth fvarKeyDepth
        name,
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment :=
        CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl
        rhoCIGSLT color rhoReflectivePresentation
      CostStaticAtomKeyCospan.TwoDepthApex rhoCIGSLT cospan
        targetDeclaration fvarRestorationDepth fvarKeyDepth
        (cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (leftEnvironment.reifyName name))))))
        (cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))))) :
    RhoReachedPlanPairTwoDepthApex leftView rightView callbackAvailable
      callbackScope restorationDepth keyDepth leftAbstract rightAbstract := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  have apex :=
    CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
      leftEnvironment rightEnvironment leftView.node.thinning
      (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
      (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
      rhoReflectivePresentation
      (fun availableDepth scopeDepth stopRestorationDepth stopKeyDepth
          {left right} stopped => by
        have endpoint := mapStop availableDepth scopeDepth stopRestorationDepth
          stopKeyDepth stopped
        apply CostStaticAtomKeyCospan.TwoDepthApex.reindex rfl _ endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (rightEnvironment.reify right)))).symm)
      (fun availableDepth scopeDepth fvarRestorationDepth fvarKeyDepth
          name => by
        have endpoint := mapFvar availableDepth scopeDepth fvarRestorationDepth
          fvarKeyDepth name
        apply CostStaticAtomKeyCospan.TwoDepthApex.reindex rfl _ endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))).symm)
      aligned callbackAvailable callbackScope restorationDepth keyDepth
  apply CostStaticAtomKeyCospan.TwoDepthApex.reindex rfl _ apex
  exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
    (thickenEq callbackScope
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))))

end RhoReachedPlanPairTwoDepthApex

/-- The fixed-colour, parent-context-polymorphic semantic action retained by a
recursively closed pair.  The recursive pair fixes only its payloads, visible
availability, and target type.  A consumer later supplies the exact parent
views, reached plans, and restoration depth. -/
def RhoReachedPlanPairApexAction
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (childAvailable : List TypeExpr) (leftPayload rightPayload : Pattern)
    (childType : TypeExpr) : Prop :=
  ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      (leftView : left.StaticRootView declarationColor)
      (rightView : right.StaticRootView declarationColor)
      (callbackAvailable callbackScope callbackRoot : Nat)
      {leftAbstract rightAbstract : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_leftAvailableEq : leftReached.sourceAvailable = childAvailable)
      (_rightAvailableEq : rightReached.sourceAvailable = childAvailable)
      (_leftTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType = childType)
      (_rightTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType = childType)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType))),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- **Separated-depth semantic action.**  Identical to
`RhoReachedPlanPairApexAction` except that the retained action is stated
over `RhoReachedPlanPairTwoDepthApex`, so a consumer supplies the
restoration depth and the canonicalization key depth independently.

This is the field type a recursive result must carry for the foreign-colour
arm: the one-index action cannot be supplied there, because the two
quotation disciplines diverge at a foreign quote. -/
def RhoReachedPlanPairTwoDepthApexAction
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (childAvailable : List TypeExpr) (leftPayload rightPayload : Pattern)
    (childType : TypeExpr) : Prop :=
  ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      (leftView : left.StaticRootView declarationColor)
      (rightView : right.StaticRootView declarationColor)
      (callbackAvailable callbackScope restorationDepth keyDepth : Nat)
      {leftAbstract rightAbstract : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_leftAvailableEq : leftReached.sourceAvailable = childAvailable)
      (_rightAvailableEq : rightReached.sourceAvailable = childAvailable)
      (_leftTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType = childType)
      (_rightTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType = childType)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType))),
    RhoReachedPlanPairTwoDepthApex leftView rightView callbackAvailable
      callbackScope restorationDepth keyDepth leftAbstract rightAbstract
/-- Recursive closure retains both the ordinary compact pair and its semantic
action in any later parent cospan.  The latter cannot be reconstructed from the
former because compact elaboration intentionally forgets parent atom slots. -/
structure RhoCanonicalPairRecursiveResult
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (available outer : List TypeExpr) (leftPattern rightPattern : Pattern)
    (type : TypeExpr) : Type where
  pair : CostCanonicalPairElaboration rhoCIGSLT
    rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type
  reachedApex : @RhoReachedPlanPairApexAction declarationColor targetFree
    available leftPattern rightPattern type

/-- **Separated-depth recursive closure.**  The same two fields, with the
retained semantic action stated over `RhoReachedPlanPairTwoDepthApexAction`.

This is the form the foreign-colour arm requires: the one-index action is not
supplyable there, because the restoration and keying disciplines diverge at a
foreign quote and no single index can serve both. -/
structure RhoCanonicalPairRecursiveTwoDepthResult
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (available outer : List TypeExpr) (leftPattern rightPattern : Pattern)
    (type : TypeExpr) : Type where
  pair : CostCanonicalPairElaboration rhoCIGSLT
    rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type
  reachedApex : @RhoReachedPlanPairTwoDepthApexAction declarationColor
    targetFree available leftPattern rightPattern type

/-- One syntax-directed layer for the proof-relevant recursive result.  Every
recursive input is constrained by the existing symmetric size measure. -/
def RhoCanonicalPairRecursiveStep (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
      {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern →
    (∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree childAvailable childType rightChild →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftChild =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
        childAvailable childOuter leftChild rightChild childType)) →
    Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
      available outer leftPattern rightPattern type)

/-- Close a proof-relevant recursive step by the same well-founded measure as
the ordinary paired elaborator.  Parent-cospan parameters occur only inside the
retained semantic action and do not alter termination. -/
noncomputable def RhoCanonicalPairRecursiveResult.nonempty_of_step
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern) :
    Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
      available outer leftPattern rightPattern type) := by
  apply step (targetFree := targetFree) admissible leftWellSorted
    rightWellSorted canonical
  intro childAvailable childOuter leftChild rightChild childType
    leftChildWellSorted rightChildWellSorted childCanonical _smaller
    childAdmissible
  exact RhoCanonicalPairRecursiveResult.nonempty_of_step step childAdmissible
    leftChildWellSorted rightChildWellSorted childCanonical
termination_by sizeOf leftPattern + sizeOf rightPattern

/-- Instantiate a strictly smaller same-colour result in the exact current
parent cospan.  This consumes retained evidence; it never inverts the compact
pair elaboration. -/
theorem RhoCanonicalPairRecursiveResult.reachedApex_sameColor
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (result : @RhoCanonicalPairRecursiveResult color targetFree
      leftReached.sourceAvailable [] leftPayload rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  exact result.reachedApex leftView rightView callbackAvailable callbackScope
    callbackRoot leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq rfl sourceAvailableEq.symm rfl
    (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq.symm)
    sourceTypeEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute

/-- **Separated-depth same-colour reached apex.**  Delegation to the
retained two-depth action, exactly as the one-index form delegates to its
own.  Supplies the restoration and keying depths independently. -/
theorem RhoCanonicalPairRecursiveTwoDepthResult.reachedApex_sameColor
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope restorationDepth keyDepth : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (result : @RhoCanonicalPairRecursiveTwoDepthResult color targetFree
      leftReached.sourceAvailable [] leftPayload rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)) :
    RhoReachedPlanPairTwoDepthApex leftView rightView callbackAvailable
      callbackScope restorationDepth keyDepth leftAbstract rightAbstract := by
  exact result.reachedApex leftView rightView callbackAvailable callbackScope
    restorationDepth keyDepth leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq rfl sourceAvailableEq.symm rfl
    (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq.symm)
    sourceTypeEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute

/-- The strict canonical stop used by rho's paired recursion. -/
def RhoCanonicalRawStop (declarationColor : CostStaticColor)
    (parentMeasure : Nat) (left right : Pattern) : Prop :=
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  ((CollapsingRoot declaration left ∨ CollapsingRoot declaration right) ∧
      canonicalize declaration left = canonicalize declaration right) ∧
    sizeOf left + sizeOf right < parentMeasure

/-- A raw collapse selected by the other generated declaration cannot occur
at an authored Quote of the current plan colour.  Its collapsing endpoint is
therefore either a certified foreign boundary or a bare parallel root. -/
theorem RhoCanonicalRawStop.foreign_reached_root_cases
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (foreign : declarationColor ≠ color)
    (stopped : RhoCanonicalRawStop declarationColor parentMeasure
      leftPayload rightPayload) :
    leftReached.plan.rootClass.IsCertifiedBoundary ∨
      rightReached.plan.rootClass.IsCertifiedBoundary ∨
      leftReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection ∨
      rightReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection := by
  rcases stopped.1.1 with leftCollapsing | rightCollapsing
  · rcases
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor
          leftReached leftCollapsing with boundaryApplication |
          boundaryCollection |
          sourceQuote | parallel
    · exact Or.inl (Or.inl boundaryApplication)
    · exact Or.inl (Or.inr boundaryCollection)
    · exact (foreign
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
          leftReached sourceQuote leftCollapsing)).elim
    · exact Or.inr (Or.inr (Or.inl parallel))
  · rcases
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor
          rightReached rightCollapsing with boundaryApplication |
          boundaryCollection |
          sourceQuote | parallel
    · exact Or.inr (Or.inl (Or.inl boundaryApplication))
    · exact Or.inr (Or.inl (Or.inr boundaryCollection))
    · exact (foreign
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
          rightReached sourceQuote rightCollapsing)).elim
    · exact Or.inr (Or.inr (Or.inr parallel))

/-- Complete reachable shape split for a foreign-colour plan stop outside
the certified-boundary/boundary quadrant.  This is the finite switchboard a
semantic proof must cover: paired authored Quote, either boundary side, or a
bare-parallel side. -/
theorem RhoCanonicalRawStop.foreign_reached_stop_cases
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (foreign : declarationColor ≠ color)
    (reason : RhoCanonicalRawStop declarationColor parentMeasure
        leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary)) :
    (leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor ∧
      rightReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor) ∨
      leftReached.plan.rootClass.IsCertifiedBoundary ∨
      rightReached.plan.rootClass.IsCertifiedBoundary ∨
      leftReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection ∨
      rightReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection := by
  rcases reason with stopped | eligible
  · rcases RhoCanonicalRawStop.foreign_reached_root_cases leftReached
        rightReached foreign stopped with leftBoundary | rightBoundary |
          leftParallel | rightParallel
    · exact Or.inr (Or.inl leftBoundary)
    · exact Or.inr (Or.inr (Or.inl rightBoundary))
    · exact Or.inr (Or.inr (Or.inr (Or.inl leftParallel)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rightParallel)))
  · rcases CostStaticPlanStopEligible.nonBoundary_cases
        rhoReflectivePresentation leftReached.plan rightReached.plan eligible
        notBothBoundary with quote | leftMixed | rightMixed | parallel
    · exact Or.inl quote
    · exact Or.inr (Or.inl (Or.inr leftMixed.1))
    · exact Or.inr (Or.inr (Or.inl (Or.inr rightMixed.2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl parallel.1)))

/-- **Which descent the paired-Quote shape uses, settled by proof.**

`foreign_sourceQuotes_arguments` exposes payloads headed by the *plan*
colour's quote constructor, while the canonicalizing declaration belongs to
the *other* colour.  Reading the name suggests this is the declaration's own
quote; it is not.  The profile recognizes the head (so the restoration depth
resets) and the declaration does not (so the key depth passes through) — the
foreign-quote configuration exactly.

Consequence: the paired-Quote shape descends by
`twoDepthApex_foreignQuote_descends`, never by the own-quote lemma, and it is
a shape where the two carriers genuinely disagree rather than one where they
coincide. -/
theorem rho_foreign_quoteHead_configuration
    {declarationColor color : CostStaticColor}
    (foreign : declarationColor ≠ color) :
    ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).quoteConstructor = true ∧
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor ≠
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor := by
  refine ⟨isQuoteConstructor_costStaticReflectivePresentationDecl color _ ?_,
    costStaticReflectivePresentationDecl_quoteConstructor_ne
      (Ne.symm foreign) _⟩
  show rhoReflectivePresentation.toReflectivePresentationDecl ∈
    rhoReflectionProfile.presentations
  simp [rhoReflectionProfile]

/-- Paired authored Quotes in the foreign-colour branch are structural, not
delegated leaves.  Their generated Quote heads are rigid for the foreign
declaration, so the retained raw alignment descends to the ordered argument
lists. -/
theorem RhoCanonicalRawStop.foreign_sourceQuotes_arguments
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (foreign : declarationColor ≠ color)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload rightPayload) :
    ∃ leftArguments rightArguments,
      leftPayload = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor leftArguments ∧
      rightPayload = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor rightArguments ∧
      CanonicalStopAlignedList
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation)
        (RhoCanonicalRawStop declarationColor parentMeasure)
        leftArguments rightArguments := by
  rcases CanonicalStopAligned.reached_sourceQuotes_cases leftReached
      rightReached leftQuote rightQuote (fun stopped => stopped.1.1)
      aligned with same | structural
  · exact (foreign same.1).elim
  · exact structural.2

/-- The ordered source-skeleton arguments below a paired foreign-colour Quote
carry provenance-correct stops that are strictly smaller than the enclosing
payload pair. -/
theorem RhoCanonicalRawStop.foreign_sourceQuoteArguments_alignedBelow
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (foreign : declarationColor ≠ color)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload rightPayload) :
    ∃ leftArguments rightArguments,
      leftReached.plan.abstractPattern =
          .apply rhoReflectivePresentation.quoteConstructor leftArguments ∧
      rightReached.plan.abstractPattern =
          .apply rhoReflectivePresentation.quoteConstructor rightArguments ∧
      CanonicalStopAlignedList rhoReflectivePresentation
        (CostStaticPlanCanonicalStopBelow leftReached.plan rightReached.plan
          rhoReflectivePresentation
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (RhoCanonicalRawStop declarationColor parentMeasure)
          (sizeOf leftPayload + sizeOf rightPayload))
        leftArguments rightArguments := by
  obtain ⟨leftGeneratedArguments, rightGeneratedArguments, leftShape,
      rightShape,
      rawArgumentsAligned⟩ :=
    RhoCanonicalRawStop.foreign_sourceQuotes_arguments leftReached rightReached
      foreign leftQuote rightQuote aligned
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  subst sourceBoundEq
  subst targetBoundEq
  subst sourceAvailableEq
  cases thinningEq
  cases lp with
  | @application _ _ _ _ _ leftWireName leftRawArguments leftConstructor
      leftRendered leftCurrent leftPreimage leftNotBare leftChildren =>
      cases rp with
      | @application _ _ _ _ _ rightWireName rightRawArguments
          rightConstructor rightRendered rightCurrent rightPreimage rightNotBare
          rightChildren =>
          have leftSourceLabelEq : leftPreimage.sourceConstructor.1.label =
              rhoReflectivePresentation.quoteConstructor := by
            simpa [CostStaticRegionPlan.rootClass] using
              CostStaticPlanRootClass.application.inj leftQuote
          have rightSourceLabelEq : rightPreimage.sourceConstructor.1.label =
              rhoReflectivePresentation.quoteConstructor := by
            simpa [CostStaticRegionPlan.rootClass] using
              CostStaticPlanRootClass.application.inj rightQuote
          have leftWireEq : _ =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation).quoteConstructor :=
            Pattern.apply.inj leftShape |>.1
          have rightWireEq : _ =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation).quoteConstructor :=
            Pattern.apply.inj rightShape |>.1
          have wireEq : rightWireName = leftWireName :=
            rightWireEq.trans leftWireEq.symm
          cases wireEq
          have constructorEq : leftConstructor = rightConstructor :=
            rhoCIGSLT.renderDeclaredCostConstructor_injective
              (leftRendered.trans rightRendered.symm)
          subst rightConstructor
          have preimageEq : leftPreimage = rightPreimage :=
            CostStaticConstructorPreimage.eq _ _
          subst rightPreimage
          have leftRawArgumentsEq : leftRawArguments =
              leftGeneratedArguments :=
            Pattern.apply.inj leftShape |>.2
          have rightRawArgumentsEq : rightRawArguments =
              rightGeneratedArguments :=
            Pattern.apply.inj rightShape |>.2
          subst leftGeneratedArguments
          subst rightGeneratedArguments
          have sourceQuoted :
              ReflectiveContextSupport.isQuoteConstructor
                rhoCIGSLT.reflection.1
                leftPreimage.sourceConstructor.1.label = true := by
            rw [leftSourceLabelEq]
            decide
          obtain ⟨leftTargetRule, leftTargetMembership, leftTargetLabel,
              _leftTargetNotBare, _leftTargetType,
              leftArgumentsTypedAtParent⟩ :=
            WellSorted.hasType_apply_inversion
              leftAdmission.wellSorted.1.1
          obtain ⟨rightTargetRule, rightTargetMembership, rightTargetLabel,
              _rightTargetNotBare, _rightTargetType,
              rightArgumentsTypedAtParent⟩ :=
            WellSorted.hasType_apply_inversion
              rightAdmission.wellSorted.1.1
          have targetRulesEq : rightTargetRule = leftTargetRule :=
            rhoCIGSLT.costWholeLanguage_labelDeterministic
              rightTargetMembership leftTargetMembership
              (rightTargetLabel.symm.trans
                (rightWireEq.trans (leftWireEq.symm.trans leftTargetLabel)))
          subst rightTargetRule
          have materializedMembership :
              rhoCIGSLT.materializeDeclaredCostConstructor leftConstructor ∈
                rhoCIGSLT.costWholeLanguage.terms := by
            simpa only [rhoCIGSLT.costWholeLanguage_terms] using
              rhoCIGSLT.materializeDeclaredCostConstructor_mem leftConstructor
          have targetRuleEq : leftTargetRule =
              rhoCIGSLT.materializeDeclaredCostConstructor leftConstructor :=
            rhoCIGSLT.costWholeLanguage_labelDeterministic
              leftTargetMembership materializedMembership
              (leftTargetLabel.symm.trans
                ((rhoCIGSLT.materializeDeclaredCostConstructor_label
                  leftConstructor).trans leftRendered).symm)
          subst leftTargetRule
          have leftArgumentsTypedForQuote := leftArgumentsTypedAtParent
          have rightArgumentsTypedForQuote := rightArgumentsTypedAtParent
          rw [leftPreimage.parametersMap] at leftArgumentsTypedAtParent
          rw [leftPreimage.parametersMap] at rightArgumentsTypedAtParent
          have leftCanonicalArguments :
              Pattern.hasCanonicalBinderMetadataList leftRawArguments =
                true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using
              leftAdmission.wellSorted.1.2.1
          have rightCanonicalArguments :
              Pattern.hasCanonicalBinderMetadataList rightRawArguments =
                true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using
              rightAdmission.wellSorted.1.2.1
          have leftObjectArguments :
              WellSorted.isObjectPatternList leftRawArguments = true := by
            simpa [WellSorted.isObjectPattern] using
              leftAdmission.wellSorted.1.2.2.1
          have rightObjectArguments :
              WellSorted.isObjectPatternList rightRawArguments = true := by
            simpa [WellSorted.isObjectPattern] using
              rightAdmission.wellSorted.1.2.2.1
          have targetQuoted :
              ReflectiveContextSupport.isQuoteConstructor
                rhoCIGSLT.costWholeReflectionProfile
                (rhoCIGSLT.materializeDeclaredCostConstructor
                  leftConstructor).label = true := by
            rw [leftPreimage.labelMap]
            simpa only [reflectiveIsQuoteConstructor_mapCostStatic] using
              sourceQuoted
          have leftParentReflective :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                rhoCIGSLT.costWholeReflectionProfile lsa.length
                (.apply
                  (rhoCIGSLT.materializeDeclaredCostConstructor
                    leftConstructor).label leftRawArguments) := by
            simpa only [rhoCIGSLT.materializeDeclaredCostConstructor_label,
              leftRendered] using leftAdmission.wellSorted.2
          have rightParentReflective :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                rhoCIGSLT.costWholeReflectionProfile lsa.length
                (.apply
                  (rhoCIGSLT.materializeDeclaredCostConstructor
                    leftConstructor).label rightRawArguments) := by
            simpa only [rhoCIGSLT.materializeDeclaredCostConstructor_label,
              rightRendered] using rightAdmission.wellSorted.2
          have leftAtZero :=
            WellSorted.isWellScopedListAt_zero_of_typed_quote
              rhoCIGSLT.costWholeLanguage_validate
              rhoCIGSLT.costWholeReflectionProfile_validate
              materializedMembership leftArgumentsTypedForQuote targetQuoted
              leftParentReflective
          have rightAtZero :=
            WellSorted.isWellScopedListAt_zero_of_typed_quote
              rhoCIGSLT.costWholeLanguage_validate
              rhoCIGSLT.costWholeReflectionProfile_validate
              materializedMembership rightArgumentsTypedForQuote targetQuoted
              rightParentReflective
          have leftArgumentsTyped :=
            leftArgumentsTypedAtParent.restrictOuterOfScoped
              (inner := []) (outer := lsa) leftAtZero
          have rightArgumentsTyped :=
            rightArgumentsTypedAtParent.restrictOuterOfScoped
              (inner := []) (outer := lsa) rightAtZero
          have leftReflective :=
            WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
              rhoCIGSLT.costWholeLanguage_validate
              rhoCIGSLT.costWholeReflectionProfile_validate
              materializedMembership leftArgumentsTypedForQuote targetQuoted
              leftParentReflective
          have rightReflective :=
            WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
              rhoCIGSLT.costWholeLanguage_validate
              rhoCIGSLT.costWholeReflectionProfile_validate
              materializedMembership rightArgumentsTypedForQuote targetQuoted
              rightParentReflective
          have parameterRoute : ∀ {parameter : TermParam}
              {expected : TypeExpr},
              parameter ∈ leftPreimage.sourceConstructor.1.params →
              WellSorted.parameterType? parameter = some expected →
                Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
                  (mapTypeExpr (color.symbols rhoCIGSLT)
                    (.base leftPreimage.sourceConstructor.1.category))
                  (mapTypeExpr (color.symbols rhoCIGSLT) expected)) := by
            intro parameter expected parameterMembership parameterTyped
            have prior : CostCanonicalTypeRoute rhoCIGSLT color
                (mapTypeExpr (color.symbols rhoCIGSLT)
                  (.base leftPreimage.sourceConstructor.1.category))
                (.base
                  (rhoCIGSLT.materializeDeclaredCostConstructor
                    leftConstructor).category) :=
              CostCanonicalTypeRoute.refl.castEndpoint (by
                simpa [mapTypeExpr] using congrArg TypeExpr.base
                  leftPreimage.categoryMap.symm)
            refine ⟨CostCanonicalTypeRoute.parameter
              (parameter := mapTermParam (color.symbols rhoCIGSLT) parameter)
              prior ?_ ?_ ?_ ?_⟩
            · simpa only [rhoCIGSLT.costWholeLanguage_terms] using
                rhoCIGSLT.materializeDeclaredCostConstructor_mem
                  leftConstructor
            · intro targetBare
              exact leftNotBare
                (leftPreimage.source_usesBareCollection leftCurrent targetBare)
            · rw [leftPreimage.parametersMap]
              exact List.mem_map_of_mem parameterMembership
            · simp [WellSorted.parameterType?_mapTermParam,
                parameterTyped]
          refine ⟨leftChildren.abstractPatterns,
            rightChildren.abstractPatterns, ?_, ?_, ?_⟩
          · simp [CostStaticRegionPlan.abstractPattern, leftSourceLabelEq]
          · simp [CostStaticRegionPlan.abstractPattern, rightSourceLabelEq]
          · exact costStaticArgumentPlan_canonicalStopAlignedBelow
              rho_collectionChoiceDeterministic rhoReflectivePresentation
              (costStaticReflectivePresentationDecl rhoCIGSLT
                declarationColor rhoReflectivePresentation)
              (.application leftConstructor leftRendered leftCurrent
                leftPreimage leftNotBare leftChildren)
              (.application leftConstructor rightRendered rightCurrent
                leftPreimage rightNotBare rightChildren)
              leftPreimage.sourceConstructor.1.label [] [] leftChildren
              rightChildren
              (by simpa [sourceQuoted] using leftArgumentsTyped)
              (by simpa [sourceQuoted] using rightArgumentsTyped)
              leftCanonicalArguments rightCanonicalArguments
              leftObjectArguments rightObjectArguments
              (by simpa [sourceQuoted] using leftReflective)
              (by simpa [sourceQuoted] using rightReflective)
              ⟨ltb, by simp [sourceQuoted]⟩
              ⟨ltb, by simp [sourceQuoted]⟩
              .hole .hole
              (by simp [CostStaticRegionPlan.abstractPattern])
              (by simp [CostStaticRegionPlan.abstractPattern])
              (CostStaticPlanEntryEmbedding.refl _)
              (CostStaticPlanEntryEmbedding.refl _)
              parameterRoute rfl (by simp) (by simp) rawArgumentsAligned
      | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
          boundaryCollection =>
          simp [CostStaticRegionPlan.rootClass] at rightQuote
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at leftQuote

/-- A same-colour raw plan stop is discharged by the strictly smaller rich
recursive result.  The ordinary pair field is insufficient here; its retained
parent-polymorphic action is instantiated in the current semantic cospan. -/
theorem RhoCanonicalPairRecursiveResult.reachedApex_of_rawStop_sameColor
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    {parentMeasure : Nat}
    (stopped : RhoCanonicalRawStop color parentMeasure leftPayload
      rightPayload)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild < parentMeasure →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult color targetFree
          childAvailable childOuter leftChild rightChild childType)) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  obtain ⟨rightRoute⟩ := rightRoute
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute rightRootAdmissible
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftReached.sourceAvailable
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
      rightPayload := by
    rw [sourceAvailableEq, sourceTypeEq]
    exact rightAdmission.wellSorted
  obtain ⟨result⟩ := closeSmaller (childOuter := [])
    leftAdmission.wellSorted rightWellSorted stopped.1.2 stopped.2
      childAdmissible
  exact result.reachedApex_sameColor leftView rightView callbackAvailable
    callbackScope callbackRoot leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    ⟨rightRoute⟩

/-- A plan-stop callback in the proof-relevant restoration relation itself.

**Payload-level raw alignment transports to abstract-level plan alignment.**

The residual switchboard receives its alignment on *payloads* under the
generated declaration of one colour, while the reached-plan apex is stated on
the *abstract patterns* of the two reached plans, under a declaration the
caller chooses.  This bridges the two.

The raw and chosen declarations are independent — which is exactly the
configuration a provider meets when it canonicalizes a same-colour pair under
the other generated Cost declaration.  The reached plans' dependent indices
(`sourceBound`, `targetBound`, `thinning`, `sourceType`) are aligned first by
the retained equality telescope, which is why those equalities are carried
through the residual at all. -/
theorem rhoReachedPlan_canonicalStopAligned_of_rawAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
      rightPayload) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalStop leftReached.plan rightReached.plan declaration
        rawDeclaration rawStop)
      leftReached.plan.abstractPattern rightReached.plan.abstractPattern := by
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  subst sourceBoundEq
  subst targetBoundEq
  subst sourceTypeEq
  cases thinningEq
  exact CostStaticRegionPlan.canonicalStopAligned_of_rawAlignment
    rho_collectionChoiceDeterministic declaration rawDeclaration lp rp
    leftAdmission rightAdmission sourceAvailableEq rawAligned

/-- Apex-aware stop obligation after the certified-boundary/boundary quadrant.

The interface does not compress a parallel apex to depth-uniform pointwise
equality.  The restoration depth is therefore explicit and may carry the
permutation witness produced by rho's parallel canonicalization. -/
def RhoStaticPlanStopCommonApex
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  ∀ callbackAvailable callbackScope callbackRoot
      {leftAbstract rightAbstract},
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
        rhoReflectivePresentation rawDeclaration rawStop leftAbstract
          rightAbstract →
      RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
        callbackScope callbackRoot leftAbstract rightAbstract

namespace RhoStaticPlanStopCommonApex

/-- Lift an established source-pattern leaf alignment into the exact mapped,
thickened, and common-reified restoration apex at one requested depth.  This
bridge is used only after a case-specific proof has earned the stronger
depth-uniform leaf relation. -/
noncomputable def ofSourcePatternLeafAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {left right : Pattern}
    (aligned :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      PatternLeafAligned (fun leftLeaf rightLeaf => ∀ depth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (leftNode.thinning.thickenAmbientBVars depth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (rightNode.thinning.thickenAmbientBVars depth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))) left right)
    (scopeDepth rootDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      rootDepth
      (cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT) left)))
      (cospan.reifyRight rightEnvironment.lookupAtom?
        (rightNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT) right))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let mappedRelation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ depth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftNode.thinning.thickenAmbientBVars depth leftLeaf))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightNode.thinning.thickenAmbientBVars depth rightLeaf))
  have mappedAligned : PatternLeafAligned mappedRelation
      (mapPattern (color.symbols rhoCIGSLT) left)
      (mapPattern (color.symbols rhoCIGSLT) right) :=
    aligned.mapPattern (color.symbols rhoCIGSLT) (fun related => related)
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftNode.thinning.thickenAmbientBVars depth pattern =
        rightNode.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
          targetBound).thickenAmbientBVars depth pattern) sameBound
  have targetAligned : PatternLeafAligned
      (fun leftLeaf rightLeaf =>
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyLeft leftEnvironment.lookupAtom? leftLeaf)
            (cospan.reifyRight rightEnvironment.lookupAtom? rightLeaf))
      (leftNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT) left))
      (rightNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT) right)) := by
    rw [← thickenEq scopeDepth]
    exact mappedAligned.thickenAmbientBVars leftNode.thinning
      (fun depth {left right} related => by
        rw [thickenEq depth right]
        exact related depth) scopeDepth
  have commonAligned := cospan.reifyPatternLeafAligned
    leftEnvironment.lookupAtom? rightEnvironment.lookupAtom?
    cospan.leftSlot cospan.rightSlot (fun related => related) targetAligned
  exact CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
    commonAligned

end RhoStaticPlanStopCommonApex

/-- Apex-aware stop obligation after the certified-boundary/boundary quadrant
has been removed.  The retained reached-plan evidence is identical to the
uniform interface, but the result remains at one proof-relevant restoration
depth. -/
def RhoStaticNonBoundaryPlanStopCommonApex
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  ∀ callbackAvailable callbackScope callbackRoot
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary)),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

namespace RhoStaticNonBoundaryPlanStopCommonApex

/-- Residual callback after every delegated same-colour canonical leaf has
been consumed by the rich recursive result. -/
def AfterSameColorAlignedLeaf
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let rawStop := RhoCanonicalRawStop declarationColor
    (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
  ∀ callbackAvailable callbackScope callbackRoot
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_afterAligned : declarationColor ≠ color ∨ ¬ ∃ stopped,
        _rawAligned = CanonicalStopAligned.leaf stopped),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- Prefer the retained recursive semantic action whenever canonical descent
actually delegated a same-colour leaf.  This also catches a collapsing stop
whose producer selected the structural-eligibility tag; the proof-relevant
alignment, rather than that tag, determines whether recursion is required. -/
noncomputable def preferSameColorAlignedLeaf
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
          childAvailable childOuter leftChild rightChild childType))
    (fallback : AfterSameColorAlignedLeaf leftView rightView
      declarationColor) :
    RhoStaticNonBoundaryPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    leftPayload rightPayload leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
    notBothBoundary
  by_cases sameColor : declarationColor = color
  · subst declarationColor
    by_cases delegated : ∃ stopped,
        rawAligned = CanonicalStopAligned.leaf stopped
    · obtain ⟨stopped, alignedEq⟩ := delegated
      cases alignedEq
      exact RhoCanonicalPairRecursiveResult.reachedApex_of_rawStop_sameColor
        leftView rightView rightRootAdmissible callbackAvailable callbackScope
        callbackRoot leftReached rightReached leftAdmission rightAdmission
        leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
        sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding
        leftRoute rightRoute stopped closeSmaller
    · exact fallback callbackAvailable callbackScope callbackRoot leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute rightRoute stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
        (Or.inr delegated)
  · exact fallback callbackAvailable callbackScope callbackRoot leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      (Or.inl sameColor)

/-- Residual plan-stop switchboard after same-colour source Quote pairs have
been removed.  The retained disjunction states exactly why the Quote terminal
does not apply. -/
def AfterSameColorQuotePair
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let rawStop := RhoCanonicalRawStop declarationColor
    (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
  ∀ callbackAvailable callbackScope callbackRoot
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_afterAligned : declarationColor ≠ color ∨ ¬ ∃ stopped,
        _rawAligned = CanonicalStopAligned.leaf stopped)
      (_remaining : declarationColor ≠ color ∨
        leftReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor ∨
        rightReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- Consume a hidden or explicit same-colour Quote stop from the rich recursive
result.  The `stopReason` tag need not have chosen the raw-stop disjunct:
`CanonicalStopAligned` itself identifies the collapsing leaf. -/
noncomputable def ofRecursiveSameColorQuotePair
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
          childAvailable childOuter leftChild rightChild childType))
    (remaining : AfterSameColorQuotePair leftView rightView declarationColor) :
    AfterSameColorAlignedLeaf leftView rightView declarationColor := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    leftPayload rightPayload leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
    notBothBoundary afterAligned
  by_cases sameColor : declarationColor = color
  · subst declarationColor
    by_cases leftQuote : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · by_cases rightQuote : rightReached.plan.rootClass =
          .application rhoReflectivePresentation.quoteConstructor
      · rcases CanonicalStopAligned.reached_sourceQuotes_cases leftReached
            rightReached leftQuote rightQuote (fun stopped => stopped.1.1)
            rawAligned with same | foreign
        · exact RhoCanonicalPairRecursiveResult.reachedApex_of_rawStop_sameColor
            leftView rightView rightRootAdmissible callbackAvailable
            callbackScope callbackRoot leftReached rightReached leftAdmission
            rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
            sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
            leftEmbedding rightEmbedding leftRoute rightRoute same.2 closeSmaller
        · exact False.elim (CostStaticColor.ne_flip color foreign.1)
      · exact remaining callbackAvailable callbackScope callbackRoot
          leftReached rightReached leftAdmission rightAdmission leftAbstractEq
          rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
          targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
          rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
          notBothBoundary afterAligned
          (Or.inr (Or.inr rightQuote))
    · exact remaining callbackAvailable callbackScope callbackRoot leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute rightRoute stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
        afterAligned
        (Or.inr (Or.inl leftQuote))
  · exact remaining callbackAvailable callbackScope callbackRoot leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      afterAligned
      (Or.inl sameColor)

/-- Separated-depth residual switchboard.  Identical obligation to
`AfterSameColorBoundarySide` except that its conclusion is stated over
`RhoReachedPlanPairTwoDepthApex`, so the restoration and key depths are
carried independently.  This is the form the foreign-colour arm can
actually satisfy. -/
def AfterSameColorBoundarySideTwoDepth
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let rawStop := RhoCanonicalRawStop declarationColor
    (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
  ∀ callbackAvailable callbackScope restorationDepth keyDepth
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_afterAligned : declarationColor ≠ color ∨ ¬ ∃ stopped,
        _rawAligned = CanonicalStopAligned.leaf stopped)
      (_afterQuote : declarationColor ≠ color ∨
        leftReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor ∨
        rightReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor)
      (_afterBoundary : declarationColor ≠ color ∨
        (¬ leftReached.plan.rootClass.IsCertifiedBoundary ∧
          ¬ rightReached.plan.rootClass.IsCertifiedBoundary)),
    RhoReachedPlanPairTwoDepthApex leftView rightView callbackAvailable
      callbackScope restorationDepth keyDepth leftAbstract rightAbstract


/-- Residual switchboard after same-colour Quote pairs and every same-colour
stop with a certified-boundary side have been consumed. -/
def AfterSameColorBoundarySide
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let rawStop := RhoCanonicalRawStop declarationColor
    (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
  ∀ callbackAvailable callbackScope callbackRoot
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_afterAligned : declarationColor ≠ color ∨ ¬ ∃ stopped,
        _rawAligned = CanonicalStopAligned.leaf stopped)
      (_afterQuote : declarationColor ≠ color ∨
        leftReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor ∨
        rightReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor)
      (_afterBoundary : declarationColor ≠ color ∨
        (¬ leftReached.plan.rootClass.IsCertifiedBoundary ∧
          ¬ rightReached.plan.rootClass.IsCertifiedBoundary)),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- The same-colour branch of the residual switchboard is necessarily paired
bare parallel.  A raw-stop tag would make the retained alignment a delegated
leaf by proof irrelevance; structural eligibility then has only the parallel
case after Quote and certified boundaries have been excluded. -/
theorem sameColor_parallelRoots_of_residual
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (stopReason : RhoCanonicalRawStop color parentMeasure leftPayload
        rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation)
      (RhoCanonicalRawStop color parentMeasure) leftPayload rightPayload)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary))
    (notDelegated : ¬ ∃ stopped,
      rawAligned = CanonicalStopAligned.leaf stopped)
    (notQuote : leftReached.plan.rootClass ≠
        .application rhoReflectivePresentation.quoteConstructor ∨
      rightReached.plan.rootClass ≠
        .application rhoReflectivePresentation.quoteConstructor)
    (neitherBoundary :
      ¬ leftReached.plan.rootClass.IsCertifiedBoundary ∧
        ¬ rightReached.plan.rootClass.IsCertifiedBoundary) :
    leftReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection ∧
      rightReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection := by
  rcases stopReason with stopped | eligible
  · exact (notDelegated ⟨stopped, Subsingleton.elim _ _⟩).elim
  · refine CostStaticPlanStopEligible.parallel_of_nonBoundary_residual
      (declaration := rhoReflectivePresentation) eligible notBothBoundary ?_
        neitherBoundary
    rintro ⟨leftQuote, rightQuote⟩
    rcases notQuote with leftNotQuote | rightNotQuote
    · exact leftNotQuote leftQuote
    · exact rightNotQuote rightQuote

/-- Use the producer-retained payload bounds to recurse on an entire
same-colour mixed stop whenever either reached plan is a certified boundary.
The strict side comes from the boundary occurrence; the other side contributes
only its retained weak root bound. -/
noncomputable def ofRecursiveSameColorBoundarySide
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
          childAvailable childOuter leftChild rightChild childType))
    (remaining : AfterSameColorBoundarySide leftView rightView
      declarationColor) :
    AfterSameColorQuotePair leftView rightView declarationColor := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    leftPayload rightPayload leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
    notBothBoundary afterAligned afterQuote
  by_cases sameColor : declarationColor = color
  · subst declarationColor
    have closeAt (smaller :
        sizeOf leftPayload + sizeOf rightPayload <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1) :
        RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
          callbackScope callbackRoot leftAbstract rightAbstract := by
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      have canonical := rawAligned.canonicalize_eq declaration
        (fun stopped => stopped.1.2)
      obtain ⟨rightRoute'⟩ := rightRoute
      have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
        rw [sourceTypeEq]
        exact CostCanonicalTypeRoute.rho_admissible rightRoute'
          rightRootAdmissible
      have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree leftReached.sourceAvailable
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
          rightPayload := by
        rw [sourceAvailableEq, sourceTypeEq]
        exact rightAdmission.wellSorted
      obtain ⟨result⟩ := closeSmaller (childOuter := [])
        leftAdmission.wellSorted rightWellSorted canonical smaller
          childAdmissible
      exact result.reachedApex_sameColor leftView rightView callbackAvailable
        callbackScope callbackRoot leftReached rightReached leftAdmission
        rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
        sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
        rightEmbedding leftRoute ⟨rightRoute'⟩
    by_cases leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary
    · obtain ⟨leftBoundaryView⟩ :=
        leftReached.nonempty_boundaryView_of_boundaryClass leftBoundary
      obtain ⟨leftEmbedding'⟩ := leftEmbedding
      exact closeAt
        (CostStaticPlanReached.mixed_pair_size_lt_of_left_boundary
          leftView.node rightView.node leftReached leftBoundaryView
            leftEmbedding' rightPayloadSizeLe)
    · by_cases rightBoundary : rightReached.plan.rootClass.IsCertifiedBoundary
      · obtain ⟨rightBoundaryView⟩ :=
          rightReached.nonempty_boundaryView_of_boundaryClass rightBoundary
        obtain ⟨rightEmbedding'⟩ := rightEmbedding
        exact closeAt
          (CostStaticPlanReached.mixed_pair_size_lt_of_right_boundary
            leftView.node rightView.node rightReached rightBoundaryView
              rightEmbedding' leftPayloadSizeLe)
      · exact remaining callbackAvailable callbackScope callbackRoot
          leftReached rightReached leftAdmission rightAdmission leftAbstractEq
          rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
          targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
          rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
          notBothBoundary afterAligned afterQuote
          (Or.inr ⟨leftBoundary, rightBoundary⟩)
  · exact remaining callbackAvailable callbackScope callbackRoot leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      afterAligned afterQuote (Or.inl sameColor)

end RhoStaticNonBoundaryPlanStopCommonApex

namespace RhoStaticPlanBoundaryRestoration

/-- Close one pair of reached boundary roots as a semantic leaf.

The reached-plan producer supplies equality of the active availability fibre.
The two singleton boundary certificates then select exact atoms in the root
environments. Recursive closure is invoked only for their strictly smaller
contents; the resulting depth-indexed apex is compressed to the uniform leaf
relation consumed by keyed canonical congruence. -/
noncomputable def boundaryPair_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightNode.plan.abstractPattern)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [leftStopped.certified.typed] leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [rightStopped.certified.typed] rightNode.plan.boundaryTable.entries)
    (supportEq : leftStopped.certified.typed.boundary.targetSupport =
      rightStopped.certified.typed.boundary.targetSupport)
    (typeEq : leftStopped.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType)
    (childDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration
          leftStopped.certified.typed.boundary.content =
        canonicalize childDeclaration
          rightStopped.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild < parentMeasure →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify
          (.fvar leftStopped.boundaryOccurrence.name)))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify
          (.fvar rightStopped.boundaryOccurrence.name))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ sourceDepth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  let leftAtRoot := leftStopped.castRoot leftNode.skeleton_pattern.symm
  let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
  obtain ⟨leftSlot, leftSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence
      leftAtRoot.boundaryOccurrence)
  obtain ⟨rightSlot, rightSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence
      rightAtRoot.boundaryOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      leftStopped.boundaryOccurrence.name = some leftSlot := by
    simpa [leftAtRoot] using leftSelectedAtRoot
  have rightSelected : rightEnvironment.slotOfName?
      rightStopped.boundaryOccurrence.name = some rightSlot := by
    simpa [rightAtRoot] using rightSelectedAtRoot
  have leftSelectedBoundary : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftStopped.certified.typed.boundary) =
        some leftSlot := by
    simpa only [CostStaticPlanStopped.boundaryOccurrence_name] using leftSelected
  have rightSelectedBoundary : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightStopped.certified.typed.boundary) =
        some rightSlot := by
    simpa only [CostStaticPlanStopped.boundaryOccurrence_name] using rightSelected
  have leftEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftAtRoot.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa [leftAtRoot] using leftEmbedding
  have rightEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightAtRoot.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa [rightAtRoot] using rightEmbedding
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
      (fun depth =>
        CostStaticPlanStopped.selectedAtoms_commonRestorationApex_of_closeSmaller
          leftAtRoot rightAtRoot leftEmbeddingAtRoot rightEmbeddingAtRoot
          leftTrees rightTrees leftEnvironment rightEnvironment leftSlot
          leftSelectedAtRoot rightSlot rightSelectedAtRoot (Or.inl (by
            simpa [leftAtRoot, rightAtRoot] using supportEq)) (by
            simpa [leftAtRoot, rightAtRoot] using typeEq) childDeclaration
          rhoReflectivePresentation (by
            simpa [leftAtRoot, rightAtRoot] using canonical) parentMeasure (by
            simpa [leftAtRoot, rightAtRoot] using smaller) (by
            simpa [rightAtRoot] using rightAdmissible) closeSmaller depth)
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomEnvironment.reifyName,
    CostStaticPlanStopped.boundaryOccurrence_name,
    leftSelectedBoundary, rightSelectedBoundary] using restores

/-- Close any pair of reached certified boundary plans once their exact
boundary views have been exposed.  Applications and collections share this
semantic proof: the views identify the singleton entries, while the retained
type route supplies admissibility of the reached target fibre. -/
noncomputable def boundaryViews_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftBoundary : leftReached.BoundaryView)
    (rightBoundary : rightReached.BoundaryView)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftBoundary.stopped.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa only [leftBoundary.entries_eq] using leftEmbedding
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightBoundary.stopped.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa only [rightBoundary.entries_eq] using rightEmbedding
  have supportEq :
      leftBoundary.stopped.certified.typed.boundary.targetSupport =
        rightBoundary.stopped.certified.typed.boundary.targetSupport :=
    leftBoundary.targetSupport_eq.trans
      (sourceAvailableEq.trans rightBoundary.targetSupport_eq.symm)
  have targetTypeEq :
      leftBoundary.stopped.certified.typed.boundary.targetType =
        rightBoundary.stopped.certified.typed.boundary.targetType :=
    leftBoundary.targetType_eq.trans
      ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
        rightBoundary.targetType_eq.symm)
  have canonical : canonicalize childDeclaration
        leftBoundary.stopped.certified.typed.boundary.content =
      canonicalize childDeclaration
        rightBoundary.stopped.certified.typed.boundary.content := by
    rw [leftBoundary.content_eq, rightBoundary.content_eq]
    exact rawAligned.canonicalize_eq childDeclaration stopCanonical
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries :=
    leftEmbedding'.subset (by simp)
  have rightMember : rightBoundary.stopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries :=
    rightEmbedding'.subset (by simp)
  have leftSmaller :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot
      leftNode.rootStatic leftBoundary.stopped.certified.typed leftMember
  have rightSmaller :=
    rightNode.plan.boundary_content_size_lt_of_isStaticRoot
      rightNode.rootStatic rightBoundary.stopped.certified.typed rightMember
  have smaller :
      sizeOf leftBoundary.stopped.certified.typed.boundary.content +
          sizeOf rightBoundary.stopped.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
    omega
  obtain ⟨rightRoute⟩ := rightRoute
  have rightEndpointAdmissible :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalTypeRoute.rho_admissible
      rightRoute rightRootAdmissible
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightBoundary.stopped.certified.typed.boundary.targetType := by
    rw [rightBoundary.targetType_eq]
    exact rightEndpointAdmissible
  simpa only [leftBoundary.abstract_eq, rightBoundary.abstract_eq,
    CostStaticPlanStopped.boundaryOccurrence_name] using
    boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode rightNode
      leftTrees rightTrees leftEnvironment rightEnvironment
      leftBoundary.stopped rightBoundary.stopped leftEmbedding' rightEmbedding'
      supportEq targetTypeEq childDeclaration canonical
      (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
      rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth

/-- Close a pair of reached foreign-application plans.

At a foreign application the reached payload is itself the sole certified
boundary content, while the plan abstraction is the boundary atom.  The
retained application typing forces a base target fibre, so recursive-domain
admissibility is local and does not require a route witness from the root. -/
noncomputable def boundaryApplications_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftClass : leftReached.plan.rootClass = .boundaryApplication)
    (rightClass : rightReached.plan.rootClass = .boundaryApplication)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  rcases leftReached with
    ⟨leftSourceBound, leftTargetBound, leftThinning, leftAvailable,
      leftOuter, leftSourceType, leftPlan, leftSkeletonContext,
      leftAbstractEq⟩
  rcases rightReached with
    ⟨rightSourceBound, rightTargetBound, rightThinning, rightAvailable,
      rightOuter, rightSourceType, rightPlan, rightSkeletonContext,
      rightAbstractEq⟩
  cases leftPlan with
  | @boundaryApplication _ _ _ _ _ leftWire leftArguments _
      leftConstructor leftRendered leftOutside leftCertified leftCertifies =>
    cases rightPlan with
    | @boundaryApplication _ _ _ _ _ rightWire rightArguments _
        rightConstructor rightRendered rightOutside rightCertified
          rightCertifies =>
      let leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.apply leftWire leftArguments) leftNode.plan.abstractPattern :=
        { boundarySupport := leftAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) leftSourceType
          content := .apply leftWire leftArguments
          certified := leftCertified
          certifies := leftCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := leftSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using leftAbstractEq }
      let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.apply rightWire rightArguments) rightNode.plan.abstractPattern :=
        { boundarySupport := rightAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) rightSourceType
          content := .apply rightWire rightArguments
          certified := rightCertified
          certifies := rightCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := rightSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using rightAbstractEq }
      have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [leftStopped.certified.typed]
            leftNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [leftCertified.typed] leftNode.plan.boundaryTable.entries at leftEmbedding
        exact leftEmbedding
      have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [rightStopped.certified.typed]
            rightNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [rightCertified.typed] rightNode.plan.boundaryTable.entries at rightEmbedding
        exact rightEmbedding
      have supportEq : leftStopped.certified.typed.boundary.targetSupport =
          rightStopped.certified.typed.boundary.targetSupport := by
        exact leftCertified.targetSupport_eq.trans
          (sourceAvailableEq.trans rightCertified.targetSupport_eq.symm)
      have targetTypeEq : leftStopped.certified.typed.boundary.targetType =
          rightStopped.certified.typed.boundary.targetType := by
        exact leftCertified.targetType_eq.trans
          ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
            rightCertified.targetType_eq.symm)
      have canonical : canonicalize childDeclaration
            leftStopped.certified.typed.boundary.content =
          canonicalize childDeclaration
            rightStopped.certified.typed.boundary.content := by
        rw [leftCertified.content_eq, rightCertified.content_eq]
        exact rawAligned.canonicalize_eq childDeclaration stopCanonical
      have leftMember : leftStopped.certified.typed ∈
          leftNode.plan.boundaryTable.entries :=
        leftEmbedding'.subset (by simp)
      have rightMember : rightStopped.certified.typed ∈
          rightNode.plan.boundaryTable.entries :=
        rightEmbedding'.subset (by simp)
      have leftSmaller :=
        leftNode.plan.boundary_content_size_lt_of_isStaticRoot
          leftNode.rootStatic leftStopped.certified.typed leftMember
      have rightSmaller :=
        rightNode.plan.boundary_content_size_lt_of_isStaticRoot
          rightNode.rootStatic rightStopped.certified.typed rightMember
      have smaller :
          sizeOf leftStopped.certified.typed.boundary.content +
              sizeOf rightStopped.certified.typed.boundary.content <
            sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
        omega
      obtain ⟨rightCategory, rightTypeBase⟩ :=
        rightCertified.exists_targetType_eq_base_of_application
      have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          rightStopped.certified.typed.boundary.targetType := by
        rw [rightTypeBase]
        exact rhoCanonicalRecursiveTypeDomain.base rightCategory
      exact boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode
        rightNode leftTrees rightTrees leftEnvironment rightEnvironment
        leftStopped rightStopped leftEmbedding' rightEmbedding' supportEq
        targetTypeEq childDeclaration canonical
        (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
        rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth
    | bvar | fvar | application | lambda | multiLambda | collection |
        boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at rightClass
  | bvar | fvar | application | lambda | multiLambda | collection |
      boundaryCollection =>
    simp [CostStaticRegionPlan.rootClass] at leftClass

/-- Close a pair of reached foreign-collection plans.

Unlike a foreign application, a certified collection boundary may inhabit
either a structural collection fibre or an authored bare-collection base
fibre.  The retained type route is therefore the authoritative admissibility
witness: it transports the admissible root fibre to the exact reached source
type, and certification identifies that type with the boundary target. -/
noncomputable def boundaryCollections_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftClass : leftReached.plan.rootClass = .boundaryCollection)
    (rightClass : rightReached.plan.rootClass = .boundaryCollection)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  rcases leftReached with
    ⟨leftSourceBound, leftTargetBound, leftThinning, leftAvailable,
      leftOuter, leftSourceType, leftPlan, leftSkeletonContext,
      leftAbstractEq⟩
  rcases rightReached with
    ⟨rightSourceBound, rightTargetBound, rightThinning, rightAvailable,
      rightOuter, rightSourceType, rightPlan, rightSkeletonContext,
      rightAbstractEq⟩
  cases leftPlan with
  | @boundaryCollection _ _ _ _ _ leftCollectionType leftElements leftRest
      leftSourceType leftCurrentRejected leftOppositeChoice
      leftOppositeSelected leftCertified leftCertifies =>
    cases rightPlan with
    | @boundaryCollection _ _ _ _ _ rightCollectionType rightElements
        rightRest rightSourceType rightCurrentRejected rightOppositeChoice
        rightOppositeSelected rightCertified rightCertifies =>
      let leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.collection leftCollectionType leftElements leftRest)
          leftNode.plan.abstractPattern :=
        { boundarySupport := leftAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) leftSourceType
          content := .collection leftCollectionType leftElements leftRest
          certified := leftCertified
          certifies := leftCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := leftSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using leftAbstractEq }
      let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.collection rightCollectionType rightElements rightRest)
          rightNode.plan.abstractPattern :=
        { boundarySupport := rightAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) rightSourceType
          content := .collection rightCollectionType rightElements rightRest
          certified := rightCertified
          certifies := rightCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := rightSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using rightAbstractEq }
      have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [leftStopped.certified.typed]
            leftNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [leftCertified.typed] leftNode.plan.boundaryTable.entries at leftEmbedding
        exact leftEmbedding
      have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [rightStopped.certified.typed]
            rightNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [rightCertified.typed] rightNode.plan.boundaryTable.entries at rightEmbedding
        exact rightEmbedding
      have supportEq : leftStopped.certified.typed.boundary.targetSupport =
          rightStopped.certified.typed.boundary.targetSupport := by
        exact leftCertified.targetSupport_eq.trans
          (sourceAvailableEq.trans rightCertified.targetSupport_eq.symm)
      have targetTypeEq : leftStopped.certified.typed.boundary.targetType =
          rightStopped.certified.typed.boundary.targetType := by
        exact leftCertified.targetType_eq.trans
          ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
            rightCertified.targetType_eq.symm)
      have canonical : canonicalize childDeclaration
            leftStopped.certified.typed.boundary.content =
          canonicalize childDeclaration
            rightStopped.certified.typed.boundary.content := by
        rw [leftCertified.content_eq, rightCertified.content_eq]
        exact rawAligned.canonicalize_eq childDeclaration stopCanonical
      have leftMember : leftStopped.certified.typed ∈
          leftNode.plan.boundaryTable.entries :=
        leftEmbedding'.subset (by simp)
      have rightMember : rightStopped.certified.typed ∈
          rightNode.plan.boundaryTable.entries :=
        rightEmbedding'.subset (by simp)
      have leftSmaller :=
        leftNode.plan.boundary_content_size_lt_of_isStaticRoot
          leftNode.rootStatic leftStopped.certified.typed leftMember
      have rightSmaller :=
        rightNode.plan.boundary_content_size_lt_of_isStaticRoot
          rightNode.rootStatic rightStopped.certified.typed rightMember
      have smaller :
          sizeOf leftStopped.certified.typed.boundary.content +
              sizeOf rightStopped.certified.typed.boundary.content <
            sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
        omega
      obtain ⟨rightRoute⟩ := rightRoute
      have rightEndpointAdmissible :=
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalTypeRoute.rho_admissible
          rightRoute rightRootAdmissible
      have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          rightStopped.certified.typed.boundary.targetType := by
        rw [rightCertified.targetType_eq]
        exact rightEndpointAdmissible
      exact boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode
        rightNode leftTrees rightTrees leftEnvironment rightEnvironment
        leftStopped rightStopped leftEmbedding' rightEmbedding' supportEq
        targetTypeEq childDeclaration canonical
        (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
        rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth
    | bvar | fvar | boundaryApplication | application | lambda | multiLambda |
        collection =>
      simp [CostStaticRegionPlan.rootClass] at rightClass
  | bvar | fvar | boundaryApplication | application | lambda | multiLambda |
      collection =>
    simp [CostStaticRegionPlan.rootClass] at leftClass

end RhoStaticPlanBoundaryRestoration

namespace RhoStaticPlanStopCommonApex

/-- Extend an apex-aware callback for stops with at least one authored-source
root to every plan stop.  Certified-boundary pairs retain their already-proved
uniform leaf relation and are lifted only at the requested apex depth. -/
noncomputable def of_nonBoundaryRemainder
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
          childAvailable childOuter leftChild rightChild childType))
    (remaining : RhoStaticNonBoundaryPlanStopCommonApex leftView rightView
      declarationColor rawStop) :
    RhoStaticPlanStopCommonApex leftView rightView declarationColor rawStop := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  intro callbackAvailable callbackScope callbackRoot leftAbstract
    rightAbstract stopped
  rcases stopped with
    ⟨leftPayload, rightPayload, leftReached, rightReached,
      leftAdmission, rightAdmission, leftAbstractEq, rightAbstractEq,
      sourceTypeEq, sourceAvailableEq, sourceBoundEq, targetBoundEq, thinningEq,
      leftEmbedding, rightEmbedding, leftRoute, rightRoute, stopReason,
      leftPayloadSizeLe, rightPayloadSizeLe, rawAligned⟩
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  by_cases leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary
  · by_cases rightBoundary : rightReached.plan.rootClass.IsCertifiedBoundary
    · obtain ⟨leftBoundaryView⟩ :=
        leftReached.nonempty_boundaryView_of_boundaryClass leftBoundary
      obtain ⟨rightBoundaryView⟩ :=
        rightReached.nonempty_boundaryView_of_boundaryClass rightBoundary
      obtain ⟨leftEmbedding⟩ := leftEmbedding
      obtain ⟨rightEmbedding⟩ := rightEmbedding
      have boundaryResult :=
        RhoStaticPlanBoundaryRestoration.boundaryViews_sourcePatternLeafAligned_of_closeSmaller
          leftView.node rightView.node leftView.children rightView.children
          leftEnvironment rightEnvironment leftReached rightReached
          leftBoundaryView rightBoundaryView sourceTypeEq sourceAvailableEq
          leftEmbedding rightEmbedding rightRoute rightRootAdmissible
          rawDeclaration rawAligned stopCanonical (fun leftWellSorted
            rightWellSorted canonical smaller admissible => by
              obtain ⟨result⟩ := closeSmaller leftWellSorted rightWellSorted
                canonical smaller admissible
              exact ⟨result.pair⟩)
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          callbackAvailable callbackScope
      have sourceAligned := by
        simpa only [leftAbstractEq, rightAbstractEq] using boundaryResult
      exact ofSourcePatternLeafAligned leftView.node rightView.node
        (leftView.targetBound_eq_targetBound rightView) leftEnvironment
        rightEnvironment sourceAligned callbackScope callbackRoot
    · exact remaining callbackAvailable callbackScope callbackRoot leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute rightRoute stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned
        (fun both => rightBoundary both.2)
  · exact remaining callbackAvailable callbackScope callbackRoot leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned
      (fun both => leftBoundary both.1)

/-- Integrated plan-stop constructor through same-colour Quote and mixed-stop
milestones.  It closes the certified-boundary quadrant, consumes every
delegated same-colour raw leaf, proves the same-colour Quote terminal, and
recurses on any remaining same-colour stop with one certified-boundary side. -/
noncomputable def ofRecursiveSameColorQuotePair
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
          childAvailable childOuter leftChild rightChild childType))
    (remaining :
      RhoStaticNonBoundaryPlanStopCommonApex.AfterSameColorBoundarySide leftView
        rightView declarationColor) :
    RhoStaticPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) := by
  apply RhoStaticPlanStopCommonApex.of_nonBoundaryRemainder leftView rightView
    declarationColor rightRootAdmissible
  · intro left right stopped
    exact stopped.1.2
  · exact closeSmaller
  · apply RhoStaticNonBoundaryPlanStopCommonApex.preferSameColorAlignedLeaf
      leftView rightView declarationColor rightRootAdmissible closeSmaller
    exact RhoStaticNonBoundaryPlanStopCommonApex.ofRecursiveSameColorQuotePair
      leftView rightView declarationColor rightRootAdmissible closeSmaller
      (RhoStaticNonBoundaryPlanStopCommonApex.ofRecursiveSameColorBoundarySide
        leftView rightView declarationColor rightRootAdmissible closeSmaller
        remaining)

end RhoStaticPlanStopCommonApex

namespace RhoMatchedStaticFramesApex

/-- Construct the exact matched-frame apex from raw canonical descent.
Membership-certified source variables are discharged internally; plan stops
remain as the sole semantic callback. -/
noncomputable def ofProvenancedRawAlignment
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) rawStop
      leftView.node.term.1 rightView.node.term.1)
    (callback : RhoStaticPlanStopCommonApex leftView rightView declarationColor
      rawStop) :
    RhoMatchedStaticFramesApex leftView rightView := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have sourceApex :=
    leftView.node.reifiedSourceProvenancedCommonApex_of_rawAlignment
      rho_collectionChoiceDeterministic rhoReflectivePresentation
      rawDeclaration rightView.node leftEnvironment rightEnvironment
      (leftView.targetBound_eq_targetBound rightView)
      (leftView.sourceSort_eq_sourceSort rightView) rawAligned
      (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
      (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
      leftView.node.targetBound.length 0 leftView.node.targetBound.length
      (fun callbackAvailable callbackScope callbackRoot {left right} stopped =>
        by
          rcases stopped with stopped | ⟨name, leftMembership,
            rightMembership⟩
          · exact callback callbackAvailable callbackScope callbackRoot stopped
          · have apex := memberFVar_commonRestorationApex leftView.node
              rightView.node leftView.children rightView.children
              leftEnvironment rightEnvironment name leftMembership
              rightMembership targetDeclaration callbackRoot
            simpa [canonicalizeByDepths, mapPattern,
              CostStaticBinderThinning.thickenAmbientBVars,
              CostStaticAtomKeyCospan.reifyLeft,
              CostStaticAtomKeyCospan.reifyRight, targetDeclaration,
              costStaticReflectivePresentationDecl_eq_map] using apex)
  have leftCovered : leftEnvironment.Covers
      (leftView.node.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftView.node.reifyTargetFrame_atomCovered leftEnvironment name
      membership
  have rightCovered : rightEnvironment.Covers
      (rightView.node.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightView.node.reifyTargetFrame_atomCovered rightEnvironment name
      membership
  have leftNaturality :=
    leftEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.leftSlot cospan.leftCommutes targetDeclaration
      leftView.node.targetBound.length
      (leftView.node.reifyTargetFrame leftEnvironment) leftCovered
  have rightNaturality :=
    rightEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.rightSlot cospan.rightCommutes targetDeclaration
      rightView.node.targetBound.length
      (rightView.node.reifyTargetFrame rightEnvironment) rightCovered
  have leftFrame :=
    canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize leftView.node
      leftEnvironment
  have rightFrame :=
    canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize rightView.node
      rightEnvironment
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex _ _ sourceApex
  · exact (congrArg (cospan.reifyLeft leftEnvironment.lookupAtom?)
      leftFrame.symm).trans leftNaturality
  · rw [leftView.targetBound_length_eq_targetBound_length rightView]
    exact (congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
      rightFrame.symm).trans rightNaturality

end RhoMatchedStaticFramesApex

namespace RhoCanonicalStaticPairSemanticCut

/-- The matched provider arm reduced to its sole plan-stop restoration
obligation.  Raw canonical descent, free-variable restoration, and the final
matched cut are assembled here. -/
noncomputable def matchedOfProvenancedPlanStops
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (roots : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern rightPattern)
    (_canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (planStops :
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
      RhoStaticPlanStopCommonApex leftView rightView declarationColor
        (fun candidateLeft candidateRight =>
          ((CollapsingRoot declaration candidateLeft ∨
              CollapsingRoot declaration candidateRight) ∧
            canonicalize declaration candidateLeft =
              canonicalize declaration candidateRight) ∧
          sizeOf candidateLeft + sizeOf candidateRight <
            sizeOf leftPattern + sizeOf rightPattern)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.aligned color leftView rightView roots) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have nodeRoots : CanonicalRootAligned declaration leftView.node.term.1
      rightView.node.term.1 := by
    rw [leftView.patternEq, rightView.patternEq]
    exact roots
  let rawAligned := canonicalStopAligned_of_root_aligned declaration nodeRoots
  exact matchedOfApex leftView rightView roots
    (RhoMatchedStaticFramesApex.ofProvenancedRawAlignment leftView rightView
      declarationColor (by
        simpa [declaration, leftView.patternEq, rightView.patternEq] using
          rawAligned)
      planStops)

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
