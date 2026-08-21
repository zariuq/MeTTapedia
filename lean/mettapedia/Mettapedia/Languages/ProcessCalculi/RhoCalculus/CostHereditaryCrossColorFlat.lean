import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness

/-!
# The cross-colour flat residual: root shape in the shared name fibre

`RhoCollapsingCrossColorFramesRestoreTogetherInDomain` quantifies over two
different-colour static root views of one generated type.  The shared fibre
is the `Name` fibre, and rho declares exactly one `Name` constructor, so both
roots are that view's own colour spelling of the authored quotation.

This module records that root shape and the consequences the flat residual's
remaining premises then have.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## The coloured quotation constructor -/

/-- Either colour's declared quote constructor is that colour's spelling of
the authored rho quotation. -/
theorem rhoDecl_quoteConstructor (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor =
      (color.symbols rhoCIGSLT).constructor "NQuote" := by
  cases color <;> rfl

/-- The two colours spell the authored quotation differently. -/
theorem rhoDecl_quoteConstructor_ne_of_color_ne
    {leftColor rightColor : CostStaticColor} (different : leftColor ≠ rightColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor := by
  cases leftColor <;> cases rightColor
  · exact absurd rfl different
  · decide
  · decide
  · exact absurd rfl different

/-! ## Every `Name`-fibre static root is that colour's quotation -/

/-- **Root shape of a `Name`-fibre static plan.**

The `Name` fibre admits no bare-collection root
(`rho_costStaticCollectionTypingChoices_name_eq_nil`), so a static root there
is an application, and rho declares exactly one `Name` constructor, so the
authored label at that root is the quotation.  Both the generated pattern and
the authored skeleton are therefore pinned. -/
theorem rhoNameFibre_staticRoot_shape
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rootStatic : plan.isStaticRoot = true)
    (nameSort : sourceType = .base "Name") :
    ∃ arguments skeletonArguments,
      pattern =
          .apply ((color.symbols rhoCIGSLT).constructor "NQuote") arguments ∧
        plan.abstractPattern = .apply "NQuote" skeletonArguments := by
  cases plan with
  | bvar | fvar | boundaryApplication | lambda | multiLambda |
      boundaryCollection =>
      simp [CostStaticRegionPlan.isStaticRoot] at rootStatic
  | collection choice selected children =>
      subst nameSort
      rw [rho_costStaticCollectionTypingChoices_name_eq_nil] at selected
      simp at selected
  | application constructor rendered current preimage notBare children =>
      rename_i wireName arguments
      have categoryEq : preimage.sourceConstructor.1.category = "Name" :=
        TypeExpr.base.inj nameSort
      have label : preimage.sourceConstructor.1.label = "NQuote" :=
        rhoCalc_label_eq_quote_of_category_name preimage.sourceConstructor.2
          categoryEq
      refine ⟨arguments, children.abstractPatterns, ?_, ?_⟩
      · rw [← rendered, ← rhoCIGSLT.materializeDeclaredCostConstructor_label
          constructor, preimage.labelMap, label]
      · show Pattern.apply preimage.sourceConstructor.1.label
            children.abstractPatterns = _
        exact congrArg (fun head => Pattern.apply head children.abstractPatterns)
          label

/-- **Root shape of a `Name`-fibre static root view.**

`CostRegionTree.StaticRootView` exposes the node's plan through its
reindexings, so the view's own pattern and the node's authored skeleton are
pinned by the plan-level shape above. -/
theorem rhoNameFibre_view_shape
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type}
    {color : CostStaticColor} (view : tree.StaticRootView color)
    (nameSort : view.node.sourceSort.1 = "Name") :
    ∃ arguments skeletonArguments,
      pattern =
          .apply ((color.symbols rhoCIGSLT).constructor "NQuote") arguments ∧
        view.node.skeleton.1 = .apply "NQuote" skeletonArguments := by
  obtain ⟨arguments, skeletonArguments, patternShape, skeletonShape⟩ :=
    rhoNameFibre_staticRoot_shape view.node.plan view.node.rootStatic
      (congrArg TypeExpr.base nameSort)
  refine ⟨arguments, skeletonArguments, ?_, ?_⟩
  · rw [← view.patternEq]
    exact patternShape
  · rw [view.node.skeleton_pattern]
    exact skeletonShape

/-! ## The declaration colour is pinned by the collapsing premise -/

/-- The two colours' spellings of the authored quotation are distinct, so a
quotation head determines its colour. -/
theorem rhoQuoteSpelling_color_eq
    {leftColor rightColor : CostStaticColor}
    (spelling : (leftColor.symbols rhoCIGSLT).constructor "NQuote" =
      (rightColor.symbols rhoCIGSLT).constructor "NQuote") :
    leftColor = rightColor := by
  cases leftColor <;> cases rightColor
  · rfl
  · exact absurd spelling (by decide)
  · exact absurd spelling (by decide)
  · rfl

/-- **A collapsing `Name`-fibre root is the declaration colour's own root.**

The parallel disjunct of `CollapsingRoot` cannot fire at an application, and
the quote disjunct forces the root's colour spelling to be the declaration's,
hence the two colours to agree. -/
theorem rhoNameFibre_collapsingRoot_color_eq
    {declarationColor color : CostStaticColor} {arguments : List Pattern}
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      (.apply ((color.symbols rhoCIGSLT).constructor "NQuote") arguments)) :
    declarationColor = color := by
  rcases collapsing with ⟨quoteArguments, shape⟩ | ⟨elements, shape⟩
  · injection shape with headEq _
    exact rhoQuoteSpelling_color_eq
      ((rhoDecl_quoteConstructor declarationColor).symm.trans headEq.symm)
  · exact absurd shape (by simp)

/-- **The cross-colour collapsing premise selects exactly one side.**

With two different-colour `Name`-fibre roots, the declaration colour is the
colour of whichever root the premise declares collapsing; the other root is
not collapsing at that declaration. -/
theorem rhoCrossColorNameFibre_declarationColor_eq
    {declarationColor leftColor rightColor : CostStaticColor}
    {leftArguments rightArguments : List Pattern}
    (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply ((leftColor.symbols rhoCIGSLT).constructor "NQuote")
          leftArguments) ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply ((rightColor.symbols rhoCIGSLT).constructor "NQuote")
          rightArguments)) :
    declarationColor = leftColor ∨ declarationColor = rightColor :=
  collapsing.imp rhoNameFibre_collapsingRoot_color_eq
    rhoNameFibre_collapsingRoot_color_eq

/-! ## What canonical equality then forces -/

/-- **The collapse equation of the cross-colour `Name` fibre.**

At the declaration colour the partner root is an opaque application, so the
canonical equality cannot be met by the quote-preserving arm of
`finishNormalizeReflectiveApply`.  The declaration-coloured root therefore has
exactly one argument, and that argument canonicalizes to a drop of the
partner's canonical form. -/
theorem rhoNameFibre_collapse_equation
    {declarationColor partnerColor : CostStaticColor}
    (different : declarationColor ≠ partnerColor)
    {arguments partnerArguments : List Pattern}
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.apply ((declarationColor.symbols rhoCIGSLT).constructor "NQuote")
            arguments) =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.apply ((partnerColor.symbols rhoCIGSLT).constructor "NQuote")
            partnerArguments)) :
    ∃ argument, arguments = [argument] ∧
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          argument =
        .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor
          [canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation.toReflectivePresentationDecl)
            (.apply ((partnerColor.symbols rhoCIGSLT).constructor "NQuote")
              partnerArguments)] := by
  set declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
    with declarationEq
  have partnerNe : (partnerColor.symbols rhoCIGSLT).constructor "NQuote" ≠
      declaration.quoteConstructor := by
    rw [declarationEq, rhoDecl_quoteConstructor]
    intro spelling
    exact different (rhoQuoteSpelling_color_eq spelling).symm
  have partnerCanonical := canonicalize_apply_of_ne_quote declaration partnerNe
    partnerArguments
  have quoteHead : (declarationColor.symbols rhoCIGSLT).constructor "NQuote" =
      declaration.quoteConstructor := (rhoDecl_quoteConstructor _).symm
  rw [quoteHead, canonicalize_apply_eq_finish] at canonical
  rcases finishNormalizeReflectiveApply_quote_cases declaration
      (arguments.map (canonicalize declaration)) with
    ⟨inner, mappedEq, resultEq⟩ | resultEq
  · rw [resultEq] at canonical
    obtain ⟨argument, argumentsEq, canonicalArgument⟩ :
        ∃ argument, arguments = [argument] ∧
          canonicalize declaration argument =
            .apply declaration.dropConstructor [inner] := by
      cases arguments with
      | nil => simp at mappedEq
      | cons head tail =>
          cases tail with
          | nil => exact ⟨head, rfl, by simpa using mappedEq⟩
          | cons second rest => simp at mappedEq
    exact ⟨argument, argumentsEq, by rw [canonicalArgument, canonical]⟩
  · rw [resultEq, partnerCanonical] at canonical
    injection canonical with headEq _
    exact absurd headEq.symm partnerNe

/-! ## The rigid quadrant is an obstruction, not a case

Both canonical frames being applications is refutable outright: reification and
supported substitution both preserve an application head, and one wire name
cannot lie in two colour namespaces.  Any proof of the flat residual must
therefore show that quadrant empty; it cannot discharge it. -/

/-- **Two different-colour application frames never restore together.** -/
theorem not_restoresTogether_reifyWith_apply_apply
    {leftColor rightColor : CostStaticColor} (different : leftColor ≠ rightColor)
    {leftWire rightWire leftSource rightSource : String}
    (leftDecoded :
      decodeCostStaticConstructor leftColor leftWire = some leftSource)
    (rightDecoded :
      decodeCostStaticConstructor rightColor rightWire = some rightSource)
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftEndpoint))
    (rightResolve : String → Option (Fin rightEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (leftArguments rightArguments : List Pattern) :
    ¬ ReflectiveContextSupport.RestoresTogether profile support assignment
        (cospan.reifyWith leftResolve leftLeg
          (.apply leftWire leftArguments))
        (cospan.reifyWith rightResolve rightLeg
          (.apply rightWire rightArguments)) := by
  intro restores
  have restored := restores 0
  simp only [CostStaticAtomKeyCospan.reifyWith,
    ReflectiveContextSupport.substituteAt, Pattern.apply.injEq] at restored
  exact decodeCostStaticConstructor_color_disjoint different leftDecoded
    (restored.1 ▸ rightDecoded)

/-- **At least one cross-colour canonical frame is a leaf.**

Combining the frame-shape classification with the previous theorem: if the
flat residual's conclusion holds at a cross-colour `Name`-fibre pair, the two
canonical frames cannot both be applications.  This is the quadrant a proof
of the residual has to show empty — it is not a case that can be discharged
by any restoration argument. -/
theorem rhoCrossColorNameFibre_leaf_frame_of_restoresTogether
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (leftName : leftView.node.sourceSort.1 = "Name")
    (rightName : rightView.node.sourceSort.1 = "Name")
    (restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile
          ((CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
            ).commonSupport
          ((CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
            ).commonAssignment
          (((CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
            ).reifyWith
            (CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
              ).lookupAtom?
            ((CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
              ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
                (rightView.node.semanticAtomEnvironment
                  (rightView.children.normalizeValues
                    (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
              ).leftSlot
            (leftView.node.canonicalizeReifiedTargetFrame
              (CostStaticAtomEnvironment.ofInventory
                (leftView.node.semanticAtomEnvironment
                  (leftView.children.normalizeValues
                    (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
              (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
                rhoReflectivePresentation.toReflectivePresentationDecl)))
          (((CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
            ).reifyWith
            (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
              ).lookupAtom?
            ((CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
              ).semanticKeyCospan (CostStaticAtomEnvironment.ofInventory
                (rightView.node.semanticAtomEnvironment
                  (rightView.children.normalizeValues
                    (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
              ).rightSlot
            (rightView.node.canonicalizeReifiedTargetFrame
              (CostStaticAtomEnvironment.ofInventory
                (rightView.node.semanticAtomEnvironment
                  (rightView.children.normalizeValues
                    (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
              (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
                rhoReflectivePresentation.toReflectivePresentationDecl)))) :
    (∃ index, leftView.node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
            rhoReflectivePresentation.toReflectivePresentationDecl) =
        .bvar index) ∨
      (∃ name, leftView.node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
            rhoReflectivePresentation.toReflectivePresentationDecl) =
        .fvar name) ∨
      (∃ index, rightView.node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (rightView.node.semanticAtomEnvironment
              (rightView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
            rhoReflectivePresentation.toReflectivePresentationDecl) =
        .bvar index) ∨
      (∃ name, rightView.node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (rightView.node.semanticAtomEnvironment
              (rightView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
            rhoReflectivePresentation.toReflectivePresentationDecl) =
        .fvar name) := by
  rcases rhoNameFibre_canonicalFrame_shape leftView.node
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 leftName with
    leftBVar | leftFVar | ⟨leftWire, leftArguments, leftSource, leftEq,
      leftDecoded⟩
  · exact Or.inl leftBVar
  · exact Or.inr (Or.inl leftFVar)
  · rcases rhoNameFibre_canonicalFrame_shape rightView.node
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        rightName with
      rightBVar | rightFVar | ⟨rightWire, rightArguments, rightSource, rightEq,
        rightDecoded⟩
    · exact Or.inr (Or.inr (Or.inl rightBVar))
    · exact Or.inr (Or.inr (Or.inr rightFVar))
    · rw [leftEq, rightEq] at restores
      exact absurd restores
        (not_restoresTogether_reifyWith_apply_apply different leftDecoded
          rightDecoded _ _ _ _ _ _ _ _ leftArguments rightArguments)

/-! ## Depth invariance where it actually holds -/

/-- Either colour's rho quotation is a quote constructor of the whole Cost
reflection profile, so supported substitution resets the available depth
beneath it. -/
theorem rho_isQuoteConstructor_colorQuote (color : CostStaticColor) :
    ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile
        ((color.symbols rhoCIGSLT).constructor "NQuote") = true := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  apply List.any_eq_true.mpr
  refine ⟨costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl,
    CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile color, ?_⟩
  cases color <;> rfl

/-- **A quotation head absorbs the ambient depth.**

Supported reflective substitution hands zero available depth to the arguments
of a quotation, so a quotation-rooted pattern restores identically at every
depth.  Reification through a cospan leg keeps the head, so this applies
directly to the reified canonical frames of the flat residual. -/
theorem substituteAt_reifyWith_quote_depth_invariant
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (color : CostStaticColor) (arguments : List Pattern)
    (firstDepth secondDepth : Nat) :
    ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile support assignment firstDepth
        (cospan.reifyWith resolve leg
          (.apply ((color.symbols rhoCIGSLT).constructor "NQuote")
            arguments)) =
      ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile support assignment secondDepth
        (cospan.reifyWith resolve leg
          (.apply ((color.symbols rhoCIGSLT).constructor "NQuote")
            arguments)) := by
  simp only [CostStaticAtomKeyCospan.reifyWith,
    ReflectiveContextSupport.substituteAt,
    rho_isQuoteConstructor_colorQuote color, if_true]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
