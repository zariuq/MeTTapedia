import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorFlat

/-!
# The cross-colour leaf hinge

The flat form of obligation A2x
(`RhoCollapsingCrossColorFramesRestoreTogetherInDomain`) is, by the existing
equivalence, exactly the cross-colour collapsing residual.  Its conclusion is
a depth-uniform restoration equation between the two reified canonical
frames.  Two cross-colour application frames can never restore together
(`not_restoresTogether_reifyWith_apply_apply`), so every proof of the flat
residual must pass through one decisive hinge:

**the declaration-coloured collapsing side's canonical frame is a leaf** —
a semantic atom or a bound variable — not an application.

This module develops that hinge in the oriented form.  The first section
packages the telescope's colour/orientation plumbing: under the Name-fibre
premises, the declaration colour is pinned to the collapsing side, that
side's pattern is its own colour's quotation of exactly one argument, and
the argument canonicalizes to a drop of the partner's canonical form
(`rhoCrossColor_orientedPack_left/right`).  Later sections descend the
actual static plan from these packed premises.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostHereditaryCrossColorLeafHinge

/-- **Left-collapsing orientation pack.**

Under the Name-fibre cross-colour telescope with the collapse declared on
the left: the declaration colour is the left colour, the left pattern is
the left colour's quotation of exactly one argument, and that argument
canonicalizes at the declaration colour to a drop of the partner's
canonical form. -/
theorem rhoCrossColor_orientedPack_left
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (sourceSortEq : leftView.node.sourceSort.1 = rightView.node.sourceSort.1)
    (notInteracting : leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (canonical :
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    ∃ argument, declarationColor = leftColor ∧
      leftPattern =
        .apply ((leftColor.symbols rhoCIGSLT).constructor "NQuote")
          [argument] ∧
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
          rightPattern] := by
  have leftName : leftView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting notInteracting
  have rightName : rightView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting (sourceSortEq ▸ notInteracting)
  obtain ⟨leftArguments, _, leftPatternShape, _⟩ :=
    rhoNameFibre_view_shape leftView leftName
  obtain ⟨rightArguments, _, rightPatternShape, _⟩ :=
    rhoNameFibre_view_shape rightView rightName
  have declEq : declarationColor = leftColor :=
    rhoNameFibre_collapsingRoot_color_eq (leftPatternShape ▸ collapsing)
  rw [leftPatternShape, rightPatternShape, ← declEq] at canonical
  obtain ⟨argument, argumentsEq, canonicalArgument⟩ :=
    rhoNameFibre_collapse_equation
      (fun h : declarationColor = rightColor => different
        (declEq.symm.trans h))
      canonical
  rw [← rightPatternShape] at canonicalArgument
  exact ⟨argument, declEq,
    leftPatternShape.trans (congrArg _ argumentsEq), canonicalArgument⟩

/-- **Right-collapsing orientation pack**: the mirror side of
`rhoCrossColor_orientedPack_left`. -/
theorem rhoCrossColor_orientedPack_right
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (sourceSortEq : leftView.node.sourceSort.1 = rightView.node.sourceSort.1)
    (notInteracting : leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (canonical :
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    ∃ argument, declarationColor = rightColor ∧
      rightPattern =
        .apply ((rightColor.symbols rhoCIGSLT).constructor "NQuote")
          [argument] ∧
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
          leftPattern] := by
  have leftName : leftView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting notInteracting
  have rightName : rightView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting (sourceSortEq ▸ notInteracting)
  obtain ⟨leftArguments, _, leftPatternShape, _⟩ :=
    rhoNameFibre_view_shape leftView leftName
  obtain ⟨rightArguments, _, rightPatternShape, _⟩ :=
    rhoNameFibre_view_shape rightView rightName
  have declEq : declarationColor = rightColor :=
    rhoNameFibre_collapsingRoot_color_eq (rightPatternShape ▸ collapsing)
  rw [leftPatternShape, rightPatternShape, ← declEq] at canonical
  obtain ⟨argument, argumentsEq, canonicalArgument⟩ :=
    rhoNameFibre_collapse_equation
      (fun h : declarationColor = leftColor => different (h.symm.trans declEq))
      canonical.symm
  rw [← leftPatternShape] at canonicalArgument
  exact ⟨argument, declEq,
    rightPatternShape.trans (congrArg _ argumentsEq), canonicalArgument⟩

/-! ## The root application plan under an oriented pack -/

/-- The rho quotation is a unary constructor.  Pinning the parameter arity
is what makes the root spine force a singleton child, before any
telescope premise is consulted. -/
theorem rhoCalc_params_length_eq_one_of_label_eq_quote
    {rule : Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule}
    (membership : rule ∈ rhoCalc.terms) (label : rule.label = "NQuote") :
    rule.params.length = 1 := by
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- An argument-plan spine has exactly as many abstract patterns as there
are argument slots, and as many argument slots as authored parameters. -/
theorem CostStaticArgumentPlan.abstractPatterns_length
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {wireName : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plans : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
        parameters) :
    plans.abstractPatterns.length = arguments.length ∧
      arguments.length = parameters.length := by
  induction parameters generalizing before arguments with
  | nil =>
      cases plans
      exact ⟨rfl, rfl⟩
  | cons parameter parameterRest inductionHypothesis =>
      cases plans with
      | cons _ _ _ tail =>
          obtain ⟨abstractLength, argumentLength⟩ :=
            inductionHypothesis tail
          simp [CostStaticArgumentPlan.abstractPatterns, abstractLength,
            argumentLength]

/-- **Every `Name`-fibre static root plan has exactly one child, at both
the generated pattern level and the authored skeleton level.**

No telescope premise is needed: rho declares `NQuote` with one parameter,
so the argument spine of any static application root at this fibre is a
singleton `cons` over `nil`.  The proof is done at variable plan indices
(Flat's recipe); the dependent spine is read off live in the application
arm. -/
theorem rhoCrossColor_staticRoot_singleton_plan
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rootStatic : plan.isStaticRoot = true)
    (nameSort : sourceType = .base "Name") :
    ∃ argument childAbstract,
      pattern =
        .apply ((color.symbols rhoCIGSLT).constructor "NQuote") [argument] ∧
      plan.abstractPattern = .apply "NQuote" [childAbstract] := by
  cases plan with
  | bvar | fvar | boundaryApplication | lambda | multiLambda |
      boundaryCollection =>
      simp [CostStaticRegionPlan.isStaticRoot] at rootStatic
  | collection choice selected children =>
      subst nameSort
      rw [rho_costStaticCollectionTypingChoices_name_eq_nil] at selected
      simp at selected
  | application constructor rendered current preimage notBare children =>
      have categoryEq : preimage.sourceConstructor.1.category = "Name" :=
        TypeExpr.base.inj nameSort
      have label : preimage.sourceConstructor.1.label = "NQuote" :=
        rhoCalc_label_eq_quote_of_category_name preimage.sourceConstructor.2
          categoryEq
      have paramsLength : preimage.sourceConstructor.1.params.length = 1 :=
        rhoCalc_params_length_eq_one_of_label_eq_quote
          preimage.sourceConstructor.2 label
      obtain ⟨abstractLength, argumentsLength⟩ :=
        CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
          children
      obtain ⟨argument, argumentsEq⟩ :=
        List.length_eq_one_iff.mp
          (argumentsLength.trans paramsLength)
      set childAbs := children.abstractPatterns with childAbsDef
      obtain ⟨childAbstract, abstractEq⟩ :
          ∃ childAbstract, childAbs = [childAbstract] :=
        List.length_eq_one_iff.mp
          (abstractLength.trans
            (argumentsLength.trans paramsLength))
      refine ⟨argument, childAbstract, ?_, ?_⟩
      · rw [argumentsEq, ← rendered,
          ← rhoCIGSLT.materializeDeclaredCostConstructor_label constructor,
          preimage.labelMap]
        exact congrArg (fun l =>
          Pattern.apply ((color.symbols rhoCIGSLT).constructor l) [argument])
          label
      · show Pattern.apply preimage.sourceConstructor.1.label childAbs = _
        rw [abstractEq]
        exact congrArg (Pattern.apply · [childAbstract]) label

/-- The view-level form of the root singleton: the built pattern and the
authored skeleton are both one-headed quotations. -/
theorem rhoCrossColor_rootSkeleton_singleton
    {leftColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (nameSort : leftView.node.sourceSort.1 = "Name") :
    ∃ argument childAbstract,
      leftPattern =
        .apply ((leftColor.symbols rhoCIGSLT).constructor "NQuote")
          [argument] ∧
      leftView.node.skeleton.1 = .apply "NQuote" [childAbstract] := by
  obtain ⟨argument, childAbstract, patternShape, abstractShape⟩ :=
    rhoCrossColor_staticRoot_singleton_plan leftView.node.plan
      leftView.node.rootStatic (congrArg TypeExpr.base nameSort)
  refine ⟨argument, childAbstract, ?_, ?_⟩
  · rw [← leftView.patternEq]
    exact patternShape
  · rw [leftView.node.skeleton_pattern]
    exact abstractShape

/-- **Frame degeneration at the quote/drop/boundary skeleton (endpoint
glue).**

When a node's authored skeleton is exactly the quote/drop spine over one
boundary variable, and its environment's atom inventory selects that
boundary variable at a slot, the canonical reified target frame is the
atom's own free variable.  This is the endpoint of the hinge: it lifts the
skeleton shape to the frame shape, mirroring the fixture's
`leftFrame_is_atom` chain at full generality. -/
theorem rhoCrossColor_frame_atom_of_quoteDrop_boundarySkeleton
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {boundaryVarName : String}
    (skeletonShape : node.skeleton.1 =
      .apply "NQuote" [.apply "PDrop" [.fvar boundaryVarName]])
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? boundaryVarName = some slot) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) =
      .fvar (environment.atomName slot) := by
  have spineReify :
      environment.reify
          (.apply "NQuote" [.apply "PDrop" [.fvar boundaryVarName]]) =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
      selected, rhoReflectivePresentation]
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName slot)]] :=
    (node.reifiedSourceFrame_pattern _).trans
      ((congrArg environment.reify skeletonShape).trans spineReify)
  exact CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
    node environment slot reifiedFrame

/-- The root view's semantic atom environment (screen constant): the
ofInventory environment over the inventory of normalized finite values,
spelled exactly as the restoration obligations do. -/
noncomputable def rootViewEnvironment
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree rhoCIGSLT targetFree available outer pattern
      type}
    (view : tree.StaticRootView color) :=
  CostStaticAtomEnvironment.ofInventory
    (view.node.semanticAtomEnvironment
      (view.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

/-- **Stopped-collapse witness → degenerate canonical frame (packaging).**

Given any stopped state of a root view — the semantic collapse witness,
with arbitrary retained skeleton context — and its context-collapse
equation, the canonical frame degenerates to the atom's own free variable
at the occurrence's selected slot.  This glues the semantic witness to the
frame-degeneration endcap without any quote/drop skeleton assumption. -/
theorem rhoCrossColor_frame_atom_of_stoppedCollapse
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree rhoCIGSLT targetFree available outer pattern
      type}
    (view : tree.StaticRootView color)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      view.node.skeleton.1)
    (collapse :
      canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill
          (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name) :
    ∃ slot,
      view.node.canonicalizeReifiedTargetFrame (rootViewEnvironment view)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) =
      .fvar ((rootViewEnvironment view).atomName slot) := by
  have slotExists := (rootViewEnvironment view).slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  refine ⟨(rootViewEnvironment view).slotOfName?
      state.boundaryOccurrence.name |>.get slotExists, ?_⟩
  have selected : (rootViewEnvironment view).slotOfName?
      state.boundaryOccurrence.name =
      some ((rootViewEnvironment view).slotOfName?
        state.boundaryOccurrence.name |>.get slotExists) :=
    (Option.some_get slotExists).symm
  exact CostStaticRegionNode.stopped_collapse_canonicalFrame view.node
    (rootViewEnvironment view) state _ selected collapse

/-- A singleton application strictly dominates its sole argument.  This is
the size box the callback call sites use: the child pair formed from the
collapsing root's unique argument is strictly smaller than the root pair. -/
theorem rhoCalc_sizeOf_singleton_child
    (constructor : String) (argument : Pattern) :
    sizeOf argument < sizeOf (Pattern.apply constructor [argument]) := by
  simp_wf
  omega

end CostHereditaryCrossColorLeafHinge

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
