import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderExposure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticCollapseExposure

/-!
# Leaf-partner normal forms for the collapsing-leaf routes

The two variable routes of `RhoCollapsingLeafExposureInDomain` quantify over a
partner endpoint whose *pattern* is already a bound or free variable.  Such a
tree has exactly one structural constructor, so its hereditary normal form is
that same variable and carries no residual content.

Consequently each variable route is *equivalent* to a statement about the
collapsed static node alone.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **Only a collapsing root reaches a bound variable.**

Canonicalization changes the outer constructor at exactly two roots, so a
pattern whose canonical form is a bound variable either is that variable
already or exposes a quote application or a bare parallel collection.  This is
the descent step of any classification of a rigid canonical leaf: the surviving
position is reached through collapsing roots only. -/
theorem eq_bvar_or_collapsingRoot_of_canonicalize_eq_bvar
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    {index : Nat}
    (collapsed : canonicalize declaration pattern = .bvar index) :
    pattern = .bvar index ∨ CollapsingRoot declaration pattern := by
  have equal : canonicalize declaration pattern =
      canonicalize declaration (.bvar index) := by
    rw [collapsed]; simp [canonicalize]
  rcases canonicalize_eq_root_cases declaration equal with
    leftCollapsing | rightCollapsing | aligned
  · exact Or.inr leftCollapsing
  · exact absurd rightCollapsing (by simp [CollapsingRoot])
  · cases aligned with
    | bvar index => exact Or.inl rfl

/-- Free-variable companion of
`eq_bvar_or_collapsingRoot_of_canonicalize_eq_bvar`. -/
theorem eq_fvar_or_collapsingRoot_of_canonicalize_eq_fvar
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    {name : String}
    (collapsed : canonicalize declaration pattern = .fvar name) :
    pattern = .fvar name ∨ CollapsingRoot declaration pattern := by
  have equal : canonicalize declaration pattern =
      canonicalize declaration (.fvar name) := by
    rw [collapsed]; simp [canonicalize]
  rcases canonicalize_eq_root_cases declaration equal with
    leftCollapsing | rightCollapsing | aligned
  · exact Or.inr leftCollapsing
  · exact absurd rightCollapsing (by simp [CollapsingRoot])
  · cases aligned with
    | fvar name => exact Or.inl rfl

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A tree indexed by a free variable is retained structurally. -/
theorem CostRegionTree.rootIsStatic_eq_false_of_fvar
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {name : String} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer (.fvar name)
      type) :
    tree.rootIsStatic = false := by
  apply Bool.eq_false_of_not_eq_true
  intro static
  rcases tree.pattern_shape_of_rootIsStatic static with
    ⟨wireName, arguments, impossible⟩ | ⟨collectionType, elements, rest,
      impossible⟩ <;> cases impossible

/-- Hereditary normalization of a bound-variable endpoint is that variable. -/
theorem rho_normalize_pattern_of_bvar
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {index : Nat} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.bvar index)
      type) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      .bvar index := by
  cases tree.structuralRootView tree.rootIsStatic_eq_false_of_bvar with
  | bvar lookup => simp [CostRegionTree.normalize]

/-- Hereditary normalization of a free-variable endpoint is that variable. -/
theorem rho_normalize_pattern_of_fvar
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {name : String} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      .fvar name := by
  cases tree.structuralRootView tree.rootIsStatic_eq_false_of_fvar with
  | fvar lookup => simp [CostRegionTree.normalize]

/-- A bound-variable endpoint exposes its own binder lookup. -/
theorem rho_bvar_lookup_of_tree
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {index : Nat} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.bvar index)
      type) :
    (available ++ outer)[index]? = some type := by
  cases tree.structuralRootView tree.rootIsStatic_eq_false_of_bvar with
  | bvar lookup => exact lookup

/-- A free-variable endpoint exposes its own free-context lookup. -/
theorem rho_fvar_lookup_of_tree
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {name : String} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type) :
    targetFree name = some type := by
  cases tree.structuralRootView tree.rootIsStatic_eq_false_of_fvar with
  | fvar lookup => exact lookup

/-! ## The variable routes are node-local statements

`RhoCollapsingLeafExposure.normalize_eq` pins the partner's normal form to the
collapsed node's, and the two lemmas above compute the partner's normal form
outright.  So each variable route says exactly one thing about the collapsed
static node: its hereditary normal form is that same variable. -/

/-- **The bound-variable route follows from the collapsed node's normal
form.**  No further datum about the partner is needed: an endpoint indexed by
a bound variable normalizes to that variable. -/
theorem rho_collapsingLeafExposureBVarRoute_of_staticNormal
    {declarationColor : CostStaticColor}
    (staticNormal : ∀ {targetFree : FreeTypeContext}
      {available outer : List TypeExpr} {collapsedPattern : Pattern}
      {index : Nat} {type : TypeExpr}
      {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
        collapsedPattern type}
      {color : CostStaticColor}
      (view : collapsed.StaticRootView color),
      CostRegionTree rhoCIGSLT targetFree available outer (.bvar index)
        type →
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type (Pattern.bvar index) →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf collapsedPattern + sizeOf (Pattern.bvar index)) →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          collapsedPattern →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          collapsedPattern =
        .bvar index →
      (rhoHereditaryStaticNormalizer view.node
        (view.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
        .bvar index) :
    RhoCollapsingLeafExposureBVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern index type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  exact ⟨.rigidBVar index
    (staticNormal view other admissible otherWellSorted close collapsing canonical)
    (rho_normalize_pattern_of_bvar other)⟩

/-- **The free-variable route follows from an authored source-variable
occurrence.**

A free-variable partner cannot be exposed rigidly: `RhoCollapsingLeafExposure`
retains a bound variable in its rigid branch, so an `fvar` endpoint must be
reached through the semantic-atom branch.  The data below is exactly what
`RhoCollapsingLeafExposure.sourceVariable` consumes — an actual occurrence of
the retagged authored variable in the node's skeleton, its atom slot, and the
canonical collapse of the reified target frame onto that slot. -/
theorem rho_collapsingLeafExposureFVarRoute_of_sourceVariable
    {declarationColor : CostStaticColor}
    (occurrenceRoute : ∀ {targetFree : FreeTypeContext}
      {available outer : List TypeExpr} {collapsedPattern : Pattern}
      {name : String} {type : TypeExpr}
      {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
        collapsedPattern type}
      {color : CostStaticColor}
      (view : collapsed.StaticRootView color),
      CostRegionTree rhoCIGSLT targetFree available outer (.fvar name) type →
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type (Pattern.fvar name) →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf collapsedPattern + sizeOf (Pattern.fvar name)) →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          collapsedPattern →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          collapsedPattern =
        .fvar name →
      ∃ occurrence : CostStaticFVarOccurrence view.node.skeleton.1,
        ∃ slot : Fin (view.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer view.children).atomCount,
        occurrence.name = costRegionSourceVariableName name ∧
          (view.node.normalizationEnvironment
              rhoHereditaryStaticNormalizer view.children).slotOfName?
              occurrence.name =
            some slot ∧
          view.node.canonicalizeReifiedTargetFrame
              (view.node.normalizationEnvironment
                rhoHereditaryStaticNormalizer view.children)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation) =
            .fvar ((view.node.normalizationEnvironment
              rhoHereditaryStaticNormalizer view.children).atomName slot)) :
    RhoCollapsingLeafExposureFVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern name type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  obtain ⟨occurrence, slot, occurrenceName, selected, staticFrame⟩ :=
    occurrenceRoute view other admissible otherWellSorted close collapsing canonical
  exact ⟨RhoCollapsingLeafExposure.sourceVariable view.node view.children
    occurrence name occurrenceName other slot selected staticFrame⟩

/-! ## The routes with the partner's admission retained

`RhoCollapsingLeafExposureInDomain` supplies a well-sortedness certificate for
the partner endpoint, and `rho_collapsingLeafExposureInDomain_of_leafRoutes`
discards it before splitting into the three routes.  Retaining it costs
nothing at the call site and is needed by every recursive closure that hands
the partner to the strictly-smaller callback, because that callback demands an
admitted child on both sides.

The three variants below keep the certificate; the dispatcher underneath shows
they still cover the obligation, so they are a strictly weaker demand than the
routes stated without it. -/

def RhoCollapsingBVarLeafDichotomy (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {color : CostStaticColor}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {index : Nat},
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 =
      .bvar index →
    (∃ sourceIndex : Nat,
        node.thinning.embedIndexAt 0 sourceIndex = index ∧
        canonicalize rhoReflectivePresentation
            (node.reifiedSourceFrame
              (CostStaticAtomEnvironment.ofInventory
                (node.semanticAtomEnvironment
                  (children.normalizeValues
                    (normalizeStatic :=
                      rhoHereditaryStaticNormalizer))).1)).1 =
          .bvar sourceIndex) ∨
      (∃ payload : Pattern,
        ∃ state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
          node.skeleton.1,
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
            [state.certified.typed] node.finiteBoundaryTable.entries) ∧
          canonicalize
              rhoReflectivePresentation.toReflectivePresentationDecl
              (state.skeletonContext.fill
                (.fvar state.boundaryOccurrence.name)) =
            .fvar state.boundaryOccurrence.name ∧
          canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
                rhoReflectivePresentation.toReflectivePresentationDecl)
              state.certified.typed.boundary.content =
            .bvar index ∧
          state.certified.typed.boundary.targetSupport = node.targetBound ∧
          state.certified.typed.boundary.targetType =
            .base (color.mapLangSort rhoCIGSLT node.sourceSort).1)

/-- **The bound-variable route from the syntactic classification.**

Both arms are already built.  The skeleton-static arm is
`RhoCollapsingLeafExposure.rigidBVarOfSourceCanonicalAtBoundVariable`, which
needs no endpoint premise because a tree indexed by a bound variable
normalizes to that variable.  The boundary arm is
`RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller`, whose recursive
call is exactly the strictly-smaller callback the route already carries. -/
theorem rho_collapsingLeafExposureBVarRoute_of_dichotomy
    {declarationColor : CostStaticColor}
    (dichotomy : RhoCollapsingBVarLeafDichotomy declarationColor) :
    RhoCollapsingLeafExposureBVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern index type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  have patternEq : view.node.term.1 = collapsedPattern := view.patternEq
  have nodeCollapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 := by
    rw [patternEq]; exact collapsing
  have nodeCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .bvar index := by
    rw [patternEq]; exact canonical
  rcases dichotomy view.node view.children nodeCollapsing nodeCanonical with
    ⟨sourceIndex, indexEq, collapse⟩ |
    ⟨payload, state, ⟨entryEmbedding⟩, contextCollapse, boundaryCanonical,
      boundarySupport, boundaryType⟩
  · exact ⟨RhoCollapsingLeafExposure.rigidBVarOfSourceCanonicalAtBoundVariable
      view.node view.children other sourceIndex collapse indexEq⟩
  · refine ⟨RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller collapsed
      other view otherWellSorted state entryEmbedding contextCollapse ?_
      (boundarySupport.trans view.availableEq)
      (boundaryType.trans view.typeEq) close⟩
    rw [boundaryCanonical]
    simp [canonicalize]

/-! ## The remaining two routes

The free-variable route splits the same way, except that its skeleton-static
arm exposes an authored source variable rather than a rigid index.  The
application route has *no* skeleton-static arm at all: `RhoCollapsingLeafExposure`
retains a bound variable in its rigid branch and a restored semantic atom in
its other branch, and an authored source variable restores to a free variable,
never to a constructor application.  So a constructor-application partner is
reachable only through a certified boundary. -/

/-- Free-variable counterpart of `RhoCollapsingBVarLeafDichotomy`. -/
def RhoCollapsingFVarLeafDichotomy (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {color : CostStaticColor}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {name : String},
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 =
      .fvar name →
    (∃ occurrence : CostStaticFVarOccurrence node.skeleton.1,
        ∃ slot : Fin (node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomCount,
        occurrence.name = costRegionSourceVariableName name ∧
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
              children).slotOfName? occurrence.name = some slot ∧
          node.canonicalizeReifiedTargetFrame
              (node.normalizationEnvironment rhoHereditaryStaticNormalizer
                children)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation) =
            .fvar ((node.normalizationEnvironment
              rhoHereditaryStaticNormalizer children).atomName slot)) ∨
      (∃ payload : Pattern,
        ∃ state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
          node.skeleton.1,
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
            [state.certified.typed] node.finiteBoundaryTable.entries) ∧
          canonicalize
              rhoReflectivePresentation.toReflectivePresentationDecl
              (state.skeletonContext.fill
                (.fvar state.boundaryOccurrence.name)) =
            .fvar state.boundaryOccurrence.name ∧
          canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
                rhoReflectivePresentation.toReflectivePresentationDecl)
              state.certified.typed.boundary.content =
            .fvar name ∧
          state.certified.typed.boundary.targetSupport = node.targetBound ∧
          state.certified.typed.boundary.targetType =
            .base (color.mapLangSort rhoCIGSLT node.sourceSort).1)

/-- **The free-variable route from its syntactic classification.** -/
theorem rho_collapsingLeafExposureFVarRoute_of_dichotomy
    {declarationColor : CostStaticColor}
    (dichotomy : RhoCollapsingFVarLeafDichotomy declarationColor) :
    RhoCollapsingLeafExposureFVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern name type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  have patternEq : view.node.term.1 = collapsedPattern := view.patternEq
  have nodeCollapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 := by
    rw [patternEq]; exact collapsing
  have nodeCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .fvar name := by
    rw [patternEq]; exact canonical
  rcases dichotomy view.node view.children nodeCollapsing nodeCanonical with
    ⟨occurrence, slot, occurrenceName, selected, staticFrame⟩ |
    ⟨payload, state, ⟨entryEmbedding⟩, contextCollapse, boundaryCanonical,
      boundarySupport, boundaryType⟩
  · exact ⟨RhoCollapsingLeafExposure.sourceVariable view.node view.children
      occurrence name occurrenceName other slot selected staticFrame⟩
  · refine ⟨RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller collapsed
      other view otherWellSorted state entryEmbedding contextCollapse ?_
      (boundarySupport.trans view.availableEq)
      (boundaryType.trans view.typeEq) close⟩
    rw [boundaryCanonical]
    simp [canonicalize]

/-- The application route's single arm: a certified boundary carrying the whole
canonical class. -/
def RhoCollapsingApplyLeafBoundary (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {color : CostStaticColor}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {label : String} {arguments : List Pattern},
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        node.term.1 =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments) →
    ∃ payload : Pattern,
      ∃ state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
        node.skeleton.1,
      Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [state.certified.typed] node.finiteBoundaryTable.entries) ∧
        canonicalize
            rhoReflectivePresentation.toReflectivePresentationDecl
            (state.skeletonContext.fill
              (.fvar state.boundaryOccurrence.name)) =
          .fvar state.boundaryOccurrence.name ∧
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation.toReflectivePresentationDecl)
            state.certified.typed.boundary.content =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation.toReflectivePresentationDecl)
            (.apply label arguments) ∧
        state.certified.typed.boundary.targetSupport = node.targetBound ∧
        state.certified.typed.boundary.targetType =
          .base (color.mapLangSort rhoCIGSLT node.sourceSort).1

/-- **The admitted application route from its single boundary arm.** -/
theorem rho_collapsingLeafExposureApplyRoute_of_boundary
    {declarationColor : CostStaticColor}
    (boundary : RhoCollapsingApplyLeafBoundary declarationColor) :
    RhoCollapsingLeafExposureApplyRoute declarationColor := by
  intro targetFree available outer collapsedPattern label arguments type
    collapsed color view other admissible otherWellSorted close collapsing
    _structural canonical
  have patternEq : view.node.term.1 = collapsedPattern := view.patternEq
  have nodeCollapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 := by
    rw [patternEq]; exact collapsing
  have nodeCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        view.node.term.1 =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments) := by
    rw [patternEq]; exact canonical
  obtain ⟨payload, state, ⟨entryEmbedding⟩, contextCollapse, boundaryCanonical,
    boundarySupport, boundaryType⟩ :=
    boundary view.node nodeCollapsing nodeCanonical
  exact ⟨RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller collapsed
    other view otherWellSorted state entryEmbedding contextCollapse
    boundaryCanonical (boundarySupport.trans view.availableEq)
    (boundaryType.trans view.typeEq) close⟩

/-- **Obligation B from the three syntactic classifications.**

This is the whole reduction: discharging the three classification statements
— each a claim about one static node's plan, its skeleton and one canonical
equation — discharges `RhoCollapsingLeafExposureInDomain` outright.  No region
tree, partner endpoint, pair elaboration or size arithmetic survives into
them. -/
theorem rho_collapsingLeafExposureInDomain_of_classifications
    {declarationColor : CostStaticColor}
    (bvarDichotomy : RhoCollapsingBVarLeafDichotomy declarationColor)
    (fvarDichotomy : RhoCollapsingFVarLeafDichotomy declarationColor)
    (applyBoundary : RhoCollapsingApplyLeafBoundary declarationColor) :
    RhoCollapsingLeafExposureInDomain declarationColor :=
  rho_collapsingLeafExposureInDomain_of_leafRoutes
    (rho_collapsingLeafExposureBVarRoute_of_dichotomy bvarDichotomy)
    (rho_collapsingLeafExposureFVarRoute_of_dichotomy fvarDichotomy)
    (rho_collapsingLeafExposureApplyRoute_of_boundary applyBoundary)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
