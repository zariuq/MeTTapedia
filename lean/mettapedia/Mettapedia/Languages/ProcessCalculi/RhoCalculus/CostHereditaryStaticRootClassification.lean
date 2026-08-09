import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.GSLT.LanguageDef.CostStaticRootView

/-!
# Root classification for rho static-to-structural canonical pairs

Canonical equality away from Quote/Drop and bare-parallel collapse preserves
the compact root.  Since a proof-relevant static rho tree retains the exact
declaration-derived root shape, that aligned case cannot turn it into a
structural tree.  Nor can the structural endpoint itself have a collapsing
root: at a base result fibre every collapsing generated rho root is static.

Thus every genuinely asymmetric static-to-structural canonical pair is
oriented by a collapsing root on the static endpoint.  This is the exact
syntax-level entry point for the semantic-atom terminal.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- If the left rho Cost tree is static and the right tree is structural,
canonical equality must collapse at the left root. -/
theorem rhoCollapsingRoot_of_static_structural_canonical_eq
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftStatic : left.rootIsStatic = true)
    (rightStructural : right.rootIsStatic = false)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · exact leftCollapsing
  · obtain ⟨category, typeEq⟩ :=
      left.type_eq_base_of_rootIsStatic leftStatic
    subst type
    have rightStatic :=
      right.rootIsStatic_of_costStatic_collapsingRoot rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by exact List.mem_cons_self) rightCollapsing
    rw [rightStatic] at rightStructural
    contradiction
  · have rightStatic :=
      left.rootIsStatic_of_canonicalRootAligned right leftStatic aligned
    rw [rightStatic] at rightStructural
    contradiction

/-- Symmetric orientation of
`rhoCollapsingRoot_of_static_structural_canonical_eq`. -/
theorem rhoCollapsingRoot_of_structural_static_canonical_eq
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftStructural : left.rootIsStatic = false)
    (rightStatic : right.rootIsStatic = true)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern :=
  rhoCollapsingRoot_of_static_structural_canonical_eq color right left
    rightStatic leftStructural canonical.symm

/-- Exhaustive proof-relevant root classification of a canonical rho pair
for which at least one endpoint has a static-root shape.  The asymmetric
constructors retain the oriented collapsing-root proof needed by the
semantic-atom terminals. -/
inductive RhoCanonicalStaticPairRootCase
    (color : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type) : Type where
  | bothStatic
      (leftStatic : left.rootIsStatic = true)
      (rightStatic : right.rootIsStatic = true) :
      RhoCanonicalStaticPairRootCase color left right
  | leftCollapsing
      (leftStatic : left.rootIsStatic = true)
      (rightStructural : right.rootIsStatic = false)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern) :
      RhoCanonicalStaticPairRootCase color left right
  | rightCollapsing
      (leftStructural : left.rootIsStatic = false)
      (rightStatic : right.rootIsStatic = true)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
      RhoCanonicalStaticPairRootCase color left right

/-- Canonical equality plus one declaration-derived static shape constructs
the exhaustive root case directly.  No pair-normalization bridge is assumed
or hidden in this classifier. -/
theorem nonempty_rhoCanonicalStaticPairRootCase
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (staticShape : CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) :
    Nonempty (RhoCanonicalStaticPairRootCase color left right) := by
  rcases staticShape with leftShape | rightShape
  · have leftStatic := leftShape.rootIsStatic left
    cases rightStatic : right.rootIsStatic with
    | false =>
        exact ⟨.leftCollapsing leftStatic rightStatic
          (rhoCollapsingRoot_of_static_structural_canonical_eq color left
            right leftStatic rightStatic canonical)⟩
    | true => exact ⟨.bothStatic leftStatic rightStatic⟩
  · have rightStatic := rightShape.rootIsStatic right
    cases leftStatic : left.rootIsStatic with
    | false =>
        exact ⟨.rightCollapsing leftStatic rightStatic
          (rhoCollapsingRoot_of_structural_static_canonical_eq color left
            right leftStatic rightStatic canonical)⟩
    | true => exact ⟨.bothStatic leftStatic rightStatic⟩

/-- Non-collapsing canonical root agreement determines the same intrinsic
static colour on both rho trees.  Application roots share one decoded wire
declaration.  Collection roots are both authored PPar nodes, so their common
target fibre and the disjoint base/wrapped images of the interacting sort
determine the colour.

This theorem is intentionally about the colours retained by the two trees;
it does not infer a colour from canonical syntax after a collapsing head has
been erased. -/
theorem rhoStaticRootView_color_eq_of_canonicalRootAligned
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {leftTree : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {rightTree : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type}
    {leftColor rightColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (rightView : rightTree.StaticRootView rightColor)
    {declaration : ReflectivePresentationDecl}
    (aligned : CanonicalRootAligned declaration leftPattern rightPattern) :
    leftColor = rightColor := by
  cases aligned with
  | @apply constructor ne leftArguments rightArguments children =>
      have leftShape : leftView.node.term.1 =
          .apply constructor leftArguments := leftView.patternEq
      have rightShape : rightView.node.term.1 =
          .apply constructor rightArguments := rightView.patternEq
      obtain ⟨leftConstructor, leftDecoded, leftRole⟩ :=
        leftView.node.plan.application_dispatch_of_isStaticRoot
          leftView.node.rootStatic leftShape
      obtain ⟨rightConstructor, rightDecoded, rightRole⟩ :=
        rightView.node.plan.application_dispatch_of_isStaticRoot
          rightView.node.rootStatic rightShape
      have constructorEq : leftConstructor = rightConstructor :=
        Option.some.inj (leftDecoded.symm.trans rightDecoded)
      subst rightConstructor
      exact CIGSLT.GeneratedCostConstructorRole.static.inj
        (leftRole.symm.trans rightRole)
  | @collection collectionType ne leftElements rightElements children =>
      have leftInteracting :=
        CostCanonicalLaws.rho_collection_node_sourceSort_interacting
          leftView.node leftView.patternEq
      have rightInteracting :=
        CostCanonicalLaws.rho_collection_node_sourceSort_interacting
          rightView.node rightView.patternEq
      apply CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting
        rhoCIGSLT leftColor rightColor leftView.node.sourceSort
          rightView.node.sourceSort leftInteracting rightInteracting
      apply Subtype.ext
      exact TypeExpr.base.inj
        (leftView.typeEq.trans rightView.typeEq.symm)
  | @collectionRest collectionType rest leftElements rightElements children =>
      have leftInteracting :=
        CostCanonicalLaws.rho_collection_node_sourceSort_interacting
          leftView.node leftView.patternEq
      have rightInteracting :=
        CostCanonicalLaws.rho_collection_node_sourceSort_interacting
          rightView.node rightView.patternEq
      apply CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting
        rhoCIGSLT leftColor rightColor leftView.node.sourceSort
          rightView.node.sourceSort leftInteracting rightInteracting
      apply Subtype.ext
      exact TypeExpr.base.inj
        (leftView.typeEq.trans rightView.typeEq.symm)
  | bvar index =>
      rcases leftView.node.plan.pattern_shape_of_isStaticRoot
          leftView.node.rootStatic with
        ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest,
          shape⟩
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
  | fvar name =>
      rcases leftView.node.plan.pattern_shape_of_isStaticRoot
          leftView.node.rootStatic with
        ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest,
          shape⟩
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
  | lambda binder body =>
      rcases leftView.node.plan.pattern_shape_of_isStaticRoot
          leftView.node.rootStatic with
        ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest,
          shape⟩
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
  | multiLambda arity binders body =>
      rcases leftView.node.plan.pattern_shape_of_isStaticRoot
          leftView.node.rootStatic with
        ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest,
          shape⟩
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
  | subst body replacement =>
      rcases leftView.node.plan.pattern_shape_of_isStaticRoot
          leftView.node.rootStatic with
        ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest,
          shape⟩
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible
      · have impossible := leftView.patternEq
        rw [shape] at impossible
        cases impossible

/-- Two rho static roots of different intrinsic colours cannot remain in the
non-collapsing arm of reflective canonical equality.  Any cross-colour static
pair must therefore be handled by an explicit collapsing-root bridge rather
than by structural child alignment. -/
theorem rhoStaticRootViews_not_canonicalRootAligned_of_color_ne
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {leftTree : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {rightTree : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type}
    {leftColor rightColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (rightView : rightTree.StaticRootView rightColor)
    {declaration : ReflectivePresentationDecl}
    (different : leftColor ≠ rightColor) :
    ¬ CanonicalRootAligned declaration leftPattern rightPattern := by
  intro aligned
  exact different
    (rhoStaticRootView_color_eq_of_canonicalRootAligned leftView rightView
      aligned)

/-- The three exact entry cases for the static-root bridge proof.

The collapsing constructors retain the actual static node selected by the
compiled tree.  The aligned constructor retains both nodes at one proved
common intrinsic colour.  Consequently a later restoration proof never has
to guess a colour from a canonical form whose head may already have
collapsed. -/
inductive RhoCanonicalStaticPairBridgeCase
    (declarationColor : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type) : Type where
  | leftCollapsing
      (leftColor : CostStaticColor)
      (leftView : left.StaticRootView leftColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern) :
      RhoCanonicalStaticPairBridgeCase declarationColor left right
  | rightCollapsing
      (rightColor : CostStaticColor)
      (rightView : right.StaticRootView rightColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
      RhoCanonicalStaticPairBridgeCase declarationColor left right
  | aligned
      (color : CostStaticColor)
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color)
      (roots : CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern rightPattern) :
      RhoCanonicalStaticPairBridgeCase declarationColor left right

/-- Canonical equality and one declaration-derived static shape construct the
bridge-oriented case split.  Cross-colour static pairs cannot survive in the
aligned arm: a common decoded application label or PPar's interacting result
sort forces the two retained colours to coincide.  Cross-colour work is thus
confined to the two explicit collapsing arms. -/
theorem nonempty_rhoCanonicalStaticPairBridgeCase
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (declarationColor : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (staticShape : CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) :
    Nonempty (RhoCanonicalStaticPairBridgeCase declarationColor left right) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have typeBase : ∃ category, type = .base category := by
    rcases staticShape with leftShape | rightShape
    · cases leftShape with
      | application color constructor decoded role => exact ⟨_, rfl⟩
      | baseCollection => exact ⟨_, rfl⟩
    · cases rightShape with
      | application color constructor decoded role => exact ⟨_, rfl⟩
      | baseCollection => exact ⟨_, rfl⟩
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | roots
  · obtain ⟨category, typeEq⟩ := typeBase
    subst type
    obtain ⟨⟨leftColor, leftRoot⟩⟩ :=
      left.nonempty_staticRootColor_of_costStatic_collapsingRoot rhoCIGSLT
        declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by exact List.mem_cons_self) leftCollapsing
    exact ⟨.leftCollapsing leftColor leftRoot.toView leftCollapsing⟩
  · obtain ⟨category, typeEq⟩ := typeBase
    subst type
    obtain ⟨⟨rightColor, rightRoot⟩⟩ :=
      right.nonempty_staticRootColor_of_costStatic_collapsingRoot rhoCIGSLT
        declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by exact List.mem_cons_self) rightCollapsing
    exact ⟨.rightCollapsing rightColor rightRoot.toView rightCollapsing⟩
  · have leftStatic : left.rootIsStatic = true := by
      rcases staticShape with leftShape | rightShape
      · exact leftShape.rootIsStatic left
      · exact right.rootIsStatic_of_canonicalRootAligned left
          (rightShape.rootIsStatic right) roots.symm
    have rightStatic : right.rootIsStatic = true :=
      left.rootIsStatic_of_canonicalRootAligned right leftStatic roots
    obtain ⟨⟨leftColor, leftRoot⟩⟩ :=
      (left.staticRootShape_of_rootIsStatic leftStatic
        ).nonempty_staticRootColor left
    obtain ⟨⟨rightColor, rightRoot⟩⟩ :=
      (right.staticRootShape_of_rootIsStatic rightStatic
        ).nonempty_staticRootColor right
    let leftView := leftRoot.toView
    let rightView := rightRoot.toView
    have colors : leftColor = rightColor :=
      rhoStaticRootView_color_eq_of_canonicalRootAligned leftView rightView
        roots
    cases colors
    exact ⟨.aligned leftColor leftView rightView roots⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
