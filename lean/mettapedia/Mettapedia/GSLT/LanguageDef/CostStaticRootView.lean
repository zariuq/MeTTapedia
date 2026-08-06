import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment

/-!
# Cast-stable views of static Cost roots

`CostRegionTree.StaticRootColor` proves that a dependent region tree is rooted
at one certified static node, but its reindexing constructors can hide that
node behind pattern, binder-context, or result-type transports.  The view
below packages the original node and children together with explicit index
equalities and one reconstruction equation.  Clients can reason about the
static data without unfolding casts in a compiled tree.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Proof-relevant static root data exposed through all three supported tree
reindexings.  `treeEq` is the sole dependent transport boundary. -/
structure CostRegionTree.StaticRootView
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (color : CostStaticColor) where
  node : CostStaticRegionNode source color targetFree
  children : CostRegionBoundaryTrees source targetFree color
    node.finiteBoundaryTable
  patternEq : node.term.1 = pattern
  availableEq : node.targetBound = available
  typeEq :
    (.base (color.mapLangSort source node.sourceSort).1 : TypeExpr) = type
  treeEq : tree =
    (((CostRegionTree.static (outer := outer) node children).reindexPattern
        patternEq).reindexAvailable availableEq).reindexType typeEq

namespace CostRegionTree.StaticRootView

/-- The unreindexed tree directly built from the exposed node and children. -/
def exposedTree
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color) :
    CostRegionTree source targetFree view.node.targetBound outer
      view.node.term.1
      (.base (color.mapLangSort source view.node.sourceSort).1) :=
  .static view.node view.children

/-- Normalization of a cast-stable view is exactly normalization of its
exposed static node after child-first boundary normalization. -/
theorem normalize_pattern
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color)
    (normalizeStatic : CostStaticRegionNormalizer source) :
    (tree.normalize (normalizeStatic := normalizeStatic)).pattern =
      (normalizeStatic view.node
        (view.children.normalizeValues
          (normalizeStatic := normalizeStatic))).1 := by
  cases view with
  | mk node children patternEq availableEq typeEq treeEq =>
      cases patternEq
      cases availableEq
      cases typeEq
      cases treeEq
      exact CostRegionTree.normalize_static_pattern normalizeStatic node
        children

/-- Exposed binder depth agrees exactly with the original tree index. -/
theorem targetBound_eq
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color) :
    view.node.targetBound = available :=
  view.availableEq

theorem targetBound_length_eq
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color) :
    view.node.targetBound.length = available.length :=
  congrArg List.length view.availableEq

/-- Transport a semantic root bridge built on two exposed static constructors
back through the exact pattern, binder-context, and result-type indices of the
original compiled trees.  No heterogeneous equality escapes this boundary. -/
noncomputable def rootBridge_reindex
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {leftTree : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {rightTree : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    {leftColor rightColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (rightView : rightTree.StaticRootView rightColor)
    (bridge : CostRegionRootNormalizationBridge source kernel targetFree
      leftView.exposedTree rightView.exposedTree) :
    CostRegionRootNormalizationBridge source kernel targetFree
      leftTree rightTree := by
  cases leftView with
  | mk leftNode leftChildren leftPatternEq leftAvailableEq leftTypeEq
      leftTreeEq =>
      cases leftPatternEq
      cases leftAvailableEq
      cases leftTypeEq
      cases leftTreeEq
      cases rightView with
      | mk rightNode rightChildren rightPatternEq rightAvailableEq rightTypeEq
          rightTreeEq =>
          cases rightPatternEq
          cases rightAvailableEq
          cases rightTypeEq
          cases rightTreeEq
          exact bridge

/-- Transport a bridge whose left endpoint is the exposed static constructor
back to the original compiled left tree.  The right endpoint need not itself
be static; this is the cast-stable boundary used by asymmetric collapse
closures. -/
noncomputable def rootBridge_reindex_left
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {leftTree : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {rightTree : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    {leftColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (bridge : CostRegionRootNormalizationBridge source kernel targetFree
      leftView.exposedTree rightTree) :
    CostRegionRootNormalizationBridge source kernel targetFree
      leftTree rightTree := by
  cases leftView with
  | mk leftNode leftChildren leftPatternEq leftAvailableEq leftTypeEq
      leftTreeEq =>
      cases leftPatternEq
      cases leftAvailableEq
      cases leftTypeEq
      cases leftTreeEq
      exact bridge

/-- Symmetric one-sided transport for a structural left endpoint and an
exposed static right endpoint. -/
noncomputable def rootBridge_reindex_right
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {leftTree : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {rightTree : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    {rightColor : CostStaticColor}
    (rightView : rightTree.StaticRootView rightColor)
    (bridge : CostRegionRootNormalizationBridge source kernel targetFree
      leftTree rightView.exposedTree) :
    CostRegionRootNormalizationBridge source kernel targetFree
      leftTree rightTree := by
  cases rightView with
  | mk rightNode rightChildren rightPatternEq rightAvailableEq rightTypeEq
      rightTreeEq =>
      cases rightPatternEq
      cases rightAvailableEq
      cases rightTypeEq
      cases rightTreeEq
      exact bridge

end CostRegionTree.StaticRootView

namespace CostRegionTree.StaticRootColor

/-- Eliminate a static-root certificate into one cast-stable node view. -/
noncomputable def toView
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (root : CostRegionTree.StaticRootColor source targetFree tree color) :
    tree.StaticRootView color := by
  induction root with
  | static node children =>
      exact
        { node := node
          children := children
          patternEq := rfl
          availableEq := rfl
          typeEq := rfl
          treeEq := rfl }
  | reindexPattern patternEq tree root inductionHypothesis =>
      cases patternEq
      exact inductionHypothesis
  | reindexAvailable availableEq tree root inductionHypothesis =>
      cases availableEq
      exact inductionHypothesis
  | reindexType typeEq tree root inductionHypothesis =>
      cases typeEq
      exact inductionHypothesis

end CostRegionTree.StaticRootColor

end Mettapedia.GSLT.LanguageDef
