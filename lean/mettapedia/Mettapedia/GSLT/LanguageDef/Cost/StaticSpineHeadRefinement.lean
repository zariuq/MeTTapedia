import Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement
import Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport

/-!
# Constructive boundary insertion in a retained argument spine

A new certified boundary replaces the first ordinary argument of a static
spine.  The existing tail's current semantic subtrees are retained exactly;
only their paths are recalculated for the changed compact prefix.  The new
forest concatenates the supplied replacement and that retained tail in
occurrence order.

This is structural grafting in the existing planner and semantic carrier.
It does not yet supply a general source substitution or binder weakening.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StaticLeafBoundaryRefinement
open RetainedBoundaryOriginTransport

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext}
  {sourceBound targetBound available : List TypeExpr}
  {thinning : CostStaticBinderThinning source color sourceBound targetBound}
  {outer : OneHoleContext} {wire : String}
  {before : List Pattern} {oldArgument : Pattern}
  {remainingArguments : List Pattern} {remainingParameters : List TermParam}
  (tail : CostStaticArgumentPlan source color targetFree sourceBound targetBound
    thinning available outer wire (before ++ [oldArgument])
    remainingArguments remainingParameters)
  (parameterName : String) {sourceType : TypeExpr}
  (principal : source.DeclaredCostConstructor)
  (outsideCurrent : source.declaredCostConstructorRole principal ≠ .static color)
  (principalArguments : List Pattern)
  (admitted : ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree available
    (mapTypeExpr (color.symbols source) sourceType)
    (.apply (source.renderDeclaredCostConstructor principal) principalArguments))

/-- The new head and the recalculated existing tail form one actual static
argument plan, indexed by the complete new compact argument sequence. -/
def plan :
    CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before
      (.apply (source.renderDeclaredCostConstructor principal) principalArguments ::
        remainingArguments)
      (.simple parameterName sourceType :: remainingParameters) :=
  .cons trivial rfl
    (replacementPlan principal outsideCurrent principalArguments admitted
      (outer.comp (.apply wire before .hole remainingArguments)))
    (tail.reprefix
      (before ++ [.apply (source.renderDeclaredCostConstructor principal) principalArguments]))

/-- No existing tail certificate is discarded or changed by the insertion. -/
theorem entries :
    (plan tail parameterName principal outsideCurrent principalArguments admitted
      ).boundaryTable.entries =
      (boundary admitted).typed :: tail.boundaryTable.entries := by
  change ((replacementPlan principal outsideCurrent principalArguments admitted
    (outer.comp (.apply wire before .hole remainingArguments))).boundaryTable.append
      (tail.reprefix _).boundaryTable).entries = _
  rw [TypedCostRegionBoundaryTable.entries_append, tail.reprefix_entries]
  rfl

theorem abstractPatterns :
    (plan tail parameterName principal outsideCurrent principalArguments admitted
      ).abstractPatterns =
      .fvar (costRegionBoundaryVariableName (boundary admitted).typed.boundary) ::
        tail.abstractPatterns := by
  change _ :: (tail.reprefix _).abstractPatterns = _
  rw [tail.reprefix_abstractPatterns]
  rfl

variable {values : TypedCostRegionBoundaryTable.Values source color targetFree
    tail.boundaryTable}
  (oldChildren : CostSemanticBoundaryTrees source targetFree color
    tail.boundaryTable values)
  (retained : CostSemanticTree source targetFree available []
    (.apply (source.renderDeclaredCostConstructor principal) principalArguments)
    (mapTypeExpr (color.symbols source) sourceType))

/-- The replacement and all supplied existing tail descendants become the
new finite child forest.  Current tail values are transported, not reset to
the original certificate contents. -/
def children :
    Σ newValues : TypedCostRegionBoundaryTable.Values source color targetFree
        (plan tail parameterName principal outsideCurrent principalArguments admitted
          ).boundaryTable,
      CostSemanticBoundaryTrees source targetFree color
        (plan tail parameterName principal outsideCurrent principalArguments admitted
          ).boundaryTable newValues := by
  let newTail := argumentTail tail oldChildren
    (before ++ [.apply (source.renderDeclaredCostConstructor principal) principalArguments])
  let newHead := replacementChildren (thinning := thinning)
    principal outsideCurrent principalArguments
    admitted (outer.comp (.apply wire before .hole remainingArguments)) retained
  exact ⟨_, RetainedBoundaryOriginTransport.append newHead newTail.2⟩

/-- The complete new ordered subtree list consists of the supplied
replacement followed by the unchanged complete old tail. -/
theorem children_packedChildren :
    packedChildren (children tail parameterName principal outsideCurrent
      principalArguments admitted oldChildren retained).2 =
      ⟨available,
        .apply (source.renderDeclaredCostConstructor principal) principalArguments,
        mapTypeExpr (color.symbols source) sourceType, retained⟩ ::
          packedChildren oldChildren := by
  change packedChildren (RetainedBoundaryOriginTransport.append
    (replacementChildren (thinning := thinning) principal outsideCurrent
      principalArguments admitted
      (outer.comp (.apply wire before .hole remainingArguments)) retained)
    (argumentTail tail oldChildren
      (before ++ [.apply (source.renderDeclaredCostConstructor principal)
        principalArguments])).2) = _
  rw [append_packedChildren]
  rw [argumentTail_packedChildren]
  rfl

/-- The supplied head remains at its exact argument path; the existing tail
is recollected under the new prefix. -/
theorem occurrences :
    (plan tail parameterName principal outsideCurrent principalArguments admitted
      ).occurrences =
      { context := outer.comp (.apply wire before .hole remainingArguments),
        content := .apply (source.renderDeclaredCostConstructor principal)
          principalArguments } ::
        (tail.reprefix
          (before ++ [.apply (source.renderDeclaredCostConstructor principal)
            principalArguments])).occurrences := rfl

#print axioms plan
#print axioms entries
#print axioms abstractPatterns
#print axioms children
#print axioms children_packedChildren
#print axioms occurrences

end Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement
