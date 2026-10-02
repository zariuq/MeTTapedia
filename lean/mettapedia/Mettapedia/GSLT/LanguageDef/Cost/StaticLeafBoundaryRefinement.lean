import Mettapedia.GSLT.LanguageDef.CostSemanticCarrier
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers

/-!
# Introducing a retained boundary at a static variable leaf

A substitution may put an interaction principal into a position formerly
occupied by an ordinary static variable.  This changes the region skeleton
and its finite boundary table.  The local refinement below derives the
existing certifier's exact singleton table from an admitted replacement,
grafts its supplied semantic tree, and proves exact compact restoration.

This is the leaf case of origin-preserving structural substitution.  It
does not reconstruct enclosing frames or compile source principals.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open WellSorted

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : FreeTypeContext} {available : List TypeExpr}
  {sourceType : TypeExpr}

/-- Admission determines the same decoded boundary as the existing
executable certifier, including the complete target support. -/
def boundary {pattern : Pattern}
    (admitted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (mapTypeExpr (color.symbols source) sourceType) pattern) :
    CertifiedCostRegionBoundary source color targetFree available
      (mapTypeExpr (color.symbols source) sourceType) pattern where
  typed :=
    { boundary :=
        { type := sourceType
          support := CostStaticBinderThinning.sourceContextOfTarget source
            color available
          targetType := mapTypeExpr (color.symbols source) sourceType
          targetSupport := available
          content := pattern }
      contentTyped := admitted.1.1
      contentCanonicalBinderMetadata := admitted.1.2.1
      contentObjectPattern := admitted.1.2.2.1
      contentReflectiveScopeSafe := admitted.2 }
  content_eq := rfl
  targetSupport_eq := rfl
  targetType_eq := rfl

theorem boundary_certifies {pattern : Pattern}
    (admitted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (mapTypeExpr (color.symbols source) sourceType) pattern) :
    certifyCostRegionBoundary? source color targetFree available
        (mapTypeExpr (color.symbols source) sourceType) pattern =
      some (boundary admitted) := by
  have checked :=
    (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (mapTypeExpr (color.symbols source) sourceType) pattern).mpr
        admitted
  simp [certifyCostRegionBoundary?, decodeCostStaticTypeExpr_mapTypeExpr,
    checked, boundary]

variable {sourceBound targetBound : List TypeExpr}
  {thinning : CostStaticBinderThinning source color sourceBound targetBound}

/-- Replace a rigid variable leaf by a certified declared application at its
original occurrence context.  The supplied subtree is not recompiled. -/
def replacementPlan (constructor : source.DeclaredCostConstructor)
    (outsideCurrent : source.declaredCostConstructorRole constructor ≠
      .static color) (arguments : List Pattern)
    (admitted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (mapTypeExpr (color.symbols source) sourceType)
      (.apply (source.renderDeclaredCostConstructor constructor) arguments))
    (outer : OneHoleContext) :
    CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning available outer
      (.apply (source.renderDeclaredCostConstructor constructor) arguments)
      sourceType :=
  .boundaryApplication constructor rfl outsideCurrent (boundary admitted)
    (boundary_certifies admitted)

variable (constructor : source.DeclaredCostConstructor)
  (outsideCurrent : source.declaredCostConstructorRole constructor ≠
    .static color) (arguments : List Pattern)
  (admitted : ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
    available (mapTypeExpr (color.symbols source) sourceType)
    (.apply (source.renderDeclaredCostConstructor constructor) arguments))
  (outer : OneHoleContext)

theorem replacement_occurrences :
    (replacementPlan (thinning := thinning) constructor outsideCurrent
      arguments admitted outer).occurrences =
      [{ context := outer,
         content := .apply (source.renderDeclaredCostConstructor constructor)
           arguments }] := rfl

theorem replacement_table :
    (replacementPlan (thinning := thinning) constructor outsideCurrent
      arguments admitted outer).boundaryTable =
      .cons (boundary admitted).typed (boundary admitted).content_eq .nil := rfl

/-- The exact retained replacement becomes the new boundary child.  Neither
the occurrence evidence nor the replacement's internal frames are rebuilt. -/
def replacementChildren
    (retained : CostSemanticTree source targetFree available []
      (.apply (source.renderDeclaredCostConstructor constructor) arguments)
      (mapTypeExpr (color.symbols source) sourceType)) :
    CostSemanticBoundaryTrees source targetFree color
      (replacementPlan (thinning := thinning) constructor outsideCurrent
        arguments admitted outer).boundaryTable
      (TypedCostRegionBoundaryTable.Values.original
        (replacementPlan (thinning := thinning) constructor outsideCurrent
          arguments admitted outer).boundaryTable) :=
  .cons retained .nil

/-- Reading the new source skeleton through its exact finite restoration
recovers the complete supplied replacement, including its binders. -/
theorem replacement_restore :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      (replacementPlan (thinning := thinning) constructor outsideCurrent
        arguments admitted outer).boundaryTable.restorationSupport
      (replacementPlan (thinning := thinning) constructor outsideCurrent
        arguments admitted outer).boundaryTable.restorationAssignment
      available.length
      (thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols source)
          (replacementPlan (thinning := thinning) constructor outsideCurrent
            arguments admitted outer).abstractPattern)) =
      .apply (source.renderDeclaredCostConstructor constructor) arguments := by
  let plan := replacementPlan (thinning := thinning) constructor outsideCurrent
    arguments admitted outer
  have restored := plan.restoreMappedAbstractPattern plan.boundaryTable
    (by intro entry membership; exact membership) admitted.1.2.2.1
  exact restored.trans plan.recomposePattern_eq

/-- Moving the selected leaf changes its occurrence context while retaining
the same decoded content, source skeleton and certificate. -/
theorem replacement_recontextualize (newOuter : OneHoleContext) :
    (replacementPlan (thinning := thinning) constructor outsideCurrent
      arguments admitted outer).recontextualize newOuter =
      replacementPlan (thinning := thinning) constructor outsideCurrent
        arguments admitted newOuter := rfl

theorem replacement_rigid_leaf_changed {name : String}
    (lookup : targetFree name =
      some (mapTypeExpr (color.symbols source) sourceType)) :
    (CostStaticRegionPlan.fvar (sourceBound := sourceBound)
      (targetBound := targetBound) (thinning := thinning)
      (sourceAvailable := available) (outer := outer) lookup).occurrences = [] ∧
    (replacementPlan (thinning := thinning) constructor outsideCurrent
      arguments admitted outer).occurrences ≠ [] := by
  constructor
  · rfl
  · simp [replacementPlan, CostStaticRegionPlan.occurrences]

#print axioms boundary_certifies
#print axioms replacementChildren
#print axioms replacement_restore
#print axioms replacement_recontextualize
#print axioms replacement_rigid_leaf_changed

end Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement
