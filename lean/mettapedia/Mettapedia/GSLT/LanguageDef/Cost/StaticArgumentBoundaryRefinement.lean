import Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement

/-!
# Retained boundary insertion in an enclosing static constructor

The enclosing operator and its single ordinary parameter come from an actual
declared static constructor and its authored preimage.  Its replacement
argument introduces a new foreign boundary.  The frame is reconstructed from
that refined plan and its derived source skeleton; the supplied semantic
subtree is grafted into the new table without compact recompilation.

This is the one-argument application case of structural frame refinement.
General argument spines, collections, binder lifting and composed source
substitutions still require their recursive construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted
open StaticLeafBoundaryRefinement

/-- Change only the parameter-list index of a retained argument plan. -/
def reindexArgumentParameters {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String} {before arguments : List Pattern}
    {first second : List TermParam} (equal : first = second)
    (p : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments first) :
    CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments second :=
  equal ▸ p

theorem reindexArgumentParameters_packet
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String} {before arguments : List Pattern}
    {first second : List TermParam} (equal : first = second)
    (p : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments first) :
    (reindexArgumentParameters equal p).boundaryPacket = p.boundaryPacket := by
  cases equal
  rfl

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
  (shell : source.DeclaredCostConstructor)
  (current : source.declaredCostConstructorRole shell = .static color)
  (preimage : CostStaticConstructorPreimage source color shell)
  (notBare : ¬ UsesBareCollection preimage.sourceConstructor.1)
  (parameterName : String) (sourceType : TypeExpr)
  (oneParameter : preimage.sourceConstructor.1.params =
    [.simple parameterName sourceType])
  (categorySupported : preimage.sourceConstructor.1.category ∈
    source.theory.presentation.presentation.language.types)

/-- The exact support convention of the existing static planner. -/
def argumentAvailable : List TypeExpr :=
  if ReflectiveContextSupport.isQuoteConstructor source.reflection.1
      preimage.sourceConstructor.1.label then [] else targetBound

variable (principal : source.DeclaredCostConstructor)
  (outsideCurrent : source.declaredCostConstructorRole principal ≠ .static color)
  (arguments : List Pattern)
  (admitted : ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
    (argumentAvailable (targetBound := targetBound) shell preimage)
    (mapTypeExpr (color.symbols source) sourceType)
    (.apply (source.renderDeclaredCostConstructor principal) arguments))

/-- The replacement is located in the shell's exact argument occurrence. -/
def argumentPlan :
    CostStaticArgumentPlan source color targetFree
      (CostStaticTypeThinning.sourceContextOfTarget source.theory color targetBound)
      targetBound (CostStaticTypeThinning.ofTargetThinning source.theory color targetBound)
      (argumentAvailable (targetBound := targetBound) shell preimage) .hole
      (source.renderDeclaredCostConstructor shell) []
      [.apply (source.renderDeclaredCostConstructor principal) arguments]
      preimage.sourceConstructor.1.params :=
  reindexArgumentParameters oneParameter.symm (.cons trivial rfl
    (replacementPlan
      (thinning := CostStaticTypeThinning.ofTargetThinning source.theory color targetBound)
      principal outsideCurrent arguments admitted
      (OneHoleContext.hole.comp
        (.apply (source.renderDeclaredCostConstructor shell) [] .hole [])))
    .nil)

/-- Reconstruct the enclosing plan from its declared source operator. -/
def plan :
    CostStaticRegionPlan source color targetFree
      (CostStaticTypeThinning.sourceContextOfTarget source.theory color targetBound)
      targetBound (CostStaticTypeThinning.ofTargetThinning source.theory color targetBound)
      targetBound .hole
      (.apply (source.renderDeclaredCostConstructor shell)
        [.apply (source.renderDeclaredCostConstructor principal) arguments])
      (.base preimage.sourceConstructor.1.category) :=
  .application shell rfl current preimage notBare
    (argumentPlan shell preimage parameterName sourceType oneParameter
      principal outsideCurrent arguments admitted)

include admitted in
private theorem replacement_typed_in_bound :
    HasType source.costWholeLanguage targetFree targetBound
      (.apply (source.renderDeclaredCostConstructor principal) arguments)
      (mapTypeExpr (color.symbols source) sourceType) := by
  by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
      source.reflection.1 preimage.sourceConstructor.1.label = true
  · have typed : HasType source.costWholeLanguage targetFree []
        (.apply (source.renderDeclaredCostConstructor principal) arguments)
        (mapTypeExpr (color.symbols source) sourceType) := by
      simpa [argumentAvailable, quoted] using admitted.1.1
    simpa using typed.extendOuter targetBound
  · simpa [argumentAvailable, quoted] using admitted.1.1

include notBare oneParameter admitted in
theorem refined_term_typed :
    HasType source.costWholeLanguage targetFree targetBound
      (.apply (source.renderDeclaredCostConstructor shell)
        [.apply (source.renderDeclaredCostConstructor principal) arguments])
      (.base ((color.symbols source).sort preimage.sourceConstructor.1.category)) := by
  let rule := source.materializeDeclaredCostConstructor shell
  have membership : rule ∈ source.costWholeLanguage.terms := by
    simpa only [source.costWholeLanguage_terms] using
      source.materializeDeclaredCostConstructor_mem shell
  have targetNotBare : ¬ UsesBareCollection rule := by
    intro bare
    exact notBare (preimage.usesBareCollection_iff.mp bare)
  have typed : HasType source.costWholeLanguage targetFree targetBound
      (.apply rule.label
        [.apply (source.renderDeclaredCostConstructor principal) arguments])
      (.base rule.category) := by
    apply HasType.constructor membership targetNotBare
    rw [show rule.params =
        [.simple parameterName (mapTypeExpr (color.symbols source) sourceType)] by
      simpa [rule, oneParameter, mapTermParam] using preimage.parametersMap]
    exact .cons trivial rfl
      (replacement_typed_in_bound (shell := shell) (preimage := preimage)
        (sourceType := sourceType) (principal := principal) (arguments := arguments)
        admitted) .nil
  simpa only [rule, source.materializeDeclaredCostConstructor_label shell,
    preimage.categoryMap] using typed

def sourceSort : LangSort source.theory.presentation.presentation.language :=
  ⟨preimage.sourceConstructor.1.category, categorySupported⟩

/-- The actual typed enclosing compact term, built from the replacement's
admission rather than by rerunning a compiler. -/
def term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
    (color.mapLangSort source (sourceSort shell preimage categorySupported)) := by
  let typed := refined_term_typed shell preimage notBare parameterName
    sourceType oneParameter principal arguments admitted
  refine ⟨_, typed, ?_, ?_, typed.isWellScopedAt⟩
  · simpa [Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList] using admitted.1.2.1
  · simpa [WellSorted.isObjectPattern, WellSorted.isObjectPatternList] using
      admitted.1.2.2.1

/-- The new frame's source skeleton, support and boundary table are all
derived from the reconstructed enclosing plan. -/
noncomputable def frame : CostStaticRegionNode source color targetFree :=
  CostStaticRegionNode.ofPlan
    (term shell preimage notBare parameterName sourceType oneParameter
      categorySupported principal arguments admitted)
    (plan shell current preimage notBare parameterName sourceType oneParameter
      principal outsideCurrent arguments admitted) rfl

/-- Enclosing the replacement preserves its one occurrence at the argument
path.  This bundled statement also preserves the exact certificate table. -/
theorem plan_boundaryPacket :
    (plan shell current preimage notBare parameterName sourceType oneParameter
      principal outsideCurrent arguments admitted).boundaryPacket =
    (replacementPlan
      (thinning := CostStaticTypeThinning.ofTargetThinning source.theory color targetBound)
      principal outsideCurrent arguments admitted
      (OneHoleContext.hole.comp
        (.apply (source.renderDeclaredCostConstructor shell) [] .hole []))).boundaryPacket := by
  change (argumentPlan shell preimage parameterName sourceType oneParameter
    principal outsideCurrent arguments admitted).boundaryPacket = _
  rw [argumentPlan, reindexArgumentParameters_packet]
  rfl

/-- Graft the supplied retained subtree into the reconstructed frame's exact
derived table.  The packet equality transports only occurrence/table indices. -/
noncomputable def children
    (retained : CostSemanticTree source targetFree
      (argumentAvailable (targetBound := targetBound) shell preimage) []
      (.apply (source.renderDeclaredCostConstructor principal) arguments)
      (mapTypeExpr (color.symbols source) sourceType)) :
    CostSemanticBoundaryTrees source targetFree color
      (frame shell current preimage notBare parameterName sourceType oneParameter
        categorySupported principal outsideCurrent arguments admitted).boundaryTable
      (TypedCostRegionBoundaryTable.Values.original
        (frame shell current preimage notBare parameterName sourceType oneParameter
          categorySupported principal outsideCurrent arguments admitted).boundaryTable) := by
  let p := plan shell current preimage notBare parameterName sourceType oneParameter
    principal outsideCurrent arguments admitted
  change CostSemanticBoundaryTrees source targetFree color p.boundaryTable
    (TypedCostRegionBoundaryTable.Values.original p.boundaryTable)
  exact (congrArg
    (fun packet : TypedCostRegionBoundaryPacket source color targetFree =>
      CostSemanticBoundaryTrees source targetFree color packet.2
        (TypedCostRegionBoundaryTable.Values.original packet.2))
    (plan_boundaryPacket shell current preimage notBare parameterName sourceType
      oneParameter principal outsideCurrent arguments admitted)).mpr
    (replacementChildren
      (thinning := CostStaticTypeThinning.ofTargetThinning source.theory color targetBound)
      principal outsideCurrent arguments admitted
      (OneHoleContext.hole.comp
        (.apply (source.renderDeclaredCostConstructor shell) [] .hole [])) retained)

/-- The reconstructed root is an actual retained semantic Cost tree, with
the original replacement subtree grafted rather than rebuilt. -/
noncomputable def semanticTree (safe : CostStaticCanonicalPathSafe source)
    (retained : CostSemanticTree source targetFree
      (argumentAvailable (targetBound := targetBound) shell preimage) []
      (.apply (source.renderDeclaredCostConstructor principal) arguments)
      (mapTypeExpr (color.symbols source) sourceType)) :
    CostSemanticTree source targetFree targetBound []
      (.apply (source.renderDeclaredCostConstructor shell)
        [.apply (source.renderDeclaredCostConstructor principal) arguments])
      (.base ((color.symbols source).sort preimage.sourceConstructor.1.category)) := by
  let f := frame shell current preimage notBare parameterName sourceType oneParameter
    categorySupported principal outsideCurrent arguments admitted
  let state := CostStaticFrameState.original f (safe f)
  let grafted := children shell current preimage notBare parameterName sourceType
    oneParameter categorySupported principal outsideCurrent arguments admitted retained
  let tree : CostSemanticTree source targetFree f.targetBound []
      (state.actAvailableWithOuter
        (TypedCostRegionBoundaryTable.Values.original f.boundaryTable) []).pattern
      (.base (color.mapLangSort source f.sourceSort).1) :=
    .static f state grafted
  exact tree.reindexPattern
    (CostStaticFrameState.original_actAvailable_pattern f (safe f))

end Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement
