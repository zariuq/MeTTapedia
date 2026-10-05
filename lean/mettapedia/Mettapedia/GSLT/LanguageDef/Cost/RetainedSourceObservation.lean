import Mettapedia.GSLT.LanguageDef.CostSemanticSection
import Mettapedia.CategoryTheory.WriterActionTransport

/-!
# Observed free accounts on existing retained semantic fibres

Each static frame already stores an authored source skeleton in its original
typed source fibre.  This module reads the canonical representatives of those
skeletons in tree order.  Semantic normalization retains the frames, so it
preserves this inventory while changing current representatives and boundary
values in place.

The inventory is deliberately named separately from the canonical key of an
erased whole source program.  Boundary placeholders occur in these skeletons;
the inventory alone is not asserted to reconstruct a whole source key, quote,
frame partition, or occurrence identity.  The observed free account model uses
the complete existing retained elaboration as its generator.  It supplies no
substitution operation or iteration of the authored Cost transformer.
-/

open CategoryTheory CategoryTheory.Category

namespace Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.CategoryTheory

set_option autoImplicit false

/-- A source fragment with its original free context, binder telescope and
sort.  The value selected below is its authored canonical representative. -/
abbrev SourceSkeletonCommitment (source : CIGSLT) :=
  Σ free : WellSorted.FreeTypeContext,
    Σ bound : List TypeExpr,
      Σ sort : LangSort source.theory.presentation.presentation.language,
        ReflectiveWellSorted.OpenTerm source.reflection.1
          source.theory.presentation.presentation.language free bound sort

/-- Read the immutable original skeleton; do not read the mutable frame state. -/
def sourceSkeletonCommitment {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (frame : CostStaticRegionNode source color targetFree) :
    SourceSkeletonCommitment source :=
  ⟨frame.boundaryTable.sourceFreeContext, frame.sourceBound, frame.sourceSort,
    source.openCanonical.normalize frame.skeleton⟩

mutual
  /-- Canonical authored skeletons in retained tree order.  Account apparatus
  and static-frame colour do not become additional inventory observations. -/
  def sourceSkeletonInventoryTree {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr} :
      CostSemanticTree source targetFree available outer pattern type →
        List (SourceSkeletonCommitment source)
    | .bvar _ | .fvar _ => []
    | .static frame _ children =>
        sourceSkeletonCommitment frame :: sourceSkeletonInventoryBoundaries children
    | .neutralApplicationOrdinary _ _ _ _ _ _ children =>
        sourceSkeletonInventoryArguments children
    | .neutralApplicationQuote _ _ _ _ _ _ children =>
        sourceSkeletonInventoryArguments children
    | .lambda body => sourceSkeletonInventoryTree body
    | .multiLambda body => sourceSkeletonInventoryTree body
    | .subst body replacement =>
        sourceSkeletonInventoryTree body ++ sourceSkeletonInventoryTree replacement
    | .collection children => sourceSkeletonInventoryElements children

  def sourceSkeletonInventoryArguments {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam} :
      CostSemanticArgumentTrees source targetFree available outer arguments parameters →
        List (SourceSkeletonCommitment source)
    | .nil => []
    | .cons _ _ head tail =>
        sourceSkeletonInventoryTree head ++ sourceSkeletonInventoryArguments tail

  def sourceSkeletonInventoryElements {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr} :
      CostSemanticElementTrees source targetFree available outer elements elementType →
        List (SourceSkeletonCommitment source)
    | .nil _ _ _ => []
    | .cons head tail =>
        sourceSkeletonInventoryTree head ++ sourceSkeletonInventoryElements tail

  def sourceSkeletonInventoryBoundaries {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree table} :
      CostSemanticBoundaryTrees source targetFree color table values →
        List (SourceSkeletonCommitment source)
    | .nil => []
    | .cons head tail =>
        sourceSkeletonInventoryTree head ++ sourceSkeletonInventoryBoundaries tail
end

/-- Bare variable leaves supply no static source skeleton. -/
theorem sourceSkeletonInventoryTree_fvar
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {name : String} {type : TypeExpr}
    (lookup : targetFree name = some type) :
    sourceSkeletonInventoryTree
      (CostSemanticTree.fvar (source := source) (available := available)
        (outer := outer) lookup) = [] := rfl

/-- Distinct admitted variable leaves have the same skeleton inventory.
Thus the inventory by itself cannot recover even their literal variable names. -/
theorem distinct_fvars_same_inventory
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {first second : String} {type : TypeExpr}
    (distinct : first ≠ second)
    (firstLookup : targetFree first = some type)
    (secondLookup : targetFree second = some type) :
    Pattern.fvar first ≠ Pattern.fvar second ∧
      sourceSkeletonInventoryTree
        (CostSemanticTree.fvar (source := source) (available := available)
          (outer := outer) firstLookup) =
      sourceSkeletonInventoryTree
        (CostSemanticTree.fvar (source := source) (available := available)
          (outer := outer) secondLookup) := by
  constructor
  · intro equality
    exact distinct (Pattern.fvar.inj equality)
  · rfl

/-- Every actual stable-frame semantic edge preserves the original source
inventory, including recursively retained boundary elaborations. -/
theorem sourceSkeletonInventoryTree_eq_of_rel
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    {left : CostSemanticTree source targetFree available outer leftPattern type}
    {right : CostSemanticTree source targetFree available outer rightPattern type}
    (relation : CostSemanticTree.Rel source targetFree left right) :
    sourceSkeletonInventoryTree left = sourceSkeletonInventoryTree right := by
  apply CostSemanticTree.Rel.rec
    (motive_1 := fun left right _ =>
      sourceSkeletonInventoryTree left = sourceSkeletonInventoryTree right)
    (motive_2 := fun left right _ =>
      sourceSkeletonInventoryArguments left = sourceSkeletonInventoryArguments right)
    (motive_3 := fun left right _ =>
      sourceSkeletonInventoryElements left = sourceSkeletonInventoryElements right)
    (motive_4 := fun left right _ =>
      sourceSkeletonInventoryBoundaries left = sourceSkeletonInventoryBoundaries right)
    (t := relation)
  all_goals
    intros
    simp_all only [sourceSkeletonInventoryTree, sourceSkeletonInventoryArguments,
      sourceSkeletonInventoryElements, sourceSkeletonInventoryBoundaries]

/-- The derived observation on the existing retained elaboration fibre. -/
def sourceSkeletonInventory {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    List (SourceSkeletonCommitment source) :=
  sourceSkeletonInventoryTree term.2

/-- This observation descends through the actual least semantic equivalence. -/
theorem sourceSkeletonInventory_eq_of_equivalent
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    {left right : CostSemanticElabTerm source targetFree targetBound targetSort}
    (equivalent : (CostSemanticOpenElaboration.equationSetoid source targetFree
      targetBound targetSort).r left right) :
    sourceSkeletonInventory left = sourceSkeletonInventory right := by
  induction equivalent with
  | rel left right edge => exact sourceSkeletonInventoryTree_eq_of_rel edge
  | refl term => rfl
  | symm left right _ equality => exact equality.symm
  | trans left middle right _ _ first second => exact first.trans second

/-- The concrete retained normalizer preserves the derived inventory. -/
theorem sourceSkeletonInventory_normalizeTerm
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    sourceSkeletonInventory (CostSemanticOpenElaboration.normalizeTerm term) =
      sourceSkeletonInventory term :=
  sourceSkeletonInventoryTree_eq_of_rel term.2.normalize_rel_original

/-- The existing retained carrier equipped with an observation computed from
its stored authored origins, rather than a supplied preservation condition. -/
def observedFibre (source : CIGSLT) (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr) (targetSort : LangSort source.costWholeLanguage) :
    Over (List (SourceSkeletonCommitment source)) :=
  Over.mk (TypeCat.ofHom (@sourceSkeletonInventory source targetFree targetBound targetSort))

/-- Install the checked free-account action on this observed retained fibre. -/
def accountFibre (M : Type) [Monoid M] (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    Over (Action.trivial M (List (SourceSkeletonCommitment source))) :=
  (WriterActionSlice.install M (List (SourceSkeletonCommitment source))).obj
    (observedFibre source targetFree targetBound targetSort)

/-- Installation retains the entire elaboration while observing its derived
inventory independently of the added account. -/
theorem accountFibre_observation_apply (M : Type) [Monoid M] (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage)
    (account : M) (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    (accountFibre M source targetFree targetBound targetSort).hom.hom (account, term) =
      sourceSkeletonInventory term := rfl

/-- A genuine map over the computed observation induced by the existing
in-place normalizer.  Its triangle is proved from the retained semantic edges. -/
def normalizeObservedFibre (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    observedFibre source targetFree targetBound targetSort ⟶
      observedFibre source targetFree targetBound targetSort :=
  Over.homMk (TypeCat.ofHom CostSemanticOpenElaboration.normalizeTerm) (by
    apply ConcreteCategory.ext_apply
    intro term
    exact sourceSkeletonInventory_normalizeTerm term)

/-- The concrete retained normalizer acts equivariantly on free accounts and
preserves the derived observation. -/
def normalizeAccountFibre (M : Type) [Monoid M] (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    accountFibre M source targetFree targetBound targetSort ⟶
      accountFibre M source targetFree targetBound targetSort :=
  (WriterActionSlice.install M (List (SourceSkeletonCommitment source))).map
    (normalizeObservedFibre source targetFree targetBound targetSort)

theorem normalizeAccountFibre_apply (M : Type) [Monoid M] (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage)
    (account : M) (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    (normalizeAccountFibre M source targetFree targetBound targetSort).left.hom
      (account, term) = (account, CostSemanticOpenElaboration.normalizeTerm term) := rfl

/-- Account changes commute with the actual retained normalization. -/
theorem normalize_account_transport {M N : Type} [Monoid M] [Monoid N]
    (accounts : M →* N) (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    (normalizeAccountFibre M source targetFree targetBound targetSort).left.hom ≫
      (WriterActionTransport.freeMap accounts id).hom =
    (WriterActionTransport.freeMap accounts id).hom ≫
      (normalizeAccountFibre N source targetFree targetBound targetSort).left.hom := rfl

end Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation
