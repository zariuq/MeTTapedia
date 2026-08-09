import Mettapedia.GSLT.LanguageDef.CostSemanticRelation

/-!
# Exact sections on retained semantic Cost syntax

Semantic Cost elaborations normalize in place.  The induced least structural
equivalence is characterized exactly by equality of complete proof-relevant
normal forms.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- One semantic Cost elaboration of an exact compact open term. -/
abbrev CostSemanticOpenElaboration (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :=
  CostSemanticTree source targetFree targetBound [] term.1
    (.base targetSort.1)

/-- The proof-relevant semantic Cost carrier above one typed open fibre. -/
abbrev CostSemanticElabTerm (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :=
  Σ term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort,
    CostSemanticOpenElaboration source term

namespace CostSemanticOpenElaboration

/-- Compile compact syntax to the semantic tree while retaining the stable
static frames certified by the unary canonical path. -/
def compile (source : CIGSLT) (canonicalPathSafe : CostStaticCanonicalPathSafe source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    CostSemanticOpenElaboration source term :=
  (CostRegionTree.buildOpenTerm (source := source) term).toSemantic
    canonicalPathSafe

/-- Package compact syntax with the semantic elaboration selected by the
total region-tree compiler. -/
def compileTerm (source : CIGSLT)
    (canonicalPathSafe : CostStaticCanonicalPathSafe source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    CostSemanticElabTerm source targetFree targetBound targetSort :=
  ⟨term, compile source canonicalPathSafe term⟩

/-- Forget semantic region evidence at the compact execution boundary. -/
def erase {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage} :
    CostSemanticElabTerm source targetFree targetBound targetSort →
      ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
        source.costWholeLanguage targetFree targetBound targetSort :=
  Sigma.fst

@[simp]
theorem erase_compileTerm (source : CIGSLT)
    (canonicalPathSafe : CostStaticCanonicalPathSafe source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    erase (compileTerm source canonicalPathSafe term) = term :=
  rfl

/-- Repackage the normalized semantic pattern in the original typed open
fibre.  No compact recompilation occurs. -/
def normalizeOpen {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (tree : CostSemanticOpenElaboration source term) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort := by
  let normalized := tree.normalize.result.toOpenPattern term.2.1.2.1
    term.2.1.2.2.1 term.2.2
  refine ⟨normalized.1, ?_⟩
  change ReflectiveWellSorted.OpenPatternWellSorted
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound (.base targetSort.1) normalized.1
  simpa using normalized.2

@[simp]
theorem normalizeOpen_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (tree : CostSemanticOpenElaboration source term) :
    (normalizeOpen term tree).1 = tree.normalize.result.pattern :=
  rfl

/-- Normalize the retained semantic tree in place. -/
def normalizeTerm {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    CostSemanticElabTerm source targetFree targetBound targetSort :=
  ⟨normalizeOpen term.1 term.2, term.2.normalize.tree⟩

/-- One semantic edge between retained Cost elaborations. -/
def Step (source : CIGSLT) (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr) (targetSort : LangSort source.costWholeLanguage)
    (left right : CostSemanticElabTerm source targetFree targetBound targetSort) :
    Prop :=
  CostSemanticTree.Rel source targetFree left.2 right.2

/-- The least equivalence generated by stable-frame semantic edges. -/
def equationSetoid (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    Setoid (CostSemanticElabTerm source targetFree targetBound targetSort) where
  r := Relation.EqvGen (Step source targetFree targetBound targetSort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- One semantic edge receives the same complete normalized elaboration. -/
theorem normalizeTerm_eq_of_step {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    {left right : CostSemanticElabTerm source targetFree targetBound targetSort}
    (step : Step source targetFree targetBound targetSort left right) :
    normalizeTerm left = normalizeTerm right := by
  have normalFormEq := CostSemanticTree.Rel.normalForm_eq step
  apply Sigma.ext
  · apply Subtype.ext
    exact congrArg Sigma.fst normalFormEq
  · exact (Sigma.ext_iff.mp normalFormEq).2

/-- Semantic normalization itself is one retained edge back to the input. -/
theorem normalizeTerm_related {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (term : CostSemanticElabTerm source targetFree targetBound targetSort) :
    (equationSetoid source targetFree targetBound targetSort).r
      (normalizeTerm term) term :=
  Relation.EqvGen.rel _ _ term.2.normalize_rel_original

/-- The in-place semantic normalizer is an exact computable section of the
least stable-frame equivalence. -/
def canonicalSection (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    ComputableSetoidSection
      (CostSemanticElabTerm source targetFree targetBound targetSort)
      (equationSetoid source targetFree targetBound targetSort) where
  normalize := normalizeTerm
  equivalent := normalizeTerm_related
  complete := by
    intro left right equivalent
    induction equivalent with
    | rel left right step => exact normalizeTerm_eq_of_step step
    | refl term => rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH

/-- Semantic equivalence is exactly equality of the complete retained normal
forms. -/
theorem equivalent_iff_normalizeTerm_eq (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {targetSort : LangSort source.costWholeLanguage}
    (left right : CostSemanticElabTerm source targetFree targetBound targetSort) :
    (equationSetoid source targetFree targetBound targetSort).r left right ↔
      normalizeTerm left = normalizeTerm right :=
  (canonicalSection source targetFree targetBound targetSort
    ).equivalent_iff_normalize_eq left right

end CostSemanticOpenElaboration

end Mettapedia.GSLT.LanguageDef
