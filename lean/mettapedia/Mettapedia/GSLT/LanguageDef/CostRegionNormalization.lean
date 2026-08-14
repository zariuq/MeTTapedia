import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# Typed normalization of proof-relevant Cost regions

This module keeps semantic normalization proofs separate from the executable
region planner and compiler.  Its primary relation is the typed, split-binder
equation setoid; raw contextual equivalence is only an erasure of that path.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT

namespace WellSorted

/-- Reindex an arbitrary-type open object across an equality of bound
contexts.  The raw pattern and all semantic certificates are unchanged. -/
def OpenPattern.reindexBound
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    (boundEquality : sourceBound = targetBound)
    (pattern : OpenPattern language free sourceBound type) :
    OpenPattern language free targetBound type := by
  cases boundEquality
  exact pattern

@[simp]
theorem OpenPattern.reindexBound_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    (boundEquality : sourceBound = targetBound)
    (pattern : OpenPattern language free sourceBound type) :
    (pattern.reindexBound boundEquality).1 = pattern.1 := by
  cases boundEquality
  rfl

/-- Bound-context reindexing maps a typed authored equation path without
changing any generator. -/
theorem openPatternEquationSetoid_reindexBound
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern language free sourceBound type}
    (boundEquality : sourceBound = targetBound)
    (equivalent :
      (openPatternEquationSetoid language free sourceBound type).r left right) :
    (openPatternEquationSetoid language free targetBound type).r
      (left.reindexBound boundEquality) (right.reindexBound boundEquality) := by
  cases boundEquality
  exact equivalent

end WellSorted

namespace ReflectiveWellSorted

/-- Reindex a reflection-certified open object across an equality of bound
contexts.  The raw pattern and both core and reflection certificates are
unchanged. -/
def OpenPattern.reindexBound
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {free : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    (boundEquality : sourceBound = targetBound)
    (pattern : OpenPattern profile language free sourceBound type) :
    OpenPattern profile language free targetBound type := by
  cases boundEquality
  exact pattern

@[simp]
theorem OpenPattern.reindexBound_pattern
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {free : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    (boundEquality : sourceBound = targetBound)
    (pattern : OpenPattern profile language free sourceBound type) :
    (pattern.reindexBound boundEquality).1 = pattern.1 := by
  cases boundEquality
  rfl

/-- Recontextualize a reflection-certified open pattern when the target free
context preserves every lookup used by its syntax.  This is the arbitrary-
type companion of `OpenTerm.recontextualizeFree`. -/
def OpenPattern.recontextualizeFree
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern profile language sourceFree bound type)
    (preserves : ∀ {name freeType},
      name ∈ pattern.1.freeFvarNames →
      sourceFree name = some freeType → targetFree name = some freeType) :
    OpenPattern profile language targetFree bound type :=
  ⟨pattern.1,
    ⟨pattern.2.1.1.recontextualizeFree preserves,
      pattern.2.1.2.1, pattern.2.1.2.2.1, pattern.2.1.2.2.2⟩,
    pattern.2.2⟩

@[simp]
theorem OpenPattern.recontextualizeFree_pattern
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern profile language sourceFree bound type)
    (preserves : ∀ {name freeType},
      name ∈ pattern.1.freeFvarNames →
      sourceFree name = some freeType → targetFree name = some freeType) :
    (pattern.recontextualizeFree preserves).1 = pattern.1 :=
  rfl

/-- Insert a block of inner binders while retaining both the five-field
typing certificate and quote-sensitive scope. -/
def OpenPattern.weakenRoot
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern profile language free bound type)
    (inner : List TypeExpr) :
    OpenPattern profile language free (inner ++ bound) type := by
  refine ⟨Substitution.liftBVars 0 inner.length pattern.1,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using pattern.2.1.1.liftBVars_insert
      (inner := []) (outer := bound) (inserted := inner)
  · simpa using pattern.2.1.2.1
  · simpa using pattern.2.1.2.2.1
  · exact (pattern.2.1.1.liftBVars_insert
      (inner := []) (outer := bound) (inserted := inner)).isWellScopedAt
  · intro presentation membership
    have lifted := ContextSubstitution.binderSafeAt_liftBVars
      presentation.quoteConstructor
      (ambient := bound.length) (cutoff := 0) (shift := inner.length)
      (pattern.2.2 presentation membership)
    simpa [List.length_append, Nat.add_comm] using lifted

@[simp]
theorem OpenPattern.weakenRoot_pattern
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern profile language free bound type)
    (inner : List TypeExpr) :
    (pattern.weakenRoot inner).1 =
      Substitution.liftBVars 0 inner.length pattern.1 :=
  rfl

/-- Bound-context reindexing preserves the reflection-certified authored
equation path without changing any generator. -/
theorem reflectiveOpenPatternEquationSetoid_reindexBound
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {free : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern profile language free sourceBound type}
    (boundEquality : sourceBound = targetBound)
    (equivalent :
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        profile defaultBasePremises language free sourceBound type).r
        left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      profile defaultBasePremises language free targetBound type).r
      (left.reindexBound boundEquality) (right.reindexBound boundEquality) := by
  cases boundEquality
  exact equivalent

/-- A typed reflective equation path can be recontextualized along a
pointwise extension of its free-variable typing context.  Every intermediate
vertex retains its own typing certificate; the raw authored generator is
unchanged. -/
theorem reflectiveOpenPatternEquationSetoid_recontextualizeFree
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (preservesLookup : ∀ {name freeType},
      sourceFree name = some freeType → targetFree name = some freeType)
    {left right : OpenPattern profile language sourceFree bound type}
    (equivalent :
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        profile defaultBasePremises language sourceFree bound type).r
        left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      profile defaultBasePremises language targetFree bound type).r
      (left.recontextualizeFree
        (fun _membership lookup => preservesLookup lookup))
      (right.recontextualizeFree
        (fun _membership lookup => preservesLookup lookup)) := by
  let map := fun pattern : OpenPattern profile language sourceFree bound type =>
    pattern.recontextualizeFree
      (fun _membership lookup => preservesLookup lookup)
  change (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
    profile defaultBasePremises language targetFree bound type).r
    (map left) (map right)
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (by
        unfold ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
          at generator ⊢
        simpa [map] using generator)
  | refl pattern => exact Relation.EqvGen.refl (map pattern)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

end ReflectiveWellSorted

/-- Root weakening for the explicit reflection-profile fibre.  This is
separate from core weakening because a quote boundary must remain sealed at
every intermediate equation vertex. -/
def ReflectiveOpenPatternEquationWeakeningStable
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (language : LanguageDef) : Prop :=
  ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr}
    {left right : ReflectiveWellSorted.OpenPattern
      profile language free bound type},
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      profile defaultBasePremises language free bound type).r left right →
      ∀ inner : List TypeExpr,
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
          profile defaultBasePremises language free (inner ++ bound) type).r
          (left.weakenRoot inner) (right.weakenRoot inner)

/-- Generator stability under root weakening lifts to the complete
reflection-certified equation setoid. -/
theorem WellSorted.ReflectiveEquationContextStepRootWeakeningStable.toReflectiveOpenPattern
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef}
    (stable : WellSorted.ReflectiveEquationContextStepRootWeakeningStable
      profile language) :
    ReflectiveOpenPatternEquationWeakeningStable profile language := by
  intro free bound type left right equivalent inner
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (by
        unfold ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
          at generator ⊢
        simpa only [ReflectiveWellSorted.OpenPattern.weakenRoot_pattern] using
          stable generator inner.length)
  | refl pattern => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- The exact laws consumed by typed unary normalization.

The same-colour action is local to one certified static region.  Weakening is
required only for already-typed child paths.  In particular, this interface
does not demand the false property that every mixed-colour raw equation path
remain in one arbitrary typing fibre. -/
structure CostTypedUnaryNormalizationLaws (source : CIGSLT) : Prop where
  mappedGeneratorFiberAction : CostStaticMappedGeneratorFiberAction source
  weakeningStable : ReflectiveOpenPatternEquationWeakeningStable
    source.costWholeReflectionProfile source.costWholeLanguage
  canonicalPathSafe : CostStaticCanonicalPathSafe source

/-- Local typed laws for an arbitrary static-region normalizer.

The frame law is deliberately stated at one static node and its current
finite boundary vector.  It is therefore strong enough to drive the
structural tree proof, but is not a conclusion-shaped assumption about a
complete Cost program. -/
structure CostTypedStaticRegionNormalizerLaws
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source) :
    Prop where
  weakeningStable : ReflectiveOpenPatternEquationWeakeningStable
    source.costWholeReflectionProfile source.costWholeLanguage
  normalizesCurrentFrame : ∀
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable),
    (values.supportedOpenAssignment node.boundaryTable).FiberEquivalent
        ((TypedCostRegionBoundaryTable.Values.original node.boundaryTable
          ).supportedOpenAssignment node.boundaryTable) →
      (WellSorted.AvailableOpenPattern.equationSetoid
        (profile := source.costWholeReflectionProfile)
        source.costWholeLanguage targetFree node.targetBound []
          (.base (color.mapLangSort source node.sourceSort).1)).r
        (WellSorted.AvailableOpenPattern.ofOpenPattern
          (normalizeStatic node values))
        node.termAvailable

namespace CostTypedUnaryNormalizationLaws

/-- The original mapped-action laws instantiate the arbitrary-normalizer
interface for the established static-frame normalizer. -/
def toStaticRegionNormalizerLaws {source : CIGSLT}
    (laws : CostTypedUnaryNormalizationLaws source) :
    CostTypedStaticRegionNormalizerLaws source
      (fun node values => node.normalizeWithReflective values) where
  weakeningStable := laws.weakeningStable
  normalizesCurrentFrame := by
    intro color targetFree node values valuesEquivalent
    simpa only [CostStaticRegionNode.normalizeWithAvailable] using
      node.normalizeWithAvailable_equationSetoid
        laws.mappedGeneratorFiberAction values valuesEquivalent
          (laws.canonicalPathSafe node)

end CostTypedUnaryNormalizationLaws

namespace CostRegionTree

/-- The proof-relevant tree index is the exact original compact pattern. -/
@[simp]
theorem originalAvailableOpenPattern_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.originalAvailableOpenPattern canonical object scope).pattern =
      pattern :=
  rfl

/-- Package the normalized endpoint in the exact split binder fibre carried
by the tree index. -/
def normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer type :=
  (tree.normalize (normalizeStatic := normalizeStatic)).toAvailableOpenPattern
    canonical object scope

@[simp]
theorem normalizedAvailable_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    (tree.normalizedAvailable canonical object scope
      (normalizeStatic := normalizeStatic)).pattern =
      (tree.normalize (normalizeStatic := normalizeStatic)).pattern :=
  rfl

/-- Package one tree as the original endpoint of an authored constructor
argument. -/
def originalArgument {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation :
      WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameter type where
  term := tree.originalAvailableOpenPattern canonical object scope
  representation := representation
  parameterType := parameterType

/-- Package the same constructor argument after recursive normalization.
Representation preservation is supplied by the normalization result itself. -/
def normalizedArgument {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation :
      WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameter type where
  term := tree.normalizedAvailable canonical object scope
    (normalizeStatic := normalizeStatic)
  representation :=
    (tree.normalize (normalizeStatic := normalizeStatic)
      ).matchesParameterRepresentation parameter representation
  parameterType := parameterType

@[simp]
theorem originalArgument_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation :
      WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.originalArgument parameter representation parameterType canonical
      object scope).term.pattern = pattern :=
  rfl

@[simp]
theorem normalizedArgument_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation :
      WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    (tree.normalizedArgument parameter representation parameterType canonical
      object scope (normalizeStatic := normalizeStatic)).term.pattern =
        (tree.normalize (normalizeStatic := normalizeStatic)).pattern :=
  rfl

end CostRegionTree

namespace CostRegionArgumentTrees

/-- Package an authored constructor spine before normalization. -/
def originalAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameters :=
  WellSorted.AvailableOpenArguments.ofCertificates trees.originalTyped
    canonical objects scope

/-- Package the normalized constructor spine in the same authored parameter
fibre. -/
def normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    WellSorted.AvailableOpenArguments source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameters :=
  let normalized := trees.normalize (normalizeStatic := normalizeStatic)
  WellSorted.AvailableOpenArguments.ofCertificates normalized.typed
    (normalized.canonicalBinderMetadata canonical)
    (normalized.objectPatterns objects)
    (fun presentation membership =>
      normalized.reflectiveScope presentation membership
        (Nat.le_refl available.length) (scope presentation membership))

@[simp]
theorem originalAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    (trees.originalAvailable canonical objects scope).patterns = arguments :=
  rfl

@[simp]
theorem normalizedAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    (trees.normalizedAvailable canonical objects scope
      (normalizeStatic := normalizeStatic)).patterns =
      (trees.normalize (normalizeStatic := normalizeStatic)).patterns :=
  rfl

end CostRegionArgumentTrees

namespace CostRegionElementTrees

/-- Package a homogeneous element spine before normalization. -/
def originalAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer elementType :=
  WellSorted.AvailableOpenElements.ofCertificates trees.originalTyped
    canonical objects scope

/-- Package the normalized homogeneous spine in the same element fibre. -/
def normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    WellSorted.AvailableOpenElements source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer elementType :=
  let normalized := trees.normalize (normalizeStatic := normalizeStatic)
  WellSorted.AvailableOpenElements.ofCertificates normalized.typed
    (normalized.canonicalBinderMetadata canonical)
    (normalized.objectPatterns objects)
    (fun presentation membership =>
      normalized.reflectiveScope presentation membership
        (Nat.le_refl available.length) (scope presentation membership))

@[simp]
theorem originalAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    (trees.originalAvailable canonical objects scope).patterns = elements :=
  rfl

@[simp]
theorem normalizedAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true)
    (normalizeStatic : CostStaticRegionNormalizer source :=
      fun node values => node.normalizeWithReflective values) :
    (trees.normalizedAvailable canonical objects scope
      (normalizeStatic := normalizeStatic)).patterns =
      (trees.normalize (normalizeStatic := normalizeStatic)).patterns :=
  rfl

end CostRegionElementTrees

namespace TypedCostRegionBoundaryTable.Values

/-- The exact original open value carried by one proof-relevant boundary. -/
private def boundaryOriginalValue
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundary source color targetFree) :
    ReflectiveWellSorted.OpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree boundary.boundary.targetSupport
      boundary.boundary.targetType :=
  ⟨boundary.boundary.content,
    ⟨boundary.contentTyped, boundary.contentCanonicalBinderMetadata,
      boundary.contentObjectPattern, boundary.contentTyped.isWellScopedAt⟩,
    boundary.contentReflectiveScopeSafe⟩

/-- A typed path for one replacement head, stable under every added inner
binder, extends a fiberwise-equivalent tail to the complete finite supported
assignment. -/
theorem supportedOpenAssignment_cons_fiberEquivalent
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    {boundary : TypedCostRegionBoundary source color targetFree}
    {content : boundary.boundary.content = occurrence.content}
    {tail : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (value : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType)
    (values : Values source color targetFree tail)
    (headEquivalent : ∀ inner : List TypeExpr,
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree
          (inner ++ boundary.boundary.targetSupport)
          boundary.boundary.targetType).r
        (value.weakenRoot inner)
        ((boundaryOriginalValue boundary).weakenRoot inner))
    (tailEquivalent :
      (values.supportedOpenAssignment tail).FiberEquivalent
        ((Values.original tail).supportedOpenAssignment tail)) :
    ((Values.cons value values).supportedOpenAssignment
      (.cons boundary content tail)).FiberEquivalent
    ((Values.original (.cons boundary content tail)).supportedOpenAssignment
      (.cons boundary content tail)) := by
  intro name type lookup inner
  cases decodedName : decodeCostRegionSourceVariableName name with
  | some sourceName =>
      simpa [WellSorted.SupportedOpenAssignment.weakenedValue,
        supportedOpenAssignment, supportedAssignment, assignment,
        TypedCostRegionBoundaryTable.restorationSupport, decodedName] using
        ((ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
          source.costWholeReflectionProfile defaultBasePremises
          source.costWholeLanguage targetFree
            (inner ++
              (TypedCostRegionBoundaryTable.cons boundary content tail
                ).restorationSupport name) type).iseqv.refl
          (WellSorted.SupportedOpenAssignment.weakenedValue
            ((Values.cons value values).supportedOpenAssignment
              (.cons boundary content tail)) lookup inner))
  | none =>
      by_cases keyEquality :
          name = costRegionBoundaryVariableName boundary.boundary
      · subst name
        have typeEquality : boundary.boundary.targetType = type := by
          simpa [TypedCostRegionBoundaryTable.mappedFreeContext,
            TypedCostRegionBoundaryTable.resolve,
            decodeCostRegionSourceVariableName_boundary] using lookup
        subst type
        have supportEquality :
            (TypedCostRegionBoundaryTable.cons boundary content tail
              ).restorationSupport
                (costRegionBoundaryVariableName boundary.boundary) =
              boundary.boundary.targetSupport := by
          simp [TypedCostRegionBoundaryTable.restorationSupport,
            TypedCostRegionBoundaryTable.resolve,
            decodeCostRegionSourceVariableName_boundary]
        let boundEquality :
            inner ++ boundary.boundary.targetSupport =
              inner ++
                (TypedCostRegionBoundaryTable.cons boundary content tail
                  ).restorationSupport
                    (costRegionBoundaryVariableName boundary.boundary) :=
          congrArg (fun support => inner ++ support) supportEquality.symm
        have transported :=
          ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
            boundEquality
            (headEquivalent inner)
        have leftEndpoint :
            (value.weakenRoot inner).reindexBound boundEquality =
              WellSorted.SupportedOpenAssignment.weakenedValue
                ((Values.cons value values).supportedOpenAssignment
                  (.cons boundary content tail)) lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodeCostRegionSourceVariableName_boundary]
        have rightEndpoint :
            ((boundaryOriginalValue boundary).weakenRoot inner).reindexBound
                boundEquality =
              WellSorted.SupportedOpenAssignment.weakenedValue
                ((Values.original (.cons boundary content tail)
                  ).supportedOpenAssignment
                    (.cons boundary content tail)) lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            original, decodeCostRegionSourceVariableName_boundary,
            boundaryOriginalValue]
        rw [leftEndpoint, rightEndpoint] at transported
        exact transported
      · have tailLookup : tail.mappedFreeContext name = some type := by
          simpa [TypedCostRegionBoundaryTable.mappedFreeContext,
            TypedCostRegionBoundaryTable.resolve, decodedName, keyEquality]
            using lookup
        have tailStep := tailEquivalent tailLookup inner
        have supportEquality :
            (TypedCostRegionBoundaryTable.cons boundary content tail
              ).restorationSupport name =
              tail.restorationSupport name := by
          simp [TypedCostRegionBoundaryTable.restorationSupport,
            TypedCostRegionBoundaryTable.resolve, decodedName, keyEquality]
        let boundEquality :
            inner ++ tail.restorationSupport name =
              inner ++
                (TypedCostRegionBoundaryTable.cons boundary content tail
                  ).restorationSupport name :=
          congrArg (fun support => inner ++ support) supportEquality.symm
        have transported :=
          ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
            boundEquality
            tailStep
        have leftEndpoint :
            ((values.supportedOpenAssignment tail).weakenedValue
              tailLookup inner).reindexBound boundEquality =
              ((Values.cons value values).supportedOpenAssignment
                (.cons boundary content tail)).weakenedValue lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodedName, keyEquality]
        have rightEndpoint :
            (((Values.original tail).supportedOpenAssignment tail
              ).weakenedValue tailLookup inner).reindexBound boundEquality =
              ((Values.original (.cons boundary content tail)
                ).supportedOpenAssignment
                  (.cons boundary content tail)).weakenedValue lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            original, decodedName, keyEquality]
        rw [leftEndpoint, rightEndpoint] at transported
        exact transported

end TypedCostRegionBoundaryTable.Values

namespace CostRegionTree

/-- Any split-fiber term path can be viewed as a path for a simple authored
parameter.  Simple parameters impose no additional representation invariant. -/
theorem simpleArgument_equationSetoid
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameterName : String) (parameterTypeExpression : TypeExpr)
    (parameterType :
      WellSorted.parameterType?
        (.simple parameterName parameterTypeExpression) = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (normalizeStatic : CostStaticRegionNormalizer source)
    (equivalent :
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope
          (normalizeStatic := normalizeStatic))
        (tree.originalAvailableOpenPattern canonical object scope)) :
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree available outer
        (.simple parameterName parameterTypeExpression) type).r
      (tree.normalizedArgument (.simple parameterName parameterTypeExpression)
        True.intro parameterType canonical object scope
          (normalizeStatic := normalizeStatic))
      (tree.originalArgument (.simple parameterName parameterTypeExpression)
        True.intro parameterType canonical object scope) := by
  let pack := fun
      (term : WellSorted.AvailableOpenPattern
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available outer type) =>
    ({ term := term
       representation := True.intro
       parameterType := parameterType } :
      WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
        source.costWholeLanguage targetFree available outer
          (.simple parameterName parameterTypeExpression) type)
  have packed :=
    WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
      (by
        intro left right generator
        exact generator)
      equivalent
  have leftEndpoint :
      pack (tree.normalizedAvailable canonical object scope
        (normalizeStatic := normalizeStatic)) =
        tree.normalizedArgument (.simple parameterName parameterTypeExpression)
          True.intro parameterType canonical object scope
            (normalizeStatic := normalizeStatic) := by
    apply WellSorted.AvailableOpenArgument.ext
    rfl
  have rightEndpoint :
      pack (tree.originalAvailableOpenPattern canonical object scope) =
        tree.originalArgument (.simple parameterName parameterTypeExpression)
          True.intro parameterType canonical object scope := by
    apply WellSorted.AvailableOpenArgument.ext
    rfl
  rw [leftEndpoint, rightEndpoint] at packed
  exact packed

end CostRegionTree

/-! ## Typed child-first normalization path

The recursive proof follows the proof-relevant region forest itself.  Each
intermediate vertex remains in the exact split binder and authored parameter
fiber carried by the corresponding tree index. -/

mutual
  /-- Child-first normalization of one complete region tree is an authored
  equation path in its exact split binder and typing fiber. -/
  theorem CostRegionTree.normalizeWithStatic_equationSetoid
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      ∀
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length pattern),
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope
          (normalizeStatic := normalizeStatic))
        (tree.originalAvailableOpenPattern canonical object scope) :=
    match tree with
    | @CostRegionTree.bvar source targetFree available outer index type lookup =>
      fun canonical object scope => by
        have endpoint :
            (CostRegionTree.bvar (source := source)
              (targetFree := targetFree) lookup).normalizedAvailable canonical
                object scope (normalizeStatic := normalizeStatic) =
              (CostRegionTree.bvar (source := source)
                (targetFree := targetFree) lookup
                ).originalAvailableOpenPattern canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.originalAvailableOpenPattern_pattern,
            CostRegionTree.normalize]
        rw [endpoint]
        exact Relation.EqvGen.refl _
    | @CostRegionTree.fvar source targetFree available outer name type lookup =>
      fun canonical object scope => by
        have endpoint :
            (CostRegionTree.fvar (source := source)
                (targetFree := targetFree) (available := available)
                (outer := outer) lookup).normalizedAvailable canonical object
                  scope (normalizeStatic := normalizeStatic) =
              (CostRegionTree.fvar (source := source)
                (targetFree := targetFree) (available := available)
                  (outer := outer) lookup
                ).originalAvailableOpenPattern canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.originalAvailableOpenPattern_pattern,
            CostRegionTree.normalize]
        rw [endpoint]
        exact Relation.EqvGen.refl _
    | @CostRegionTree.static source targetFree color outer node children =>
      fun canonical object scope => by
        let values := children.normalizeValues
          (normalizeStatic := normalizeStatic)
        have valuesEquivalent :
            (values.supportedOpenAssignment
              node.finiteBoundaryTable).FiberEquivalent
              ((TypedCostRegionBoundaryTable.Values.original
                node.finiteBoundaryTable).supportedOpenAssignment
                  node.finiteBoundaryTable) := by
          intro name type lookup inner
          exact children.normalizeValuesWithStatic_fiberEquivalent
            normalizeStatic laws lookup inner
        have localStep := laws.normalizesCurrentFrame node values
          valuesEquivalent
        have openStepRaw :=
          WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
            localStep
        have openStep :=
          ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
            (List.append_nil node.targetBound) openStepRaw
        have lifted :=
          WellSorted.AvailableOpenPattern.reflectiveOpenPatternEquationSetoid_to_availableWithOuter
            outer openStep
        have leftEndpoint :
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
                ((WellSorted.AvailableOpenPattern.ofOpenPattern
                  (normalizeStatic node values)
                    ).toReflectiveOpenPattern.reindexBound
                      (List.append_nil node.targetBound)) outer =
              (CostRegionTree.static node children).normalizedAvailable
                canonical object scope (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenPattern.ext
          simp only [
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
            WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
            CostRegionTree.normalizedAvailable_pattern]
          simp only [WellSorted.AvailableOpenPattern.ofOpenPattern_pattern,
            CostRegionTree.normalize, values]
        have rightEndpoint :
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
                (node.termAvailable.toReflectiveOpenPattern.reindexBound
                  (List.append_nil node.targetBound)) outer =
              (CostRegionTree.static node children).originalAvailableOpenPattern
                canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          simp only [
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
            WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
            CostRegionTree.originalAvailableOpenPattern_pattern]
          change node.term.1 = node.term.1
          rfl
        rw [leftEndpoint, rightEndpoint] at lifted
        exact lifted
    | @CostRegionTree.neutralApplicationOrdinary source targetFree available outer rule
        arguments membership notBareCollection constructor materializes neutral
        ordinary children => fun canonical object scope => by
        have argumentCanonical :
            Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have argumentObjects :
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPattern] using object
        have argumentScope : ∀ presentation ∈
            source.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor available.length
              arguments = true := by
          intro presentation presentationMembership
          have notThisQuote :
              rule.label ≠ presentation.quoteConstructor := by
            intro labelEquality
            have detected : ReflectiveContextSupport.isQuoteConstructor
                source.costWholeReflectionProfile rule.label = true := by
              unfold ReflectiveContextSupport.isQuoteConstructor
              rw [List.any_eq_true]
              exact ⟨presentation, presentationMembership,
                by simp [labelEquality]⟩
            rw [detected] at ordinary
            contradiction
          exact binderSafeListAt_of_binderSafeAt_apply_of_ne
            presentation.quoteConstructor rule.label available.length
              arguments notThisQuote (scope presentation
                presentationMembership)
        have argumentsStep := children.normalizeWithStatic_equationForall₂ normalizeStatic laws
          argumentCanonical argumentObjects argumentScope
        have assembled := argumentsStep.assembleOrdinary membership
          notBareCollection ordinary
        have leftEndpoint :
            (children.normalizedAvailable argumentCanonical argumentObjects
              argumentScope (normalizeStatic := normalizeStatic)
                ).applyOrdinary membership notBareCollection
                ordinary =
              (CostRegionTree.neutralApplicationOrdinary membership
                notBareCollection constructor materializes neutral ordinary
                  children).normalizedAvailable canonical object scope
                    (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [CostRegionArgumentTrees.normalizedAvailable_patterns,
            CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.normalize]
        have rightEndpoint :
            (children.originalAvailable argumentCanonical argumentObjects
              argumentScope).applyOrdinary membership notBareCollection
                ordinary =
              (CostRegionTree.neutralApplicationOrdinary membership
                notBareCollection constructor materializes neutral ordinary
                  children).originalAvailableOpenPattern canonical object
                    scope := by
          apply WellSorted.AvailableOpenPattern.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at assembled
        exact assembled
    | @CostRegionTree.neutralApplicationQuote source targetFree available outer rule arguments
        membership notBareCollection constructor materializes neutral quoted
        children => fun canonical object scope => by
        have argumentCanonical :
            Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have argumentObjects :
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPattern] using object
        have parentScopeAtBound :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              source.costWholeReflectionProfile
              (available ++ outer).length (.apply rule.label arguments) := by
          intro presentation presentationMembership
          exact binderSafeAt_mono presentation.quoteConstructor
            (scope presentation presentationMembership) (by simp)
        have argumentsTyped :
            WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
              (available ++ outer) arguments rule.params := by
          simpa only [List.nil_append] using children.originalTyped
        have argumentScope :=
          WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
            source.costWholeLanguage_validate
              source.costWholeReflectionProfile_validate membership
                argumentsTyped quoted parentScopeAtBound
        have argumentsStep := children.normalizeWithStatic_equationForall₂ normalizeStatic laws
          argumentCanonical argumentObjects argumentScope
        have assembled := argumentsStep.assembleQuote membership
          notBareCollection quoted
        have leftEndpoint :
            (children.normalizedAvailable argumentCanonical argumentObjects
              argumentScope (normalizeStatic := normalizeStatic)).applyQuote
                membership notBareCollection quoted =
              (CostRegionTree.neutralApplicationQuote membership
                notBareCollection constructor materializes neutral quoted
                  children).normalizedAvailable canonical object scope
                    (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [CostRegionArgumentTrees.normalizedAvailable_patterns,
            CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.normalize]
        have rightEndpoint :
            (children.originalAvailable argumentCanonical argumentObjects
              argumentScope).applyQuote membership notBareCollection quoted =
              (CostRegionTree.neutralApplicationQuote membership
                notBareCollection constructor materializes neutral quoted
                  children).originalAvailableOpenPattern canonical object
                    scope := by
          apply WellSorted.AvailableOpenPattern.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at assembled
        exact assembled
    | @CostRegionTree.lambda source targetFree available outer binder body domain codomain
        bodyTree => fun canonical object scope => by
        have canonicalParts :
            binder.isNone = true ∧
              body.hasCanonicalBinderMetadata = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have bodyObject : WellSorted.isObjectPattern body = true := by
          simpa [WellSorted.isObjectPattern] using object
        have bodyScope :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              source.costWholeReflectionProfile
                (domain :: available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_cons] using
            scope presentation presentationMembership
        have bodyStep := bodyTree.normalizeWithStatic_equationSetoid normalizeStatic laws
          canonicalParts.2 bodyObject bodyScope
        have assembled :=
          WellSorted.AvailableOpenPattern.equationSetoid_lambda_congr binder
            canonicalParts.1 bodyStep
        have leftEndpoint :
            (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
              (normalizeStatic := normalizeStatic)).lambda binder
                canonicalParts.1 =
              (CostRegionTree.lambda bodyTree).normalizedAvailable canonical
                object scope (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [WellSorted.AvailableOpenPattern.lambda_pattern,
            CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.normalize]
        have rightEndpoint :
            (bodyTree.originalAvailableOpenPattern canonicalParts.2 bodyObject
              bodyScope).lambda binder canonicalParts.1 =
              (CostRegionTree.lambda bodyTree).originalAvailableOpenPattern
                canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at assembled
        exact assembled
    | @CostRegionTree.multiLambda source targetFree available outer arity binders body domain
        codomain bodyTree => fun canonical object scope => by
        have canonicalParts :
            binders.isEmpty = true ∧
              body.hasCanonicalBinderMetadata = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have bindersCanonical : binders = [] := by
          simpa using canonicalParts.1
        have bodyObject : WellSorted.isObjectPattern body = true := by
          simpa [WellSorted.isObjectPattern] using object
        have bodyScope :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              source.costWholeReflectionProfile
                (List.replicate arity domain ++ available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_append, List.length_replicate,
            Nat.add_comm] using scope presentation presentationMembership
        have bodyStep := bodyTree.normalizeWithStatic_equationSetoid normalizeStatic laws
          canonicalParts.2 bodyObject bodyScope
        have assembled :=
          WellSorted.AvailableOpenPattern.equationSetoid_multiLambda_congr
            arity binders bindersCanonical bodyStep
        have leftEndpoint :
            (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
              (normalizeStatic := normalizeStatic)).multiLambda arity binders
                bindersCanonical =
              (CostRegionTree.multiLambda bodyTree).normalizedAvailable
                canonical object scope (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenPattern.ext
          simp [WellSorted.AvailableOpenPattern.multiLambda_pattern,
            CostRegionTree.normalizedAvailable_pattern,
            CostRegionTree.normalize]
        have rightEndpoint :
            (bodyTree.originalAvailableOpenPattern canonicalParts.2 bodyObject
              bodyScope).multiLambda arity binders bindersCanonical =
              (CostRegionTree.multiLambda bodyTree
                ).originalAvailableOpenPattern canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at assembled
        exact assembled
    | @CostRegionTree.subst source targetFree available outer body replacement domain codomain
        bodyTree replacementTree => fun canonical object scope => by
        simp [WellSorted.isObjectPattern] at object
    | @CostRegionTree.collection source targetFree available outer collectionType elements
        rest elementType children => fun canonical object scope => by
        cases rest with
        | some restName =>
            simp [WellSorted.isObjectPattern] at object
        | none =>
            have elementCanonical :
                Pattern.hasCanonicalBinderMetadataList elements = true := by
              simpa [Pattern.hasCanonicalBinderMetadata] using canonical
            have elementObjects :
                WellSorted.isObjectPatternList elements = true := by
              simpa [WellSorted.isObjectPattern] using object
            have elementScope : ∀ presentation ∈
                source.costWholeReflectionProfile.presentations,
                binderSafeListAt presentation.quoteConstructor available.length
                  elements = true := by
              intro presentation presentationMembership
              simpa [binderSafeAt] using
                scope presentation presentationMembership
            have elementsStep := children.normalizeWithStatic_equationForall₂ normalizeStatic laws
              elementCanonical elementObjects elementScope
            have assembled := elementsStep.assemble collectionType
            have leftEndpoint :
                (children.normalizedAvailable elementCanonical elementObjects
                  elementScope (normalizeStatic := normalizeStatic)).collection
                    collectionType =
                  (CostRegionTree.collection children).normalizedAvailable
                    canonical object scope
                      (normalizeStatic := normalizeStatic) := by
              apply WellSorted.AvailableOpenPattern.ext
              simp [WellSorted.AvailableOpenElements.collection_pattern,
                CostRegionElementTrees.normalizedAvailable_patterns,
                CostRegionTree.normalizedAvailable_pattern,
                CostRegionTree.normalize]
            have rightEndpoint :
                (children.originalAvailable elementCanonical elementObjects
                  elementScope).collection collectionType =
                  (CostRegionTree.collection children
                    ).originalAvailableOpenPattern canonical object scope := by
              apply WellSorted.AvailableOpenPattern.ext
              rfl
            rw [leftEndpoint, rightEndpoint] at assembled
            exact assembled
  termination_by 8 * tree.weight + 4
  decreasing_by
    all_goals simp [CostRegionTree.weight]
    all_goals omega

  /-- Normalization of one constructor argument retains the authored
  parameter representation at every intermediate equation vertex. -/
  theorem CostRegionTree.normalizeArgumentWithStatic_equationSetoid
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      ∀
      (parameter : TermParam)
      (representation :
        WellSorted.MatchesParameterRepresentation parameter pattern)
      (parameterType : WellSorted.parameterType? parameter = some type)
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile available.length pattern),
      (WellSorted.AvailableOpenArgument.equationSetoid
        source.costWholeLanguage targetFree available outer parameter type).r
        (tree.normalizedArgument parameter representation parameterType
          canonical object scope (normalizeStatic := normalizeStatic))
        (tree.originalArgument parameter representation parameterType
          canonical object scope) :=
    match tree with
    | @CostRegionTree.bvar source targetFree available outer index type lookup =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.bvar lookup).simpleArgument_equationSetoid
              name declared parameterType canonical object scope
                (normalizeStatic := normalizeStatic)
                ((CostRegionTree.bvar lookup).normalizeWithStatic_equationSetoid normalizeStatic laws
                  canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
    | @CostRegionTree.fvar source targetFree available outer name type lookup =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple parameterName declared =>
            exact (CostRegionTree.fvar lookup).simpleArgument_equationSetoid
              parameterName declared parameterType canonical object scope
                (normalizeStatic := normalizeStatic)
                ((CostRegionTree.fvar lookup).normalizeWithStatic_equationSetoid normalizeStatic laws
                  canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
    | @CostRegionTree.static source targetFree color outer node children =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.static node children
              ).simpleArgument_equationSetoid name declared parameterType
                canonical object scope (normalizeStatic := normalizeStatic)
                  ((CostRegionTree.static node children
                    ).normalizeWithStatic_equationSetoid normalizeStatic laws
                      canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            cases declared <;>
              simp [WellSorted.parameterType?] at parameterType
        | multiAbstractionNamed binderNames bodyName declared =>
            cases declared with
            | base sort =>
                simp [WellSorted.parameterType?] at parameterType
            | arrow domain codomain =>
                cases domain <;>
                  simp [WellSorted.parameterType?] at parameterType
            | multiBinder domain =>
                simp [WellSorted.parameterType?] at parameterType
            | collection collectionType elementType =>
                simp [WellSorted.parameterType?] at parameterType
    | @CostRegionTree.neutralApplicationOrdinary source targetFree available
        outer rule arguments membership notBareCollection constructor
        materializes neutral ordinary children =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.neutralApplicationOrdinary membership
              notBareCollection constructor materializes neutral ordinary
                children).simpleArgument_equationSetoid name declared
                  parameterType canonical object scope
                    (normalizeStatic := normalizeStatic)
                    ((CostRegionTree.neutralApplicationOrdinary membership
                      notBareCollection constructor materializes neutral
                        ordinary children).normalizeWithStatic_equationSetoid normalizeStatic laws
                          canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
    | @CostRegionTree.neutralApplicationQuote source targetFree available outer
        rule arguments membership notBareCollection constructor materializes
        neutral quoted children =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.neutralApplicationQuote membership
              notBareCollection constructor materializes neutral quoted
                children).simpleArgument_equationSetoid name declared
                  parameterType canonical object scope
                    (normalizeStatic := normalizeStatic)
                    ((CostRegionTree.neutralApplicationQuote membership
                      notBareCollection constructor materializes neutral quoted
                        children).normalizeWithStatic_equationSetoid
                          normalizeStatic laws canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
    | @CostRegionTree.lambda source targetFree available outer binder body
        domain codomain bodyTree =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.lambda bodyTree
              ).simpleArgument_equationSetoid name declared parameterType
                canonical object scope (normalizeStatic := normalizeStatic)
                  ((CostRegionTree.lambda bodyTree
                    ).normalizeWithStatic_equationSetoid normalizeStatic laws
                      canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            cases binder with
            | some display =>
                simp [WellSorted.MatchesParameterRepresentation] at representation
            | none =>
                have bodyCanonical :
                    body.hasCanonicalBinderMetadata = true := by
                  simpa [Pattern.hasCanonicalBinderMetadata] using canonical
                have bodyObject : WellSorted.isObjectPattern body = true := by
                  simpa [WellSorted.isObjectPattern] using object
                have bodyScope :
                    ReflectiveWellSorted.ReflectiveScopeSafeAt
                      source.costWholeReflectionProfile
                        (domain :: available).length body := by
                  intro presentation presentationMembership
                  simpa [binderSafeAt, List.length_cons] using
                    scope presentation presentationMembership
                have bodyStep := bodyTree.normalizeWithStatic_equationSetoid normalizeStatic laws
                  bodyCanonical bodyObject bodyScope
                let pack := fun
                    (term : WellSorted.AvailableOpenPattern
                      source.costWholeReflectionProfile
                        source.costWholeLanguage targetFree
                          (domain :: available) outer codomain) =>
                  ({ term := term.lambda none rfl
                     representation := True.intro
                     parameterType := parameterType } :
                    WellSorted.AvailableOpenArgument
                      source.costWholeReflectionProfile
                        source.costWholeLanguage targetFree available outer
                        (.abstractionNamed binderName bodyName declared)
                          (.arrow domain codomain))
                have packed :=
                  WellSorted.AvailableOpenArgument.equationSetoid_of_term_map
                    pack
                    (by
                      intro left right generator
                      exact EquationSemantics.reflectiveEquationContextStep_fill
                        (.lambda none .hole) generator)
                    bodyStep
                have leftEndpoint :
                    pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                      bodyScope (normalizeStatic := normalizeStatic)) =
                      (CostRegionTree.lambda bodyTree).normalizedArgument
                        (.abstractionNamed binderName bodyName declared)
                          representation parameterType canonical object
                            scope (normalizeStatic := normalizeStatic) := by
                  apply WellSorted.AvailableOpenArgument.ext
                  simp [pack, CostRegionTree.normalizedArgument_pattern,
                    CostRegionTree.normalize]
                have rightEndpoint :
                    pack (bodyTree.originalAvailableOpenPattern bodyCanonical
                      bodyObject bodyScope) =
                      (CostRegionTree.lambda bodyTree).originalArgument
                        (.abstractionNamed binderName bodyName declared)
                          representation parameterType canonical object
                            scope := by
                  apply WellSorted.AvailableOpenArgument.ext
                  rfl
                rw [leftEndpoint, rightEndpoint] at packed
                exact packed
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
    | @CostRegionTree.multiLambda source targetFree available outer arity
        binders body domain codomain bodyTree =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.multiLambda bodyTree
              ).simpleArgument_equationSetoid name declared parameterType
                canonical object scope (normalizeStatic := normalizeStatic)
                  ((CostRegionTree.multiLambda bodyTree
                    ).normalizeWithStatic_equationSetoid normalizeStatic laws
                      canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            cases binders with
            | cons display displays =>
                simp [WellSorted.MatchesParameterRepresentation] at representation
            | nil =>
                have bodyCanonical :
                    body.hasCanonicalBinderMetadata = true := by
                  simpa [Pattern.hasCanonicalBinderMetadata] using canonical
                have bodyObject : WellSorted.isObjectPattern body = true := by
                  simpa [WellSorted.isObjectPattern] using object
                have bodyScope :
                    ReflectiveWellSorted.ReflectiveScopeSafeAt
                      source.costWholeReflectionProfile
                        (List.replicate arity domain ++ available).length
                          body := by
                  intro presentation presentationMembership
                  simpa [binderSafeAt, List.length_append,
                    List.length_replicate, Nat.add_comm] using
                      scope presentation presentationMembership
                have bodyStep := bodyTree.normalizeWithStatic_equationSetoid normalizeStatic laws
                  bodyCanonical bodyObject bodyScope
                let pack := fun
                    (term : WellSorted.AvailableOpenPattern
                      source.costWholeReflectionProfile
                        source.costWholeLanguage targetFree
                          (List.replicate arity domain ++ available) outer
                            codomain) =>
                  ({ term := term.multiLambda arity [] rfl
                     representation := True.intro
                     parameterType := parameterType } :
                    WellSorted.AvailableOpenArgument
                      source.costWholeReflectionProfile
                        source.costWholeLanguage targetFree available outer
                        (.multiAbstractionNamed binderNames bodyName declared)
                          (.arrow (.multiBinder domain) codomain))
                have packed :=
                  WellSorted.AvailableOpenArgument.equationSetoid_of_term_map
                    pack
                    (by
                      intro left right generator
                      exact EquationSemantics.reflectiveEquationContextStep_fill
                        (.multiLambda arity [] .hole) generator)
                    bodyStep
                have leftEndpoint :
                    pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                      bodyScope (normalizeStatic := normalizeStatic)) =
                      (CostRegionTree.multiLambda bodyTree).normalizedArgument
                        (.multiAbstractionNamed binderNames bodyName declared)
                          representation parameterType canonical object
                            scope (normalizeStatic := normalizeStatic) := by
                  apply WellSorted.AvailableOpenArgument.ext
                  simp [pack, CostRegionTree.normalizedArgument_pattern,
                    CostRegionTree.normalize]
                have rightEndpoint :
                    pack (bodyTree.originalAvailableOpenPattern bodyCanonical
                      bodyObject bodyScope) =
                      (CostRegionTree.multiLambda bodyTree).originalArgument
                        (.multiAbstractionNamed binderNames bodyName declared)
                          representation parameterType canonical object
                            scope := by
                  apply WellSorted.AvailableOpenArgument.ext
                  rfl
                rw [leftEndpoint, rightEndpoint] at packed
                exact packed
    | @CostRegionTree.subst source targetFree available outer body replacement
        domain codomain bodyTree replacementTree =>
      fun parameter representation parameterType canonical object scope => by
        simp [WellSorted.isObjectPattern] at object
    | @CostRegionTree.collection source targetFree available outer
        collectionType elements rest elementType children =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.collection children
              ).simpleArgument_equationSetoid name declared parameterType
                canonical object scope (normalizeStatic := normalizeStatic)
                  ((CostRegionTree.collection children
                    ).normalizeWithStatic_equationSetoid normalizeStatic laws
                      canonical object scope)
        | abstractionNamed binderName bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | multiAbstractionNamed binderNames bodyName declared =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
  termination_by 8 * tree.weight + 5
  decreasing_by
    all_goals simp [CostRegionTree.weight]
    all_goals omega

  /-- Constructor argument spines normalize pointwise in their exact authored
  parameter carriers. -/
  theorem CostRegionArgumentTrees.normalizeWithStatic_equationForall₂
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      ∀
      (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
      (objects : WellSorted.isObjectPatternList arguments = true)
      (scope : ∀ presentation ∈
          source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          arguments = true),
      WellSorted.AvailableOpenArguments.EquationForall₂
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
          available outer
        (trees.normalizedAvailable canonical objects scope
          (normalizeStatic := normalizeStatic))
        (trees.originalAvailable canonical objects scope) :=
    match trees with
    | @CostRegionArgumentTrees.nil source targetFree available outer =>
      fun canonical objects scope => by
        let empty :=
          WellSorted.AvailableOpenArguments.nil
            (profile := source.costWholeReflectionProfile)
              source.costWholeLanguage targetFree available outer
        have leftEndpoint :
            (CostRegionArgumentTrees.nil (source := source)
              (targetFree := targetFree)).normalizedAvailable canonical objects
                scope (normalizeStatic := normalizeStatic) = empty := by
          apply WellSorted.AvailableOpenArguments.ext
          simp [empty, CostRegionArgumentTrees.normalizedAvailable_patterns,
            CostRegionArgumentTrees.normalize]
        have rightEndpoint :
            (CostRegionArgumentTrees.nil (source := source)
              (targetFree := targetFree)).originalAvailable canonical objects
                scope = empty := by
          apply WellSorted.AvailableOpenArguments.ext
          rfl
        rw [leftEndpoint, rightEndpoint]
        exact WellSorted.AvailableOpenArguments.EquationForall₂.nil
    | @CostRegionArgumentTrees.cons source targetFree available outer argument arguments
        parameter parameters expected representation parameterType head tail =>
      fun canonical objects scope => by
        have canonicalParts :
            argument.hasCanonicalBinderMetadata = true ∧
              Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
        have objectParts :
            WellSorted.isObjectPattern argument = true ∧
              WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPatternList] using objects
        have headScope :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              source.costWholeReflectionProfile available.length argument := by
          intro presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    argument = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length arguments = true := by
            simpa [binderSafeListAt] using
              scope presentation presentationMembership
          exact parts.1
        have tailScope : ∀ presentation ∈
            source.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor available.length
              arguments = true := by
          intro presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    argument = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length arguments = true := by
            simpa [binderSafeListAt] using
              scope presentation presentationMembership
          exact parts.2
        have headStep := head.normalizeArgumentWithStatic_equationSetoid normalizeStatic laws parameter
          representation parameterType canonicalParts.1 objectParts.1
            headScope
        have tailStep := tail.normalizeWithStatic_equationForall₂ normalizeStatic laws canonicalParts.2
          objectParts.2 tailScope
        have combined :=
          WellSorted.AvailableOpenArguments.EquationForall₂.cons
            headStep tailStep
        have leftEndpoint :
            WellSorted.AvailableOpenArguments.cons
                (head.normalizedArgument parameter representation parameterType
                  canonicalParts.1 objectParts.1 headScope
                    (normalizeStatic := normalizeStatic))
                (tail.normalizedAvailable canonicalParts.2 objectParts.2
                  tailScope (normalizeStatic := normalizeStatic)) =
              (CostRegionArgumentTrees.cons representation parameterType head
                tail).normalizedAvailable canonical objects scope
                  (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenArguments.ext
          simp [CostRegionArgumentTrees.normalizedAvailable_patterns,
            CostRegionArgumentTrees.normalize]
        have rightEndpoint :
            WellSorted.AvailableOpenArguments.cons
                (head.originalArgument parameter representation parameterType
                  canonicalParts.1 objectParts.1 headScope)
                (tail.originalAvailable canonicalParts.2 objectParts.2
                  tailScope) =
              (CostRegionArgumentTrees.cons representation parameterType head
                tail).originalAvailable canonical objects scope := by
          apply WellSorted.AvailableOpenArguments.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at combined
        exact combined
  termination_by 8 * trees.weight + 3
  decreasing_by
    all_goals simp [CostRegionArgumentTrees.weight]
    all_goals omega

  /-- Homogeneous collection spines normalize pointwise in their exact
  element fiber. -/
  theorem CostRegionElementTrees.normalizeWithStatic_equationForall₂
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer elements
        elementType) :
      ∀
      (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
      (objects : WellSorted.isObjectPatternList elements = true)
      (scope : ∀ presentation ∈
          source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          elements = true),
      WellSorted.AvailableOpenElements.EquationForall₂
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
          available outer elementType
        (trees.normalizedAvailable canonical objects scope
          (normalizeStatic := normalizeStatic))
        (trees.originalAvailable canonical objects scope) :=
    match trees with
    | @CostRegionElementTrees.nil source targetFree available outer elementType =>
      fun canonical objects scope => by
        let empty :=
          WellSorted.AvailableOpenElements.nil
            (profile := source.costWholeReflectionProfile)
              source.costWholeLanguage targetFree available outer elementType
        have leftEndpoint :
            (CostRegionElementTrees.nil (source := source)
              (targetFree := targetFree) available outer elementType
              ).normalizedAvailable canonical objects scope
                (normalizeStatic := normalizeStatic) = empty := by
          apply WellSorted.AvailableOpenElements.ext
          simp [empty, CostRegionElementTrees.normalizedAvailable_patterns,
            CostRegionElementTrees.normalize]
        have rightEndpoint :
            (CostRegionElementTrees.nil (source := source)
              (targetFree := targetFree) available outer elementType
              ).originalAvailable canonical objects scope = empty := by
          apply WellSorted.AvailableOpenElements.ext
          rfl
        rw [leftEndpoint, rightEndpoint]
        exact WellSorted.AvailableOpenElements.EquationForall₂.nil
    | @CostRegionElementTrees.cons source targetFree available outer element elements
        elementType head tail => fun canonical objects scope => by
        have canonicalParts :
            element.hasCanonicalBinderMetadata = true ∧
              Pattern.hasCanonicalBinderMetadataList elements = true := by
          simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
        have objectParts :
            WellSorted.isObjectPattern element = true ∧
              WellSorted.isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPatternList] using objects
        have headScope :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              source.costWholeReflectionProfile available.length element := by
          intro presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    element = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length elements = true := by
            simpa [binderSafeListAt] using
              scope presentation presentationMembership
          exact parts.1
        have tailScope : ∀ presentation ∈
            source.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor available.length
              elements = true := by
          intro presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    element = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length elements = true := by
            simpa [binderSafeListAt] using
              scope presentation presentationMembership
          exact parts.2
        have headStep := head.normalizeWithStatic_equationSetoid normalizeStatic laws canonicalParts.1
          objectParts.1 headScope
        have tailStep := tail.normalizeWithStatic_equationForall₂ normalizeStatic laws canonicalParts.2
          objectParts.2 tailScope
        have combined :=
          WellSorted.AvailableOpenElements.EquationForall₂.cons
            headStep tailStep
        have leftEndpoint :
            WellSorted.AvailableOpenElements.cons
                (head.normalizedAvailable canonicalParts.1 objectParts.1
                  headScope (normalizeStatic := normalizeStatic))
                (tail.normalizedAvailable canonicalParts.2 objectParts.2
                  tailScope (normalizeStatic := normalizeStatic)) =
              (CostRegionElementTrees.cons head tail).normalizedAvailable
                canonical objects scope
                  (normalizeStatic := normalizeStatic) := by
          apply WellSorted.AvailableOpenElements.ext
          simp [CostRegionElementTrees.normalizedAvailable_patterns,
            CostRegionElementTrees.normalize]
        have rightEndpoint :
            WellSorted.AvailableOpenElements.cons
                (head.originalAvailableOpenPattern canonicalParts.1
                  objectParts.1 headScope)
                (tail.originalAvailable canonicalParts.2 objectParts.2
                  tailScope) =
              (CostRegionElementTrees.cons head tail).originalAvailable
                canonical objects scope := by
          apply WellSorted.AvailableOpenElements.ext
          rfl
        rw [leftEndpoint, rightEndpoint] at combined
        exact combined
  termination_by 8 * trees.weight + 2
  decreasing_by
    all_goals simp [CostRegionElementTrees.weight]
    all_goals omega

  /-- Normalized finite boundary values are fiberwise equivalent to their
  exact source occurrences under every later binder weakening. -/
  theorem CostRegionBoundaryTrees.normalizeValuesWithStatic_fiberEquivalent
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      ((trees.normalizeValues (normalizeStatic := normalizeStatic)
        ).supportedOpenAssignment table).FiberEquivalent
        ((TypedCostRegionBoundaryTable.Values.original table
          ).supportedOpenAssignment table) :=
    match trees with
    | @CostRegionBoundaryTrees.nil source targetFree color => by
        intro lookup inner
        simp only [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.original]
        exact Relation.EqvGen.refl _
    | @CostRegionBoundaryTrees.cons source targetFree color occurrence occurrences boundary
        content tail head children => by
        let normalizedHead := head.normalize (normalizeStatic := normalizeStatic)
        let value :
            ReflectiveWellSorted.OpenPattern
              source.costWholeReflectionProfile source.costWholeLanguage
                targetFree boundary.boundary.targetSupport
                  boundary.boundary.targetType :=
          ⟨normalizedHead.pattern,
            ⟨by simpa only [List.append_nil] using normalizedHead.typed,
              normalizedHead.canonicalBinderMetadata
                boundary.contentCanonicalBinderMetadata,
              normalizedHead.objectPattern boundary.contentObjectPattern,
              by
                change normalizedHead.pattern.isWellScopedAt
                  boundary.boundary.targetSupport.length = true
                simpa only [List.append_nil] using
                  normalizedHead.typed.isWellScopedAt⟩,
            by
              intro presentation membership
              exact normalizedHead.reflectiveScope presentation membership
                (Nat.le_refl boundary.boundary.targetSupport.length)
                (boundary.contentReflectiveScopeSafe presentation membership)⟩
        have headSplitStep := head.normalizeWithStatic_equationSetoid normalizeStatic laws
          boundary.contentCanonicalBinderMetadata
            boundary.contentObjectPattern
              boundary.contentReflectiveScopeSafe
        have headOpenRaw :=
          WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
            headSplitStep
        have headOpenTransported :=
          ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
            (List.append_nil boundary.boundary.targetSupport) headOpenRaw
        have headOpen :
            (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
              source.costWholeReflectionProfile defaultBasePremises
                source.costWholeLanguage targetFree
                  boundary.boundary.targetSupport
                    boundary.boundary.targetType).r value
              (TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                boundary) := by
          have leftEndpoint :
              ((head.normalizedAvailable
                boundary.contentCanonicalBinderMetadata
                  boundary.contentObjectPattern
                    boundary.contentReflectiveScopeSafe
                      (normalizeStatic := normalizeStatic)
                  ).toReflectiveOpenPattern
                ).reindexBound
                  (List.append_nil boundary.boundary.targetSupport) =
                value := by
            apply Subtype.ext
            simp [value, normalizedHead,
              ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
              WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
              CostRegionTree.normalizedAvailable_pattern]
          have rightEndpoint :
              ((head.originalAvailableOpenPattern
                boundary.contentCanonicalBinderMetadata
                  boundary.contentObjectPattern
                    boundary.contentReflectiveScopeSafe).toReflectiveOpenPattern
                ).reindexBound
                  (List.append_nil boundary.boundary.targetSupport) =
                TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                  boundary := by
            apply Subtype.ext
            simp [ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
              WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
              CostRegionTree.originalAvailableOpenPattern,
              TypedCostRegionBoundaryTable.Values.boundaryOriginalValue]
          rw [leftEndpoint, rightEndpoint] at headOpenTransported
          exact headOpenTransported
        have headEquivalent : ∀ inner : List TypeExpr,
            (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
              source.costWholeReflectionProfile defaultBasePremises
                source.costWholeLanguage targetFree
                  (inner ++ boundary.boundary.targetSupport)
                    boundary.boundary.targetType).r
              (value.weakenRoot inner)
              ((TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                boundary).weakenRoot inner) := by
          intro inner
          exact laws.weakeningStable headOpen inner
        have tailEquivalent :
            ((children.normalizeValues (normalizeStatic := normalizeStatic)
              ).supportedOpenAssignment
              tail).FiberEquivalent
              ((TypedCostRegionBoundaryTable.Values.original tail
                ).supportedOpenAssignment tail) := by
          intro name type lookup inner
          exact children.normalizeValuesWithStatic_fiberEquivalent
            normalizeStatic laws lookup inner
        simpa only [CostRegionBoundaryTrees.normalizeValues, value,
          normalizedHead] using
          (TypedCostRegionBoundaryTable.Values.supportedOpenAssignment_cons_fiberEquivalent
            value (children.normalizeValues (normalizeStatic := normalizeStatic))
              headEquivalent tailEquivalent)
  termination_by 8 * trees.weight + 1
  decreasing_by
    all_goals simp [CostRegionBoundaryTrees.weight]
    all_goals omega
end

/-- Compatibility specialization of typed tree normalization to the
established mapped-action static normalizer. -/
theorem CostRegionTree.normalize_equationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile available.length pattern) :
    (WellSorted.AvailableOpenPattern.equationSetoid
      source.costWholeLanguage targetFree available outer type).r
      (tree.normalizedAvailable canonical object scope)
      (tree.originalAvailableOpenPattern canonical object scope) :=
  tree.normalizeWithStatic_equationSetoid
    (fun node values => node.normalizeWithReflective values)
    laws.toStaticRegionNormalizerLaws canonical object scope

/-- Compatibility specialization for one authored constructor argument. -/
theorem CostRegionTree.normalize_argument_equationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation :
      WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile available.length pattern) :
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree available outer parameter type).r
      (tree.normalizedArgument parameter representation parameterType
        canonical object scope)
      (tree.originalArgument parameter representation parameterType
        canonical object scope) :=
  tree.normalizeArgumentWithStatic_equationSetoid
    (fun node values => node.normalizeWithReflective values)
    laws.toStaticRegionNormalizerLaws parameter representation parameterType
      canonical object scope

/-- Compatibility specialization for constructor argument spines. -/
theorem CostRegionArgumentTrees.normalize_equationForall₂
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostRegionArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments.EquationForall₂
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available outer
      (trees.normalizedAvailable canonical objects scope)
      (trees.originalAvailable canonical objects scope) :=
  trees.normalizeWithStatic_equationForall₂
    (fun node values => node.normalizeWithReflective values)
    laws.toStaticRegionNormalizerLaws canonical objects scope

/-- Compatibility specialization for homogeneous element spines. -/
theorem CostRegionElementTrees.normalize_equationForall₂
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostRegionElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements.EquationForall₂
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available outer elementType
      (trees.normalizedAvailable canonical objects scope)
      (trees.originalAvailable canonical objects scope) :=
  trees.normalizeWithStatic_equationForall₂
    (fun node values => node.normalizeWithReflective values)
    laws.toStaticRegionNormalizerLaws canonical objects scope

/-- Compatibility specialization for finite boundary vectors. -/
theorem CostRegionBoundaryTrees.normalizeValues_fiberEquivalent
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    (trees.normalizeValues.supportedOpenAssignment table).FiberEquivalent
      ((TypedCostRegionBoundaryTable.Values.original table
        ).supportedOpenAssignment table) :=
  trees.normalizeValuesWithStatic_fiberEquivalent
    (fun node values => node.normalizeWithReflective values)
    laws.toStaticRegionNormalizerLaws

/-- Forget the quote-visible binder split while retaining every typed
intermediate vertex of the child-first normalization path. -/
theorem CostRegionTree.normalize_openPatternEquationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile available.length pattern) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree (available ++ outer) type).r
      (tree.normalizedAvailable canonical object scope).toReflectiveOpenPattern
      (tree.originalAvailableOpenPattern canonical object
        scope).toReflectiveOpenPattern :=
  WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
    (tree.normalize_equationSetoid laws canonical object scope)

/-- Erasing the typed normalization path gives the unary authored contextual
equivalence theorem.  No global raw fiber-stability hypothesis is used. -/
theorem CostRegionTree.normalize_typed_equationEquiv
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile available.length pattern) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage tree.normalize.pattern pattern := by
  have typed := tree.normalize_openPatternEquationSetoid laws canonical object
    scope
  have erased :=
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid_to_equiv
      typed
  simpa only [WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
    CostRegionTree.normalizedAvailable_pattern,
    CostRegionTree.originalAvailableOpenPattern_pattern] using erased

/-- Unary typed soundness makes every proof-relevant decomposition and every
executable chooser semantically irrelevant.  This quantifies over arbitrary
trees for one exact compact term, rather than over a particular enumeration
order. -/
theorem CostRegionTree.normalize_typed_overlap_equivalent
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (first second :
      CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile available.length pattern) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage first.normalize.pattern
        second.normalize.pattern := by
  have firstToInput :=
    first.normalize_typed_equationEquiv laws canonical object scope
  have secondToInput :=
    second.normalize_typed_equationEquiv laws canonical object scope
  exact Relation.EqvGen.trans _ _ _ firstToInput
    (Relation.EqvGen.symm _ _ secondToInput)

/-- Typed soundness holds for every proof-relevant Cost elaboration, not only
for the deterministic tree selected by compact execution. -/
theorem CostOpenElaboration.normalizeErasure_typed_openEquationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r elaboration.normalizeErasure term := by
  have split := elaboration.tree.normalize_openPatternEquationSetoid laws
    term.2.1.2.1 term.2.1.2.2.1 term.2.2
  have transported :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
    (List.append_nil targetBound) split
  have leftEndpoint :
      ((elaboration.tree.normalizedAvailable term.2.1.2.1 term.2.1.2.2.1
        term.2.2).toReflectiveOpenPattern.reindexBound
          (List.append_nil targetBound)) =
        elaboration.normalizeErasure := by
    apply Subtype.ext
    simp [CostOpenElaboration.normalizeErasure,
      CostRegionTree.normalizeOpen_pattern,
      CostRegionTree.normalizedAvailable_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  have rightEndpoint :
      ((elaboration.tree.originalAvailableOpenPattern term.2.1.2.1
        term.2.1.2.2.1 term.2.2).toReflectiveOpenPattern.reindexBound
          (List.append_nil targetBound)) =
        term := by
    apply Subtype.ext
    simp [CostRegionTree.originalAvailableOpenPattern_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  rw [leftEndpoint, rightEndpoint] at transported
  exact transported

/-- The executable compact Cost normalizer inherits typed soundness from its
proof-relevant elaboration; compilation chooses a tree but contributes no
semantic equation authority. -/
theorem CIGSLT.costNormalizeOpen_typed_openEquationSetoid
    (source : CIGSLT) (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r (source.costNormalizeOpen term) term :=
  (CostOpenElaboration.compile source term
    ).normalizeErasure_typed_openEquationSetoid laws

/-! ## Exact contextual typed canonical sections -/

/-- A Cost normalizer factors through the finite free-variable support of its
input when unused entries of the ambient free context cannot affect the raw
normal form.  The restriction retains the exact lookup of every occurring
free name, so this property is weaker than independence from used typing
information and stronger than mere preservation of output free names. -/
def CostOpenNormalizerFactorsThroughFreeSupport (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source) : Prop :=
  ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage free bound
        sort),
    (@normalizeOpen
      (free.restrictTo term.1.freeFvarNames) bound sort
      term.restrictFreeContext).1 =
      (@normalizeOpen free bound sort term).1

/-- Reindexing the free-context parameter of an open normalizer along an
equality changes no raw output.  This is dependent transport only; unlike
finite-support factorization below, it states no semantic naturality across
distinct contexts. -/
theorem CostOpenNormalizer.reindexFree_pattern
    {source : CIGSLT} (normalizeOpen : CostOpenNormalizer source)
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort source.costWholeLanguage}
    (freeEquality : sourceFree = targetFree)
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage sourceFree
        bound sort) :
    (@normalizeOpen targetFree bound sort
      (term.reindex freeEquality rfl rfl)).1 =
      (@normalizeOpen sourceFree bound sort term).1 := by
  cases freeEquality
  rfl

/-- Finite-support factorization supplies exact naturality under extension or
replacement of unused ambient free-context entries.  The proof compares both
executions in their common finite restriction; it never asks the two ambient
contexts themselves to be extensionally equal. -/
theorem CostOpenNormalizerFactorsThroughFreeSupport.normalizeRecontextualizeFree
    {source : CIGSLT} {normalizeOpen : CostOpenNormalizer source}
    (factors : CostOpenNormalizerFactorsThroughFreeSupport source
      normalizeOpen)
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage sourceFree
        bound sort)
    (preserves : ∀ {name freeType},
      name ∈ term.1.freeFvarNames →
      sourceFree name = some freeType →
        targetFree name = some freeType) :
    (@normalizeOpen targetFree bound sort
      (term.recontextualizeFree preserves)).1 =
      (@normalizeOpen sourceFree bound sort term).1 := by
  have restrictedContexts :
      sourceFree.restrictTo term.1.freeFvarNames =
        targetFree.restrictTo term.1.freeFvarNames :=
    term.toCore.restrictTo_freeFvarNames_eq_of_preserves preserves
  have targetFactor := factors (term.recontextualizeFree preserves)
  have sourceFactor := factors term
  let targetRestricted :=
    (term.recontextualizeFree preserves).restrictFreeContext
  let sourceRestricted := term.restrictFreeContext
  have restrictedTerms :
      targetRestricted.reindex restrictedContexts.symm rfl rfl =
        sourceRestricted := by
    apply Subtype.ext
    simp [targetRestricted, sourceRestricted]
  have restrictedOutputs :
      (@normalizeOpen
        (targetFree.restrictTo term.1.freeFvarNames) bound sort
        targetRestricted).1 =
      (@normalizeOpen
        (sourceFree.restrictTo term.1.freeFvarNames) bound sort
        sourceRestricted).1 := by
    calc
      (@normalizeOpen
          (targetFree.restrictTo term.1.freeFvarNames) bound sort
          targetRestricted).1 =
          (@normalizeOpen
            (sourceFree.restrictTo term.1.freeFvarNames) bound sort
            (targetRestricted.reindex restrictedContexts.symm rfl rfl)).1 :=
        (CostOpenNormalizer.reindexFree_pattern normalizeOpen
          restrictedContexts.symm targetRestricted).symm
      _ = (@normalizeOpen
            (sourceFree.restrictTo term.1.freeFvarNames) bound sort
            sourceRestricted).1 := by
        exact congrArg
          (fun restricted : ReflectiveWellSorted.OpenTerm
              source.costWholeReflectionProfile source.costWholeLanguage
              (sourceFree.restrictTo term.1.freeFvarNames) bound sort =>
            (@normalizeOpen
              (sourceFree.restrictTo term.1.freeFvarNames) bound sort
              restricted).1)
          restrictedTerms
  calc
    (@normalizeOpen targetFree bound sort
        (term.recontextualizeFree preserves)).1 =
        (@normalizeOpen
          (targetFree.restrictTo term.1.freeFvarNames) bound sort
          (term.recontextualizeFree preserves).restrictFreeContext).1 := by
      exact targetFactor.symm
    _ = (@normalizeOpen
          (sourceFree.restrictTo term.1.freeFvarNames) bound sort
          term.restrictFreeContext).1 := by
      exact restrictedOutputs
    _ = (@normalizeOpen sourceFree bound sort term).1 := sourceFactor

/-- Positive control: the identity open normalizer factors through finite
free support.  This witnesses that the factorization interface itself adds
no hidden inhabitance or global-context premise. -/
theorem costIdentityOpenNormalizer_factorsThroughFreeSupport
    (source : CIGSLT) :
    CostOpenNormalizerFactorsThroughFreeSupport source (fun term => term) := by
  intro free bound sort term
  rfl

/-- Contextual laws for an explicitly selected Cost normalizer.  They are
independent of unary equation soundness and of the algorithm used to obtain
the representative. -/
structure CostContextualOpenLawsFor (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source) : Prop where
  preservesFreeVariableSupport : ∀
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort)
      {name : String},
    name ∈ (@normalizeOpen free bound sort term).1.freeFvarNames →
      name ∈ term.1.freeFvarNames
  normalizeRecontextualizeFree :
    ∀ {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage sourceFree
          bound sort)
      (preserves : ∀ {name freeType},
        name ∈ term.1.freeFvarNames →
        sourceFree name = some freeType →
          targetFree name = some freeType),
    (@normalizeOpen targetFree bound sort
      (term.recontextualizeFree preserves)).1 =
      (@normalizeOpen sourceFree bound sort term).1
  preservesReflectiveSupport :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort)
      (support : ContextSupport.Support) (available : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr),
    term.2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage →
      (@normalizeOpen free bound sort term).2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage

/-- Complete semantic laws needed for an explicitly selected normalizer to
supply the Cost open section.  `equivalent` rules out vacuous completeness;
`generatorInvariant` then extends to every finite equation path. -/
structure CostOpenSectionLawsFor (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source) : Prop
    extends CostContextualOpenLawsFor source normalizeOpen where
  equivalent : ∀
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort),
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage free bound (.base sort.1)).r
      (@normalizeOpen free bound sort term) term
  generatorInvariant : CostOpenGeneratorInvariantFor source normalizeOpen

/-- Contextual laws needed for the generated Cost open section and its next
continued-interaction layer.

These laws are deliberately separate from unary equation soundness.  They
state that the chosen exact representative is natural in unused free-context
entries, introduces no new free names, preserves arbitrary reflective support,
and therefore supplies the contextual fields independently of equation
soundness.  Preservation of the *next* continuation fragment is defined later,
after that continuation plan itself exists. -/
structure CostReferenceContextualOpenLaws (source : CIGSLT) : Prop where
  preservesFreeVariableSupport : ∀
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort)
      {name : String},
    name ∈ (source.costNormalizeOpen term).1.freeFvarNames →
      name ∈ term.1.freeFvarNames
  normalizeRecontextualizeFree :
    ∀ {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage sourceFree
          bound sort)
      (preserves : ∀ {name freeType},
        name ∈ term.1.freeFvarNames →
        sourceFree name = some freeType →
          targetFree name = some freeType),
    (source.costNormalizeOpen (term.recontextualizeFree preserves)).1 =
      (source.costNormalizeOpen term).1
  preservesReflectiveSupport :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        source.costWholeReflectionProfile source.costWholeLanguage free bound
          sort)
      (support : ContextSupport.Support) (available : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr),
    term.2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage →
      (source.costNormalizeOpen term).2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage

/-- Exact laws needed for the chosen compact Cost executor to supply a
contextual sort-indexed open section.

Typed unary normalization supplies soundness inside the exact free, bound,
and sort fiber, while generator invariance collapses each authored equation
generator.  The contextual extension carries the independent support laws
required to inhabit `CIGSLT`.  No claim is made here that all proof-relevant
elaborations erase to the same normal form; that strictly stronger property
is separated below because it is not hereditary under Cost iteration. -/
structure CostReferenceOpenSectionLaws (source : CIGSLT) : Prop
    extends CostTypedUnaryNormalizationLaws source,
      CostReferenceContextualOpenLaws source where
  generatorInvariant : CostReferenceOpenGeneratorInvariant source

/-- The established compact-executor laws instantiate the generic
normalizer-parameterized section laws.  This is a compatibility theorem, not
a second semantic authority: both bundles name the same executor. -/
def CostReferenceOpenSectionLaws.toCostOpenSectionLawsFor
    {source : CIGSLT} (laws : CostReferenceOpenSectionLaws source) :
    CostOpenSectionLawsFor source source.costNormalizeOpen where
  equivalent := by
    intro free bound sort term
    exact source.costNormalizeOpen_typed_openEquationSetoid
      laws.toCostTypedUnaryNormalizationLaws term
  generatorInvariant := laws.generatorInvariant
  preservesFreeVariableSupport := by
    intro free bound sort term name membership
    exact laws.preservesFreeVariableSupport term membership
  normalizeRecontextualizeFree := by
    intro sourceFree targetFree bound sort term preserves
    exact laws.normalizeRecontextualizeFree term preserves
  preservesReflectiveSupport := by
    intro free bound sort term support available binderImage safe
    exact laws.preservesReflectiveSupport term support available binderImage
      safe

/-- Additional compact-factorization law.

This says every proof-relevant elaboration of one compact term erases to the
same exact representative.  It is useful when true, but it is intentionally
not required to construct the next continued Cost object: distinct semantic
fibres may share one compact observation at higher Cost layers. -/
structure CostReferenceOpenCanonicalLaws (source : CIGSLT) : Prop
    extends CostReferenceOpenSectionLaws source where
  compactCoherent : CompactCostNormalizationCoherent source

/-- Object property selecting the ciGSLTs on which the proof-relevant Cost
normalizer additionally factors through one exact compact representative. -/
def CostReferenceCanonicalObjectProperty :
    CategoryTheory.ObjectProperty CIGSLT :=
  CostReferenceOpenCanonicalLaws

/-- Full subcategory of ciGSLTs carrying the exact typed Cost laws.  The
eventual Cost₁ category further restricts morphisms to maps preserving the
generated structural data and canonical-key order. -/
abbrev CostReferenceCanonicalObjects :=
  CostReferenceCanonicalObjectProperty.FullSubcategory

/-- Forget exact Cost canonical laws while retaining the underlying ciGSLT. -/
def costReferenceCanonicalObjectsForget :
    CategoryTheory.Functor CostReferenceCanonicalObjects CIGSLT :=
  CostReferenceCanonicalObjectProperty.ι

/-- Exact computable section for an explicitly selected lawful Cost
normalizer.  The section is generic in the source ciGSLT and in the
normalization algorithm. -/
def CIGSLT.costOpenSectionWith (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source)
    (laws : CostOpenSectionLawsFor source normalizeOpen) :
    ComputableReflectiveFiberSection source.costIGSLT
      source.costWholeAdmittedReflection :=
  ComputableReflectiveFiberSection.ofGeneratorInvariant normalizeOpen
    (fun term => laws.equivalent term)
    (fun generator => laws.generatorInvariant generator)

/-- Contextual Cost section for an explicitly selected lawful normalizer. -/
def CIGSLT.costContextualOpenSectionWith (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source)
    (laws : CostOpenSectionLawsFor source normalizeOpen) :
    ComputableReflectiveFiberContextualSection source.costIGSLT
      source.costWholeAdmittedReflection where
  toComputableReflectiveFiberSection :=
    source.costOpenSectionWith normalizeOpen laws
  preservesFreeVariableSupport := by
    intro free bound sort term name membership
    exact laws.preservesFreeVariableSupport term membership
  normalizeRecontextualizeFree := by
    intro sourceFree targetFree bound sort term preserves
    exact laws.normalizeRecontextualizeFree term preserves
  preservesReflectiveSupport := by
    intro free bound sort term support available binderImage safe
    exact laws.preservesReflectiveSupport term support available binderImage
      safe

/-- Exact computable section of every typed open Cost fiber.  Soundness comes
from proof-relevant tree normalization; completeness is generated solely from
exact invariance under the authored open-equation generators. -/
def CIGSLT.costReferenceOpenSection (source : CIGSLT)
    (laws : CostReferenceOpenSectionLaws source) :
    ComputableReflectiveFiberSection source.costIGSLT
      source.costWholeAdmittedReflection :=
  source.costOpenSectionWith source.costNormalizeOpen
    laws.toCostOpenSectionLawsFor

/-- Exact contextual open section of the generated Cost presentation.
Every additional field is supplied by the Cost₁ object law rather than
inferred from equation equivalence. -/
def CIGSLT.costReferenceContextualOpenSection (source : CIGSLT)
    (laws : CostReferenceOpenSectionLaws source) :
    ComputableReflectiveFiberContextualSection source.costIGSLT
      source.costWholeAdmittedReflection :=
  source.costContextualOpenSectionWith source.costNormalizeOpen
    laws.toCostOpenSectionLawsFor

/-- Exact representative independence on every typed open Cost equation
path.  This theorem is downstream of the local generator law. -/
theorem CIGSLT.costReferenceNormalizeOpen_complete (source : CIGSLT)
    (laws : CostReferenceOpenSectionLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        targetBound targetSort}
    (equivalent :
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        source.costWholeReflectionProfile defaultBasePremises
          source.costWholeLanguage targetFree targetBound
            (.base targetSort.1)).r left right) :
    source.costNormalizeOpen left = source.costNormalizeOpen right :=
  (source.costReferenceOpenSection laws).complete equivalent

/-- Canonical section for compact observations of proof-relevant Cost
elaborations.  The observation relation deliberately forgets elaboration
identity; the elaborated semantic carrier itself retains it. -/
def CIGSLT.costReferenceCompactObservationSection (source : CIGSLT)
    (laws : CostReferenceOpenCanonicalLaws source)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    ComputableSetoidSection
      (CostElabTerm source targetFree targetBound targetSort)
      (CostOpenElaboration.costCompactObservationSetoid source targetFree
        targetBound targetSort) where
  normalize := CostOpenElaboration.normalizeTerm source
  equivalent := by
    intro term
    change (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r term.2.normalizeErasure term.1
    exact term.2.normalizeErasure_typed_openEquationSetoid
      laws.toCostReferenceOpenSectionLaws.toCostTypedUnaryNormalizationLaws
  complete := by
    intro left right equivalent
    change (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r left.1 right.1 at equivalent
    change CostOpenElaboration.compileTerm source
        left.2.normalizeErasure =
      CostOpenElaboration.compileTerm source right.2.normalizeErasure
    apply congrArg (CostOpenElaboration.compileTerm source)
    exact (left.2.normalizeErasure_eq_costNormalizeOpen laws.compactCoherent
      ).trans ((source.costReferenceNormalizeOpen_complete
        laws.toCostReferenceOpenSectionLaws
        equivalent).trans
        (right.2.normalizeErasure_eq_costNormalizeOpen
          laws.compactCoherent).symm)

/-- Erasing the semantic representative of any elaboration agrees exactly
with the executable compact normalizer. -/
theorem CIGSLT.costReferenceCompactObservationSection_normalize_erase
    (source : CIGSLT)
    (laws : CostReferenceOpenCanonicalLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    CostOpenElaboration.erase
        ((source.costReferenceCompactObservationSection laws targetFree
          targetBound
          targetSort).normalize term) =
      source.costNormalizeOpen term.1 := by
  change term.2.normalizeErasure = source.costNormalizeOpen term.1
  exact term.2.normalizeErasure_eq_costNormalizeOpen laws.compactCoherent

/-- Exact chooser independence for one admitted typed compact term, derived
only from the explicit compact-coherence law. -/
theorem CostRegionTree.normalize_overlap_exact
    {source : CIGSLT} (laws : CostReferenceOpenCanonicalLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (first second : CostRegionTree source targetFree targetBound [] term.1
      (.base targetSort.1)) :
    first.normalize.pattern = second.normalize.pattern := by
  have coherent := laws.compactCoherent term
    (⟨first⟩ : CostOpenElaboration source term)
    (⟨second⟩ : CostOpenElaboration source term)
  exact congrArg (fun normalized => normalized.1) coherent

/-- Every valid elaboration agrees semantically with deterministic compact
execution.  This theorem intentionally concludes authored equivalence rather
than exact syntax equality. -/
theorem CostRegionTree.normalize_equationEquiv_costNormalizeOpen
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (tree : CostRegionTree source targetFree targetBound [] term.1
      (.base targetSort.1)) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage tree.normalize.pattern
        (source.costNormalizeOpen term).1 := by
  simpa only [source.costNormalizeOpen_pattern] using
    tree.normalize_typed_overlap_equivalent laws
      (CostRegionTree.buildOpenTerm (source := source) term)
      term.2.1.2.1 term.2.1.2.2.1 term.2.2

end Mettapedia.GSLT.LanguageDef
