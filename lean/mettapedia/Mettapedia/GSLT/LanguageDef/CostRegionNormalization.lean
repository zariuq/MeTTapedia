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

/-- The exact laws consumed by typed unary normalization.

The same-colour action is local to one certified static region.  Weakening is
required only for already-typed child paths.  In particular, this interface
does not demand the false property that every mixed-colour raw equation path
remain in one arbitrary typing fibre. -/
structure CostTypedUnaryNormalizationLaws (source : CIGSLT) : Prop where
  mappedGeneratorFiberAction : CostStaticMappedGeneratorFiberAction source
  weakeningStable :
    WellSorted.OpenPatternEquationWeakeningStable source.costWholeLanguage
  canonicalPathSafe : CostStaticCanonicalPathSafe source

namespace CostRegionTree

/-- The proof-relevant tree index is the exact original compact pattern. -/
@[simp]
theorem originalAvailableOpenPattern_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    WellSorted.AvailableOpenPattern source.costWholeLanguage targetFree
      available outer type :=
  tree.normalize.toAvailableOpenPattern canonical object scope

@[simp]
theorem normalizedAvailable_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    (tree.normalizedAvailable canonical object scope).pattern =
      tree.normalize.pattern :=
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    WellSorted.AvailableOpenArgument source.costWholeLanguage targetFree
      available outer parameter type where
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    WellSorted.AvailableOpenArgument source.costWholeLanguage targetFree
      available outer parameter type where
  term := tree.normalizedAvailable canonical object scope
  representation :=
    tree.normalize.matchesParameterRepresentation parameter representation
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    (tree.normalizedArgument parameter representation parameterType canonical
      object scope).term.pattern = tree.normalize.pattern :=
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments source.costWholeLanguage targetFree
      available outer parameters :=
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments source.costWholeLanguage targetFree
      available outer parameters :=
  WellSorted.AvailableOpenArguments.ofCertificates trees.normalize.typed
    (trees.normalize.canonicalBinderMetadata canonical)
    (trees.normalize.objectPatterns objects)
    (fun presentation membership =>
      trees.normalize.reflectiveScope presentation membership
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
        source.costWholeLanguage.reflectivePresentations,
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    (trees.normalizedAvailable canonical objects scope).patterns =
      trees.normalize.patterns :=
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements source.costWholeLanguage targetFree
      available outer elementType :=
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements source.costWholeLanguage targetFree
      available outer elementType :=
  WellSorted.AvailableOpenElements.ofCertificates trees.normalize.typed
    (trees.normalize.canonicalBinderMetadata canonical)
    (trees.normalize.objectPatterns objects)
    (fun presentation membership =>
      trees.normalize.reflectiveScope presentation membership
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
        source.costWholeLanguage.reflectivePresentations,
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
        source.costWholeLanguage.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    (trees.normalizedAvailable canonical objects scope).patterns =
      trees.normalize.patterns :=
  rfl

end CostRegionElementTrees

namespace TypedCostRegionBoundaryTable.Values

/-- The exact original open value carried by one proof-relevant boundary. -/
private def boundaryOriginalValue
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundary source color targetFree) :
    WellSorted.OpenPattern source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType :=
  ⟨boundary.boundary.content, boundary.contentTyped,
    boundary.contentCanonicalBinderMetadata, boundary.contentObjectPattern,
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
    (value : WellSorted.OpenPattern source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType)
    (values : Values source color targetFree tail)
    (headEquivalent : ∀ inner : List TypeExpr,
      (openPatternEquationSetoid source.costWholeLanguage targetFree
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
        ((openPatternEquationSetoid source.costWholeLanguage targetFree
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
          WellSorted.openPatternEquationSetoid_reindexBound boundEquality
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
          WellSorted.openPatternEquationSetoid_reindexBound boundEquality
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern)
    (equivalent :
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope)
        (tree.originalAvailableOpenPattern canonical object scope)) :
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree available outer
        (.simple parameterName parameterTypeExpression) type).r
      (tree.normalizedArgument (.simple parameterName parameterTypeExpression)
        True.intro parameterType canonical object scope)
      (tree.originalArgument (.simple parameterName parameterTypeExpression)
        True.intro parameterType canonical object scope) := by
  let pack := fun
      (term : WellSorted.AvailableOpenPattern source.costWholeLanguage
        targetFree available outer type) =>
    ({ term := term
       representation := True.intro
       parameterType := parameterType } :
      WellSorted.AvailableOpenArgument source.costWholeLanguage targetFree
        available outer (.simple parameterName parameterTypeExpression) type)
  have packed :=
    WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
      (by
        intro left right generator
        exact generator)
      equivalent
  have leftEndpoint :
      pack (tree.normalizedAvailable canonical object scope) =
        tree.normalizedArgument (.simple parameterName parameterTypeExpression)
          True.intro parameterType canonical object scope := by
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
  theorem CostRegionTree.normalize_equationSetoid
      {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      ∀
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
        available.length pattern),
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope)
        (tree.originalAvailableOpenPattern canonical object scope) :=
    match tree with
    | @CostRegionTree.bvar source targetFree available outer index type lookup =>
      fun canonical object scope => by
        have endpoint :
            (CostRegionTree.bvar (source := source)
              (targetFree := targetFree) lookup).normalizedAvailable canonical
                object scope =
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
                  scope =
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
        have valuesEquivalent :
            (children.normalizeValues.supportedOpenAssignment
              node.finiteBoundaryTable).FiberEquivalent
              ((TypedCostRegionBoundaryTable.Values.original
                node.finiteBoundaryTable).supportedOpenAssignment
                  node.finiteBoundaryTable) := by
          intro name type lookup inner
          exact children.normalizeValues_fiberEquivalent laws lookup inner
        have localStep := node.normalizeWithAvailable_equationSetoid
          laws.mappedGeneratorFiberAction children.normalizeValues
            valuesEquivalent (laws.canonicalPathSafe node)
        have openStepRaw :=
          WellSorted.AvailableOpenPattern.equationSetoid_to_openPatternEquationSetoid
            localStep
        have openStep :=
          WellSorted.openPatternEquationSetoid_reindexBound
            (List.append_nil node.targetBound) openStepRaw
        have lifted :=
          WellSorted.AvailableOpenPattern.openPatternEquationSetoid_to_availableWithOuter
            outer openStep
        have leftEndpoint :
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
                ((node.normalizeWithAvailable
                  children.normalizeValues).toOpenPattern.reindexBound
                    (List.append_nil node.targetBound)) outer =
              (CostRegionTree.static node children).normalizedAvailable
                canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          simp only [
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            WellSorted.OpenPattern.reindexBound_pattern,
            WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
            CostRegionTree.normalizedAvailable_pattern]
          simp only [CostStaticRegionNode.normalizeWithAvailable,
            CostStaticRegionNode.normalizeWith,
            WellSorted.AvailableOpenPattern.ofOpenPattern_pattern,
            CostRegionTree.normalize]
        have rightEndpoint :
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
                (node.termAvailable.toOpenPattern.reindexBound
                  (List.append_nil node.targetBound)) outer =
              (CostRegionTree.static node children).originalAvailableOpenPattern
                canonical object scope := by
          apply WellSorted.AvailableOpenPattern.ext
          simp only [
            WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            WellSorted.OpenPattern.reindexBound_pattern,
            WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
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
            source.costWholeLanguage.reflectivePresentations,
            binderSafeListAt presentation.quoteConstructor available.length
              arguments = true := by
          intro presentation presentationMembership
          have notThisQuote :
              rule.label ≠ presentation.quoteConstructor := by
            intro labelEquality
            have detected : ReflectiveContextSupport.isQuoteConstructor
                source.costWholeLanguage rule.label = true := by
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
        have argumentsStep := children.normalize_equationForall₂ laws
          argumentCanonical argumentObjects argumentScope
        have assembled := argumentsStep.assembleOrdinary membership
          notBareCollection ordinary
        have leftEndpoint :
            (children.normalizedAvailable argumentCanonical argumentObjects
              argumentScope).applyOrdinary membership notBareCollection
                ordinary =
              (CostRegionTree.neutralApplicationOrdinary membership
                notBareCollection constructor materializes neutral ordinary
                  children).normalizedAvailable canonical object scope := by
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
            WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
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
            source.costWholeLanguage_validate membership argumentsTyped quoted
              parentScopeAtBound
        have argumentsStep := children.normalize_equationForall₂ laws
          argumentCanonical argumentObjects argumentScope
        have assembled := argumentsStep.assembleQuote membership
          notBareCollection quoted
        have leftEndpoint :
            (children.normalizedAvailable argumentCanonical argumentObjects
              argumentScope).applyQuote membership notBareCollection quoted =
              (CostRegionTree.neutralApplicationQuote membership
                notBareCollection constructor materializes neutral quoted
                  children).normalizedAvailable canonical object scope := by
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
            WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
              (domain :: available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_cons] using
            scope presentation presentationMembership
        have bodyStep := bodyTree.normalize_equationSetoid laws
          canonicalParts.2 bodyObject bodyScope
        have assembled :=
          WellSorted.AvailableOpenPattern.equationSetoid_lambda_congr binder
            canonicalParts.1 bodyStep
        have leftEndpoint :
            (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
              ).lambda binder canonicalParts.1 =
              (CostRegionTree.lambda bodyTree).normalizedAvailable canonical
                object scope := by
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
            WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
              (List.replicate arity domain ++ available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_append, List.length_replicate,
            Nat.add_comm] using scope presentation presentationMembership
        have bodyStep := bodyTree.normalize_equationSetoid laws
          canonicalParts.2 bodyObject bodyScope
        have assembled :=
          WellSorted.AvailableOpenPattern.equationSetoid_multiLambda_congr
            arity binders bindersCanonical bodyStep
        have leftEndpoint :
            (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
              ).multiLambda arity binders bindersCanonical =
              (CostRegionTree.multiLambda bodyTree).normalizedAvailable
                canonical object scope := by
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
                source.costWholeLanguage.reflectivePresentations,
                binderSafeListAt presentation.quoteConstructor available.length
                  elements = true := by
              intro presentation presentationMembership
              simpa [binderSafeAt] using
                scope presentation presentationMembership
            have elementsStep := children.normalize_equationForall₂ laws
              elementCanonical elementObjects elementScope
            have assembled := elementsStep.assemble collectionType
            have leftEndpoint :
                (children.normalizedAvailable elementCanonical elementObjects
                  elementScope).collection collectionType =
                  (CostRegionTree.collection children).normalizedAvailable
                    canonical object scope := by
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
  theorem CostRegionTree.normalize_argument_equationSetoid
      {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
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
      (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
        available.length pattern),
      (WellSorted.AvailableOpenArgument.equationSetoid
        source.costWholeLanguage targetFree available outer parameter type).r
        (tree.normalizedArgument parameter representation parameterType
          canonical object scope)
        (tree.originalArgument parameter representation parameterType
          canonical object scope) :=
    match tree with
    | @CostRegionTree.bvar source targetFree available outer index type lookup =>
      fun parameter representation parameterType canonical object scope => by
        cases parameter with
        | simple name declared =>
            exact (CostRegionTree.bvar lookup).simpleArgument_equationSetoid
              name declared parameterType canonical object scope
                ((CostRegionTree.bvar lookup).normalize_equationSetoid laws
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
                ((CostRegionTree.fvar lookup).normalize_equationSetoid laws
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
                canonical object scope
                  ((CostRegionTree.static node children).normalize_equationSetoid
                    laws canonical object scope)
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
                    ((CostRegionTree.neutralApplicationOrdinary membership
                      notBareCollection constructor materializes neutral
                        ordinary children).normalize_equationSetoid laws
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
                    ((CostRegionTree.neutralApplicationQuote membership
                      notBareCollection constructor materializes neutral quoted
                        children).normalize_equationSetoid laws canonical object
                          scope)
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
                canonical object scope
                  ((CostRegionTree.lambda bodyTree).normalize_equationSetoid
                    laws canonical object scope)
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
                    WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
                      (domain :: available).length body := by
                  intro presentation presentationMembership
                  simpa [binderSafeAt, List.length_cons] using
                    scope presentation presentationMembership
                have bodyStep := bodyTree.normalize_equationSetoid laws
                  bodyCanonical bodyObject bodyScope
                let pack := fun
                    (term : WellSorted.AvailableOpenPattern
                      source.costWholeLanguage targetFree
                        (domain :: available) outer codomain) =>
                  ({ term := term.lambda none rfl
                     representation := True.intro
                     parameterType := parameterType } :
                    WellSorted.AvailableOpenArgument source.costWholeLanguage
                      targetFree available outer
                        (.abstractionNamed binderName bodyName declared)
                          (.arrow domain codomain))
                have packed :=
                  WellSorted.AvailableOpenArgument.equationSetoid_of_term_map
                    pack
                    (by
                      intro left right generator
                      exact EquationSemantics.equationContextStep_fill
                        (.lambda none .hole) generator)
                    bodyStep
                have leftEndpoint :
                    pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                      bodyScope) =
                      (CostRegionTree.lambda bodyTree).normalizedArgument
                        (.abstractionNamed binderName bodyName declared)
                          representation parameterType canonical object
                            scope := by
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
                canonical object scope
                  ((CostRegionTree.multiLambda bodyTree
                    ).normalize_equationSetoid laws canonical object scope)
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
                    WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
                      (List.replicate arity domain ++ available).length
                        body := by
                  intro presentation presentationMembership
                  simpa [binderSafeAt, List.length_append,
                    List.length_replicate, Nat.add_comm] using
                      scope presentation presentationMembership
                have bodyStep := bodyTree.normalize_equationSetoid laws
                  bodyCanonical bodyObject bodyScope
                let pack := fun
                    (term : WellSorted.AvailableOpenPattern
                      source.costWholeLanguage targetFree
                        (List.replicate arity domain ++ available) outer
                          codomain) =>
                  ({ term := term.multiLambda arity [] rfl
                     representation := True.intro
                     parameterType := parameterType } :
                    WellSorted.AvailableOpenArgument source.costWholeLanguage
                      targetFree available outer
                        (.multiAbstractionNamed binderNames bodyName declared)
                          (.arrow (.multiBinder domain) codomain))
                have packed :=
                  WellSorted.AvailableOpenArgument.equationSetoid_of_term_map
                    pack
                    (by
                      intro left right generator
                      exact EquationSemantics.equationContextStep_fill
                        (.multiLambda arity [] .hole) generator)
                    bodyStep
                have leftEndpoint :
                    pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                      bodyScope) =
                      (CostRegionTree.multiLambda bodyTree).normalizedArgument
                        (.multiAbstractionNamed binderNames bodyName declared)
                          representation parameterType canonical object
                            scope := by
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
                canonical object scope
                  ((CostRegionTree.collection children
                    ).normalize_equationSetoid laws canonical object scope)
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
  theorem CostRegionArgumentTrees.normalize_equationForall₂
      {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      ∀
      (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
      (objects : WellSorted.isObjectPatternList arguments = true)
      (scope : ∀ presentation ∈
          source.costWholeLanguage.reflectivePresentations,
        binderSafeListAt presentation.quoteConstructor available.length
          arguments = true),
      WellSorted.AvailableOpenArguments.EquationForall₂
        source.costWholeLanguage targetFree available outer
        (trees.normalizedAvailable canonical objects scope)
        (trees.originalAvailable canonical objects scope) :=
    match trees with
    | @CostRegionArgumentTrees.nil source targetFree available outer =>
      fun canonical objects scope => by
        let empty :=
          WellSorted.AvailableOpenArguments.nil source.costWholeLanguage
            targetFree available outer
        have leftEndpoint :
            (CostRegionArgumentTrees.nil (source := source)
              (targetFree := targetFree)).normalizedAvailable canonical objects
                scope = empty := by
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
            WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
              available.length argument := by
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
            source.costWholeLanguage.reflectivePresentations,
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
        have headStep := head.normalize_argument_equationSetoid laws parameter
          representation parameterType canonicalParts.1 objectParts.1
            headScope
        have tailStep := tail.normalize_equationForall₂ laws canonicalParts.2
          objectParts.2 tailScope
        have combined :=
          WellSorted.AvailableOpenArguments.EquationForall₂.cons
            headStep tailStep
        have leftEndpoint :
            WellSorted.AvailableOpenArguments.cons
                (head.normalizedArgument parameter representation parameterType
                  canonicalParts.1 objectParts.1 headScope)
                (tail.normalizedAvailable canonicalParts.2 objectParts.2
                  tailScope) =
              (CostRegionArgumentTrees.cons representation parameterType head
                tail).normalizedAvailable canonical objects scope := by
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
  theorem CostRegionElementTrees.normalize_equationForall₂
      {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer elements
        elementType) :
      ∀
      (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
      (objects : WellSorted.isObjectPatternList elements = true)
      (scope : ∀ presentation ∈
          source.costWholeLanguage.reflectivePresentations,
        binderSafeListAt presentation.quoteConstructor available.length
          elements = true),
      WellSorted.AvailableOpenElements.EquationForall₂
        source.costWholeLanguage targetFree available outer elementType
        (trees.normalizedAvailable canonical objects scope)
        (trees.originalAvailable canonical objects scope) :=
    match trees with
    | @CostRegionElementTrees.nil source targetFree available outer elementType =>
      fun canonical objects scope => by
        let empty :=
          WellSorted.AvailableOpenElements.nil source.costWholeLanguage
            targetFree available outer elementType
        have leftEndpoint :
            (CostRegionElementTrees.nil (source := source)
              (targetFree := targetFree) available outer elementType
              ).normalizedAvailable canonical objects scope = empty := by
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
            WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
              available.length element := by
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
            source.costWholeLanguage.reflectivePresentations,
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
        have headStep := head.normalize_equationSetoid laws canonicalParts.1
          objectParts.1 headScope
        have tailStep := tail.normalize_equationForall₂ laws canonicalParts.2
          objectParts.2 tailScope
        have combined :=
          WellSorted.AvailableOpenElements.EquationForall₂.cons
            headStep tailStep
        have leftEndpoint :
            WellSorted.AvailableOpenElements.cons
                (head.normalizedAvailable canonicalParts.1 objectParts.1
                  headScope)
                (tail.normalizedAvailable canonicalParts.2 objectParts.2
                  tailScope) =
              (CostRegionElementTrees.cons head tail).normalizedAvailable
                canonical objects scope := by
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
  theorem CostRegionBoundaryTrees.normalizeValues_fiberEquivalent
      {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      (trees.normalizeValues.supportedOpenAssignment table).FiberEquivalent
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
        let normalizedHead := head.normalize
        let value :
            WellSorted.OpenPattern source.costWholeLanguage targetFree
              boundary.boundary.targetSupport
                boundary.boundary.targetType :=
          ⟨normalizedHead.pattern,
            by simpa only [List.append_nil] using normalizedHead.typed,
            normalizedHead.canonicalBinderMetadata
              boundary.contentCanonicalBinderMetadata,
            normalizedHead.objectPattern boundary.contentObjectPattern,
            by
              intro presentation membership
              exact normalizedHead.reflectiveScope presentation membership
                (Nat.le_refl boundary.boundary.targetSupport.length)
                (boundary.contentReflectiveScopeSafe presentation membership)⟩
        have headSplitStep := head.normalize_equationSetoid laws
          boundary.contentCanonicalBinderMetadata
            boundary.contentObjectPattern
              boundary.contentReflectiveScopeSafe
        have headOpenRaw :=
          WellSorted.AvailableOpenPattern.equationSetoid_to_openPatternEquationSetoid
            headSplitStep
        have headOpenTransported :=
          WellSorted.openPatternEquationSetoid_reindexBound
            (List.append_nil boundary.boundary.targetSupport) headOpenRaw
        have headOpen :
            (openPatternEquationSetoid source.costWholeLanguage
              targetFree boundary.boundary.targetSupport
                boundary.boundary.targetType).r value
              (TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                boundary) := by
          have leftEndpoint :
              ((head.normalizedAvailable
                boundary.contentCanonicalBinderMetadata
                  boundary.contentObjectPattern
                    boundary.contentReflectiveScopeSafe).toOpenPattern
                ).reindexBound
                  (List.append_nil boundary.boundary.targetSupport) =
                value := by
            apply Subtype.ext
            simp [value, normalizedHead,
              WellSorted.OpenPattern.reindexBound_pattern,
              WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
              CostRegionTree.normalizedAvailable_pattern]
          have rightEndpoint :
              ((head.originalAvailableOpenPattern
                boundary.contentCanonicalBinderMetadata
                  boundary.contentObjectPattern
                    boundary.contentReflectiveScopeSafe).toOpenPattern
                ).reindexBound
                  (List.append_nil boundary.boundary.targetSupport) =
                TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                  boundary := by
            apply Subtype.ext
            simp [WellSorted.OpenPattern.reindexBound_pattern,
              WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
              CostRegionTree.originalAvailableOpenPattern,
              TypedCostRegionBoundaryTable.Values.boundaryOriginalValue]
          rw [leftEndpoint, rightEndpoint] at headOpenTransported
          exact headOpenTransported
        have headEquivalent : ∀ inner : List TypeExpr,
            (openPatternEquationSetoid source.costWholeLanguage
              targetFree (inner ++ boundary.boundary.targetSupport)
                boundary.boundary.targetType).r
              (value.weakenRoot inner)
              ((TypedCostRegionBoundaryTable.Values.boundaryOriginalValue
                boundary).weakenRoot inner) := by
          intro inner
          exact laws.weakeningStable headOpen inner
        have tailEquivalent :
            (children.normalizeValues.supportedOpenAssignment
              tail).FiberEquivalent
              ((TypedCostRegionBoundaryTable.Values.original tail
                ).supportedOpenAssignment tail) := by
          intro name type lookup inner
          exact children.normalizeValues_fiberEquivalent laws lookup inner
        simpa only [CostRegionBoundaryTrees.normalizeValues, value,
          normalizedHead] using
          (TypedCostRegionBoundaryTable.Values.supportedOpenAssignment_cons_fiberEquivalent
            value children.normalizeValues headEquivalent tailEquivalent)
  termination_by 8 * trees.weight + 1
  decreasing_by
    all_goals simp [CostRegionBoundaryTrees.weight]
    all_goals omega
end

/-- Forget the quote-visible binder split while retaining every typed
intermediate vertex of the child-first normalization path. -/
theorem CostRegionTree.normalize_openPatternEquationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    (openPatternEquationSetoid source.costWholeLanguage targetFree
      (available ++ outer) type).r
      (tree.normalizedAvailable canonical object scope).toOpenPattern
      (tree.originalAvailableOpenPattern canonical object scope).toOpenPattern :=
  WellSorted.AvailableOpenPattern.equationSetoid_to_openPatternEquationSetoid
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage tree.normalize.pattern pattern := by
  have typed := tree.normalize_openPatternEquationSetoid laws canonical object
    scope
  have erased :=
    openPatternEquationSetoid_to_equationEquiv typed
  simpa only [WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
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
    (scope : WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      available.length pattern) :
    EquationSemantics.EquationEquiv defaultBasePremises
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
    {term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (elaboration : CostOpenElaboration source term) :
    (openEquationSetoid source.costIGSLT targetFree targetBound targetSort).r
      elaboration.normalizeErasure term := by
  have split := elaboration.tree.normalize_openPatternEquationSetoid laws
    term.2.2.1 term.2.2.2.1 term.2.2.2.2
  have transported := WellSorted.openPatternEquationSetoid_reindexBound
    (List.append_nil targetBound) split
  have leftEndpoint :
      ((elaboration.tree.normalizedAvailable term.2.2.1 term.2.2.2.1
        term.2.2.2.2).toOpenPattern.reindexBound
          (List.append_nil targetBound)) =
        elaboration.normalizeErasure := by
    apply Subtype.ext
    simp [CostOpenElaboration.normalizeErasure,
      CostRegionTree.normalizeOpen_pattern,
      CostRegionTree.normalizedAvailable_pattern,
      WellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toOpenPattern_pattern]
  have rightEndpoint :
      ((elaboration.tree.originalAvailableOpenPattern term.2.2.1
        term.2.2.2.1 term.2.2.2.2).toOpenPattern.reindexBound
          (List.append_nil targetBound)) =
        term := by
    apply Subtype.ext
    simp [CostRegionTree.originalAvailableOpenPattern_pattern,
      WellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toOpenPattern_pattern]
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
    (term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort) :
    (openEquationSetoid source.costIGSLT targetFree targetBound targetSort).r
      (source.costNormalizeOpen term) term :=
  (CostOpenElaboration.compile source term
    ).normalizeErasure_typed_openEquationSetoid laws

/-! ## Exact contextual typed canonical sections -/

/-- Contextual laws needed for the generated Cost open section and its next
continued-interaction layer.

These laws are deliberately separate from unary equation soundness.  They
state that the chosen exact representative is natural in unused free-context
entries, introduces no new free names, preserves arbitrary reflective support,
and therefore supplies the contextual fields independently of equation
soundness.  Preservation of the *next* continuation fragment is defined later,
after that continuation plan itself exists. -/
structure CostContextualOpenLaws (source : CIGSLT) : Prop where
  preservesFreeVariableSupport : ∀
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : WellSorted.OpenTerm source.costWholeLanguage free bound sort)
      {name : String},
    name ∈ (source.costNormalizeOpen term).1.freeFvarNames →
      name ∈ term.1.freeFvarNames
  normalizeRecontextualizeFree :
    ∀ {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : WellSorted.OpenTerm source.costWholeLanguage sourceFree bound sort)
      (preserves : ∀ {name freeType},
        name ∈ term.1.freeFvarNames →
        sourceFree name = some freeType →
          targetFree name = some freeType),
    (source.costNormalizeOpen (term.recontextualizeFree preserves)).1 =
      (source.costNormalizeOpen term).1
  preservesReflectiveSupport :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort source.costWholeLanguage}
      (term : WellSorted.OpenTerm source.costWholeLanguage free bound sort)
      (support : ContextSupport.Support) (available : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr),
    term.2.1.ReflectiveSupportSafeAt support available binderImage →
      (source.costNormalizeOpen term).2.1.ReflectiveSupportSafeAt
        support available binderImage

/-- Exact laws needed for the chosen compact Cost executor to supply a
contextual sort-indexed open section.

Typed unary normalization supplies soundness inside the exact free, bound,
and sort fiber, while generator invariance collapses each authored equation
generator.  The contextual extension carries the independent support laws
required to inhabit `CIGSLT`.  No claim is made here that all proof-relevant
elaborations erase to the same normal form; that strictly stronger property
is separated below because it is not hereditary under Cost iteration. -/
structure CostOpenSectionLaws (source : CIGSLT) : Prop
    extends CostTypedUnaryNormalizationLaws source,
      CostContextualOpenLaws source where
  generatorInvariant : CostOpenGeneratorInvariant source

/-- Additional compact-factorization law.

This says every proof-relevant elaboration of one compact term erases to the
same exact representative.  It is useful when true, but it is intentionally
not required to construct the next continued Cost object: distinct semantic
fibres may share one compact observation at higher Cost layers. -/
structure CostOpenCanonicalLaws (source : CIGSLT) : Prop
    extends CostOpenSectionLaws source where
  compactCoherent : CompactCostNormalizationCoherent source

/-- Object property selecting the ciGSLTs on which the proof-relevant Cost
normalizer additionally factors through one exact compact representative. -/
def CostCanonicalObjectProperty : CategoryTheory.ObjectProperty CIGSLT :=
  CostOpenCanonicalLaws

/-- Full subcategory of ciGSLTs carrying the exact typed Cost laws.  The
eventual Cost₁ category further restricts morphisms to maps preserving the
generated structural data and canonical-key order. -/
abbrev CostCanonicalObjects :=
  CostCanonicalObjectProperty.FullSubcategory

/-- Forget exact Cost canonical laws while retaining the underlying ciGSLT. -/
def costCanonicalObjectsForget :
    CategoryTheory.Functor CostCanonicalObjects CIGSLT :=
  CostCanonicalObjectProperty.ι

/-- Exact computable section of every typed open Cost fiber.  Soundness comes
from proof-relevant tree normalization; completeness is generated solely from
exact invariance under the authored open-equation generators. -/
def CIGSLT.costOpenSection (source : CIGSLT)
    (laws : CostOpenSectionLaws source) :
    ComputableOpenSection source.costIGSLT :=
  ComputableOpenSection.ofGeneratorInvariant source.costNormalizeOpen
    (fun term => source.costNormalizeOpen_typed_openEquationSetoid
      laws.toCostTypedUnaryNormalizationLaws term)
    (fun generator => laws.generatorInvariant generator)

/-- Exact contextual open section of the generated Cost presentation.
Every additional field is supplied by the Cost₁ object law rather than
inferred from equation equivalence. -/
def CIGSLT.costContextualOpenSection (source : CIGSLT)
    (laws : CostOpenSectionLaws source) :
    ComputableContextualOpenSection source.costIGSLT where
  toComputableOpenSection := source.costOpenSection laws
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

/-- Exact representative independence on every typed open Cost equation
path.  This theorem is downstream of the local generator law. -/
theorem CIGSLT.costNormalizeOpen_complete (source : CIGSLT)
    (laws : CostOpenSectionLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (equivalent :
      (openEquationSetoid source.costIGSLT targetFree targetBound targetSort).r
        left right) :
    source.costNormalizeOpen left = source.costNormalizeOpen right :=
  (source.costOpenSection laws).complete equivalent

/-- Canonical section for compact observations of proof-relevant Cost
elaborations.  The observation relation deliberately forgets elaboration
identity; the elaborated semantic carrier itself retains it. -/
def CIGSLT.costCompactObservationSection (source : CIGSLT)
    (laws : CostOpenCanonicalLaws source)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage) :
    ComputableSetoidSection
      (CostElabTerm source targetFree targetBound targetSort)
      (CostOpenElaboration.costCompactObservationSetoid source targetFree
        targetBound targetSort) where
  normalize := CostOpenElaboration.normalizeTerm source
  equivalent := by
    intro term
    change (openEquationSetoid source.costIGSLT targetFree targetBound
      targetSort).r term.2.normalizeErasure term.1
    exact term.2.normalizeErasure_typed_openEquationSetoid
      laws.toCostOpenSectionLaws.toCostTypedUnaryNormalizationLaws
  complete := by
    intro left right equivalent
    change (openEquationSetoid source.costIGSLT targetFree targetBound
      targetSort).r left.1 right.1 at equivalent
    change CostOpenElaboration.compileTerm source
        left.2.normalizeErasure =
      CostOpenElaboration.compileTerm source right.2.normalizeErasure
    apply congrArg (CostOpenElaboration.compileTerm source)
    exact (left.2.normalizeErasure_eq_costNormalizeOpen laws.compactCoherent
      ).trans ((source.costNormalizeOpen_complete laws.toCostOpenSectionLaws
        equivalent).trans
        (right.2.normalizeErasure_eq_costNormalizeOpen
          laws.compactCoherent).symm)

/-- Erasing the semantic representative of any elaboration agrees exactly
with the executable compact normalizer. -/
theorem CIGSLT.costCompactObservationSection_normalize_erase (source : CIGSLT)
    (laws : CostOpenCanonicalLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    CostOpenElaboration.erase
        ((source.costCompactObservationSection laws targetFree targetBound
          targetSort).normalize term) =
      source.costNormalizeOpen term.1 := by
  change term.2.normalizeErasure = source.costNormalizeOpen term.1
  exact term.2.normalizeErasure_eq_costNormalizeOpen laws.compactCoherent

/-- Exact chooser independence for one admitted typed compact term, derived
only from the explicit compact-coherence law. -/
theorem CostRegionTree.normalize_overlap_exact
    {source : CIGSLT} (laws : CostOpenCanonicalLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort)
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
    (term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort)
    (tree : CostRegionTree source targetFree targetBound [] term.1
      (.base targetSort.1)) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage tree.normalize.pattern
        (source.costNormalizeOpen term).1 := by
  simpa only [source.costNormalizeOpen_pattern] using
    tree.normalize_typed_overlap_equivalent laws
      (CostRegionTree.buildOpenTerm (source := source) term)
      term.2.2.1 term.2.2.2.1 term.2.2.2.2

end Mettapedia.GSLT.LanguageDef
