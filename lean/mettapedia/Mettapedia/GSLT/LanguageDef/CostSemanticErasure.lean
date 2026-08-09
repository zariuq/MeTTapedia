import Mettapedia.GSLT.LanguageDef.CostSemanticSoundness

/-!
# Authored erasure and the exact semantic Cost object

The retained semantic relation projects to paths in the admitted reflective
equation theory over the sole authored Cost `IGSLT`.  Together with in-place
exact normalization, this packages semantic Cost as a
`ReflectiveElaboratedOpenTheory` without imposing compact faithfulness or a
second equation authority.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace TypedCostRegionBoundaryTable.Values

/-- Pointwise equivalence of a replacement head and tail extends to the
complete finite supported assignment.  Unlike the original-value specialization,
both sides may be evolving semantic boundary values. -/
theorem supportedOpenAssignment_cons_fiberEquivalent_of_values
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    {boundary : TypedCostRegionBoundary source color targetFree}
    {content : boundary.boundary.content = occurrence.content}
    {tail : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (leftValue rightValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType)
    (leftValues rightValues : Values source color targetFree tail)
    (headEquivalent : ∀ inner : List TypeExpr,
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree
        (inner ++ boundary.boundary.targetSupport)
        boundary.boundary.targetType).r
        (leftValue.weakenRoot inner) (rightValue.weakenRoot inner))
    (tailEquivalent :
      (leftValues.supportedOpenAssignment tail).FiberEquivalent
        (rightValues.supportedOpenAssignment tail)) :
    ((Values.cons leftValue leftValues).supportedOpenAssignment
      (.cons boundary content tail)).FiberEquivalent
    ((Values.cons rightValue rightValues).supportedOpenAssignment
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
            ((Values.cons leftValue leftValues).supportedOpenAssignment
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
            (leftValue.weakenRoot inner).reindexBound boundEquality =
              WellSorted.SupportedOpenAssignment.weakenedValue
                ((Values.cons leftValue leftValues).supportedOpenAssignment
                  (.cons boundary content tail)) lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodeCostRegionSourceVariableName_boundary]
        have rightEndpoint :
            (rightValue.weakenRoot inner).reindexBound boundEquality =
              WellSorted.SupportedOpenAssignment.weakenedValue
                ((Values.cons rightValue rightValues).supportedOpenAssignment
                  (.cons boundary content tail)) lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodeCostRegionSourceVariableName_boundary]
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
            ((leftValues.supportedOpenAssignment tail).weakenedValue
              tailLookup inner).reindexBound boundEquality =
              ((Values.cons leftValue leftValues).supportedOpenAssignment
                (.cons boundary content tail)).weakenedValue lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodedName, keyEquality]
        have rightEndpoint :
            ((rightValues.supportedOpenAssignment tail).weakenedValue
              tailLookup inner).reindexBound boundEquality =
              ((Values.cons rightValue rightValues).supportedOpenAssignment
                (.cons boundary content tail)).weakenedValue lookup inner := by
          apply Subtype.ext
          simp [WellSorted.SupportedOpenAssignment.weakenedValue,
            supportedOpenAssignment, supportedAssignment, assignment, resolve,
            decodedName, keyEquality]
        rw [leftEndpoint, rightEndpoint] at transported
        exact transported

end TypedCostRegionBoundaryTable.Values

namespace CostSemanticTree

@[simp]
theorem normalizedArgument_pattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation : WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.normalizedArgument parameter representation parameterType canonical
      object scope).term.pattern = tree.normalize.result.pattern :=
  rfl

@[simp]
theorem originalArgument_pattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (parameter : TermParam)
    (representation : WellSorted.MatchesParameterRepresentation parameter pattern)
    (parameterType : WellSorted.parameterType? parameter = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.originalArgument parameter representation parameterType canonical object
      scope).term.pattern = pattern :=
  rfl

/-- Any split-fiber term path can be viewed as a path for a simple authored
parameter.  Simple parameters impose no additional representation invariant. -/
theorem simpleArgument_equationSetoid
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (parameterName : String) (parameterTypeExpression : TypeExpr)
    (parameterType :
      WellSorted.parameterType?
        (.simple parameterName parameterTypeExpression) = some type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern)
    (equivalent :
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope)
        (tree.originalAvailable canonical object scope)) :
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree available outer
        (.simple parameterName parameterTypeExpression) type).r
      (tree.normalizedArgument (.simple parameterName parameterTypeExpression)
        True.intro parameterType canonical object scope)
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
      pack (tree.normalizedAvailable canonical object scope) =
        tree.normalizedArgument (.simple parameterName parameterTypeExpression)
          True.intro parameterType canonical object scope := by
    apply WellSorted.AvailableOpenArgument.ext
    rfl
  have rightEndpoint :
      pack (tree.originalAvailable canonical object scope) =
        tree.originalArgument (.simple parameterName parameterTypeExpression)
          True.intro parameterType canonical object scope := by
    apply WellSorted.AvailableOpenArgument.ext
    rfl
  rw [leftEndpoint, rightEndpoint] at packed
  exact packed

/-- The two mutually needed authored-soundness statements for one semantic
tree: its term path and every admissible authored-parameter packaging. -/
def NormalizationSound {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    Prop :=
  (∀
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length pattern),
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree available outer type).r
        (tree.normalizedAvailable canonical object scope)
        (tree.originalAvailable canonical object scope)) ∧
  (∀
      (parameter : TermParam)
      (representation :
        WellSorted.MatchesParameterRepresentation parameter pattern)
      (parameterType : WellSorted.parameterType? parameter = some type)
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length pattern),
      (WellSorted.AvailableOpenArgument.equationSetoid
        source.costWholeLanguage targetFree available outer parameter type).r
        (tree.normalizedArgument parameter representation parameterType
          canonical object scope)
        (tree.originalArgument parameter representation parameterType
          canonical object scope))

end CostSemanticTree

namespace CostSemanticArgumentTrees

/-- Authored pointwise normalization of a semantic constructor spine. -/
def NormalizationSound {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters) : Prop :=
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
      (trees.normalizedAvailable canonical objects scope)
      (trees.originalAvailable canonical objects scope)

end CostSemanticArgumentTrees

namespace CostSemanticElementTrees

/-- Authored pointwise normalization of a semantic collection spine. -/
def NormalizationSound {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType) : Prop :=
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
      (trees.normalizedAvailable canonical objects scope)
      (trees.originalAvailable canonical objects scope)

end CostSemanticElementTrees

namespace CostSemanticBoundaryTrees

/-- Normalization of evolving proof-relevant boundary values is pointwise
authored-equivalent to the current finite assignment. -/
def NormalizationSound {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    (trees : CostSemanticBoundaryTrees source targetFree color table values) :
    Prop :=
  (trees.normalize.1.supportedOpenAssignment table).FiberEquivalent
    (values.supportedOpenAssignment table)

end CostSemanticBoundaryTrees

@[simp]
theorem CostSemanticTree.normalize_static_result_pattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {outer : List TypeExpr}
    (frame : CostStaticRegionNode source color targetFree)
    (state : CostStaticFrameState frame)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color
      frame.boundaryTable values) :
    (CostSemanticTree.static (outer := outer) frame state children
      ).normalize.result.pattern =
      (state.normalize.actAvailableWithOuter children.normalize.1 outer).pattern :=
  congrArg
    (fun normalized : NormalizedCostSemanticTree source targetFree
        frame.targetBound outer
        (state.actAvailableWithOuter values outer).pattern
        (.base (color.mapLangSort source frame.sourceSort).1) =>
      normalized.result.pattern)
    (CostSemanticTree.normalize.eq_3 (outer := outer) color frame state values
      children)

private theorem CostSemanticTree.normalizationSound_static
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {outer : List TypeExpr}
    (frame : CostStaticRegionNode source color targetFree)
    (state : CostStaticFrameState frame)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color
      frame.boundaryTable values)
    (childrenSound : children.NormalizationSound) :
    (CostSemanticTree.static (outer := outer) frame state children
      ).NormalizationSound := by
  let current := CostSemanticTree.static (outer := outer) frame state children
  have termSound : ∀
      (canonical : (state.actAvailableWithOuter values outer).pattern.hasCanonicalBinderMetadata = true)
      (object : WellSorted.isObjectPattern
        (state.actAvailableWithOuter values outer).pattern = true)
      (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        frame.targetBound.length
          (state.actAvailableWithOuter values outer).pattern),
      (WellSorted.AvailableOpenPattern.equationSetoid
        source.costWholeLanguage targetFree frame.targetBound outer
          (.base (color.mapLangSort source frame.sourceSort).1)).r
        (current.normalizedAvailable canonical object scope)
        (current.originalAvailable canonical object scope) := by
    intro canonical object scope
    have localStep := state.normalize_actAvailable_equationSetoid
      laws.mappedGeneratorFiberAction children.normalize.1 values childrenSound
    have openStepRaw :=
      WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
        localStep
    have openStep :=
      ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
        (List.append_nil frame.targetBound) openStepRaw
    have lifted :=
      WellSorted.AvailableOpenPattern.reflectiveOpenPatternEquationSetoid_to_availableWithOuter
        outer openStep
    have leftEndpoint :
        WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
            ((state.normalize.actAvailable children.normalize.1).toReflectiveOpenPattern
              |>.reindexBound (List.append_nil frame.targetBound)) outer =
          current.normalizedAvailable canonical object scope := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [
        WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
        ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
        WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
        CostSemanticTree.normalizedAvailable_pattern]
      rw [CostSemanticTree.normalize_static_result_pattern]
      rfl
    have rightEndpoint :
        WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
            ((state.actAvailable values).toReflectiveOpenPattern
              |>.reindexBound (List.append_nil frame.targetBound)) outer =
          current.originalAvailable canonical object scope := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [
        WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
        ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
        WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
        CostSemanticTree.originalAvailable_pattern]
      rfl
    rw [leftEndpoint, rightEndpoint] at lifted
    exact lifted
  refine ⟨termSound, ?_⟩
  intro parameter representation parameterType canonical object scope
  cases parameter with
  | simple name declared =>
      exact current.simpleArgument_equationSetoid name declared parameterType
        canonical object scope (termSound canonical object scope)
  | abstractionNamed binderName bodyName declared =>
      cases declared <;> simp [WellSorted.parameterType?] at parameterType
  | multiAbstractionNamed binderNames bodyName declared =>
      cases declared with
      | base sort => simp [WellSorted.parameterType?] at parameterType
      | arrow domain codomain =>
          cases domain <;> simp [WellSorted.parameterType?] at parameterType
      | multiBinder domain => simp [WellSorted.parameterType?] at parameterType
      | collection collectionType elementType =>
          simp [WellSorted.parameterType?] at parameterType

/-- The semantic normalizer erases to an admitted reflective equation path
while retaining the exact split binder, parameter, collection, and
finite-boundary fibers.  The generated four-way recursor supplies all mutually
recursive hypotheses, so this proof has no auxiliary termination measure or
heartbeat-sensitive mutual block. -/
theorem CostSemanticTree.normalizationSound
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    tree.NormalizationSound := by
  apply CostSemanticTree.rec
    (motive_1 := fun _ _ _ _ tree => tree.NormalizationSound)
    (motive_2 := fun _ _ _ _ trees => trees.NormalizationSound)
    (motive_3 := fun _ _ _ _ trees => trees.NormalizationSound)
    (motive_4 := fun _ _ _ _ trees => trees.NormalizationSound)
    (t := tree)
  · intros
    rename_i available' outer' index type' lookup
    let current := CostSemanticTree.bvar (source := source)
      (targetFree := targetFree) lookup
    have termSound : ∀
        (canonical : (Pattern.bvar index).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern (.bvar index) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.bvar index)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer' type').r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have endpoint : current.normalizedAvailable canonical object scope =
          current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, CostSemanticTree.normalizedAvailable_pattern,
          CostSemanticTree.originalAvailable_pattern, CostSemanticTree.normalize]
      rw [endpoint]
      exact Relation.EqvGen.refl _
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i available' outer' name type' lookup
    let current := CostSemanticTree.fvar (source := source)
      (targetFree := targetFree) (available := available') (outer := outer') lookup
    have termSound : ∀
        (canonical : (Pattern.fvar name).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern (.fvar name) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.fvar name)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer' type').r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have endpoint : current.normalizedAvailable canonical object scope =
          current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, CostSemanticTree.normalizedAvailable_pattern,
          CostSemanticTree.originalAvailable_pattern, CostSemanticTree.normalize]
      rw [endpoint]
      exact Relation.EqvGen.refl _
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple parameterName declared =>
        exact current.simpleArgument_equationSetoid parameterName declared
          parameterType canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i color outer' frame state values children childrenSound
    exact CostSemanticTree.normalizationSound_static laws frame state children
      childrenSound
  · intros
    rename_i available' outer' rule arguments membership notBareCollection
      constructor materializes neutral ordinary children childrenSound
    let current := CostSemanticTree.neutralApplicationOrdinary membership
      notBareCollection constructor materializes neutral ordinary children
    have termSound : ∀
        (canonical : (Pattern.apply rule.label arguments).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern (.apply rule.label arguments) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.apply rule.label arguments)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer'
            (.base rule.category)).r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have argumentCanonical :
          Pattern.hasCanonicalBinderMetadataList arguments = true := by
        simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
      have argumentObjects :
          WellSorted.isObjectPatternList arguments = true := by
        simpa [current, WellSorted.isObjectPattern] using object
      have argumentScope : ∀ presentation ∈
          source.costWholeReflectionProfile.presentations,
          binderSafeListAt presentation.quoteConstructor available'.length
            arguments = true := by
        intro presentation presentationMembership
        have notThisQuote : rule.label ≠ presentation.quoteConstructor := by
          intro labelEquality
          have detected : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = true := by
            unfold ReflectiveContextSupport.isQuoteConstructor
            rw [List.any_eq_true]
            exact ⟨presentation, presentationMembership, by simp [labelEquality]⟩
          rw [detected] at ordinary
          contradiction
        exact binderSafeListAt_of_binderSafeAt_apply_of_ne
          presentation.quoteConstructor rule.label available'.length arguments
          notThisQuote (scope presentation presentationMembership)
      have assembled := (childrenSound argumentCanonical argumentObjects
        argumentScope).assembleOrdinary membership notBareCollection ordinary
      have leftEndpoint :
          (children.normalizedAvailable argumentCanonical argumentObjects
            argumentScope).applyOrdinary membership notBareCollection ordinary =
            current.normalizedAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, CostSemanticArgumentTrees.normalizedAvailable_patterns,
          CostSemanticTree.normalizedAvailable_pattern, CostSemanticTree.normalize]
      have rightEndpoint :
          (children.originalAvailable argumentCanonical argumentObjects
            argumentScope).applyOrdinary membership notBareCollection ordinary =
            current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        rfl
      rw [leftEndpoint, rightEndpoint] at assembled
      exact assembled
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i available' outer' rule arguments membership notBareCollection
      constructor materializes neutral quoted children childrenSound
    let current := CostSemanticTree.neutralApplicationQuote membership
      notBareCollection constructor materializes neutral quoted children
    have termSound : ∀
        (canonical : (Pattern.apply rule.label arguments).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern (.apply rule.label arguments) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.apply rule.label arguments)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer'
            (.base rule.category)).r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have argumentCanonical :
          Pattern.hasCanonicalBinderMetadataList arguments = true := by
        simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
      have argumentObjects :
          WellSorted.isObjectPatternList arguments = true := by
        simpa [current, WellSorted.isObjectPattern] using object
      have parentScopeAtBound :
          ReflectiveWellSorted.ReflectiveScopeSafeAt
            source.costWholeReflectionProfile
            (available' ++ outer').length (.apply rule.label arguments) := by
        intro presentation presentationMembership
        exact binderSafeAt_mono presentation.quoteConstructor
          (scope presentation presentationMembership) (by simp)
      have argumentsTyped :
          WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
            (available' ++ outer') arguments rule.params := by
        simpa only [List.nil_append] using children.originalTyped
      have argumentScope :=
        WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
          source.costWholeLanguage_validate
            source.costWholeReflectionProfile_validate membership
              argumentsTyped quoted parentScopeAtBound
      have assembled := (childrenSound argumentCanonical argumentObjects
        argumentScope).assembleQuote membership notBareCollection quoted
      have leftEndpoint :
          (children.normalizedAvailable argumentCanonical argumentObjects
            argumentScope).applyQuote membership notBareCollection quoted =
            current.normalizedAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, CostSemanticArgumentTrees.normalizedAvailable_patterns,
          CostSemanticTree.normalizedAvailable_pattern, CostSemanticTree.normalize]
      have rightEndpoint :
          (children.originalAvailable argumentCanonical argumentObjects
            argumentScope).applyQuote membership notBareCollection quoted =
            current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        rfl
      rw [leftEndpoint, rightEndpoint] at assembled
      exact assembled
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i available' outer' binder body domain codomain bodyTree bodySound
    let current := CostSemanticTree.lambda (binder := binder) bodyTree
    have termSound : ∀
        (canonical : (Pattern.lambda binder body).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern (.lambda binder body) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.lambda binder body)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer'
            (.arrow domain codomain)).r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have canonicalParts : binder.isNone = true ∧
          body.hasCanonicalBinderMetadata = true := by
        simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [current, WellSorted.isObjectPattern] using object
      have bodyScope :
          ReflectiveWellSorted.ReflectiveScopeSafeAt
            source.costWholeReflectionProfile
            (domain :: available').length body := by
        intro presentation presentationMembership
        simpa [binderSafeAt, List.length_cons] using
          scope presentation presentationMembership
      have assembled :=
        WellSorted.AvailableOpenPattern.equationSetoid_lambda_congr binder
          canonicalParts.1 (bodySound.1 canonicalParts.2 bodyObject bodyScope)
      have leftEndpoint :
          (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
            ).lambda binder canonicalParts.1 =
            current.normalizedAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, WellSorted.AvailableOpenPattern.lambda_pattern,
          CostSemanticTree.normalizedAvailable_pattern, CostSemanticTree.normalize]
      have rightEndpoint :
          (bodyTree.originalAvailable canonicalParts.2 bodyObject bodyScope
            ).lambda binder canonicalParts.1 =
            current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        rfl
      rw [leftEndpoint, rightEndpoint] at assembled
      exact assembled
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        cases binder with
        | some display =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | none =>
            have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
              simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
            have bodyObject : WellSorted.isObjectPattern body = true := by
              simpa [current, WellSorted.isObjectPattern] using object
            have bodyScope :
                ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile
                  (domain :: available').length body := by
              intro presentation presentationMembership
              simpa [binderSafeAt, List.length_cons] using
                scope presentation presentationMembership
            let pack := fun
                (term : WellSorted.AvailableOpenPattern
                  source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree (domain :: available') outer' codomain) =>
              ({ term := term.lambda none rfl
                 representation := True.intro
                 parameterType := parameterType } :
                WellSorted.AvailableOpenArgument
                  source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree available' outer'
                    (.abstractionNamed binderName bodyName declared)
                      (.arrow domain codomain))
            have packed :=
              WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
                (by
                  intro left right generator
                  exact EquationSemantics.reflectiveEquationContextStep_fill
                    (.lambda none .hole) generator)
                (bodySound.1 bodyCanonical bodyObject bodyScope)
            have leftEndpoint :
                pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                  bodyScope) =
                  current.normalizedArgument
                    (.abstractionNamed binderName bodyName declared)
                      representation parameterType canonical object scope := by
              apply WellSorted.AvailableOpenArgument.ext
              simp [pack, current, CostSemanticTree.normalize]
            have rightEndpoint :
                pack (bodyTree.originalAvailable bodyCanonical bodyObject
                  bodyScope) =
                  current.originalArgument
                    (.abstractionNamed binderName bodyName declared)
                      representation parameterType canonical object scope := by
              apply WellSorted.AvailableOpenArgument.ext
              rfl
            rw [leftEndpoint, rightEndpoint] at packed
            exact packed
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i available' outer' arity binders body domain codomain bodyTree
      bodySound
    let current := CostSemanticTree.multiLambda (binders := binders) bodyTree
    have termSound : ∀
        (canonical : (Pattern.multiLambda arity binders body).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern
          (.multiLambda arity binders body) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.multiLambda arity binders body)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer'
            (.arrow (.multiBinder domain) codomain)).r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      have canonicalParts : binders.isEmpty = true ∧
          body.hasCanonicalBinderMetadata = true := by
        simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
      have bindersCanonical : binders = [] := by simpa using canonicalParts.1
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [current, WellSorted.isObjectPattern] using object
      have bodyScope :
          ReflectiveWellSorted.ReflectiveScopeSafeAt
            source.costWholeReflectionProfile
            (List.replicate arity domain ++ available').length body := by
        intro presentation presentationMembership
        simpa [binderSafeAt, List.length_append, List.length_replicate,
          Nat.add_comm] using scope presentation presentationMembership
      have assembled :=
        WellSorted.AvailableOpenPattern.equationSetoid_multiLambda_congr
          arity binders bindersCanonical
            (bodySound.1 canonicalParts.2 bodyObject bodyScope)
      have leftEndpoint :
          (bodyTree.normalizedAvailable canonicalParts.2 bodyObject bodyScope
            ).multiLambda arity binders bindersCanonical =
            current.normalizedAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        simp [current, WellSorted.AvailableOpenPattern.multiLambda_pattern,
          CostSemanticTree.normalizedAvailable_pattern, CostSemanticTree.normalize]
      have rightEndpoint :
          (bodyTree.originalAvailable canonicalParts.2 bodyObject bodyScope
            ).multiLambda arity binders bindersCanonical =
            current.originalAvailable canonical object scope := by
        apply WellSorted.AvailableOpenPattern.ext
        rfl
      rw [leftEndpoint, rightEndpoint] at assembled
      exact assembled
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        cases binders with
        | cons display displays =>
            simp [WellSorted.MatchesParameterRepresentation] at representation
        | nil =>
            have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
              simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
            have bodyObject : WellSorted.isObjectPattern body = true := by
              simpa [current, WellSorted.isObjectPattern] using object
            have bodyScope :
                ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile
                  (List.replicate arity domain ++ available').length body := by
              intro presentation presentationMembership
              simpa [binderSafeAt, List.length_append, List.length_replicate,
                Nat.add_comm] using scope presentation presentationMembership
            let pack := fun
                (term : WellSorted.AvailableOpenPattern
                  source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree (List.replicate arity domain ++ available') outer'
                    codomain) =>
              ({ term := term.multiLambda arity [] rfl
                 representation := True.intro
                 parameterType := parameterType } :
                WellSorted.AvailableOpenArgument
                  source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree available' outer'
                    (.multiAbstractionNamed binderNames bodyName declared)
                      (.arrow (.multiBinder domain) codomain))
            have packed :=
              WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
                (by
                  intro left right generator
                  exact EquationSemantics.reflectiveEquationContextStep_fill
                    (.multiLambda arity [] .hole) generator)
                (bodySound.1 bodyCanonical bodyObject bodyScope)
            have leftEndpoint :
                pack (bodyTree.normalizedAvailable bodyCanonical bodyObject
                  bodyScope) =
                  current.normalizedArgument
                    (.multiAbstractionNamed binderNames bodyName declared)
                      representation parameterType canonical object scope := by
              apply WellSorted.AvailableOpenArgument.ext
              simp [pack, current, CostSemanticTree.normalize]
            have rightEndpoint :
                pack (bodyTree.originalAvailable bodyCanonical bodyObject
                  bodyScope) =
                  current.originalArgument
                    (.multiAbstractionNamed binderNames bodyName declared)
                      representation parameterType canonical object scope := by
              apply WellSorted.AvailableOpenArgument.ext
              rfl
            rw [leftEndpoint, rightEndpoint] at packed
            exact packed
  · intros
    rename_i available' outer' body replacement domain codomain bodyTree
      replacementTree bodySound replacementSound
    constructor
    · intro canonical object scope
      simp [WellSorted.isObjectPattern] at object
    · intro parameter representation parameterType canonical object scope
      simp [WellSorted.isObjectPattern] at object
  · intros
    rename_i available' outer' collectionType elements rest elementType children
      childrenSound
    let current := CostSemanticTree.collection (collectionType := collectionType)
      (rest := rest) children
    have termSound : ∀
        (canonical : (Pattern.collection collectionType elements rest
          ).hasCanonicalBinderMetadata = true)
        (object : WellSorted.isObjectPattern
          (.collection collectionType elements rest) = true)
        (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          available'.length (.collection collectionType elements rest)),
        (WellSorted.AvailableOpenPattern.equationSetoid
          source.costWholeLanguage targetFree available' outer'
            (.collection collectionType elementType)).r
          (current.normalizedAvailable canonical object scope)
          (current.originalAvailable canonical object scope) := by
      intro canonical object scope
      cases rest with
      | some restName => simp [WellSorted.isObjectPattern] at object
      | none =>
          have elementCanonical :
              Pattern.hasCanonicalBinderMetadataList elements = true := by
            simpa [current, Pattern.hasCanonicalBinderMetadata] using canonical
          have elementObjects :
              WellSorted.isObjectPatternList elements = true := by
            simpa [current, WellSorted.isObjectPattern] using object
          have elementScope : ∀ presentation ∈
              source.costWholeReflectionProfile.presentations,
              binderSafeListAt presentation.quoteConstructor available'.length
                elements = true := by
            intro presentation presentationMembership
            simpa [binderSafeAt] using scope presentation presentationMembership
          have assembled := (childrenSound elementCanonical elementObjects
            elementScope).assemble collectionType
          have leftEndpoint :
              (children.normalizedAvailable elementCanonical elementObjects
                elementScope).collection collectionType =
                current.normalizedAvailable canonical object scope := by
            apply WellSorted.AvailableOpenPattern.ext
            simp [current, WellSorted.AvailableOpenElements.collection_pattern,
              CostSemanticElementTrees.normalizedAvailable_patterns,
              CostSemanticTree.normalizedAvailable_pattern,
              CostSemanticTree.normalize]
          have rightEndpoint :
              (children.originalAvailable elementCanonical elementObjects
                elementScope).collection collectionType =
                current.originalAvailable canonical object scope := by
            apply WellSorted.AvailableOpenPattern.ext
            rfl
          rw [leftEndpoint, rightEndpoint] at assembled
          exact assembled
    refine ⟨termSound, ?_⟩
    intro parameter representation parameterType canonical object scope
    cases parameter with
    | simple name declared =>
        exact current.simpleArgument_equationSetoid name declared parameterType
          canonical object scope (termSound canonical object scope)
    | abstractionNamed binderName bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
    | multiAbstractionNamed binderNames bodyName declared =>
        simp [WellSorted.MatchesParameterRepresentation] at representation
  · intros
    rename_i available' outer'
    intro canonical objects scope
    let empty := WellSorted.AvailableOpenArguments.nil
      (profile := source.costWholeReflectionProfile)
      source.costWholeLanguage targetFree available' outer'
    have leftEndpoint :
        (CostSemanticArgumentTrees.nil (source := source)
          (targetFree := targetFree)).normalizedAvailable canonical objects scope =
          empty := by
      apply WellSorted.AvailableOpenArguments.ext
      simp [empty, CostSemanticArgumentTrees.normalizedAvailable_patterns,
        CostSemanticArgumentTrees.normalize]
    have rightEndpoint :
        (CostSemanticArgumentTrees.nil (source := source)
          (targetFree := targetFree)).originalAvailable canonical objects scope =
          empty := by
      apply WellSorted.AvailableOpenArguments.ext
      rfl
    rw [leftEndpoint, rightEndpoint]
    exact WellSorted.AvailableOpenArguments.EquationForall₂.nil
  · intros
    rename_i available' outer' argument arguments parameter parameters expected
      representation parameterType head tail headSound tailSound
    intro canonical objects scope
    have canonicalParts : argument.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList arguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
    have objectParts : WellSorted.isObjectPattern argument = true ∧
        WellSorted.isObjectPatternList arguments = true := by
      simpa [WellSorted.isObjectPatternList] using objects
    have headScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile available'.length argument := by
      intro presentation presentationMembership
      have parts :
          binderSafeAt presentation.quoteConstructor available'.length argument = true ∧
            binderSafeListAt presentation.quoteConstructor available'.length
              arguments = true := by
        simpa [binderSafeListAt] using scope presentation presentationMembership
      exact parts.1
    have tailScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available'.length
          arguments = true := by
      intro presentation presentationMembership
      have parts :
          binderSafeAt presentation.quoteConstructor available'.length argument = true ∧
            binderSafeListAt presentation.quoteConstructor available'.length
              arguments = true := by
        simpa [binderSafeListAt] using scope presentation presentationMembership
      exact parts.2
    have combined := WellSorted.AvailableOpenArguments.EquationForall₂.cons
      (headSound.2 parameter representation parameterType canonicalParts.1
        objectParts.1 headScope)
      (tailSound canonicalParts.2 objectParts.2 tailScope)
    have leftEndpoint :
        WellSorted.AvailableOpenArguments.cons
            (head.normalizedArgument parameter representation parameterType
              canonicalParts.1 objectParts.1 headScope)
            (tail.normalizedAvailable canonicalParts.2 objectParts.2 tailScope) =
          (CostSemanticArgumentTrees.cons representation parameterType head tail
            ).normalizedAvailable canonical objects scope := by
      apply WellSorted.AvailableOpenArguments.ext
      simp [CostSemanticArgumentTrees.normalizedAvailable_patterns,
        CostSemanticArgumentTrees.normalize]
    have rightEndpoint :
        WellSorted.AvailableOpenArguments.cons
            (head.originalArgument parameter representation parameterType
              canonicalParts.1 objectParts.1 headScope)
            (tail.originalAvailable canonicalParts.2 objectParts.2 tailScope) =
          (CostSemanticArgumentTrees.cons representation parameterType head tail
            ).originalAvailable canonical objects scope := by
      apply WellSorted.AvailableOpenArguments.ext
      rfl
    rw [leftEndpoint, rightEndpoint] at combined
    exact combined
  · intros
    rename_i available' outer' elementType
    intro canonical objects scope
    let empty := WellSorted.AvailableOpenElements.nil
      (profile := source.costWholeReflectionProfile)
      source.costWholeLanguage targetFree available' outer' elementType
    have leftEndpoint :
        (CostSemanticElementTrees.nil (source := source)
          (targetFree := targetFree) available' outer' elementType
          ).normalizedAvailable canonical objects scope = empty := by
      apply WellSorted.AvailableOpenElements.ext
      simp [empty, CostSemanticElementTrees.normalizedAvailable_patterns,
        CostSemanticElementTrees.normalize]
    have rightEndpoint :
        (CostSemanticElementTrees.nil (source := source)
          (targetFree := targetFree) available' outer' elementType
          ).originalAvailable canonical objects scope = empty := by
      apply WellSorted.AvailableOpenElements.ext
      rfl
    rw [leftEndpoint, rightEndpoint]
    exact WellSorted.AvailableOpenElements.EquationForall₂.nil
  · intros
    rename_i available' outer' element elements elementType head tail headSound
      tailSound
    intro canonical objects scope
    have canonicalParts : element.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList elements = true := by
      simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
    have objectParts : WellSorted.isObjectPattern element = true ∧
        WellSorted.isObjectPatternList elements = true := by
      simpa [WellSorted.isObjectPatternList] using objects
    have headScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile available'.length element := by
      intro presentation presentationMembership
      have parts :
          binderSafeAt presentation.quoteConstructor available'.length element = true ∧
            binderSafeListAt presentation.quoteConstructor available'.length
              elements = true := by
        simpa [binderSafeListAt] using scope presentation presentationMembership
      exact parts.1
    have tailScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available'.length
          elements = true := by
      intro presentation presentationMembership
      have parts :
          binderSafeAt presentation.quoteConstructor available'.length element = true ∧
            binderSafeListAt presentation.quoteConstructor available'.length
              elements = true := by
        simpa [binderSafeListAt] using scope presentation presentationMembership
      exact parts.2
    have combined := WellSorted.AvailableOpenElements.EquationForall₂.cons
      (headSound.1 canonicalParts.1 objectParts.1 headScope)
      (tailSound canonicalParts.2 objectParts.2 tailScope)
    have leftEndpoint :
        WellSorted.AvailableOpenElements.cons
            (head.normalizedAvailable canonicalParts.1 objectParts.1 headScope)
            (tail.normalizedAvailable canonicalParts.2 objectParts.2 tailScope) =
          (CostSemanticElementTrees.cons head tail).normalizedAvailable
            canonical objects scope := by
      apply WellSorted.AvailableOpenElements.ext
      simp [CostSemanticElementTrees.normalizedAvailable_patterns,
        CostSemanticElementTrees.normalize]
    have rightEndpoint :
        WellSorted.AvailableOpenElements.cons
            (head.originalAvailable canonicalParts.1 objectParts.1 headScope)
            (tail.originalAvailable canonicalParts.2 objectParts.2 tailScope) =
          (CostSemanticElementTrees.cons head tail).originalAvailable
            canonical objects scope := by
      apply WellSorted.AvailableOpenElements.ext
      rfl
    rw [leftEndpoint, rightEndpoint] at combined
    exact combined
  · intros
    rename_i color
    intro name type lookup inner
    simp [CostSemanticBoundaryTrees.normalize]
    exact Relation.EqvGen.refl _
  · intros
    rename_i color occurrence occurrences boundary content tail value values head
      children headSound childrenSound
    let normalizedHead := head.normalize
    let normalizedValue := normalizedHead.toBoundaryValue value rfl
    have headSplitStep :=
      headSound.1 value.2.1.2.1 value.2.1.2.2.1 value.2.2
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
          boundary.boundary.targetSupport boundary.boundary.targetType).r
          normalizedValue value := by
      have leftEndpoint :
          ((head.normalizedAvailable value.2.1.2.1 value.2.1.2.2.1 value.2.2
            ).toReflectiveOpenPattern).reindexBound
              (List.append_nil boundary.boundary.targetSupport) =
            normalizedValue := by
        apply Subtype.ext
        simp only [ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
          WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
          CostSemanticTree.normalizedAvailable_pattern]
        change head.normalize.result.pattern = normalizedValue.1
        rfl
      have rightEndpoint :
          ((head.originalAvailable value.2.1.2.1 value.2.1.2.2.1 value.2.2
            ).toReflectiveOpenPattern).reindexBound
              (List.append_nil boundary.boundary.targetSupport) = value := by
        apply Subtype.ext
        simp only [ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
          WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
          CostSemanticTree.originalAvailable_pattern]
      rw [leftEndpoint, rightEndpoint] at headOpenTransported
      exact headOpenTransported
    have headEquivalent : ∀ inner : List TypeExpr,
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
          source.costWholeReflectionProfile defaultBasePremises
          source.costWholeLanguage targetFree
          (inner ++ boundary.boundary.targetSupport)
          boundary.boundary.targetType).r
          (normalizedValue.weakenRoot inner) (value.weakenRoot inner) := by
      intro inner
      exact laws.weakeningStable headOpen inner
    unfold CostSemanticBoundaryTrees.NormalizationSound
    rw [CostSemanticBoundaryTrees.normalize.eq_2]
    intro name type lookup inner
    exact
      (TypedCostRegionBoundaryTable.Values.supportedOpenAssignment_cons_fiberEquivalent_of_values
        (content := content) (head.normalize.toBoundaryValue value rfl) value
          children.normalize.1 values (by
            simpa only [normalizedValue, normalizedHead] using headEquivalent)
          childrenSound) lookup inner

namespace CostSemanticOpenElaboration

/-- In-place semantic normalization erases to the admitted reflective open
equation setoid over the authored Cost language.  The retained frame and
boundary evidence contribute no second semantic authority. -/
theorem normalizeOpen_typed_openEquationSetoid
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort)
    (tree : CostSemanticOpenElaboration source term) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound
        (.base targetSort.1)).r (normalizeOpen term tree) term := by
  have split := (tree.normalizationSound laws).1 term.2.1.2.1
    term.2.1.2.2.1 term.2.2
  have openRaw :=
    WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
      split
  have transported :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
      (List.append_nil targetBound) openRaw
  have leftEndpoint :
      ((tree.normalizedAvailable term.2.1.2.1 term.2.1.2.2.1 term.2.2
        ).toReflectiveOpenPattern.reindexBound (List.append_nil targetBound)) =
        normalizeOpen term tree := by
    apply Subtype.ext
    simp [normalizeOpen_pattern,
      CostSemanticTree.normalizedAvailable_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  have rightEndpoint :
      ((tree.originalAvailable term.2.1.2.1 term.2.1.2.2.1 term.2.2
        ).toReflectiveOpenPattern.reindexBound
          (List.append_nil targetBound)) = term := by
    apply Subtype.ext
    simp [CostSemanticTree.originalAvailable_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  rw [leftEndpoint, rightEndpoint] at transported
  exact transported

/-- One proof-relevant semantic edge projects to an admitted reflective
equation path.  Exact equality of retained normal forms supplies the common
middle vertex. -/
theorem Step.erasesToAuthored
    {source : CIGSLT} (laws : CostTypedUnaryNormalizationLaws source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostSemanticElabTerm source targetFree targetBound targetSort}
    (step : Step source targetFree targetBound targetSort left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound
        (.base targetSort.1)).r left.1 right.1 := by
  have leftPath := normalizeOpen_typed_openEquationSetoid laws left.1 left.2
  have rightPath := normalizeOpen_typed_openEquationSetoid laws right.1 right.2
  have normalizedTermEq : normalizeOpen left.1 left.2 =
      normalizeOpen right.1 right.2 :=
    congrArg Sigma.fst (normalizeTerm_eq_of_step step)
  have commonToRight :
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r (normalizeOpen left.1 left.2) right.1 := by
    rw [normalizedTermEq]
    exact rightPath
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ leftPath) commonToRight

end CostSemanticOpenElaboration

namespace CIGSLT

/-- The retained semantic Cost tree as a proof-relevant carrier over the one
generated authored Cost presentation. -/
def costSemanticOpenElaborationCarrier (source : CIGSLT)
    (canonicalPathSafe : CostStaticCanonicalPathSafe source) :
    ReflectiveOpenElaborationCarrier source.costIGSLT
      source.costWholeAdmittedReflection where
  Carrier := CostSemanticElabTerm source
  erase := CostSemanticOpenElaboration.erase
  compile := CostSemanticOpenElaboration.compileTerm source canonicalPathSafe
  erase_compile := CostSemanticOpenElaboration.erase_compileTerm source
    canonicalPathSafe

/-- Stable-frame semantic edges form an authored path lift. -/
def costSemanticPathLift (source : CIGSLT)
    (laws : CostTypedUnaryNormalizationLaws source) :
    ReflectiveOpenElaborationPathLift
      (source.costSemanticOpenElaborationCarrier laws.canonicalPathSafe) where
  step := fun free bound sort =>
    CostSemanticOpenElaboration.Step source free bound sort
  erasesToReflectivePath := fun step =>
    CostSemanticOpenElaboration.Step.erasesToAuthored laws step

/-- The exact proof-relevant Cost relation with its mandatory erasure into the
admitted reflective equation theory over the authored Cost `IGSLT`. -/
def costSemanticSemantics (source : CIGSLT)
    (laws : CostTypedUnaryNormalizationLaws source) :
    ReflectiveOpenElaborationSemantics
      (source.costSemanticOpenElaborationCarrier laws.canonicalPathSafe) :=
  ReflectiveOpenElaborationSemantics.ofPathLift
    (source.costSemanticPathLift laws)

/-- The retained child-first normalizer is an exact section of semantic Cost
equivalence on every typed open fibre. -/
def costSemanticCanonicalSection (source : CIGSLT)
    (laws : CostTypedUnaryNormalizationLaws source) :
    ReflectiveOpenElaborationSemantics.ComputableSection
      (source.costSemanticSemantics laws) :=
  ReflectiveOpenElaborationSemantics.ComputableSection.ofPathInvariant
    (source.costSemanticPathLift laws)
    (fun term => CostSemanticOpenElaboration.normalizeTerm term)
    (fun term => CostSemanticOpenElaboration.normalizeTerm_related term)
    (fun step => CostSemanticOpenElaboration.normalizeTerm_eq_of_step step)

/-- Cost with retained frames, colour, declaration choices, and finite boundary
values is an exact reflective elaborated open theory over the generated Cost
`IGSLT`. -/
def costSemanticElaboratedOpenTheory (source : CIGSLT)
    (laws : CostTypedUnaryNormalizationLaws source) :
    ReflectiveElaboratedOpenTheory where
  theory := source.costIGSLT
  reflection := source.costWholeAdmittedReflection
  carrier := source.costSemanticOpenElaborationCarrier laws.canonicalPathSafe
  semantics := source.costSemanticSemantics laws
  canonical := source.costSemanticCanonicalSection laws

end CIGSLT

end Mettapedia.GSLT.LanguageDef
