import Mettapedia.GSLT.LanguageDef.CostSemanticSection

/-!
# Intrinsic typing and static-frame soundness for semantic Cost regions

The intrinsic tree indices reconstruct typed compact terms without declaration
search.  Static-frame normalization then composes authored source
canonicalization with pointwise finite-boundary substitution.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory

mutual
  /-- Intrinsic typing of the exact compact pattern indexed by a semantic
  tree.  No checker or declaration search is rerun. -/
  def CostSemanticTree.originalTyped {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostSemanticTree source targetFree available outer pattern type) :
      WellSorted.HasType source.costWholeLanguage targetFree
        (available ++ outer) pattern type :=
    match tree with
    | .bvar lookup => .bvar lookup
    | .fvar lookup => .fvar lookup
    | @CostSemanticTree.static _ _ color outer frame state values children =>
        state.actAvailableWithOuter values outer |>.typed
    | .neutralApplicationOrdinary membership notBareCollection _ _ _ _ children =>
        .constructor membership notBareCollection children.originalTyped
    | @CostSemanticTree.neutralApplicationQuote _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        quoted children =>
        .constructor membership notBareCollection (by
          simpa only [List.nil_append, List.append_assoc] using
            children.originalTyped)
    | .lambda bodyTree => .lambda bodyTree.originalTyped
    | @CostSemanticTree.multiLambda _ _ available outer arity binders body domain
        codomain bodyTree =>
        .multiLambda (by
          simpa only [List.append_assoc] using bodyTree.originalTyped)
    | .subst bodyTree replacementTree =>
        .subst bodyTree.originalTyped replacementTree.originalTyped
    | .collection children => .collection children.originalTyped
  termination_by tree.weight
  decreasing_by
    all_goals simp [CostSemanticTree.weight]
    all_goals omega

  /-- Intrinsic typing of a semantic constructor-argument spine. -/
  def CostSemanticArgumentTrees.originalTyped {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostSemanticArgumentTrees source targetFree available outer
        arguments parameters) :
      WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
        (available ++ outer) arguments parameters :=
    match trees with
    | .nil => .nil
    | .cons representation parameterType head tail =>
        .cons representation parameterType head.originalTyped tail.originalTyped
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostSemanticArgumentTrees.weight]
    all_goals omega

  /-- Intrinsic typing of a semantic collection-element spine. -/
  def CostSemanticElementTrees.originalTyped {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostSemanticElementTrees source targetFree available outer
        elements elementType) :
      WellSorted.ElementsHaveType source.costWholeLanguage targetFree
        (available ++ outer) elements elementType :=
    match trees with
    | .nil _ _ _ => .nil _ _
    | .cons head tail => .cons head.originalTyped tail.originalTyped
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostSemanticElementTrees.weight]
    all_goals omega
end

/-- Package the exact semantic-tree index in the split typed carrier. -/
def CostSemanticTree.originalAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer type where
  pattern := pattern
  typed := tree.originalTyped
  canonicalBinderMetadata := canonical
  objectPattern := object
  reflectiveScope := scope

/-- Package the retained normalized tree in the same split typed carrier. -/
def CostSemanticTree.normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer type :=
  tree.normalize.result.toAvailableOpenPattern canonical object scope

@[simp]
theorem CostSemanticTree.originalAvailable_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.originalAvailable canonical object scope).pattern = pattern :=
  rfl

@[simp]
theorem CostSemanticTree.normalizedAvailable_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      available.length pattern) :
    (tree.normalizedAvailable canonical object scope).pattern =
      tree.normalize.result.pattern :=
  rfl

/-- Package a semantic tree as one authored constructor argument before
normalization. -/
def CostSemanticTree.originalArgument {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
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
    WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameter type where
  term := tree.originalAvailable canonical object scope
  representation := representation
  parameterType := parameterType

/-- Package the normalized semantic tree in the same authored parameter
fibre. -/
def CostSemanticTree.normalizedArgument {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
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
    WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameter type where
  term := tree.normalizedAvailable canonical object scope
  representation :=
    tree.normalize.result.matchesParameterRepresentation parameter representation
  parameterType := parameterType

namespace CostSemanticArgumentTrees

/-- Package an authored semantic argument spine before normalization. -/
def originalAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameters :=
  WellSorted.AvailableOpenArguments.ofCertificates trees.originalTyped canonical
    objects scope

/-- Package the normalized semantic argument spine in the same fibre. -/
def normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    WellSorted.AvailableOpenArguments source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer parameters :=
  WellSorted.AvailableOpenArguments.ofCertificates trees.normalize.result.typed
    (trees.normalize.result.canonicalBinderMetadata canonical)
    (trees.normalize.result.objectPatterns objects)
    (fun presentation membership =>
      trees.normalize.result.reflectiveScope presentation membership
        (Nat.le_refl available.length) (scope presentation membership))

@[simp]
theorem originalAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    (trees.originalAvailable canonical objects scope).patterns = arguments :=
  rfl

@[simp]
theorem normalizedAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true)
    (objects : WellSorted.isObjectPatternList arguments = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        arguments = true) :
    (trees.normalizedAvailable canonical objects scope).patterns =
      trees.normalize.result.patterns :=
  rfl

end CostSemanticArgumentTrees

namespace CostSemanticElementTrees

/-- Package a homogeneous semantic element spine before normalization. -/
def originalAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer elementType :=
  WellSorted.AvailableOpenElements.ofCertificates trees.originalTyped canonical
    objects scope

/-- Package the normalized semantic element spine in the same fibre. -/
def normalizedAvailable {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    WellSorted.AvailableOpenElements source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available outer elementType :=
  WellSorted.AvailableOpenElements.ofCertificates trees.normalize.result.typed
    (trees.normalize.result.canonicalBinderMetadata canonical)
    (trees.normalize.result.objectPatterns objects)
    (fun presentation membership =>
      trees.normalize.result.reflectiveScope presentation membership
        (Nat.le_refl available.length) (scope presentation membership))

@[simp]
theorem originalAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    (trees.originalAvailable canonical objects scope).patterns = elements :=
  rfl

@[simp]
theorem normalizedAvailable_patterns {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objects : WellSorted.isObjectPatternList elements = true)
    (scope : ∀ presentation ∈ source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        elements = true) :
    (trees.normalizedAvailable canonical objects scope).patterns =
      trees.normalize.result.patterns :=
  rfl

end CostSemanticElementTrees

namespace CostStaticFrameState

/-- Normalize the current authored source representative and independently
normalize its exact finite boundary assignment.  The two changes compose in
the same split target fibre. -/
theorem normalize_actAvailable_equationSetoid
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (stable : CostStaticMappedGeneratorFiberAction source)
    (normalizedValues values : TypedCostRegionBoundaryTable.Values source color
      targetFree frame.boundaryTable)
    (valuesEquivalent :
      (normalizedValues.supportedOpenAssignment frame.boundaryTable
        ).FiberEquivalent
      (values.supportedOpenAssignment frame.boundaryTable)) :
    (WellSorted.AvailableOpenPattern.equationSetoid
      source.costWholeLanguage targetFree frame.targetBound []
        (.base (color.mapLangSort source frame.sourceSort).1)).r
      (state.normalize.actAvailable normalizedValues)
      (state.actAvailable values) := by
  let normalizedAssignment :=
    normalizedValues.supportedOpenAssignment frame.boundaryTable
  let currentAssignment := values.supportedOpenAssignment frame.boundaryTable
  let mappedAvailableRaw :=
    state.current.mappedThickenedAvailable frame.thinning
  let mappedAvailable := mappedAvailableRaw.castFree frame.transport.freeContext
  have mappedAvailableSafe :
      mappedAvailable.typed.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile
        frame.boundaryTable.restorationSupport frame.targetBound :=
    mappedAvailableRaw.castFree_supportSafe frame.transport.freeContext
      (state.current.mappedThickenedAvailable_supportSafe frame.thinning)
  have patternStep := CostStaticRegionNode.CostStaticSourceTerm.equationSetoid_actAvailable
    stable frame.thinning normalizedAssignment frame.transport.freeContext
      frame.transport.reflectiveSupport state.canonicalPath
  have assignmentStep := mappedAvailable.equationSetoid_substitute_pointwise
    source.costWholeLanguage_validate
      source.costWholeReflectionProfile_validate mappedAvailableSafe
      normalizedAssignment currentAssignment valuesEquivalent
  have leftEndpoint :
      state.current.normalize.actAvailable frame.thinning normalizedAssignment
          frame.transport.freeContext frame.transport.reflectiveSupport =
        state.normalize.actAvailable normalizedValues := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      CostStaticFrameState.actAvailable_pattern]
    rfl
  have middleEndpoint :
      state.current.actAvailable frame.thinning normalizedAssignment
          frame.transport.freeContext frame.transport.reflectiveSupport =
        mappedAvailable.substitute normalizedAssignment mappedAvailableSafe := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      WellSorted.AvailableOpenPattern.substitute_pattern,
      WellSorted.AvailableOpenPattern.castFree_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.mappedThickenedAvailable_pattern]
    rfl
  have rightEndpoint :
      mappedAvailable.substitute currentAssignment mappedAvailableSafe =
        state.actAvailable values := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [WellSorted.AvailableOpenPattern.substitute_pattern,
      WellSorted.AvailableOpenPattern.castFree_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.mappedThickenedAvailable_pattern,
      CostStaticFrameState.actAvailable_pattern]
    rfl
  rw [leftEndpoint, middleEndpoint] at patternStep
  rw [rightEndpoint] at assignmentStep
  exact Relation.EqvGen.trans _ _ _ patternStep assignmentStep

end CostStaticFrameState

end Mettapedia.GSLT.LanguageDef
