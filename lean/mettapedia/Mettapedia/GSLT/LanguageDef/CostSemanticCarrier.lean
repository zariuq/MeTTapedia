import Mettapedia.GSLT.LanguageDef.CostElaborationTransportSound

/-!
# Stable proof-relevant semantic Cost regions

This module retains static region frames, current authored representatives, and
finite boundary values while normalizing the represented Cost term in place.
Compact syntax remains the checked execution boundary; semantic choices live in
the indexed tree and are never recovered by reparsing an erasure.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open CostStaticRegionNode

namespace CostStaticRegionNode.CostStaticSourceTerm

def normalize {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support sourceBound
      targetBound sort) :
    CostStaticSourceTerm source color free support sourceBound targetBound sort
    where
  term := source.openCanonical.normalize term.term
  supported := source.openCanonicalPreservesWrappedConstructorTyping
    term.term term.supported
  safe := source.openCanonical.preservesReflectiveSupport term.term support
    targetBound (mapTypeExpr (color.symbols source)) term.safe

@[simp]
theorem normalize_term {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support sourceBound
      targetBound sort) :
    term.normalize.term = source.openCanonical.normalize term.term :=
  rfl

theorem normalize_idempotent {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support sourceBound
      targetBound sort) :
    term.normalize.normalize = term.normalize := by
  cases term with
  | mk term supported safe =>
      have identity :=
        ComputableReflectiveFiberSection.normalize_idempotent
          source.openCanonical.toComputableReflectiveFiberSection term
      unfold CostStaticSourceTerm.normalize
      congr

theorem normalize_eq_of_equationSetoid
    {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    {left right : CostStaticSourceTerm source color free support sourceBound
      targetBound sort}
    (equivalent : (CostStaticSourceTerm.equationSetoid source color free support
      sourceBound targetBound sort).r left right) :
    left.normalize = right.normalize := by
  have erased :
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        source.reflection.1 defaultBasePremises
        source.theory.presentation.presentation.language free sourceBound
          (.base sort.1)).r left.term right.term := by
    induction equivalent with
    | rel left right generator =>
        exact Relation.EqvGen.rel _ _ generator
    | refl term => exact Relation.EqvGen.refl _
    | symm left right relation inductionHypothesis =>
        exact Relation.EqvGen.symm _ _ inductionHypothesis
    | trans left middle right first second firstIH secondIH =>
        exact Relation.EqvGen.trans _ _ _ firstIH secondIH
  have identity := source.openCanonical.complete erased
  cases left with
  | mk leftTerm leftSupported leftSafe =>
      cases right with
      | mk rightTerm rightSupported rightSafe =>
          unfold CostStaticSourceTerm.normalize
          congr

end CostStaticSourceTerm
end CostStaticRegionNode

/-- A stable proof-relevant region frame together with its current authored
source representative.  Boundary values are supplied independently. -/
structure CostStaticFrameState {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (frame : CostStaticRegionNode source color targetFree) where
  current : CostStaticSourceTerm source color
    frame.boundaryTable.sourceFreeContext frame.boundaryTable.sourceSupport
    frame.sourceBound frame.targetBound frame.sourceSort
  canonicalPath :
    (CostStaticSourceTerm.equationSetoid source color
      frame.boundaryTable.sourceFreeContext frame.boundaryTable.sourceSupport
      frame.sourceBound frame.targetBound frame.sourceSort).r
      current.normalize current

namespace CostStaticFrameState

def original {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (frame : CostStaticRegionNode source color targetFree)
    (canonicalPath :
      (CostStaticSourceTerm.equationSetoid source color
        frame.boundaryTable.sourceFreeContext frame.boundaryTable.sourceSupport
        frame.sourceBound frame.targetBound frame.sourceSort).r
        frame.normalizedSourceActionTerm frame.sourceActionTerm) :
    CostStaticFrameState frame where
  current := frame.sourceActionTerm
  canonicalPath := by
    simpa [CostStaticSourceTerm.normalize,
      CostStaticRegionNode.sourceActionTerm,
      CostStaticRegionNode.normalizedSourceActionTerm] using canonicalPath

def normalize {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame) : CostStaticFrameState frame where
  current := state.current.normalize
  canonicalPath := by
    rw [CostStaticSourceTerm.normalize_idempotent]
    exact Relation.EqvGen.refl _

@[simp]
theorem normalize_current {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame) :
    state.normalize.current = state.current.normalize :=
  rfl

theorem normalize_idempotent {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame) :
    state.normalize.normalize = state.normalize := by
  cases state with
  | mk current canonicalPath =>
      have identity := current.normalize_idempotent
      unfold CostStaticFrameState.normalize
      congr

def actAvailable {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree frame.targetBound []
      (.base (color.mapLangSort source frame.sourceSort).1) :=
  state.current.actAvailable frame.thinning
    (values.supportedOpenAssignment frame.boundaryTable)
    frame.transport.freeContext frame.transport.reflectiveSupport

@[simp]
theorem actAvailable_pattern {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable) :
    (state.actAvailable values).pattern =
      state.current.act frame.thinning
        (values.supportedOpenAssignment frame.boundaryTable) := by
  exact CostStaticSourceTerm.actAvailable_pattern state.current frame.thinning
    (values.supportedOpenAssignment frame.boundaryTable)
    frame.transport.freeContext frame.transport.reflectiveSupport

/-- Extend the sealed outer binder suffix without changing the current
static-frame representative. -/
def actAvailableWithOuter {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable)
    (outer : List TypeExpr) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree frame.targetBound outer
      (.base (color.mapLangSort source frame.sourceSort).1) := by
  let current := state.actAvailable values
  exact {
    pattern := current.pattern
    typed := by simpa only [List.append_nil, List.append_assoc] using
      current.typed.extendOuter outer
    canonicalBinderMetadata := current.canonicalBinderMetadata
    objectPattern := current.objectPattern
    reflectiveScope := current.reflectiveScope }

@[simp]
theorem actAvailableWithOuter_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      frame.boundaryTable)
    (outer : List TypeExpr) :
    (state.actAvailableWithOuter values outer).pattern =
      (state.actAvailable values).pattern :=
  rfl

theorem original_actAvailable_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (frame : CostStaticRegionNode source color targetFree)
    (canonicalPath :
      (CostStaticSourceTerm.equationSetoid source color
        frame.boundaryTable.sourceFreeContext frame.boundaryTable.sourceSupport
        frame.sourceBound frame.targetBound frame.sourceSort).r
        frame.normalizedSourceActionTerm frame.sourceActionTerm) :
    ((original frame canonicalPath).actAvailable
      (TypedCostRegionBoundaryTable.Values.original frame.boundaryTable)
      ).pattern = frame.term.1 := by
  rw [actAvailable_pattern]
  change ReflectiveContextSupport.substitute source.costWholeReflectionProfile
      frame.boundaryTable.restorationSupport
      ((TypedCostRegionBoundaryTable.Values.original frame.boundaryTable
        ).assignment frame.boundaryTable)
      frame.targetBound
      (frame.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols source) frame.skeleton.1)) = frame.term.1
  rw [TypedCostRegionBoundaryTable.Values.original_assignment]
  exact frame.restore_mappedThickenedSkeleton_eq_term

end CostStaticFrameState

/-! A semantic region tree retains a stable static frame while allowing the
current source representative and the finite boundary values to evolve. -/

mutual
  inductive CostSemanticTree (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      List TypeExpr → List TypeExpr → Pattern → TypeExpr → Type where
    | bvar {available outer : List TypeExpr} {index : Nat} {type : TypeExpr}
        (lookup : (available ++ outer)[index]? = some type) :
        CostSemanticTree source targetFree available outer (.bvar index) type
    | fvar {available outer : List TypeExpr} {name : String} {type : TypeExpr}
        (lookup : targetFree name = some type) :
        CostSemanticTree source targetFree available outer (.fvar name) type
    | static {color : CostStaticColor} {outer : List TypeExpr}
        (frame : CostStaticRegionNode source color targetFree)
        (state : CostStaticFrameState frame)
        {values : TypedCostRegionBoundaryTable.Values source color targetFree
          frame.boundaryTable}
        (children : CostSemanticBoundaryTrees source targetFree color
          frame.boundaryTable values) :
        CostSemanticTree source targetFree frame.targetBound outer
          (state.actAvailableWithOuter values outer).pattern
          (.base (color.mapLangSort source frame.sourceSort).1)
    | neutralApplicationOrdinary
        {available outer : List TypeExpr} {rule : GrammarRule}
        {arguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ WellSorted.UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (ordinary : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeReflectionProfile rule.label = false)
        (children : CostSemanticArgumentTrees source targetFree available outer
          arguments rule.params) :
        CostSemanticTree source targetFree available outer
          (.apply rule.label arguments) (.base rule.category)
    | neutralApplicationQuote
        {available outer : List TypeExpr} {rule : GrammarRule}
        {arguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ WellSorted.UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (quoted : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeReflectionProfile rule.label = true)
        (children : CostSemanticArgumentTrees source targetFree []
          (available ++ outer) arguments rule.params) :
        CostSemanticTree source targetFree available outer
          (.apply rule.label arguments) (.base rule.category)
    | lambda
        {available outer : List TypeExpr}
        {binder : Option String} {body : Pattern}
        {domain codomain : TypeExpr}
        (bodyTree : CostSemanticTree source targetFree
          (domain :: available) outer body codomain) :
        CostSemanticTree source targetFree available outer (.lambda binder body)
          (.arrow domain codomain)
    | multiLambda
        {available outer : List TypeExpr}
        {arity : Nat} {binders : List String}
        {body : Pattern} {domain codomain : TypeExpr}
        (bodyTree : CostSemanticTree source targetFree
          (List.replicate arity domain ++ available) outer body codomain) :
        CostSemanticTree source targetFree available outer
          (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain)
    | subst
        {available outer : List TypeExpr} {body replacement : Pattern}
        {domain codomain : TypeExpr}
        (bodyTree : CostSemanticTree source targetFree
          (domain :: available) outer body codomain)
        (replacementTree : CostSemanticTree source targetFree
          available outer replacement domain) :
        CostSemanticTree source targetFree available outer
          (.subst body replacement) codomain
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {elements : List Pattern} {rest : Option String}
        {elementType : TypeExpr}
        (children : CostSemanticElementTrees source targetFree available outer
          elements elementType) :
        CostSemanticTree source targetFree available outer
          (.collection collectionType elements rest)
          (.collection collectionType elementType)

  inductive CostSemanticArgumentTrees (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      List TypeExpr → List TypeExpr → List Pattern → List TermParam → Type where
    | nil {available outer : List TypeExpr} :
        CostSemanticArgumentTrees source targetFree available outer [] []
    | cons
        {argument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (representation : WellSorted.MatchesParameterRepresentation parameter
          argument)
        (parameterType : WellSorted.parameterType? parameter = some expected)
        (head : CostSemanticTree source targetFree available outer argument
          expected)
        (tail : CostSemanticArgumentTrees source targetFree available outer
          arguments parameters) :
        CostSemanticArgumentTrees source targetFree available outer
          (argument :: arguments) (parameter :: parameters)

  inductive CostSemanticElementTrees (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      List TypeExpr → List TypeExpr → List Pattern → TypeExpr → Type where
    | nil (available outer : List TypeExpr) (elementType : TypeExpr) :
        CostSemanticElementTrees source targetFree available outer []
          elementType
    | cons {element : Pattern} {elements : List Pattern}
        {elementType : TypeExpr}
        (head : CostSemanticTree source targetFree available outer element
          elementType)
        (tail : CostSemanticElementTrees source targetFree available outer
          elements elementType) :
        CostSemanticElementTrees source targetFree available outer
          (element :: elements) elementType

  inductive CostSemanticBoundaryTrees (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      (color : CostStaticColor) → {occurrences : List CostRegionOccurrence} →
      (table : TypedCostRegionBoundaryTable source color targetFree
        occurrences) →
      TypedCostRegionBoundaryTable.Values source color targetFree table →
      Type where
    | nil {color : CostStaticColor} :
        CostSemanticBoundaryTrees source targetFree color .nil .nil
    | cons {color : CostStaticColor} {occurrence : CostRegionOccurrence}
        {occurrences : List CostRegionOccurrence}
        {boundary : TypedCostRegionBoundary source color targetFree}
        {content : boundary.boundary.content = occurrence.content}
        {tail : TypedCostRegionBoundaryTable source color targetFree occurrences}
        {value : ReflectiveWellSorted.OpenPattern
          source.costWholeReflectionProfile source.costWholeLanguage targetFree
            boundary.boundary.targetSupport boundary.boundary.targetType}
        {values : TypedCostRegionBoundaryTable.Values source color targetFree
          tail}
        (head : CostSemanticTree source targetFree
          boundary.boundary.targetSupport [] value.1
          boundary.boundary.targetType)
        (children : CostSemanticBoundaryTrees source targetFree color tail
          values) :
        CostSemanticBoundaryTrees source targetFree color
          (.cons boundary content tail) (.cons value values)
end

/-- Change only the raw-pattern index of a semantic tree. -/
def CostSemanticTree.reindexPattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {first second : Pattern}
    {type : TypeExpr}
    (patternEq : first = second)
    (tree : CostSemanticTree source targetFree available outer first type) :
    CostSemanticTree source targetFree available outer second type := by
  cases patternEq
  exact tree

@[simp]
theorem CostSemanticTree.reindexPattern_rfl
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    tree.reindexPattern rfl = tree :=
  rfl

mutual
  def CostSemanticTree.weight {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr} :
      CostSemanticTree source targetFree available outer pattern type → Nat
    | .bvar _ | .fvar _ => 1
    | .static _ _ children => children.weight + 1
    | .neutralApplicationOrdinary _ _ _ _ _ _ children =>
        children.weight + 1
    | .neutralApplicationQuote _ _ _ _ _ _ children => children.weight + 1
    | .lambda body => body.weight + 1
    | .multiLambda body => body.weight + 1
    | .subst body replacement => body.weight + replacement.weight + 1
    | .collection children => children.weight + 1

  def CostSemanticArgumentTrees.weight {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam} :
      CostSemanticArgumentTrees source targetFree available outer arguments
        parameters → Nat
    | .nil => 1
    | .cons _ _ head tail => head.weight + tail.weight + 1

  def CostSemanticElementTrees.weight {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr} :
      CostSemanticElementTrees source targetFree available outer elements
        elementType → Nat
    | .nil _ _ _ => 1
    | .cons head tail => head.weight + tail.weight + 1

  def CostSemanticBoundaryTrees.weight {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree
        table} :
      CostSemanticBoundaryTrees source targetFree color table values → Nat
    | .nil => 1
    | .cons head children => head.weight + children.weight + 1
end

/-- A semantic normalization result retains its complete framed tree rather
than recompiling the compact pattern selected by that tree. -/
structure NormalizedCostSemanticTree (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext)
    (available outer : List TypeExpr) (original : Pattern) (type : TypeExpr)
    where
  result : NormalizedCostRegionPattern source targetFree available outer
    original type
  tree : CostSemanticTree source targetFree available outer result.pattern type

/-- Repackage a normalized boundary child in the exact open fiber of its
unchanged boundary.  The source value supplies only the object and reflective
side conditions; the normalized tree supplies the new typed pattern. -/
def NormalizedCostSemanticTree.toBoundaryValue
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available : List TypeExpr} {original : Pattern} {type : TypeExpr}
    (normalized : NormalizedCostSemanticTree source targetFree available []
      original type)
    (value : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available type)
    (original_eq : original = value.1) :
    ReflectiveWellSorted.OpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree available type := by
  subst original
  exact ⟨normalized.result.pattern,
    ⟨⟨by simpa only [List.append_nil] using normalized.result.typed,
      normalized.result.canonicalBinderMetadata value.2.1.2.1,
      normalized.result.objectPattern value.2.1.2.2.1,
      by simpa [WellSorted.ScopeSafeAt] using
        normalized.result.typed.isWellScopedAt⟩,
      by
        intro presentation membership
        exact normalized.result.reflectiveScope presentation membership
          (Nat.le_refl available.length)
          (value.2.2 presentation membership)⟩⟩

/-- A normalized argument spine with its proof-relevant semantic children. -/
structure NormalizedCostSemanticArguments (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext)
    (available outer : List TypeExpr) (original : List Pattern)
    (parameters : List TermParam) where
  result : NormalizedCostRegionArguments source targetFree available outer
    original parameters
  trees : CostSemanticArgumentTrees source targetFree available outer
    result.patterns parameters

/-- A normalized collection spine with its proof-relevant semantic children. -/
structure NormalizedCostSemanticElements (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext)
    (available outer : List TypeExpr) (original : List Pattern)
    (elementType : TypeExpr) where
  result : NormalizedCostRegionElements source targetFree available outer
    original elementType
  trees : CostSemanticElementTrees source targetFree available outer
    result.patterns elementType

/-- Normalized current values and the semantic child forest that produces
them, aligned to one unchanged finite boundary table. -/
abbrev NormalizedCostSemanticBoundaries (source : CIGSLT)
    (targetFree : WellSorted.FreeTypeContext) (color : CostStaticColor)
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences) :=
  Σ values : TypedCostRegionBoundaryTable.Values source color targetFree table,
    CostSemanticBoundaryTrees source targetFree color table values

mutual
  /-- Normalize a semantic tree in place: static frame identity is retained,
  children are normalized first, and only the current authored source
  representative changes. -/
  def CostSemanticTree.normalize {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostSemanticTree source targetFree available outer pattern type) :
      NormalizedCostSemanticTree source targetFree available outer pattern
        type :=
    match tree with
    | @CostSemanticTree.bvar _ _ available outer index type lookup =>
        { result := {
            pattern := .bvar index
            typed := .bvar lookup
            canonicalBinderMetadata := by simp
            objectPattern := by simp [WellSorted.isObjectPattern]
            reflectiveScope := by
              intro presentation membership depth availableWithin safe
              exact safe
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .bvar lookup }
    | @CostSemanticTree.fvar _ _ available outer name type lookup =>
        { result := {
            pattern := .fvar name
            typed := .fvar lookup
            canonicalBinderMetadata := by simp
            objectPattern := by simp [WellSorted.isObjectPattern]
            reflectiveScope := by
              intro presentation membership depth availableWithin safe
              exact safe
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .fvar lookup }
    | @CostSemanticTree.static _ _ color outer frame state values children =>
        let normalizedChildren := children.normalize
        let normalizedState := state.normalize
        let normalized := normalizedState.actAvailableWithOuter
          normalizedChildren.1 outer
        { result := {
            pattern := normalized.pattern
            typed := normalized.typed
            canonicalBinderMetadata := fun _ =>
              normalized.canonicalBinderMetadata
            objectPattern := fun _ => normalized.objectPattern
            reflectiveScope := by
              intro presentation membership depth availableWithin safe
              exact binderSafeAt_mono presentation.quoteConstructor
                (normalized.reflectiveScope presentation membership)
                availableWithin
            matchesParameterRepresentation := by
              intro parameter representation
              exact matchesParameterRepresentation_of_base_typed parameter
                (state.actAvailableWithOuter values outer).typed
                representation }
          tree := .static frame normalizedState normalizedChildren.2 }
    | @CostSemanticTree.neutralApplicationOrdinary _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        ordinary children =>
        let normalized := children.normalize
        { result := {
            pattern := .apply rule.label normalized.result.patterns
            typed := .constructor membership notBareCollection
              normalized.result.typed
            canonicalBinderMetadata := by
              intro canonical
              exact normalized.result.canonicalBinderMetadata (by
                simpa [Pattern.hasCanonicalBinderMetadata] using canonical)
            objectPattern := by
              intro objects
              exact normalized.result.objectPatterns (by
                simpa [WellSorted.isObjectPattern] using objects)
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
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
              have inputList : binderSafeListAt presentation.quoteConstructor
                  depth arguments = true :=
                binderSafeListAt_of_binderSafeAt_apply_of_ne
                  presentation.quoteConstructor rule.label depth arguments
                  notThisQuote safe
              have outputList := normalized.result.reflectiveScope presentation
                presentationMembership availableWithin inputList
              exact binderSafeAt_apply_of_spines
                presentation.quoteConstructor rule.label depth
                normalized.result.patterns
                (fun equality => (notThisQuote equality).elim)
                outputList
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .neutralApplicationOrdinary membership notBareCollection
            constructor materializes neutral ordinary normalized.trees }
    | @CostSemanticTree.neutralApplicationQuote _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        quoted children =>
        let normalized := children.normalize
        { result := {
            pattern := .apply rule.label normalized.result.patterns
            typed := .constructor membership notBareCollection (by
              simpa only [List.nil_append, List.append_assoc] using
                normalized.result.typed)
            canonicalBinderMetadata := by
              intro canonical
              exact normalized.result.canonicalBinderMetadata (by
                simpa [Pattern.hasCanonicalBinderMetadata] using canonical)
            objectPattern := by
              intro objects
              exact normalized.result.objectPatterns (by
                simpa [WellSorted.isObjectPattern] using objects)
            reflectiveScope := by
              intro presentation presentationMembership depth _ safe
              exact binderSafeAt_apply_of_length_eq_of_list_preserving
                presentation.quoteConstructor rule.label depth
                normalized.result.length_eq
                (fun localDepth inputList =>
                  normalized.result.reflectiveScope presentation
                    presentationMembership (Nat.zero_le localDepth) inputList)
                safe
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .neutralApplicationQuote membership notBareCollection
            constructor materializes neutral quoted normalized.trees }
    | @CostSemanticTree.lambda _ _ available outer binder body domain codomain
        bodyTree =>
        let normalized := bodyTree.normalize
        { result := {
            pattern := .lambda binder normalized.result.pattern
            typed := .lambda normalized.result.typed
            canonicalBinderMetadata := by
              intro canonical
              simp only [Pattern.hasCanonicalBinderMetadata,
                Bool.and_eq_true] at canonical ⊢
              exact ⟨canonical.1,
                normalized.result.canonicalBinderMetadata canonical.2⟩
            objectPattern := by
              intro object
              simpa [WellSorted.isObjectPattern] using
                normalized.result.objectPattern object
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              simp only [binderSafeAt] at safe ⊢
              exact normalized.result.reflectiveScope presentation
                presentationMembership (by simp; omega) safe
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;> cases binder <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .lambda normalized.tree }
    | @CostSemanticTree.multiLambda _ _ available outer arity binders body
        domain codomain bodyTree =>
        let normalized := bodyTree.normalize
        { result := {
            pattern := .multiLambda arity binders normalized.result.pattern
            typed := .multiLambda (by
              simpa only [List.append_assoc] using normalized.result.typed)
            canonicalBinderMetadata := by
              intro canonical
              simp only [Pattern.hasCanonicalBinderMetadata,
                Bool.and_eq_true] at canonical ⊢
              exact ⟨canonical.1,
                normalized.result.canonicalBinderMetadata canonical.2⟩
            objectPattern := by
              intro object
              simpa [WellSorted.isObjectPattern] using
                normalized.result.objectPattern object
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              simp only [binderSafeAt] at safe ⊢
              exact normalized.result.reflectiveScope presentation
                presentationMembership (by
                  simp [List.length_append, List.length_replicate]
                  omega) safe
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;> cases binders <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .multiLambda normalized.tree }
    | @CostSemanticTree.subst _ _ available outer body replacement domain
        codomain bodyTree replacementTree =>
        let normalizedBody := bodyTree.normalize
        let normalizedReplacement := replacementTree.normalize
        { result := {
            pattern := .subst normalizedBody.result.pattern
              normalizedReplacement.result.pattern
            typed := .subst normalizedBody.result.typed
              normalizedReplacement.result.typed
            canonicalBinderMetadata := by
              intro canonical
              simp only [Pattern.hasCanonicalBinderMetadata,
                Bool.and_eq_true] at canonical ⊢
              exact ⟨normalizedBody.result.canonicalBinderMetadata canonical.1,
                normalizedReplacement.result.canonicalBinderMetadata
                  canonical.2⟩
            objectPattern := by
              intro object
              simp [WellSorted.isObjectPattern] at object
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              simp only [binderSafeAt, Bool.and_eq_true] at safe ⊢
              exact ⟨normalizedBody.result.reflectiveScope presentation
                  presentationMembership (by simp; omega) safe.1,
                normalizedReplacement.result.reflectiveScope presentation
                  presentationMembership availableWithin safe.2⟩
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .subst normalizedBody.tree normalizedReplacement.tree }
    | @CostSemanticTree.collection _ _ available outer collectionType elements
        rest elementType children =>
        let normalized := children.normalize
        { result := {
            pattern := .collection collectionType normalized.result.patterns
              rest
            typed := .collection normalized.result.typed
            canonicalBinderMetadata := by
              intro canonical
              exact normalized.result.canonicalBinderMetadata (by
                simpa [Pattern.hasCanonicalBinderMetadata] using canonical)
            objectPattern := by
              intro objects
              have sourceParts : rest.isNone = true ∧
                  WellSorted.isObjectPatternList elements = true := by
                simpa [WellSorted.isObjectPattern] using objects
              simpa [WellSorted.isObjectPattern, sourceParts.1] using
                normalized.result.objectPatterns sourceParts.2
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              have inputList : binderSafeListAt presentation.quoteConstructor
                  depth elements = true := by
                simpa [binderSafeAt] using safe
              simpa [binderSafeAt] using
                normalized.result.reflectiveScope presentation
                  presentationMembership availableWithin inputList
            matchesParameterRepresentation := by
              intro parameter representation
              cases parameter <;>
                simp_all [WellSorted.MatchesParameterRepresentation] }
          tree := .collection normalized.trees }
  termination_by tree.weight
  decreasing_by
    all_goals subst_vars
    all_goals simp [CostSemanticTree.weight]
    all_goals omega

  def CostSemanticArgumentTrees.normalize {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostSemanticArgumentTrees source targetFree available outer
        arguments parameters) :
      NormalizedCostSemanticArguments source targetFree available outer
        arguments parameters :=
    match trees with
    | @CostSemanticArgumentTrees.nil _ _ available outer =>
        { result := {
            patterns := []
            length_eq := rfl
            typed := .nil
            canonicalBinderMetadata := by
              simp [Pattern.hasCanonicalBinderMetadataList]
            objectPatterns := by simp [WellSorted.isObjectPatternList]
            reflectiveScope := by simp [binderSafeListAt] }
          trees := .nil }
    | @CostSemanticArgumentTrees.cons _ _ available outer argument arguments
        parameter parameters expected representation parameterType head tail =>
        let normalizedHead := head.normalize
        let normalizedTail := tail.normalize
        { result := {
            patterns := normalizedHead.result.pattern ::
              normalizedTail.result.patterns
            length_eq := by simp [normalizedTail.result.length_eq]
            typed := .cons
              (normalizedHead.result.matchesParameterRepresentation _
                representation)
              parameterType normalizedHead.result.typed
                normalizedTail.result.typed
            canonicalBinderMetadata := by
              intro canonical
              simp only [Pattern.hasCanonicalBinderMetadataList,
                Bool.and_eq_true] at canonical ⊢
              exact ⟨normalizedHead.result.canonicalBinderMetadata canonical.1,
                normalizedTail.result.canonicalBinderMetadata canonical.2⟩
            objectPatterns := by
              intro objects
              simp only [WellSorted.isObjectPatternList,
                Bool.and_eq_true] at objects ⊢
              exact ⟨normalizedHead.result.objectPattern objects.1,
                normalizedTail.result.objectPatterns objects.2⟩
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              simp only [binderSafeListAt, Bool.and_eq_true] at safe ⊢
              exact ⟨normalizedHead.result.reflectiveScope presentation
                  presentationMembership availableWithin safe.1,
                normalizedTail.result.reflectiveScope presentation
                  presentationMembership availableWithin safe.2⟩ }
          trees := .cons
            (normalizedHead.result.matchesParameterRepresentation _
              representation)
            parameterType normalizedHead.tree normalizedTail.trees }
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostSemanticArgumentTrees.weight]
    all_goals omega

  def CostSemanticElementTrees.normalize {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostSemanticElementTrees source targetFree available outer
        elements elementType) :
      NormalizedCostSemanticElements source targetFree available outer elements
        elementType :=
    match trees with
    | @CostSemanticElementTrees.nil _ _ available outer elementType =>
        { result := {
            patterns := []
            length_eq := rfl
            typed := .nil _ _
            canonicalBinderMetadata := by
              simp [Pattern.hasCanonicalBinderMetadataList]
            objectPatterns := by simp [WellSorted.isObjectPatternList]
            reflectiveScope := by simp [binderSafeListAt] }
          trees := .nil available outer elementType }
    | @CostSemanticElementTrees.cons _ _ available outer element elements
        elementType head tail =>
        let normalizedHead := head.normalize
        let normalizedTail := tail.normalize
        { result := {
            patterns := normalizedHead.result.pattern ::
              normalizedTail.result.patterns
            length_eq := by simp [normalizedTail.result.length_eq]
            typed := .cons normalizedHead.result.typed
              normalizedTail.result.typed
            canonicalBinderMetadata := by
              intro canonical
              simp only [Pattern.hasCanonicalBinderMetadataList,
                Bool.and_eq_true] at canonical ⊢
              exact ⟨normalizedHead.result.canonicalBinderMetadata canonical.1,
                normalizedTail.result.canonicalBinderMetadata canonical.2⟩
            objectPatterns := by
              intro objects
              simp only [WellSorted.isObjectPatternList,
                Bool.and_eq_true] at objects ⊢
              exact ⟨normalizedHead.result.objectPattern objects.1,
                normalizedTail.result.objectPatterns objects.2⟩
            reflectiveScope := by
              intro presentation presentationMembership depth availableWithin
                safe
              simp only [binderSafeListAt, Bool.and_eq_true] at safe ⊢
              exact ⟨normalizedHead.result.reflectiveScope presentation
                  presentationMembership availableWithin safe.1,
                normalizedTail.result.reflectiveScope presentation
                  presentationMembership availableWithin safe.2⟩ }
          trees := .cons normalizedHead.tree normalizedTail.trees }
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostSemanticElementTrees.weight]
    all_goals omega

  def CostSemanticBoundaryTrees.normalize {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      {values : TypedCostRegionBoundaryTable.Values source color targetFree
        table}
      (trees : CostSemanticBoundaryTrees source targetFree color table values) :
      NormalizedCostSemanticBoundaries source targetFree color table :=
    match trees with
    | @CostSemanticBoundaryTrees.nil _ _ color => ⟨.nil, .nil⟩
    | @CostSemanticBoundaryTrees.cons _ _ color occurrence occurrences
        boundary content tail value values head children =>
        let normalizedHead := head.normalize
        let normalizedChildren := children.normalize
        let normalizedValue := normalizedHead.toBoundaryValue value rfl
        ⟨.cons normalizedValue normalizedChildren.1,
          .cons normalizedHead.tree normalizedChildren.2⟩
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostSemanticBoundaryTrees.weight]
    all_goals omega
end

mutual
  /-- Embed a checked executable decomposition into the stable-frame semantic
  carrier.  The only extra hypothesis is the authored canonical path already
  required by unary Cost normalization. -/
  def CostRegionTree.toSemantic
      {source : CIGSLT} (canonicalPathSafe : CostStaticCanonicalPathSafe source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      CostSemanticTree source targetFree available outer pattern type :=
    match tree with
    | @CostRegionTree.bvar _ _ available outer index type lookup =>
        .bvar lookup
    | @CostRegionTree.fvar _ _ available outer name type lookup =>
        .fvar lookup
    | @CostRegionTree.static _ _ color outer frame children => by
        let path := canonicalPathSafe frame
        let state := CostStaticFrameState.original frame path
        let semanticChildren := children.toSemantic canonicalPathSafe
        let semantic : CostSemanticTree source targetFree frame.targetBound outer
            (state.actAvailableWithOuter
              (TypedCostRegionBoundaryTable.Values.original
                frame.boundaryTable) outer).pattern
            (.base (color.mapLangSort source frame.sourceSort).1) :=
          .static frame state semanticChildren
        exact semantic.reindexPattern
          (CostStaticFrameState.original_actAvailable_pattern frame path)
    | @CostRegionTree.neutralApplicationOrdinary _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        ordinary children =>
        .neutralApplicationOrdinary membership notBareCollection constructor
          materializes neutral ordinary (children.toSemantic canonicalPathSafe)
    | @CostRegionTree.neutralApplicationQuote _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        quoted children =>
        .neutralApplicationQuote membership notBareCollection constructor
          materializes neutral quoted (children.toSemantic canonicalPathSafe)
    | @CostRegionTree.lambda _ _ available outer binder body domain codomain
        bodyTree =>
        .lambda (bodyTree.toSemantic canonicalPathSafe)
    | @CostRegionTree.multiLambda _ _ available outer arity binders body domain
        codomain bodyTree =>
        .multiLambda (bodyTree.toSemantic canonicalPathSafe)
    | @CostRegionTree.subst _ _ available outer body replacement domain codomain
        bodyTree replacementTree =>
        .subst (bodyTree.toSemantic canonicalPathSafe)
          (replacementTree.toSemantic canonicalPathSafe)
    | @CostRegionTree.collection _ _ available outer collectionType elements
        rest elementType children =>
        .collection (children.toSemantic canonicalPathSafe)
  termination_by tree.weight
  decreasing_by
    all_goals subst_vars
    all_goals simp [CostRegionTree.weight]
    all_goals omega

  def CostRegionArgumentTrees.toSemantic
      {source : CIGSLT} (canonicalPathSafe : CostStaticCanonicalPathSafe source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      CostSemanticArgumentTrees source targetFree available outer arguments
        parameters :=
    match trees with
    | @CostRegionArgumentTrees.nil _ _ available outer => .nil
    | @CostRegionArgumentTrees.cons _ _ available outer argument arguments
        parameter parameters expected representation parameterType head tail =>
        .cons representation parameterType (head.toSemantic canonicalPathSafe)
          (tail.toSemantic canonicalPathSafe)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionArgumentTrees.weight]
    all_goals omega

  def CostRegionElementTrees.toSemantic
      {source : CIGSLT} (canonicalPathSafe : CostStaticCanonicalPathSafe source)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer elements
        elementType) :
      CostSemanticElementTrees source targetFree available outer elements
        elementType :=
    match trees with
    | @CostRegionElementTrees.nil _ _ available outer elementType =>
        .nil available outer elementType
    | @CostRegionElementTrees.cons _ _ available outer element elements
        elementType head tail =>
        .cons (head.toSemantic canonicalPathSafe)
          (tail.toSemantic canonicalPathSafe)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionElementTrees.weight]
    all_goals omega

  def CostRegionBoundaryTrees.toSemantic
      {source : CIGSLT} (canonicalPathSafe : CostStaticCanonicalPathSafe source)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      CostSemanticBoundaryTrees source targetFree color table
        (TypedCostRegionBoundaryTable.Values.original table) :=
    match trees with
    | @CostRegionBoundaryTrees.nil _ _ color => .nil
    | @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences boundary
        content tail head children =>
        .cons (head.toSemantic canonicalPathSafe)
          (children.toSemantic canonicalPathSafe)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionBoundaryTrees.weight]
    all_goals omega
end

end Mettapedia.GSLT.LanguageDef
