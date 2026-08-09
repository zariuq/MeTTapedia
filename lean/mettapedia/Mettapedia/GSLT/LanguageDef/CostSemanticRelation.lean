import Mettapedia.GSLT.LanguageDef.CostSemanticCarrier

/-!
# Structural equations on semantic Cost regions

The relation in this module preserves stable frame, declaration, colour, and
boundary-slot identity.  Its exact normal-form theorem concerns the complete
dependent semantic tree, not merely the compact pattern obtained by erasure.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open CostStaticRegionNode

mutual
  /-- One proof-relevant semantic edge.  Static regions retain the exact frame
  and colour while their authored source representative and recursively stored
  boundary values may move inside their respective equation classes. -/
  inductive CostSemanticTree.Rel (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftPattern rightPattern : Pattern} → {type : TypeExpr} →
      CostSemanticTree source targetFree available outer leftPattern type →
      CostSemanticTree source targetFree available outer rightPattern type →
      Prop where
    | bvar {available outer : List TypeExpr} {index : Nat} {type : TypeExpr}
        (leftLookup rightLookup :
          (available ++ outer)[index]? = some type) :
        CostSemanticTree.Rel source targetFree
          (.bvar leftLookup) (.bvar rightLookup)
    | fvar {available outer : List TypeExpr} {name : String} {type : TypeExpr}
        (leftLookup rightLookup : targetFree name = some type) :
        CostSemanticTree.Rel source targetFree
          (.fvar leftLookup) (.fvar rightLookup)
    | static {color : CostStaticColor} {outer : List TypeExpr}
        (frame : CostStaticRegionNode source color targetFree)
        (leftState rightState : CostStaticFrameState frame)
        {leftValues rightValues :
          TypedCostRegionBoundaryTable.Values source color targetFree
            frame.boundaryTable}
        (leftChildren : CostSemanticBoundaryTrees source targetFree color
          frame.boundaryTable leftValues)
        (rightChildren : CostSemanticBoundaryTrees source targetFree color
          frame.boundaryTable rightValues)
        (sourceEquivalent :
          (CostStaticSourceTerm.equationSetoid source color
            frame.boundaryTable.sourceFreeContext
            frame.boundaryTable.sourceSupport frame.sourceBound
            frame.targetBound frame.sourceSort).r
            leftState.current rightState.current)
        (children : CostSemanticBoundaryTrees.Rel source targetFree
          leftChildren rightChildren) :
        CostSemanticTree.Rel source targetFree
          (CostSemanticTree.static (outer := outer) frame leftState
            leftChildren)
          (CostSemanticTree.static (outer := outer) frame rightState
            rightChildren)
    | neutralApplicationOrdinary
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
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
        (leftChildren : CostSemanticArgumentTrees source targetFree available
          outer leftArguments rule.params)
        (rightChildren : CostSemanticArgumentTrees source targetFree available
          outer rightArguments rule.params)
        (arguments : CostSemanticArgumentTrees.Rel source targetFree
          leftChildren rightChildren) :
        CostSemanticTree.Rel source targetFree
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary leftChildren)
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary rightChildren)
    | neutralApplicationQuote
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
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
        (leftChildren : CostSemanticArgumentTrees source targetFree []
          (available ++ outer) leftArguments rule.params)
        (rightChildren : CostSemanticArgumentTrees source targetFree []
          (available ++ outer) rightArguments rule.params)
        (arguments : CostSemanticArgumentTrees.Rel source targetFree
          leftChildren rightChildren) :
        CostSemanticTree.Rel source targetFree
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted leftChildren)
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted rightChildren)
    | lambda
        {available outer : List TypeExpr} {binder : Option String}
        {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
        (leftTree : CostSemanticTree source targetFree (domain :: available)
          outer leftBody codomain)
        (rightTree : CostSemanticTree source targetFree (domain :: available)
          outer rightBody codomain)
        (body : CostSemanticTree.Rel source targetFree leftTree rightTree) :
        CostSemanticTree.Rel source targetFree
          (.lambda (binder := binder) leftTree)
          (.lambda (binder := binder) rightTree)
    | multiLambda
        {available outer : List TypeExpr} {arity : Nat}
        {binders : List String} {leftBody rightBody : Pattern}
        {domain codomain : TypeExpr}
        (leftTree : CostSemanticTree source targetFree
          (List.replicate arity domain ++ available) outer leftBody codomain)
        (rightTree : CostSemanticTree source targetFree
          (List.replicate arity domain ++ available) outer rightBody codomain)
        (body : CostSemanticTree.Rel source targetFree leftTree rightTree) :
        CostSemanticTree.Rel source targetFree
          (.multiLambda (arity := arity) (binders := binders) leftTree)
          (.multiLambda (arity := arity) (binders := binders) rightTree)
    | subst
        {available outer : List TypeExpr}
        {leftBody rightBody leftReplacement rightReplacement : Pattern}
        {domain codomain : TypeExpr}
        (leftBodyTree : CostSemanticTree source targetFree
          (domain :: available) outer leftBody codomain)
        (rightBodyTree : CostSemanticTree source targetFree
          (domain :: available) outer rightBody codomain)
        (leftReplacementTree : CostSemanticTree source targetFree available
          outer leftReplacement domain)
        (rightReplacementTree : CostSemanticTree source targetFree available
          outer rightReplacement domain)
        (body : CostSemanticTree.Rel source targetFree leftBodyTree
          rightBodyTree)
        (replacement : CostSemanticTree.Rel source targetFree
          leftReplacementTree rightReplacementTree) :
        CostSemanticTree.Rel source targetFree
          (.subst leftBodyTree leftReplacementTree)
          (.subst rightBodyTree rightReplacementTree)
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {leftElements rightElements : List Pattern} {rest : Option String}
        {elementType : TypeExpr}
        (leftChildren : CostSemanticElementTrees source targetFree available
          outer leftElements elementType)
        (rightChildren : CostSemanticElementTrees source targetFree available
          outer rightElements elementType)
        (elements : CostSemanticElementTrees.Rel source targetFree leftChildren
          rightChildren) :
        CostSemanticTree.Rel source targetFree
          (.collection (collectionType := collectionType) (rest := rest)
            leftChildren)
          (.collection (collectionType := collectionType) (rest := rest)
            rightChildren)

  /-- Positional semantic relation for one fixed constructor parameter list. -/
  inductive CostSemanticArgumentTrees.Rel (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftArguments rightArguments : List Pattern} →
      {parameters : List TermParam} →
      CostSemanticArgumentTrees source targetFree available outer leftArguments
          parameters →
      CostSemanticArgumentTrees source targetFree available outer rightArguments
          parameters → Prop where
    | nil {available outer : List TypeExpr} :
        CostSemanticArgumentTrees.Rel source targetFree
          (CostSemanticArgumentTrees.nil (available := available)
            (outer := outer))
          (CostSemanticArgumentTrees.nil (available := available)
            (outer := outer))
    | cons
        {available outer : List TypeExpr}
        {leftArgument rightArgument : Pattern}
        {leftArguments rightArguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (leftRepresentation :
          WellSorted.MatchesParameterRepresentation parameter leftArgument)
        (rightRepresentation :
          WellSorted.MatchesParameterRepresentation parameter rightArgument)
        (parameterType : WellSorted.parameterType? parameter = some expected)
        (leftHead : CostSemanticTree source targetFree available outer
          leftArgument expected)
        (rightHead : CostSemanticTree source targetFree available outer
          rightArgument expected)
        (leftTail : CostSemanticArgumentTrees source targetFree available outer
          leftArguments parameters)
        (rightTail : CostSemanticArgumentTrees source targetFree available outer
          rightArguments parameters)
        (head : CostSemanticTree.Rel source targetFree leftHead rightHead)
        (tail : CostSemanticArgumentTrees.Rel source targetFree leftTail
          rightTail) :
        CostSemanticArgumentTrees.Rel source targetFree
          (.cons leftRepresentation parameterType leftHead leftTail)
          (.cons rightRepresentation parameterType rightHead rightTail)

  /-- Positional semantic relation for homogeneous collections. -/
  inductive CostSemanticElementTrees.Rel (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftElements rightElements : List Pattern} → {elementType : TypeExpr} →
      CostSemanticElementTrees source targetFree available outer leftElements
          elementType →
      CostSemanticElementTrees source targetFree available outer rightElements
          elementType → Prop where
    | nil (available outer : List TypeExpr) (elementType : TypeExpr) :
        CostSemanticElementTrees.Rel source targetFree
          (.nil available outer elementType) (.nil available outer elementType)
    | cons
        {available outer : List TypeExpr} {leftElement rightElement : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (leftHead : CostSemanticTree source targetFree available outer
          leftElement elementType)
        (rightHead : CostSemanticTree source targetFree available outer
          rightElement elementType)
        (leftTail : CostSemanticElementTrees source targetFree available outer
          leftElements elementType)
        (rightTail : CostSemanticElementTrees source targetFree available outer
          rightElements elementType)
        (head : CostSemanticTree.Rel source targetFree leftHead rightHead)
        (tail : CostSemanticElementTrees.Rel source targetFree leftTail
          rightTail) :
        CostSemanticElementTrees.Rel source targetFree
          (.cons leftHead leftTail) (.cons rightHead rightTail)

  /-- Positional semantic relation for the finite values of one unchanged
  static boundary table. -/
  inductive CostSemanticBoundaryTrees.Rel (source : CIGSLT)
      (targetFree : WellSorted.FreeTypeContext) :
      {color : CostStaticColor} →
      {occurrences : List CostRegionOccurrence} →
      {table : TypedCostRegionBoundaryTable source color targetFree
        occurrences} →
      {leftValues rightValues :
        TypedCostRegionBoundaryTable.Values source color targetFree table} →
      CostSemanticBoundaryTrees source targetFree color table leftValues →
      CostSemanticBoundaryTrees source targetFree color table rightValues →
      Prop where
    | nil {color : CostStaticColor} :
        CostSemanticBoundaryTrees.Rel source targetFree
          (CostSemanticBoundaryTrees.nil (color := color))
          (CostSemanticBoundaryTrees.nil (color := color))
    | cons {color : CostStaticColor} {occurrence : CostRegionOccurrence}
        {occurrences : List CostRegionOccurrence}
        {boundary : TypedCostRegionBoundary source color targetFree}
        {content : boundary.boundary.content = occurrence.content}
        {tail : TypedCostRegionBoundaryTable source color targetFree occurrences}
        {leftValue rightValue : ReflectiveWellSorted.OpenPattern
          source.costWholeReflectionProfile source.costWholeLanguage targetFree
            boundary.boundary.targetSupport boundary.boundary.targetType}
        {leftValues rightValues : TypedCostRegionBoundaryTable.Values source
          color targetFree tail}
        (leftHead : CostSemanticTree source targetFree
          boundary.boundary.targetSupport [] leftValue.1
          boundary.boundary.targetType)
        (rightHead : CostSemanticTree source targetFree
          boundary.boundary.targetSupport [] rightValue.1
          boundary.boundary.targetType)
        (leftChildren : CostSemanticBoundaryTrees source targetFree color tail
          leftValues)
        (rightChildren : CostSemanticBoundaryTrees source targetFree color tail
          rightValues)
        (head : CostSemanticTree.Rel source targetFree leftHead rightHead)
        (children : CostSemanticBoundaryTrees.Rel source targetFree leftChildren
          rightChildren) :
        CostSemanticBoundaryTrees.Rel source targetFree
          (CostSemanticBoundaryTrees.cons (content := content) leftHead
            leftChildren)
          (CostSemanticBoundaryTrees.cons (content := content) rightHead
            rightChildren)
end

theorem CostStaticFrameState.normalize_eq_of_current_equivalent
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {frame : CostStaticRegionNode source color targetFree}
    (left right : CostStaticFrameState frame)
    (equivalent :
      (CostStaticSourceTerm.equationSetoid source color
        frame.boundaryTable.sourceFreeContext
        frame.boundaryTable.sourceSupport frame.sourceBound frame.targetBound
        frame.sourceSort).r left.current right.current) :
    left.normalize = right.normalize := by
  apply (CostStaticFrameState.mk.injEq _ _ _ _).mpr
  exact CostStaticSourceTerm.normalize_eq_of_equationSetoid equivalent

/-- The exact compact pattern selected by semantic normalization. -/
def CostSemanticTree.normalizedPattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    Pattern :=
  tree.normalize.result.pattern

/-- Exact normalized argument patterns. -/
def CostSemanticArgumentTrees.normalizedPatterns
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters) : List Pattern :=
  trees.normalize.result.patterns

/-- Exact normalized collection elements. -/
def CostSemanticElementTrees.normalizedPatterns
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType) : List Pattern :=
  trees.normalize.result.patterns

/-- Exact normalized finite values of one unchanged boundary table. -/
def CostSemanticBoundaryTrees.normalizedValues
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    (trees : CostSemanticBoundaryTrees source targetFree color table values) :
    TypedCostRegionBoundaryTable.Values source color targetFree table :=
  trees.normalize.1

/-- The complete proof-relevant normal form of one semantic tree. -/
def CostSemanticTree.normalForm
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    Σ normalized : Pattern,
      CostSemanticTree source targetFree available outer normalized type :=
  ⟨tree.normalize.result.pattern, tree.normalize.tree⟩

/-- The complete proof-relevant normal form of an argument spine. -/
def CostSemanticArgumentTrees.normalForm
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (trees : CostSemanticArgumentTrees source targetFree available outer
      arguments parameters) :
    Σ normalized : List Pattern,
      CostSemanticArgumentTrees source targetFree available outer normalized
        parameters :=
  ⟨trees.normalize.result.patterns, trees.normalize.trees⟩

/-- The complete proof-relevant normal form of a collection spine. -/
def CostSemanticElementTrees.normalForm
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (trees : CostSemanticElementTrees source targetFree available outer elements
      elementType) :
    Σ normalized : List Pattern,
      CostSemanticElementTrees source targetFree available outer normalized
        elementType :=
  ⟨trees.normalize.result.patterns, trees.normalize.trees⟩

/-- The complete proof-relevant normal form of a finite boundary forest. -/
def CostSemanticBoundaryTrees.normalForm
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    (trees : CostSemanticBoundaryTrees source targetFree color table values) :
    NormalizedCostSemanticBoundaries source targetFree color table :=
  trees.normalize

/-- Semantic edges are invisible to the exact semantic normalizer.  The
generated mutual recursor is used directly so the proof follows the
proof-relevant relation rather than an auxiliary size measure. -/
theorem CostSemanticTree.Rel.normalize_pattern_eq
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    {left : CostSemanticTree source targetFree available outer leftPattern type}
    {right : CostSemanticTree source targetFree available outer rightPattern type}
    (relation : CostSemanticTree.Rel source targetFree left right) :
    left.normalizedPattern = right.normalizedPattern := by
  apply CostSemanticTree.Rel.rec
    (motive_1 := fun left right _ =>
      left.normalizedPattern = right.normalizedPattern)
    (motive_2 := fun left right _ =>
      left.normalizedPatterns = right.normalizedPatterns)
    (motive_3 := fun left right _ =>
      left.normalizedPatterns = right.normalizedPatterns)
    (motive_4 := fun left right _ =>
      left.normalizedValues = right.normalizedValues)
    (t := relation)
  · intros
    rfl
  · intros
    rfl
  · intros
    rename_i color' outer' frame leftState rightState leftValues rightValues
      leftChildren rightChildren sourceEquivalent children childrenEq
    have stateEq := CostStaticFrameState.normalize_eq_of_current_equivalent
      leftState rightState sourceEquivalent
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change
      (leftState.normalize.actAvailableWithOuter
          leftChildren.normalizedValues _).pattern =
        (rightState.normalize.actAvailableWithOuter
          rightChildren.normalizedValues _).pattern
    rw [stateEq, childrenEq]
  · intros
    rename_i available' outer' rule leftArguments rightArguments membership
      notBareCollection constructor materializes neutral ordinary leftChildren
      rightChildren arguments argumentsEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.apply _ leftChildren.normalizedPatterns =
      Pattern.apply _ rightChildren.normalizedPatterns
    exact congrArg (Pattern.apply _) argumentsEq
  · intros
    rename_i available' outer' rule leftArguments rightArguments membership
      notBareCollection constructor materializes neutral quoted leftChildren
      rightChildren arguments argumentsEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.apply _ leftChildren.normalizedPatterns =
      Pattern.apply _ rightChildren.normalizedPatterns
    exact congrArg (Pattern.apply _) argumentsEq
  · intros
    rename_i available' outer' binder leftBody rightBody domain codomain leftTree
      rightTree body bodyEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.lambda _ leftTree.normalizedPattern =
      Pattern.lambda _ rightTree.normalizedPattern
    exact congrArg (Pattern.lambda _) bodyEq
  · intros
    rename_i available' outer' arity binders leftBody rightBody domain codomain
      leftTree rightTree body bodyEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.multiLambda _ _ leftTree.normalizedPattern =
      Pattern.multiLambda _ _ rightTree.normalizedPattern
    exact congrArg (Pattern.multiLambda _ _) bodyEq
  · intros
    rename_i available' outer' leftBody rightBody leftReplacement
      rightReplacement domain codomain leftBodyTree rightBodyTree
      leftReplacementTree rightReplacementTree body replacement bodyEq
      replacementEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.subst leftBodyTree.normalizedPattern
        leftReplacementTree.normalizedPattern =
      Pattern.subst rightBodyTree.normalizedPattern
        rightReplacementTree.normalizedPattern
    exact congrArg₂ Pattern.subst bodyEq replacementEq
  · intros
    rename_i available' outer' collectionType leftElements rightElements rest
      elementType leftChildren rightChildren elements elementsEq
    simp only [CostSemanticTree.normalizedPattern, CostSemanticTree.normalize]
    change Pattern.collection _ leftChildren.normalizedPatterns _ =
      Pattern.collection _ rightChildren.normalizedPatterns _
    exact congrArg (fun xs => Pattern.collection _ xs _) elementsEq
  · intros
    rfl
  · intros
    rename_i available' outer' leftArgument rightArgument leftArguments
      rightArguments parameter parameters expected leftRepresentation
      rightRepresentation parameterType leftHead rightHead leftTail rightTail head
      tail headEq tailEq
    simp only [CostSemanticArgumentTrees.normalizedPatterns,
      CostSemanticArgumentTrees.normalize]
    change leftHead.normalizedPattern :: leftTail.normalizedPatterns =
      rightHead.normalizedPattern :: rightTail.normalizedPatterns
    exact congrArg₂ List.cons headEq tailEq
  · intros
    rfl
  · intros
    rename_i available' outer' leftElement rightElement leftElements rightElements
      elementType leftHead rightHead leftTail rightTail head tail headEq tailEq
    simp only [CostSemanticElementTrees.normalizedPatterns,
      CostSemanticElementTrees.normalize]
    change leftHead.normalizedPattern :: leftTail.normalizedPatterns =
      rightHead.normalizedPattern :: rightTail.normalizedPatterns
    exact congrArg₂ List.cons headEq tailEq
  · intros
    rfl
  · intros
    rename_i color' occurrence occurrences boundary content tail leftValue
      rightValue leftValues rightValues leftHead rightHead leftChildren
      rightChildren head children headEq childrenEq
    unfold CostSemanticBoundaryTrees.normalizedValues
    simp only [CostSemanticBoundaryTrees.normalize]
    rw [TypedCostRegionBoundaryTable.Values.cons.injEq]
    refine ⟨?_, childrenEq⟩
    apply Subtype.ext
    exact headEq

/-- A semantic edge receives one identical proof-relevant normal form, not
merely the same erased compact pattern. -/
theorem CostSemanticTree.Rel.normalForm_eq
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    {left : CostSemanticTree source targetFree available outer leftPattern type}
    {right : CostSemanticTree source targetFree available outer rightPattern type}
    (relation : CostSemanticTree.Rel source targetFree left right) :
    left.normalForm = right.normalForm := by
  apply CostSemanticTree.Rel.rec
    (motive_1 := fun left right _ => left.normalForm = right.normalForm)
    (motive_2 := fun left right _ => left.normalForm = right.normalForm)
    (motive_3 := fun left right _ => left.normalForm = right.normalForm)
    (motive_4 := fun left right _ => left.normalForm = right.normalForm)
    (t := relation)
  · intros
    rename_i available' outer' index type' leftLookup rightLookup
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
  · intros
    rename_i firstAvailable firstOuter secondAvailable secondOuter name type'
      leftLookup rightLookup
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
  · intros
    rename_i color' outer' frame leftState rightState leftValues rightValues
      leftChildren rightChildren sourceEquivalent children childrenEq
    have stateEq := CostStaticFrameState.normalize_eq_of_current_equivalent
      leftState rightState sourceEquivalent
    unfold CostSemanticBoundaryTrees.normalForm at childrenEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    simp only
    change
      (⟨_, CostSemanticTree.static frame leftState.normalize
        leftChildren.normalize.2⟩ :
        Σ normalized, CostSemanticTree source targetFree frame.targetBound
          outer' normalized
            (.base (color'.mapLangSort source frame.sourceSort).1)) =
      (⟨_, CostSemanticTree.static frame rightState.normalize
        rightChildren.normalize.2⟩ :
        Σ normalized, CostSemanticTree source targetFree frame.targetBound
          outer' normalized
            (.base (color'.mapLangSort source frame.sourceSort).1))
    exact congrArg₂
      (fun (state : CostStaticFrameState frame)
          (normalizedChildren : NormalizedCostSemanticBoundaries source
            targetFree color' frame.boundaryTable) =>
        (⟨(state.actAvailableWithOuter normalizedChildren.1 outer').pattern,
          CostSemanticTree.static frame state normalizedChildren.2⟩ :
          Σ normalized, CostSemanticTree source targetFree frame.targetBound
            outer' normalized
              (.base (color'.mapLangSort source frame.sourceSort).1)))
      stateEq childrenEq
  · intros
    rename_i available' outer' rule leftArguments rightArguments membership
      notBareCollection constructor materializes neutral ordinary leftChildren
      rightChildren arguments argumentsEq
    unfold CostSemanticArgumentTrees.normalForm at argumentsEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.neutralApplicationOrdinary membership
        notBareCollection constructor materializes neutral ordinary
          leftChildren.normalize.trees⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized (.base rule.category)) =
      ⟨_, CostSemanticTree.neutralApplicationOrdinary membership
        notBareCollection constructor materializes neutral ordinary
          rightChildren.normalize.trees⟩
    exact congrArg
      (fun normalizedChildren :
          Σ patterns, CostSemanticArgumentTrees source targetFree available'
            outer' patterns rule.params =>
        (⟨.apply rule.label normalizedChildren.1,
          CostSemanticTree.neutralApplicationOrdinary membership
            notBareCollection constructor materializes neutral ordinary
              normalizedChildren.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized (.base rule.category)))
      argumentsEq
  · intros
    rename_i available' outer' rule leftArguments rightArguments membership
      notBareCollection constructor materializes neutral quoted leftChildren
      rightChildren arguments argumentsEq
    unfold CostSemanticArgumentTrees.normalForm at argumentsEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.neutralApplicationQuote membership
        notBareCollection constructor materializes neutral quoted
          leftChildren.normalize.trees⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized (.base rule.category)) =
      ⟨_, CostSemanticTree.neutralApplicationQuote membership
        notBareCollection constructor materializes neutral quoted
          rightChildren.normalize.trees⟩
    exact congrArg
      (fun normalizedChildren :
          Σ patterns, CostSemanticArgumentTrees source targetFree []
            (available' ++ outer') patterns rule.params =>
        (⟨.apply rule.label normalizedChildren.1,
          CostSemanticTree.neutralApplicationQuote membership
            notBareCollection constructor materializes neutral quoted
              normalizedChildren.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized (.base rule.category)))
      argumentsEq
  · intros
    rename_i available' outer' binder leftBody rightBody domain codomain leftTree
      rightTree body bodyEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.lambda leftTree.normalize.tree⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized (.arrow domain codomain)) =
      ⟨_, CostSemanticTree.lambda rightTree.normalize.tree⟩
    exact congrArg
      (fun normalizedBody :
          Σ body, CostSemanticTree source targetFree (domain :: available')
            outer' body codomain =>
        (⟨.lambda binder normalizedBody.1,
          CostSemanticTree.lambda normalizedBody.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized (.arrow domain codomain)))
      bodyEq
  · intros
    rename_i available' outer' arity binders leftBody rightBody domain codomain
      leftTree rightTree body bodyEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.multiLambda leftTree.normalize.tree⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized (.arrow (.multiBinder domain) codomain)) =
      ⟨_, CostSemanticTree.multiLambda rightTree.normalize.tree⟩
    exact congrArg
      (fun normalizedBody :
          Σ body, CostSemanticTree source targetFree
            (List.replicate arity domain ++ available') outer' body codomain =>
        (⟨.multiLambda arity binders normalizedBody.1,
          CostSemanticTree.multiLambda normalizedBody.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized (.arrow (.multiBinder domain) codomain)))
      bodyEq
  · intros
    rename_i available' outer' leftBody rightBody leftReplacement
      rightReplacement domain codomain leftBodyTree rightBodyTree
      leftReplacementTree rightReplacementTree body replacement bodyEq
      replacementEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.subst leftBodyTree.normalize.tree
        leftReplacementTree.normalize.tree⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized codomain) =
      ⟨_, CostSemanticTree.subst rightBodyTree.normalize.tree
        rightReplacementTree.normalize.tree⟩
    exact congrArg₂
      (fun (normalizedBody :
          Σ body, CostSemanticTree source targetFree (domain :: available')
            outer' body codomain)
          (normalizedReplacement :
          Σ replacement, CostSemanticTree source targetFree available' outer'
            replacement domain) =>
        (⟨.subst normalizedBody.1 normalizedReplacement.1,
          CostSemanticTree.subst normalizedBody.2 normalizedReplacement.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized codomain))
      bodyEq replacementEq
  · intros
    rename_i available' outer' collectionType leftElements rightElements rest
      elementType leftChildren rightChildren elements elementsEq
    unfold CostSemanticElementTrees.normalForm at elementsEq
    unfold CostSemanticTree.normalForm
    repeat rw [CostSemanticTree.normalize.eq_def]
    change
      (⟨_, CostSemanticTree.collection leftChildren.normalize.trees⟩ :
        Σ normalized, CostSemanticTree source targetFree available' outer'
          normalized (.collection collectionType elementType)) =
      ⟨_, CostSemanticTree.collection rightChildren.normalize.trees⟩
    exact congrArg
      (fun normalizedChildren :
          Σ elements, CostSemanticElementTrees source targetFree available'
            outer' elements elementType =>
        (⟨.collection collectionType normalizedChildren.1 rest,
          CostSemanticTree.collection normalizedChildren.2⟩ :
          Σ normalized, CostSemanticTree source targetFree available' outer'
            normalized (.collection collectionType elementType)))
      elementsEq
  · intros
    rename_i available' outer'
    simp only [CostSemanticArgumentTrees.normalForm]
  · intros
    rename_i available' outer' leftArgument rightArgument leftArguments
      rightArguments parameter parameters expected leftRepresentation
      rightRepresentation parameterType leftHead rightHead leftTail rightTail head
      tail headEq tailEq
    unfold CostSemanticTree.normalForm at headEq
    unfold CostSemanticArgumentTrees.normalForm at tailEq
    unfold CostSemanticArgumentTrees.normalForm
    repeat rw [CostSemanticArgumentTrees.normalize.eq_def]
    change
      (⟨_, CostSemanticArgumentTrees.cons
        (leftHead.normalize.result.matchesParameterRepresentation _
          leftRepresentation)
        parameterType leftHead.normalize.tree leftTail.normalize.trees⟩ :
        Σ normalized, CostSemanticArgumentTrees source targetFree available'
          outer' normalized (parameter :: parameters)) =
      ⟨_, CostSemanticArgumentTrees.cons
        (rightHead.normalize.result.matchesParameterRepresentation _
          rightRepresentation)
        parameterType rightHead.normalize.tree rightTail.normalize.trees⟩
    let NormalizedHeadWithRepresentation :=
      { normalizedHead :
          (Σ argument, CostSemanticTree source targetFree available' outer'
            argument expected) //
        WellSorted.MatchesParameterRepresentation parameter normalizedHead.1 }
    have packagedHeadEq :
        (⟨⟨leftHead.normalize.result.pattern, leftHead.normalize.tree⟩,
          leftHead.normalize.result.matchesParameterRepresentation _
            leftRepresentation⟩ : NormalizedHeadWithRepresentation) =
        ⟨⟨rightHead.normalize.result.pattern, rightHead.normalize.tree⟩,
          rightHead.normalize.result.matchesParameterRepresentation _
            rightRepresentation⟩ := by
      apply Subtype.ext
      exact headEq
    exact congrArg₂
      (fun (normalizedHead : NormalizedHeadWithRepresentation)
          (normalizedTail :
          Σ arguments, CostSemanticArgumentTrees source targetFree available'
            outer' arguments parameters) =>
        (⟨normalizedHead.1.1 :: normalizedTail.1,
          CostSemanticArgumentTrees.cons normalizedHead.2 parameterType
            normalizedHead.1.2 normalizedTail.2⟩ :
          Σ normalized, CostSemanticArgumentTrees source targetFree available'
            outer' normalized (parameter :: parameters)))
      packagedHeadEq tailEq
  · intros
    rename_i available' outer' elementType
    simp only [CostSemanticElementTrees.normalForm]
  · intros
    rename_i available' outer' leftElement rightElement leftElements rightElements
      elementType leftHead rightHead leftTail rightTail head tail headEq tailEq
    unfold CostSemanticTree.normalForm at headEq
    unfold CostSemanticElementTrees.normalForm at tailEq
    unfold CostSemanticElementTrees.normalForm
    repeat rw [CostSemanticElementTrees.normalize.eq_def]
    change
      (⟨_, CostSemanticElementTrees.cons leftHead.normalize.tree
        leftTail.normalize.trees⟩ :
        Σ normalized, CostSemanticElementTrees source targetFree available'
          outer' normalized elementType) =
      ⟨_, CostSemanticElementTrees.cons rightHead.normalize.tree
        rightTail.normalize.trees⟩
    exact congrArg₂
      (fun (normalizedHead :
          Σ element, CostSemanticTree source targetFree available' outer'
            element elementType)
          (normalizedTail :
          Σ elements, CostSemanticElementTrees source targetFree available'
            outer' elements elementType) =>
        (⟨normalizedHead.1 :: normalizedTail.1,
          CostSemanticElementTrees.cons normalizedHead.2 normalizedTail.2⟩ :
          Σ normalized, CostSemanticElementTrees source targetFree available'
            outer' normalized elementType))
      headEq tailEq
  · intros
    rename_i color'
    simp only [CostSemanticBoundaryTrees.normalForm,
      CostSemanticBoundaryTrees.normalize]
  · intros
    rename_i color' occurrence occurrences boundary content tail leftValue
      rightValue leftValues rightValues leftHead rightHead leftChildren
      rightChildren head children headEq childrenEq
    unfold CostSemanticTree.normalForm at headEq
    unfold CostSemanticBoundaryTrees.normalForm at childrenEq
    unfold CostSemanticBoundaryTrees.normalForm
    repeat rw [CostSemanticBoundaryTrees.normalize.eq_def]
    change
      (⟨TypedCostRegionBoundaryTable.Values.cons
          (leftHead.normalize.toBoundaryValue leftValue rfl)
          leftChildren.normalize.1,
        CostSemanticBoundaryTrees.cons leftHead.normalize.tree
          leftChildren.normalize.2⟩ :
        NormalizedCostSemanticBoundaries source targetFree color'
          (.cons boundary content tail)) =
      ⟨TypedCostRegionBoundaryTable.Values.cons
          (rightHead.normalize.toBoundaryValue rightValue rfl)
          rightChildren.normalize.1,
        CostSemanticBoundaryTrees.cons rightHead.normalize.tree
          rightChildren.normalize.2⟩
    let NormalizedBoundaryHead :=
      Σ normalizedValue : ReflectiveWellSorted.OpenPattern
          source.costWholeReflectionProfile source.costWholeLanguage targetFree
            boundary.boundary.targetSupport boundary.boundary.targetType,
        CostSemanticTree source targetFree boundary.boundary.targetSupport []
          normalizedValue.1 boundary.boundary.targetType
    have packagedHeadEq :
        (⟨leftHead.normalize.toBoundaryValue leftValue rfl,
          leftHead.normalize.tree⟩ : NormalizedBoundaryHead) =
        ⟨rightHead.normalize.toBoundaryValue rightValue rfl,
          rightHead.normalize.tree⟩ := by
      apply Sigma.ext
      · apply Subtype.ext
        exact congrArg Sigma.fst headEq
      · exact (Sigma.ext_iff.mp headEq).2
    exact congrArg₂
      (fun (normalizedHead : NormalizedBoundaryHead)
          (normalizedChildren : NormalizedCostSemanticBoundaries source
            targetFree color' tail) =>
        (⟨TypedCostRegionBoundaryTable.Values.cons normalizedHead.1
            normalizedChildren.1,
          CostSemanticBoundaryTrees.cons normalizedHead.2 normalizedChildren.2⟩ :
          NormalizedCostSemanticBoundaries source targetFree color'
            (.cons boundary content tail)))
      packagedHeadEq childrenEq

/-- Semantic normalization stays in the relation generated by stable frames
and recursive boundary-value equations.  As above, the mutual recursor carries
the exact four induction hypotheses without a separate termination argument. -/
theorem CostSemanticTree.normalize_rel_original
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostSemanticTree source targetFree available outer pattern type) :
    CostSemanticTree.Rel source targetFree tree.normalize.tree tree := by
  apply CostSemanticTree.rec
    (motive_1 := fun _ _ _ _ tree =>
      CostSemanticTree.Rel source targetFree tree.normalize.tree tree)
    (motive_2 := fun _ _ _ _ trees =>
      CostSemanticArgumentTrees.Rel source targetFree trees.normalize.trees
        trees)
    (motive_3 := fun _ _ _ _ trees =>
      CostSemanticElementTrees.Rel source targetFree trees.normalize.trees
        trees)
    (motive_4 := fun _ _ _ _ trees =>
      CostSemanticBoundaryTrees.Rel source targetFree trees.normalize.2 trees)
    (t := tree)
  · intros
    rename_i available' outer' index type' lookup
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.bvar (source := source)
      (targetFree := targetFree) lookup lookup
  · intros
    rename_i available' outer' name type' lookup
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.fvar (source := source)
      (targetFree := targetFree) (available := available') (outer := outer')
      lookup lookup
  · intros
    rename_i color outer' frame state values children childrenRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.static (source := source)
      (targetFree := targetFree) frame state.normalize state
      children.normalize.2 children state.canonicalPath childrenRel
  · intros
    rename_i available' outer' rule arguments membership notBareCollection
      constructor materializes neutral ordinary children childrenRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.neutralApplicationOrdinary (source := source)
      (targetFree := targetFree) membership notBareCollection constructor
      materializes neutral ordinary children.normalize.trees children
      childrenRel
  · intros
    rename_i available' outer' rule arguments membership notBareCollection
      constructor materializes neutral quoted children childrenRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.neutralApplicationQuote (source := source)
      (targetFree := targetFree) membership notBareCollection constructor
      materializes neutral quoted children.normalize.trees children childrenRel
  · intros
    rename_i available' outer' binder body domain codomain bodyTree bodyRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.lambda (source := source)
      (targetFree := targetFree) bodyTree.normalize.tree bodyTree bodyRel
  · intros
    rename_i available' outer' arity binders body domain codomain bodyTree
      bodyRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.multiLambda (source := source)
      (targetFree := targetFree) bodyTree.normalize.tree bodyTree bodyRel
  · intros
    rename_i available' outer' body replacement domain codomain bodyTree
      replacementTree bodyRel replacementRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.subst (source := source)
      (targetFree := targetFree) bodyTree.normalize.tree bodyTree
      replacementTree.normalize.tree replacementTree bodyRel replacementRel
  · intros
    rename_i available' outer' collectionType elements rest elementType children
      childrenRel
    rw [CostSemanticTree.normalize.eq_def]
    exact CostSemanticTree.Rel.collection (source := source)
      (targetFree := targetFree) children.normalize.trees children childrenRel
  · intros
    rename_i available' outer'
    rw [CostSemanticArgumentTrees.normalize.eq_def]
    exact CostSemanticArgumentTrees.Rel.nil (source := source)
      (targetFree := targetFree) (available := available') (outer := outer')
  · intros
    rename_i available' outer' argument arguments parameter parameters expected
      representation parameterType head tail headRel tailRel
    rw [CostSemanticArgumentTrees.normalize.eq_def]
    exact CostSemanticArgumentTrees.Rel.cons (source := source)
      (targetFree := targetFree)
      (head.normalize.result.matchesParameterRepresentation _ representation)
      representation parameterType head.normalize.tree head
      tail.normalize.trees tail headRel tailRel
  · intros
    rename_i available' outer' elementType
    rw [CostSemanticElementTrees.normalize.eq_def]
    exact CostSemanticElementTrees.Rel.nil (source := source)
      (targetFree := targetFree) available' outer' elementType
  · intros
    rename_i available' outer' element elements elementType head tail headRel
      tailRel
    rw [CostSemanticElementTrees.normalize.eq_def]
    exact CostSemanticElementTrees.Rel.cons (source := source)
      (targetFree := targetFree) head.normalize.tree head tail.normalize.trees
      tail headRel tailRel
  · intros
    rename_i color
    rw [CostSemanticBoundaryTrees.normalize.eq_def]
    exact CostSemanticBoundaryTrees.Rel.nil (source := source)
      (targetFree := targetFree) (color := color)
  · intros
    rename_i color occurrence occurrences boundary content tail value values
      head children headRel childrenRel
    rw [CostSemanticBoundaryTrees.normalize.eq_def]
    exact CostSemanticBoundaryTrees.Rel.cons (source := source)
      (targetFree := targetFree)
      (leftValue := head.normalize.toBoundaryValue value rfl)
      (rightValue := value) head.normalize.tree head children.normalize.2
      children headRel childrenRel

end Mettapedia.GSLT.LanguageDef
