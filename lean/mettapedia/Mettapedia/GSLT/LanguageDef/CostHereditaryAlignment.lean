import Mettapedia.GSLT.LanguageDef.CostHereditaryTreeNormalization
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment

/-!
# Root-aware semantic alignment of hereditary Cost trees

Exact generator normalization may change a region-tree root or its finite
boundary inventory.  This file defines the structural closure of local
semantic-atom evaluation bridges.  Ordinary frames lift aligned children;
root-changing constructors retain complete finite atom evidence rather than
an equality of final patterns.

The relation is independent of any particular language's occurrence
classifier.  A language instance must still construct its bridges from exact
authored generator occurrences.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- A named static normalization kernel.  Bundling the dependent function
keeps it uniform across the mutually recursive tree and spine alignments. -/
structure CostStaticNormalizationKernel (source : CIGSLT) where
  normalize : CostStaticRegionNormalizer source

/-- A one-environment semantic-atom join for a static-to-structural root
change.  Both results must factor through restoration of one exact typed atom
from a retained finite occurrence inventory. -/
structure PackedCostSemanticAtomJoin
    (source : CIGSLT) (leftResult rightResult : Pattern) where
  color : CostStaticColor
  targetFree : FreeTypeContext
  occurrences : List CostRegionOccurrence
  table : TypedCostRegionBoundaryTable source color targetFree occurrences
  values : TypedCostRegionBoundaryTable.Values source color targetFree table
  root : Pattern
  inventory : CostStaticParameterInventory source color targetFree table values
    root
  environment : CostStaticAtomEnvironment source color targetFree inventory
  bound : List TypeExpr
  slot : Fin environment.atomCount
  leftFactors : leftResult = environment.restore bound
    (.fvar (environment.atomName slot))
  rightFactors : rightResult = environment.restore bound
    (.fvar (environment.atomName slot))

namespace PackedCostSemanticAtomJoin

/-- Reindex only the two exposed result patterns of a retained atom join.
The finite environment, occurrence inventory, and restoration factors remain
unchanged. -/
def transport
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (join : PackedCostSemanticAtomJoin source leftResult rightResult)
    {leftResult' rightResult' : Pattern}
    (leftEquality : leftResult' = leftResult)
    (rightEquality : rightResult' = rightResult) :
    PackedCostSemanticAtomJoin source leftResult' rightResult' where
  color := join.color
  targetFree := join.targetFree
  occurrences := join.occurrences
  table := join.table
  values := join.values
  root := join.root
  inventory := join.inventory
  environment := join.environment
  bound := join.bound
  slot := join.slot
  leftFactors := leftEquality.trans join.leftFactors
  rightFactors := rightEquality.trans join.rightFactors

/-- Both endpoints of a one-atom join have the same exact compact result. -/
theorem results_eq
    {source : CIGSLT} {leftResult rightResult : Pattern}
    (join : PackedCostSemanticAtomJoin source leftResult rightResult) :
    leftResult = rightResult :=
  join.leftFactors.trans join.rightFactors.symm

end PackedCostSemanticAtomJoin

/-- Evidence that a retained Cost tree is rooted at one exact static colour.
The constructor exposes the proof-relevant node and its finite boundary
children; the colour is therefore recovered from the decomposition rather
than guessed from the compact pattern. -/
inductive CostRegionTree.StaticRootColor
    (source : CIGSLT) (targetFree : FreeTypeContext) :
    {available outer : List TypeExpr} → {pattern : Pattern} →
      {type : TypeExpr} →
      CostRegionTree source targetFree available outer pattern type →
      CostStaticColor → Type where
  | static
      {color : CostStaticColor} {outer : List TypeExpr}
      (node : CostStaticRegionNode source color targetFree)
      (children : CostRegionBoundaryTrees source targetFree color
        node.finiteBoundaryTable) :
      CostRegionTree.StaticRootColor source targetFree
        (CostRegionTree.static (outer := outer) node children) color
  | reindexPattern
      {color : CostStaticColor} {available outer : List TypeExpr}
      {first second : Pattern} {type : TypeExpr}
      (patternEq : first = second)
      (tree : CostRegionTree source targetFree available outer first type)
      (root : CostRegionTree.StaticRootColor source targetFree tree color) :
      CostRegionTree.StaticRootColor source targetFree
        (tree.reindexPattern patternEq) color
  | reindexAvailable
      {color : CostStaticColor} {first second outer : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (availableEq : first = second)
      (tree : CostRegionTree source targetFree first outer pattern type)
      (root : CostRegionTree.StaticRootColor source targetFree tree color) :
      CostRegionTree.StaticRootColor source targetFree
        (tree.reindexAvailable availableEq) color
  | reindexType
      {color : CostStaticColor} {available outer : List TypeExpr}
      {pattern : Pattern} {first second : TypeExpr}
      (typeEq : first = second)
      (tree : CostRegionTree source targetFree available outer pattern first)
      (root : CostRegionTree.StaticRootColor source targetFree tree color) :
      CostRegionTree.StaticRootColor source targetFree
        (tree.reindexType typeEq) color

/-- The genuine root-changing semantic certificates.  Positional-frame,
canonical-atom-frame, and common-restoration cospans retain their distinct
semantic boundaries; a one-atom join handles the asymmetric
static-to-structural cell.  No constructor stores final equality as an
assumption. -/
inductive CostRegionRootNormalizationBridge
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (targetFree : FreeTypeContext) :
    {leftAvailable leftOuter : List TypeExpr} →
      {leftPattern : Pattern} → {leftType : TypeExpr} →
      (left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType) →
      {rightAvailable rightOuter : List TypeExpr} →
      {rightPattern : Pattern} → {rightType : TypeExpr} →
      (right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType) → Type where
  | semanticRoot
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      (left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType)
      (right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType)
      (bridge : PackedCostStaticAtomEvaluationBridge source
        (left.normalize (normalizeStatic := kernel.normalize)).pattern
        (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
      CostRegionRootNormalizationBridge source kernel targetFree left right
  | canonicalAtomRoot
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      (left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType)
      (right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType)
      (bridge : PackedCostStaticCanonicalAtomEvaluationBridge source
        (left.normalize (normalizeStatic := kernel.normalize)).pattern
        (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
      CostRegionRootNormalizationBridge source kernel targetFree left right
  | canonicalAtomRestorationRoot
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      (left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType)
      (right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType)
      (bridge : PackedCostStaticCanonicalAtomRestorationEvaluationBridge source
        (left.normalize (normalizeStatic := kernel.normalize)).pattern
        (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
      CostRegionRootNormalizationBridge source kernel targetFree left right
  | semanticAtom
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      (left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType)
      (right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType)
      (join : PackedCostSemanticAtomJoin source
        (left.normalize (normalizeStatic := kernel.normalize)).pattern
        (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
      CostRegionRootNormalizationBridge source kernel targetFree left right

mutual
  /-- Structural closure of finite semantic-atom root bridges between two
  actual proof-relevant Cost region trees. -/
  inductive CostRegionTreeNormalizationAlignment
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {leftAvailable leftOuter : List TypeExpr} →
      {leftPattern : Pattern} → {leftType : TypeExpr} →
      CostRegionTree source targetFree leftAvailable leftOuter leftPattern
          leftType →
      {rightAvailable rightOuter : List TypeExpr} →
      {rightPattern : Pattern} → {rightType : TypeExpr} →
      CostRegionTree source targetFree rightAvailable rightOuter rightPattern
          rightType → Type where
    | refl
        {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
        (tree : CostRegionTree source targetFree available outer pattern type) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          tree tree
    | semanticRoot
        {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
        {leftPattern rightPattern : Pattern}
        {leftType rightType : TypeExpr}
        (left : CostRegionTree source targetFree leftAvailable leftOuter
          leftPattern leftType)
        (right : CostRegionTree source targetFree rightAvailable rightOuter
          rightPattern rightType)
        (bridge : PackedCostStaticAtomEvaluationBridge source
          (left.normalize (normalizeStatic := kernel.normalize)).pattern
          (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          left right
    | canonicalAtomRoot
        {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
        {leftPattern rightPattern : Pattern}
        {leftType rightType : TypeExpr}
        (left : CostRegionTree source targetFree leftAvailable leftOuter
          leftPattern leftType)
        (right : CostRegionTree source targetFree rightAvailable rightOuter
          rightPattern rightType)
        (bridge : PackedCostStaticCanonicalAtomEvaluationBridge source
          (left.normalize (normalizeStatic := kernel.normalize)).pattern
          (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          left right
    | canonicalAtomRestorationRoot
        {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
        {leftPattern rightPattern : Pattern}
        {leftType rightType : TypeExpr}
        (left : CostRegionTree source targetFree leftAvailable leftOuter
          leftPattern leftType)
        (right : CostRegionTree source targetFree rightAvailable rightOuter
          rightPattern rightType)
        (bridge :
          PackedCostStaticCanonicalAtomRestorationEvaluationBridge source
            (left.normalize (normalizeStatic := kernel.normalize)).pattern
            (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          left right
    | semanticAtom
        {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
        {leftPattern rightPattern : Pattern}
        {leftType rightType : TypeExpr}
        (left : CostRegionTree source targetFree leftAvailable leftOuter
          leftPattern leftType)
        (right : CostRegionTree source targetFree rightAvailable rightOuter
          rightPattern rightType)
        (join : PackedCostSemanticAtomJoin source
          (left.normalize (normalizeStatic := kernel.normalize)).pattern
          (right.normalize (normalizeStatic := kernel.normalize)).pattern) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          left right
    | neutralApplicationOrdinary
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (ordinary : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeLanguage rule.label = false)
        (leftChildren : CostRegionArgumentTrees source targetFree available
          outer leftArguments rule.params)
        (rightChildren : CostRegionArgumentTrees source targetFree available
          outer rightArguments rule.params)
        (arguments : CostRegionArgumentTreesNormalizationAlignment source
          kernel targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary leftChildren)
          (.neutralApplicationOrdinary membership notBareCollection constructor
            materializes neutral ordinary rightChildren)
    | neutralApplicationQuote
        {available outer : List TypeExpr} {rule : GrammarRule}
        {leftArguments rightArguments : List Pattern}
        (membership : rule ∈ source.costWholeLanguage.terms)
        (notBareCollection : ¬ UsesBareCollection rule)
        (constructor : source.DeclaredCostConstructor)
        (materializes :
          source.materializeDeclaredCostConstructor constructor = rule)
        (neutral :
          source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨
            ∃ kind, source.declaredCostConstructorRole constructor =
              .apparatus kind)
        (quoted : ReflectiveContextSupport.isQuoteConstructor
          source.costWholeLanguage rule.label = true)
        (leftChildren : CostRegionArgumentTrees source targetFree []
          (available ++ outer) leftArguments rule.params)
        (rightChildren : CostRegionArgumentTrees source targetFree []
          (available ++ outer) rightArguments rule.params)
        (arguments : CostRegionArgumentTreesNormalizationAlignment source
          kernel targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted leftChildren)
          (.neutralApplicationQuote membership notBareCollection constructor
            materializes neutral quoted rightChildren)
    | lambda
        {available outer : List TypeExpr} {binder : Option String}
        {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
        (left : CostRegionTree source targetFree (domain :: available) outer
          leftBody codomain)
        (right : CostRegionTree source targetFree (domain :: available) outer
          rightBody codomain)
        (body : CostRegionTreeNormalizationAlignment source kernel
          targetFree left right) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.lambda (binder := binder) left) (.lambda (binder := binder) right)
    | multiLambda
        {available outer : List TypeExpr} {arity : Nat}
        {binders : List String} {leftBody rightBody : Pattern}
        {domain codomain : TypeExpr}
        (left : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer leftBody codomain)
        (right : CostRegionTree source targetFree
          (List.replicate arity domain ++ available) outer rightBody codomain)
        (body : CostRegionTreeNormalizationAlignment source kernel
          targetFree left right) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.multiLambda (arity := arity) (binders := binders) left)
          (.multiLambda (arity := arity) (binders := binders) right)
    | subst
        {available outer : List TypeExpr}
        {leftBody rightBody leftReplacement rightReplacement : Pattern}
        {domain codomain : TypeExpr}
        (leftBodyTree : CostRegionTree source targetFree
          (domain :: available) outer leftBody codomain)
        (rightBodyTree : CostRegionTree source targetFree
          (domain :: available) outer rightBody codomain)
        (leftReplacementTree : CostRegionTree source targetFree available outer
          leftReplacement domain)
        (rightReplacementTree : CostRegionTree source targetFree available
          outer rightReplacement domain)
        (body : CostRegionTreeNormalizationAlignment source kernel
          targetFree leftBodyTree rightBodyTree)
        (replacement : CostRegionTreeNormalizationAlignment source
          kernel targetFree leftReplacementTree rightReplacementTree) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.subst leftBodyTree leftReplacementTree)
          (.subst rightBodyTree rightReplacementTree)
    | collection
        {available outer : List TypeExpr} {collectionType : CollType}
        {leftElements rightElements : List Pattern} {rest : Option String}
        {elementType : TypeExpr}
        (leftChildren : CostRegionElementTrees source targetFree available outer
          leftElements elementType)
        (rightChildren : CostRegionElementTrees source targetFree available
          outer rightElements elementType)
        (elements : CostRegionElementTreesNormalizationAlignment source
          kernel targetFree leftChildren rightChildren) :
        CostRegionTreeNormalizationAlignment source kernel targetFree
          (.collection (collectionType := collectionType) (rest := rest)
            leftChildren)
          (.collection (collectionType := collectionType) (rest := rest)
            rightChildren)

  /-- Positional alignment of one fixed authored constructor's argument
  spine. -/
  inductive CostRegionArgumentTreesNormalizationAlignment
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftArguments rightArguments : List Pattern} →
      {parameters : List TermParam} →
      CostRegionArgumentTrees source targetFree available outer leftArguments
          parameters →
      CostRegionArgumentTrees source targetFree available outer rightArguments
          parameters → Type where
    | nil {available outer : List TypeExpr} :
        CostRegionArgumentTreesNormalizationAlignment source kernel
          targetFree
          (CostRegionArgumentTrees.nil (available := available) (outer := outer))
          (CostRegionArgumentTrees.nil (available := available) (outer := outer))
    | cons
        {available outer : List TypeExpr}
        {leftArgument rightArgument : Pattern}
        {leftArguments rightArguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (leftRepresentation :
          MatchesParameterRepresentation parameter leftArgument)
        (rightRepresentation :
          MatchesParameterRepresentation parameter rightArgument)
        (parameterType : parameterType? parameter = some expected)
        (leftHead : CostRegionTree source targetFree available outer
          leftArgument expected)
        (rightHead : CostRegionTree source targetFree available outer
          rightArgument expected)
        (leftTail : CostRegionArgumentTrees source targetFree available outer
          leftArguments parameters)
        (rightTail : CostRegionArgumentTrees source targetFree available outer
          rightArguments parameters)
        (head : CostRegionTreeNormalizationAlignment source kernel
          targetFree leftHead rightHead)
        (tail : CostRegionArgumentTreesNormalizationAlignment source
          kernel targetFree leftTail rightTail) :
        CostRegionArgumentTreesNormalizationAlignment source kernel
          targetFree
          (.cons leftRepresentation parameterType leftHead leftTail)
          (.cons rightRepresentation parameterType rightHead rightTail)

  /-- Positional alignment of a homogeneous structural collection. -/
  inductive CostRegionElementTreesNormalizationAlignment
      (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext) :
      {available outer : List TypeExpr} →
      {leftElements rightElements : List Pattern} →
      {elementType : TypeExpr} →
      CostRegionElementTrees source targetFree available outer leftElements
          elementType →
      CostRegionElementTrees source targetFree available outer rightElements
          elementType → Type where
    | nil (available outer : List TypeExpr) (elementType : TypeExpr) :
        CostRegionElementTreesNormalizationAlignment source kernel
          targetFree (.nil available outer elementType)
          (.nil available outer elementType)
    | cons
        {available outer : List TypeExpr}
        {leftElement rightElement : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (leftHead : CostRegionTree source targetFree available outer leftElement
          elementType)
        (rightHead : CostRegionTree source targetFree available outer
          rightElement elementType)
        (leftTail : CostRegionElementTrees source targetFree available outer
          leftElements elementType)
        (rightTail : CostRegionElementTrees source targetFree available outer
          rightElements elementType)
        (head : CostRegionTreeNormalizationAlignment source kernel
          targetFree leftHead rightHead)
        (tail : CostRegionElementTreesNormalizationAlignment source
          kernel targetFree leftTail rightTail) :
        CostRegionElementTreesNormalizationAlignment source kernel
          targetFree (.cons leftHead leftTail) (.cons rightHead rightTail)
end

namespace CostRegionRootNormalizationBridge

/-- Forget only the local-root classification while retaining its complete
semantic certificate in the structural alignment relation. -/
def toTreeAlignment
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (bridge : CostRegionRootNormalizationBridge source kernel targetFree
      left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree left right :=
  match bridge with
  | .semanticRoot left right evaluation =>
      .semanticRoot left right evaluation
  | .canonicalAtomRoot left right evaluation =>
      .canonicalAtomRoot left right evaluation
  | .canonicalAtomRestorationRoot left right evaluation =>
      .canonicalAtomRestorationRoot left right evaluation
  | .semanticAtom left right join =>
      .semanticAtom left right join

end CostRegionRootNormalizationBridge

mutual
  /-- Every root-aware semantic alignment yields exact equality of hereditary
  normalized patterns. -/
  theorem CostRegionTreeNormalizationAlignment.normalize_pattern_eq
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (alignment : CostRegionTreeNormalizationAlignment source kernel
        targetFree left right) :
      (left.normalize (normalizeStatic := kernel.normalize)).pattern =
        (right.normalize (normalizeStatic := kernel.normalize)).pattern := by
    cases alignment with
    | refl => rfl
    | semanticRoot left right bridge => exact bridge.results_eq
    | canonicalAtomRoot left right bridge => exact bridge.results_eq
    | canonicalAtomRestorationRoot left right bridge =>
        exact bridge.results_eq
    | semanticAtom left right join => exact join.results_eq
    | neutralApplicationOrdinary membership notBare constructor materializes
        neutral ordinary leftChildren rightChildren arguments =>
        simp only [CostRegionTree.normalize]
        exact congrArg (Pattern.apply _) arguments.normalize_patterns_eq
    | neutralApplicationQuote membership notBare constructor materializes
        neutral quoted leftChildren rightChildren arguments =>
        simp only [CostRegionTree.normalize]
        exact congrArg (Pattern.apply _) arguments.normalize_patterns_eq
    | lambda left right body =>
        simp only [CostRegionTree.normalize]
        exact congrArg (Pattern.lambda _) body.normalize_pattern_eq
    | multiLambda left right body =>
        simp only [CostRegionTree.normalize]
        exact congrArg (Pattern.multiLambda _ _) body.normalize_pattern_eq
    | subst leftBody rightBody leftReplacement rightReplacement body replacement
        =>
        simp only [CostRegionTree.normalize]
        exact congrArg₂ Pattern.subst body.normalize_pattern_eq
          replacement.normalize_pattern_eq
    | collection leftChildren rightChildren elements =>
        simp only [CostRegionTree.normalize]
        exact congrArg (fun patterns => Pattern.collection _ patterns _)
          elements.normalize_patterns_eq

  /-- Argument alignment preserves the complete normalized pattern spine. -/
  theorem CostRegionArgumentTreesNormalizationAlignment.normalize_patterns_eq
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (alignment : CostRegionArgumentTreesNormalizationAlignment source
        kernel targetFree left right) :
      (left.normalize (normalizeStatic := kernel.normalize)).patterns =
        (right.normalize (normalizeStatic := kernel.normalize)).patterns := by
    cases alignment with
    | nil => rfl
    | cons leftRepresentation rightRepresentation parameterType leftHead
        rightHead leftTail rightTail head tail =>
        simp only [CostRegionArgumentTrees.normalize]
        exact congrArg₂ List.cons head.normalize_pattern_eq
          tail.normalize_patterns_eq

  /-- Collection alignment preserves the complete normalized element spine. -/
  theorem CostRegionElementTreesNormalizationAlignment.normalize_patterns_eq
      {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (alignment : CostRegionElementTreesNormalizationAlignment source
        kernel targetFree left right) :
      (left.normalize (normalizeStatic := kernel.normalize)).patterns =
        (right.normalize (normalizeStatic := kernel.normalize)).patterns := by
    cases alignment with
    | nil => rfl
    | cons leftHead rightHead leftTail rightTail head tail =>
        simp only [CostRegionElementTrees.normalize]
        exact congrArg₂ List.cons head.normalize_pattern_eq
          tail.normalize_patterns_eq
end

end Mettapedia.GSLT.LanguageDef
