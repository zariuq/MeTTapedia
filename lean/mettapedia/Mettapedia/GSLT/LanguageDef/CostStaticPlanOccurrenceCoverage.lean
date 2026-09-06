import Mettapedia.GSLT.LanguageDef.CostStaticPlanPairAlignment
import Mettapedia.GSLT.LanguageDef.CostGeneratedOccurrence
import Mettapedia.GSLT.LanguageDef.CostGeneratorHereditaryAlignment
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence

/-!
# Occurrence-tied coverage of changed static sites

The raw candidate carrier `CostStaticPlanGeneratorPairCandidates` stores a
bag of endpoint pairs: it proves neither that its cells belong to the
enclosing generated occurrence nor that the changed sites of that occurrence
are all represented.  This module adds the missing layer.

A changed site is witnessed by a cell together with an explicit localization
context: the site's two argument patterns are the same one-hole context
filled with the cell's two endpoint region patterns.  A `.hole` context is a
skeleton-level cell; a non-trivial context localizes a boundary-content
change, which the respelling falsifier proved can never take a
decoration-level edge and must instead close through a restoration
certificate.  Every changed site also carries the declaration tie: the
cell edge's authored source declaration is exactly the declaration retained
by the enclosing occurrence's origin.

Coverage itself is a per-position classification of one shared constructor
spine: every position is either unchanged — the same region tree on both
endpoints, closed reflexively — or changed, carrying a tied, localized,
closed cell.  Assembly folds the classification through the neutral frame
into a `CostRegionTreeNormalizationAlignment`, and nonemptiness proves that
a syntax-changing occurrence forces at least one changed site.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted

/-- The authored source declaration retained by a generated-Cost occurrence
origin.  This is the declaration *before* the two-colour static image, so a
cell whose edge lives in the source language can be compared against it. -/
def CostAuthoredGeneratorOrigin.sourceDeclaration
    {source : CIGSLT} {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage left right} :
    CostAuthoredGeneratorOrigin source witness →
      SourceGeneratorDeclaration :=
  match witness with
  | .core (.equation _ instanceWitness) =>
      match instanceWitness with
      | .forward _ _ _ _ _ _ _ => fun origin =>
          .equation (CostEquationDeclarationOrigin.sourceEquation origin)
      | .reverse _ _ _ _ _ _ _ => fun origin =>
          .equation (CostEquationDeclarationOrigin.sourceEquation origin)
  | .core (.derived _ lawWitness) => fun _ => .derived lawWitness.rule
  | .reflective _ _ _ => fun origin =>
      .reflective (CostReflectiveDeclarationOrigin.sourceDeclaration origin)

/-- The declaration retained by a typed generated occurrence. -/
def CostTypedGeneratorOccurrence.sourceDeclaration
    {source : CIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort}
    {generator :
      ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound (.base targetSort.1)
        left right}
    (occurrence : CostTypedGeneratorOccurrence source generator) :
    SourceGeneratorDeclaration :=
  occurrence.origin.sourceDeclaration

/-- The root generator witness of an endpoint pair uses exactly the edge's
authored declaration: endpoint-index transport cannot change it. -/
theorem CostStaticPlanContextPair.rootGeneratorWitness_sourceDeclaration
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    {leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries) :
    pair.rootGeneratorWitness.sourceDeclaration =
      edge.generatorWitness.sourceDeclaration := by
  obtain ⟨left, right, leftRoot_eq, rightRoot_eq, leftTable_eq,
    rightTable_eq⟩ := pair
  subst leftRoot_eq
  subst rightRoot_eq
  rfl

/-- A changed static site witnessed by one endpoint-pair cell and an explicit
localization context.  A `.hole` context is a skeleton-level cell; a
non-trivial context localizes a boundary-content change inside an otherwise
unchanged frame.  Nothing here assumes the cell edge equals the enclosing
occurrence — the declaration tie is a separate obligation carried where the
site is used. -/
structure CostChangedSiteWitness (source : CIGSLT)
    (targetFree : FreeTypeContext)
    (leftArgument rightArgument : Pattern) : Type where
  cell : CostStaticPlanSiblingPairCell source targetFree
  context : OneHoleContext
  leftLocal : leftArgument = context.fill cell.first.pattern
  rightLocal : rightArgument = context.fill cell.second.pattern

namespace CostChangedSiteWitness

/-- A localized changed site consumes a certificate for exactly its fixed
context and one semantic relation witness for the selected cell. -/
def patternLeafAlignedWithContext
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {leftArgument rightArgument : Pattern}
    (witness : CostChangedSiteWitness source targetFree leftArgument
      rightArgument)
    {relation : Pattern → Pattern → Prop}
    (fixedContext : PatternLeafAlignedContext relation witness.context)
    (changedLeaf : relation witness.cell.first.pattern
      witness.cell.second.pattern) :
    PatternLeafAligned relation leftArgument rightArgument := by
  cases witness with
  | mk cell context leftLocal rightLocal =>
      cases leftLocal
      cases rightLocal
      exact fixedContext.fill (.leaf changedLeaf)

/-- A localized changed site induces structural alignment outside one
explicit semantic leaf.  This is the exact bridge from occurrence coverage
to restoration-level closure: the localization context is consumed rather
than reasserted as an unrelated frame-equality premise. -/
def patternLeafAligned
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {leftArgument rightArgument : Pattern}
    (witness : CostChangedSiteWitness source targetFree leftArgument
      rightArgument)
    {relation : Pattern → Pattern → Prop}
    (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name))
    (changedLeaf : relation witness.cell.first.pattern
      witness.cell.second.pattern) :
    PatternLeafAligned relation leftArgument rightArgument :=
  witness.patternLeafAlignedWithContext
    (PatternLeafAlignedContext.ofFvarReflexive fvarReflexive witness.context)
    changedLeaf

/-- Restoration equality for one localized changed site lifts through the
shared context recorded by the witness.  Fixed free variables and the one
selected leaf remain separate premises: this prevents a boundary-content
cell from manufacturing agreement for an unrelated occurrence. -/
theorem substituteAt_reifyWith_eq
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {leftArgument rightArgument : Pattern}
    (witness : CostChangedSiteWitness source targetFree leftArgument
      rightArgument)
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftEndpoint))
    (rightResolve : String → Option (Fin rightEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    {relation : Pattern → Pattern → Prop}
    (fixedContext : PatternLeafAlignedContext relation witness.context)
    (changedLeaf : relation witness.cell.first.pattern
      witness.cell.second.pattern)
    (relatedLeavesRestore : ∀ {leftLeaf rightLeaf},
      relation leftLeaf rightLeaf → ∀ leafDepth,
        ReflectiveContextSupport.substituteAt profile support assignment
            leafDepth (cospan.reifyWith leftResolve leftLeg leftLeaf) =
          ReflectiveContextSupport.substituteAt profile support assignment
            leafDepth (cospan.reifyWith rightResolve rightLeg rightLeaf))
    (depth : Nat) :
    ReflectiveContextSupport.substituteAt profile support assignment depth
        (cospan.reifyWith leftResolve leftLeg leftArgument) =
      ReflectiveContextSupport.substituteAt profile support assignment depth
        (cospan.reifyWith rightResolve rightLeg rightArgument) := by
  have aligned : PatternLeafAligned relation leftArgument rightArgument :=
    witness.patternLeafAlignedWithContext fixedContext changedLeaf
  apply cospan.substituteAt_reifyWith_eq_of_patternLeafAligned
    leftResolve rightResolve leftLeg rightLeg profile support assignment
    relatedLeavesRestore aligned depth

end CostChangedSiteWitness

/-- A closed changed site: the localized cell, its declaration tie to the
enclosing occurrence, and the semantic alignment of the two site trees.
The alignment is the honest currency of the hereditary layer: a
skeleton-level cell typically supplies a root certificate, while a
boundary-content cell must route through restoration, as the respelling
falsifier demands. -/
structure CostChangedSiteClosure (source : CIGSLT)
    (kernel : CostStaticNormalizationKernel source)
    (targetFree : FreeTypeContext)
    (occurrenceDeclaration : SourceGeneratorDeclaration)
    {available outer : List TypeExpr}
    {leftArgument rightArgument : Pattern} {expected : TypeExpr}
    (leftTree : CostRegionTree source targetFree available outer leftArgument
      expected)
    (rightTree : CostRegionTree source targetFree available outer
      rightArgument expected) : Type where
  witness : CostChangedSiteWitness source targetFree leftArgument
    rightArgument
  tie : witness.cell.sourceDeclaration = occurrenceDeclaration
  alignment : CostRegionTreeNormalizationAlignment source kernel targetFree
    leftTree rightTree

namespace CostChangedSiteClosure

/-- The cached declaration tie is faithful to the underlying edge.  Clients
may use the cheap cached projection without weakening occurrence identity. -/
theorem edgeDeclaration_eq_occurrence
    {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
    {available outer : List TypeExpr}
    {leftArgument rightArgument : Pattern} {expected : TypeExpr}
    {leftTree : CostRegionTree source targetFree available outer leftArgument
      expected}
    {rightTree : CostRegionTree source targetFree available outer rightArgument
      expected}
    (closure : CostChangedSiteClosure source kernel targetFree
      occurrenceDeclaration leftTree rightTree) :
    closure.witness.cell.edge.generatorWitness.sourceDeclaration =
      occurrenceDeclaration :=
  closure.witness.cell.sourceDeclaration_eq.trans closure.tie

/-- Close a skeleton-level (reached-style) changed site from a root-changing
semantic certificate.  The localization context is the hole: the site's own
patterns are the cell's endpoint region patterns. -/
def ofRootBridge {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
    {available outer : List TypeExpr}
    {leftArgument rightArgument : Pattern} {expected : TypeExpr}
    {leftTree : CostRegionTree source targetFree available outer leftArgument
      expected}
    {rightTree : CostRegionTree source targetFree available outer
      rightArgument expected}
    (witness : CostChangedSiteWitness source targetFree leftArgument
      rightArgument)
    (tie : witness.cell.sourceDeclaration = occurrenceDeclaration)
    (bridge : CostRegionRootNormalizationBridge source kernel targetFree
      leftTree rightTree) :
    CostChangedSiteClosure source kernel targetFree occurrenceDeclaration
      leftTree rightTree where
  witness := witness
  tie := tie
  alignment := bridge.toTreeAlignment

end CostChangedSiteClosure

mutual
  /-- Per-position occurrence classification of one shared constructor
  spine.  Every position is unchanged — the same region tree on both
  endpoints — or changed, carrying a tied, localized, closed cell.  Untouched
  siblings are therefore reflexive by construction rather than by an opaque
  assumption, and coverage is the totality of the classification itself. -/
  inductive CostArgumentSiteClassification (source : CIGSLT)
      (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext)
      (occurrenceDeclaration : SourceGeneratorDeclaration) :
      {available outer : List TypeExpr} →
      {leftArguments rightArguments : List Pattern} →
      {parameters : List TermParam} →
      CostRegionArgumentTrees source targetFree available outer leftArguments
        parameters →
      CostRegionArgumentTrees source targetFree available outer rightArguments
        parameters → Type where
    | nil {available outer : List TypeExpr} :
        CostArgumentSiteClassification source kernel targetFree
          occurrenceDeclaration
          (CostRegionArgumentTrees.nil (available := available)
            (outer := outer))
          (CostRegionArgumentTrees.nil (available := available)
            (outer := outer))
    | unchanged
        {available outer : List TypeExpr} {argument : Pattern}
        {leftArguments rightArguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr}
        (representation : MatchesParameterRepresentation parameter argument)
        (parameterType : parameterType? parameter = some expected)
        (head : CostRegionTree source targetFree available outer argument
          expected)
        {leftTail : CostRegionArgumentTrees source targetFree available outer
          leftArguments parameters}
        {rightTail : CostRegionArgumentTrees source targetFree available outer
          rightArguments parameters}
        (tail : CostArgumentSiteClassification source kernel targetFree
          occurrenceDeclaration leftTail rightTail) :
        CostArgumentSiteClassification source kernel targetFree
          occurrenceDeclaration
          (.cons representation parameterType head leftTail)
          (.cons representation parameterType head rightTail)
    | changed
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
        (closure : CostChangedSiteClosure source kernel targetFree
          occurrenceDeclaration leftHead rightHead)
        {leftTail : CostRegionArgumentTrees source targetFree available outer
          leftArguments parameters}
        {rightTail : CostRegionArgumentTrees source targetFree available outer
          rightArguments parameters}
        (tail : CostArgumentSiteClassification source kernel targetFree
          occurrenceDeclaration leftTail rightTail) :
        CostArgumentSiteClassification source kernel targetFree
          occurrenceDeclaration
          (.cons leftRepresentation parameterType leftHead leftTail)
          (.cons rightRepresentation parameterType rightHead rightTail)
end

mutual
  /-- Per-position occurrence classification of one homogeneous collection
  spine. -/
  inductive CostElementSiteClassification (source : CIGSLT)
      (kernel : CostStaticNormalizationKernel source)
      (targetFree : FreeTypeContext)
      (occurrenceDeclaration : SourceGeneratorDeclaration) :
      {available outer : List TypeExpr} →
      {leftElements rightElements : List Pattern} →
      {elementType : TypeExpr} →
      CostRegionElementTrees source targetFree available outer leftElements
        elementType →
      CostRegionElementTrees source targetFree available outer rightElements
        elementType → Type where
    | nil (available outer : List TypeExpr) (elementType : TypeExpr) :
        CostElementSiteClassification source kernel targetFree
          occurrenceDeclaration (.nil available outer elementType)
          (.nil available outer elementType)
    | unchanged
        {available outer : List TypeExpr} {element : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (head : CostRegionTree source targetFree available outer element
          elementType)
        {leftTail : CostRegionElementTrees source targetFree available outer
          leftElements elementType}
        {rightTail : CostRegionElementTrees source targetFree available outer
          rightElements elementType}
        (tail : CostElementSiteClassification source kernel targetFree
          occurrenceDeclaration leftTail rightTail) :
        CostElementSiteClassification source kernel targetFree
          occurrenceDeclaration (.cons head leftTail) (.cons head rightTail)
    | changed
        {available outer : List TypeExpr}
        {leftElement rightElement : Pattern}
        {leftElements rightElements : List Pattern} {elementType : TypeExpr}
        (leftHead : CostRegionTree source targetFree available outer
          leftElement elementType)
        (rightHead : CostRegionTree source targetFree available outer
          rightElement elementType)
        (closure : CostChangedSiteClosure source kernel targetFree
          occurrenceDeclaration leftHead rightHead)
        {leftTail : CostRegionElementTrees source targetFree available outer
          leftElements elementType}
        {rightTail : CostRegionElementTrees source targetFree available outer
          rightElements elementType}
        (tail : CostElementSiteClassification source kernel targetFree
          occurrenceDeclaration leftTail rightTail) :
        CostElementSiteClassification source kernel targetFree
          occurrenceDeclaration (.cons leftHead leftTail)
          (.cons rightHead rightTail)
end

namespace CostArgumentSiteClassification

/-- Coverage erases to the positional spine alignment: unchanged sites close
reflexively, changed sites close by their carried semantic alignment. -/
def toAlignment {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {leftSpine : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {rightSpine : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters},
      CostArgumentSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine →
      CostRegionArgumentTreesNormalizationAlignment source kernel targetFree
        leftSpine rightSpine
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _,
      .unchanged representation parameterType head tail =>
      .cons representation representation parameterType head head _ _
        (.refl head) tail.toAlignment
  | _, _, _, _, _, _, _,
      .changed leftRepresentation rightRepresentation parameterType leftHead
        rightHead closure tail =>
      .cons leftRepresentation rightRepresentation parameterType leftHead
        rightHead _ _ closure.alignment tail.toAlignment

/-- Number of changed sites recorded by a classification. -/
def changedCount {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {leftSpine : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {rightSpine : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters},
      CostArgumentSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine → Nat
  | _, _, _, _, _, _, _, .nil => 0
  | _, _, _, _, _, _, _, .unchanged _ _ _ tail => tail.changedCount
  | _, _, _, _, _, _, _, .changed _ _ _ _ _ _ tail =>
      tail.changedCount + 1

/-- With no changed site the two argument lists are exactly equal: untouched
siblings really are untouched. -/
theorem arguments_eq_of_changedCount_zero {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {leftSpine : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {rightSpine : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (sites : CostArgumentSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine),
      sites.changedCount = 0 → leftArguments = rightArguments
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, _, _, .unchanged _ _ _ tail, zero => by
      rw [arguments_eq_of_changedCount_zero tail zero]
  | _, _, _, _, _, _, _, .changed _ _ _ _ _ _ tail, zero => by
      simp [changedCount] at zero

/-- A syntax-changing occurrence forces at least one covered changed site:
the classification cannot be empty of cells when the two endpoint argument
lists differ. -/
theorem changedCount_pos_of_arguments_ne {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
    {available outer : List TypeExpr}
    {leftArguments rightArguments : List Pattern}
    {parameters : List TermParam}
    {leftSpine : CostRegionArgumentTrees source targetFree available outer
      leftArguments parameters}
    {rightSpine : CostRegionArgumentTrees source targetFree available outer
      rightArguments parameters}
    (sites : CostArgumentSiteClassification source kernel targetFree
      occurrenceDeclaration leftSpine rightSpine)
    (changed : leftArguments ≠ rightArguments) :
    0 < sites.changedCount := by
  by_contra unchanged
  exact changed (sites.arguments_eq_of_changedCount_zero
    (Nat.eq_zero_of_not_pos unchanged))

end CostArgumentSiteClassification

namespace CostElementSiteClassification

/-- Collection coverage erases to the positional element alignment. -/
def toAlignment {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {leftSpine : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {rightSpine : CostRegionElementTrees source targetFree available outer
        rightElements elementType},
      CostElementSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine →
      CostRegionElementTreesNormalizationAlignment source kernel targetFree
        leftSpine rightSpine
  | _, _, _, _, _, _, _, .nil available outer elementType =>
      .nil available outer elementType
  | _, _, _, _, _, _, _, .unchanged head tail =>
      .cons head head _ _ (.refl head) tail.toAlignment
  | _, _, _, _, _, _, _, .changed leftHead rightHead closure tail =>
      .cons leftHead rightHead _ _ closure.alignment tail.toAlignment

/-- Number of changed collection sites. -/
def changedCount {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {leftSpine : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {rightSpine : CostRegionElementTrees source targetFree available outer
        rightElements elementType},
      CostElementSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine → Nat
  | _, _, _, _, _, _, _, .nil _ _ _ => 0
  | _, _, _, _, _, _, _, .unchanged _ tail => tail.changedCount
  | _, _, _, _, _, _, _, .changed _ _ _ tail => tail.changedCount + 1

/-- With no changed site the two element lists are exactly equal. -/
theorem elements_eq_of_changedCount_zero {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration} :
    ∀ {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {leftSpine : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {rightSpine : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (sites : CostElementSiteClassification source kernel targetFree
        occurrenceDeclaration leftSpine rightSpine),
      sites.changedCount = 0 → leftElements = rightElements
  | _, _, _, _, _, _, _, .nil _ _ _, _ => rfl
  | _, _, _, _, _, _, _, .unchanged _ tail, zero => by
      rw [elements_eq_of_changedCount_zero tail zero]
  | _, _, _, _, _, _, _, .changed _ _ _ tail, zero => by
      simp [changedCount] at zero

end CostElementSiteClassification

/-- Assemble a classified ordinary neutral frame into a hereditary tree
alignment: unchanged siblings close reflexively, changed siblings by their
tied closures. -/
def CostArgumentSiteClassification.assembleNeutralOrdinary {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
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
      source.costWholeReflectionProfile rule.label = false)
    {leftSpine : CostRegionArgumentTrees source targetFree available outer
      leftArguments rule.params}
    {rightSpine : CostRegionArgumentTrees source targetFree available outer
      rightArguments rule.params}
    (sites : CostArgumentSiteClassification source kernel targetFree
      occurrenceDeclaration leftSpine rightSpine) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (.neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary leftSpine)
      (.neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary rightSpine) :=
  .neutralApplicationOrdinary membership notBareCollection constructor
    materializes neutral ordinary leftSpine rightSpine sites.toAlignment

/-- Assemble a classified quote neutral frame. -/
def CostArgumentSiteClassification.assembleNeutralQuote {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
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
      source.costWholeReflectionProfile rule.label = true)
    {leftSpine : CostRegionArgumentTrees source targetFree []
      (available ++ outer) leftArguments rule.params}
    {rightSpine : CostRegionArgumentTrees source targetFree []
      (available ++ outer) rightArguments rule.params}
    (sites : CostArgumentSiteClassification source kernel targetFree
      occurrenceDeclaration leftSpine rightSpine) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (.neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted leftSpine)
      (.neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted rightSpine) :=
  .neutralApplicationQuote membership notBareCollection constructor
    materializes neutral quoted leftSpine rightSpine sites.toAlignment

/-- Assemble a classified structural collection frame. -/
def CostElementSiteClassification.assembleCollection {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {occurrenceDeclaration : SourceGeneratorDeclaration}
    {available outer : List TypeExpr} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    {elementType : TypeExpr}
    {leftSpine : CostRegionElementTrees source targetFree available outer
      leftElements elementType}
    {rightSpine : CostRegionElementTrees source targetFree available outer
      rightElements elementType}
    (sites : CostElementSiteClassification source kernel targetFree
      occurrenceDeclaration leftSpine rightSpine) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (.collection (collectionType := collectionType) (rest := rest)
        leftSpine)
      (.collection (collectionType := collectionType) (rest := rest)
        rightSpine) :=
  .collection leftSpine rightSpine sites.toAlignment

/-- Lift an assembled alignment through a lambda binder frame. -/
def CostRegionTreeNormalizationAlignment.assembleLambda {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {binder : Option String}
    {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
    {left : CostRegionTree source targetFree (domain :: available) outer
      leftBody codomain}
    {right : CostRegionTree source targetFree (domain :: available) outer
      rightBody codomain}
    (body : CostRegionTreeNormalizationAlignment source kernel targetFree
      left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (.lambda (binder := binder) left) (.lambda (binder := binder) right) :=
  .lambda left right body

/-- Lift an assembled alignment through a multi-lambda binder frame. -/
def CostRegionTreeNormalizationAlignment.assembleMultiLambda {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {arity : Nat} {binders : List String}
    {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
    {left : CostRegionTree source targetFree
      (List.replicate arity domain ++ available) outer leftBody codomain}
    {right : CostRegionTree source targetFree
      (List.replicate arity domain ++ available) outer rightBody codomain}
    (body : CostRegionTreeNormalizationAlignment source kernel targetFree
      left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (.multiLambda (arity := arity) (binders := binders) left)
      (.multiLambda (arity := arity) (binders := binders) right) :=
  .multiLambda left right body

/-- Transport a hereditary alignment along type-index equalities on both
endpoints. -/
def CostRegionTreeNormalizationAlignment.reindexTypes {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern}
    {leftFirst leftSecond rightFirst rightSecond : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter
      leftPattern leftFirst}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightFirst}
    (leftEq : leftFirst = leftSecond) (rightEq : rightFirst = rightSecond)
    (alignment : CostRegionTreeNormalizationAlignment source kernel
      targetFree left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.reindexType leftEq) (right.reindexType rightEq) := by
  cases leftEq
  cases rightEq
  exact alignment

/-- Transport a hereditary alignment along pattern-index equalities on both
endpoints.  The transport is the quarantined cast of `reindexPattern`; no
tree or alignment structure changes. -/
def CostRegionTreeNormalizationAlignment.reindexPatterns {source : CIGSLT}
    {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftFirst leftSecond rightFirst rightSecond : Pattern}
    {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter
      leftFirst leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightFirst rightType}
    (leftEq : leftFirst = leftSecond) (rightEq : rightFirst = rightSecond)
    (alignment : CostRegionTreeNormalizationAlignment source kernel
      targetFree left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.reindexPattern leftEq) (right.reindexPattern rightEq) := by
  cases leftEq
  cases rightEq
  exact alignment

/-- Occurrence-tied covered family above the raw pair candidates: one
enclosing typed generated occurrence, one shared neutral frame decomposition
of both endpoint terms, and a total per-site classification whose changed
sites are tied, localized, closed cells.  Coverage is the classification's
totality over the spine; it is not a nonempty-list surrogate. -/
structure CostOccurrenceTiedSpineCoverage (source : CIGSLT)
    (kernel : CostStaticNormalizationKernel source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator :
      ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound (.base targetSort.1)
        left right)
    (occurrence : CostTypedGeneratorOccurrence source generator) : Type where
  rule : GrammarRule
  membership : rule ∈ source.costWholeLanguage.terms
  notBareCollection : ¬ UsesBareCollection rule
  constructor : source.DeclaredCostConstructor
  materializes : source.materializeDeclaredCostConstructor constructor = rule
  neutral : source.declaredCostConstructorRole constructor =
      .interactionPrincipal ∨
    ∃ kind, source.declaredCostConstructorRole constructor = .apparatus kind
  ordinary : ReflectiveContextSupport.isQuoteConstructor
    source.costWholeReflectionProfile rule.label = false
  category_eq : rule.category = targetSort.1
  leftArguments : List Pattern
  rightArguments : List Pattern
  leftPattern_eq : left.1 = .apply rule.label leftArguments
  rightPattern_eq : right.1 = .apply rule.label rightArguments
  leftSpine : CostRegionArgumentTrees source targetFree targetBound []
    leftArguments rule.params
  rightSpine : CostRegionArgumentTrees source targetFree targetBound []
    rightArguments rule.params
  sites : CostArgumentSiteClassification source kernel targetFree
    occurrence.sourceDeclaration leftSpine rightSpine

namespace CostOccurrenceTiedSpineCoverage

variable {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
  {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
  {targetSort : LangSort source.costWholeLanguage}
  {left right : ReflectiveWellSorted.OpenTerm
    source.costWholeReflectionProfile source.costWholeLanguage targetFree
    targetBound targetSort}
  {generator :
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound (.base targetSort.1)
      left right}
  {occurrence : CostTypedGeneratorOccurrence source generator}

/-- The left endpoint elaboration selected by the coverage's neutral frame. -/
def leftTree
    (coverage : CostOccurrenceTiedSpineCoverage source kernel generator
      occurrence) :
    CostRegionTree source targetFree targetBound [] left.1
      (.base targetSort.1) :=
  (((CostRegionTree.neutralApplicationOrdinary coverage.membership
    coverage.notBareCollection coverage.constructor coverage.materializes
    coverage.neutral coverage.ordinary coverage.leftSpine).reindexType
      (congrArg TypeExpr.base coverage.category_eq)).reindexPattern
      coverage.leftPattern_eq.symm)

/-- The right endpoint elaboration selected by the coverage's neutral
frame. -/
def rightTree
    (coverage : CostOccurrenceTiedSpineCoverage source kernel generator
      occurrence) :
    CostRegionTree source targetFree targetBound [] right.1
      (.base targetSort.1) :=
  (((CostRegionTree.neutralApplicationOrdinary coverage.membership
    coverage.notBareCollection coverage.constructor coverage.materializes
    coverage.neutral coverage.ordinary coverage.rightSpine).reindexType
      (congrArg TypeExpr.base coverage.category_eq)).reindexPattern
      coverage.rightPattern_eq.symm)

/-- Coverage assembles into the root-aware hereditary tree alignment of the
two selected endpoint elaborations. -/
def toTreeAlignment
    (coverage : CostOccurrenceTiedSpineCoverage source kernel generator
      occurrence) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      coverage.leftTree coverage.rightTree :=
  CostRegionTreeNormalizationAlignment.reindexPatterns
    coverage.leftPattern_eq.symm coverage.rightPattern_eq.symm
    (CostRegionTreeNormalizationAlignment.reindexTypes
      (congrArg TypeExpr.base coverage.category_eq)
      (congrArg TypeExpr.base coverage.category_eq)
      (coverage.sites.assembleNeutralOrdinary coverage.membership
        coverage.notBareCollection coverage.constructor coverage.materializes
        coverage.neutral coverage.ordinary))

/-- Coverage assembles into the full generator alignment consumed by the
exact-invariance composition theorem. -/
def toGeneratorAlignment
    (coverage : CostOccurrenceTiedSpineCoverage source kernel generator
      occurrence) :
    CostGeneratorTreeNormalizationAlignment source kernel generator where
  occurrence := occurrence.witness
  erasesTo := occurrence.erasesTo
  leftElaboration := ⟨coverage.leftTree⟩
  rightElaboration := ⟨coverage.rightTree⟩
  treeAlignment := coverage.toTreeAlignment

/-- A syntax-changing occurrence cannot be covered without at least one
changed cell: the raw empty candidate list is not coverage. -/
theorem changedCount_pos_of_endpoints_ne
    (coverage : CostOccurrenceTiedSpineCoverage source kernel generator
      occurrence)
    (changed : left.1 ≠ right.1) :
    0 < coverage.sites.changedCount := by
  apply coverage.sites.changedCount_pos_of_arguments_ne
  intro argumentsEq
  apply changed
  rw [coverage.leftPattern_eq, coverage.rightPattern_eq, argumentsEq]

end CostOccurrenceTiedSpineCoverage

end Mettapedia.GSLT.LanguageDef
