import Mettapedia.GSLT.LanguageDef.CostElaboratedCarrier

/-!
# Structural decorations retained by Cost elaboration

`CostRegionTree` is indexed by its compact `Pattern`, which is ideal for
proving checked compilation but awkward for stating transport between two
different compact terms.  This module projects each checked tree to explicit,
nondependent decoration data.  The projection records the structural choices;
it does not parse, typecheck, or admit terms and is therefore not a second
syntax authority.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory

mutual
  /-- Complete structural snapshot of one static-region plan node.  Source and
  target binder fibers, reflective availability, occurrence context, compact
  content, and source type are retained at every recursive node. -/
  inductive CostStaticPlanDecoration (source : CIGSLT) where
    | mk
        (sourceBound targetBound sourceAvailable : List TypeExpr)
        (outer : OneHoleContext) (pattern : Pattern) (sourceType : TypeExpr)
        (boundaries : List CostRegionBoundary)
        (node : CostStaticPlanDecorationNode source) :
        CostStaticPlanDecoration source

  /-- The proof-relevant choice made at one static plan node.  Exact generated
  declarations and collection choices are data; boundary records retain both
  source and target types/supports and the canonical compact content. -/
  inductive CostStaticPlanDecorationNode (source : CIGSLT) where
    | bvar (sourceIndex : Nat)
    | fvar (sourceName : String)
    | boundaryApplication
        (constructor : source.DeclaredCostConstructor)
        (boundary : CostRegionBoundary)
    | application
        (sourceLabel : String)
        (constructor : source.DeclaredCostConstructor)
        (children : List (CostStaticPlanDecoration source))
    | lambda (binder : Option String)
        (body : CostStaticPlanDecoration source)
    | multiLambda (arity : Nat) (binders : List String)
        (body : CostStaticPlanDecoration source)
    | collection (collectionType : CollType) (sourceRest : Option String)
        (choice : CostCollectionTypingChoice)
        (children : List (CostStaticPlanDecoration source))
    | boundaryCollection (collectionType : CollType)
        (oppositeChoice : CostCollectionTypingChoice)
        (boundary : CostRegionBoundary)
end

namespace CostStaticPlanDecoration

def sourceBound {source : CIGSLT} :
    CostStaticPlanDecoration source → List TypeExpr
  | .mk sourceBound _ _ _ _ _ _ _ => sourceBound

def targetBound {source : CIGSLT} :
    CostStaticPlanDecoration source → List TypeExpr
  | .mk _ targetBound _ _ _ _ _ _ => targetBound

def sourceAvailable {source : CIGSLT} :
    CostStaticPlanDecoration source → List TypeExpr
  | .mk _ _ sourceAvailable _ _ _ _ _ => sourceAvailable

def outer {source : CIGSLT} :
    CostStaticPlanDecoration source → OneHoleContext
  | .mk _ _ _ outer _ _ _ _ => outer

def pattern {source : CIGSLT} : CostStaticPlanDecoration source → Pattern
  | .mk _ _ _ _ pattern _ _ _ => pattern

def sourceType {source : CIGSLT} :
    CostStaticPlanDecoration source → TypeExpr
  | .mk _ _ _ _ _ sourceType _ _ => sourceType

def boundaries {source : CIGSLT} :
    CostStaticPlanDecoration source → List CostRegionBoundary
  | .mk _ _ _ _ _ _ boundaries _ => boundaries

end CostStaticPlanDecoration

mutual
  /-- The exact source-language skeleton carried by a decoration.  It is
  derived from the proof-relevant node rather than stored as a second,
  potentially inconsistent copy. -/
  def CostStaticPlanDecoration.abstractPattern {source : CIGSLT} :
      CostStaticPlanDecoration source → Pattern
    | .mk _ _ _ _ _ _ _ node =>
        CostStaticPlanDecorationNode.abstractPattern node

  /-- Source skeleton represented by one proof-relevant plan node. -/
  def CostStaticPlanDecorationNode.abstractPattern {source : CIGSLT} :
      CostStaticPlanDecorationNode source → Pattern
    | .bvar sourceIndex => .bvar sourceIndex
    | .fvar sourceName => .fvar sourceName
    | .boundaryApplication _ boundary =>
        .fvar (costRegionBoundaryVariableName boundary)
    | .application sourceLabel _ children =>
        .apply sourceLabel
          (children.map CostStaticPlanDecoration.abstractPattern)
    | .lambda binder body => .lambda binder body.abstractPattern
    | .multiLambda arity binders body =>
        .multiLambda arity binders body.abstractPattern
    | .collection collectionType sourceRest _ children =>
        .collection collectionType
          (children.map CostStaticPlanDecoration.abstractPattern) sourceRest
    | .boundaryCollection _ _ boundary =>
        .fvar (costRegionBoundaryVariableName boundary)
end

mutual
  /-- Project a checked static plan to the complete structural decoration it
  selected.  Proof fields are proof-irrelevant; their indexed data remain. -/
  def CostStaticRegionPlan.decoration {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      CostStaticPlanDecoration source :=
    .mk sourceBound targetBound sourceAvailable outer pattern sourceType
      (plan.boundaryTable.entries.map fun boundary => boundary.boundary) <|
        match plan with
      | .bvar sourceIndex _ _ _ => .bvar sourceIndex
      | @CostStaticRegionPlan.fvar _ _ _ _ _ _ _ _ name _ _ =>
          .fvar (costRegionSourceVariableName name)
      | .boundaryApplication constructor _ _ certified _ =>
          .boundaryApplication constructor certified.typed.boundary
      | .application constructor _ _ preimage _ children =>
          .application preimage.sourceConstructor.1.label constructor
            children.decorations
      | @CostStaticRegionPlan.lambda _ _ _ _ _ _ _ _ binder _ _ _ bodyPlan =>
          .lambda binder bodyPlan.decoration
      | @CostStaticRegionPlan.multiLambda _ _ _ _ _ _ _ _ arity binders _ _ _
          bodyPlan =>
          .multiLambda arity binders bodyPlan.decoration
      | @CostStaticRegionPlan.collection _ _ _ _ _ _ _ _ collectionType _ rest
          _ choice _ children =>
          .collection collectionType (rest.map costRegionSourceVariableName)
            choice children.decorations
      | @CostStaticRegionPlan.boundaryCollection _ _ _ _ _ _ _ _ collectionType
          _ _ _ _ oppositeChoice _ certified _ =>
          .boundaryCollection collectionType oppositeChoice
            certified.typed.boundary

  /-- Ordered decorations of a checked static application spine. -/
  def CostStaticArgumentPlan.decorations {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters) :
      List (CostStaticPlanDecoration source) :=
    match plan with
    | .nil => []
    | .cons _ _ head tail => head.decoration :: tail.decorations

  /-- Ordered decorations of a checked static homogeneous-collection spine. -/
  def CostStaticElementPlan.decorations {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType) :
      List (CostStaticPlanDecoration source) :=
    match plan with
    | .nil => []
    | .cons head tail => head.decoration :: tail.decorations
end


@[simp]
theorem CostStaticRegionPlan.decoration_sourceBound {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.sourceBound = sourceBound :=
  by cases plan <;> rfl

@[simp]
theorem CostStaticRegionPlan.decoration_targetBound {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.targetBound = targetBound :=
  by cases plan <;> rfl

@[simp]
theorem CostStaticRegionPlan.decoration_sourceAvailable {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.sourceAvailable = sourceAvailable :=
  by cases plan <;> rfl

@[simp]
theorem CostStaticRegionPlan.decoration_outer {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.outer = outer :=
  by cases plan <;> rfl

@[simp]
theorem CostStaticRegionPlan.decoration_pattern {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.pattern = pattern :=
  by cases plan <;> rfl

@[simp]
theorem CostStaticRegionPlan.decoration_sourceType {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.sourceType = sourceType :=
  by cases plan <;> rfl

mutual
  @[simp]
  theorem CostStaticRegionPlan.decoration_abstractPattern {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      plan.decoration.abstractPattern = plan.abstractPattern := by
    cases plan with
    | bvar =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern]
    | fvar =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern]
    | boundaryApplication =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern]
    | application constructor rendered current preimage notBare children =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern,
          CostStaticArgumentPlan.decorations_abstractPatterns]
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern,
          CostStaticRegionPlan.decoration_abstractPattern]
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern,
          CostStaticRegionPlan.decoration_abstractPattern]
    | collection choice selected children =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern,
          CostStaticElementPlan.decorations_abstractPatterns]
    | boundaryCollection =>
        simp [CostStaticRegionPlan.decoration,
          CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern,
          CostStaticRegionPlan.abstractPattern]

  @[simp]
  theorem CostStaticArgumentPlan.decorations_abstractPatterns
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters) :
      plan.decorations.map CostStaticPlanDecoration.abstractPattern =
        plan.abstractPatterns := by
    cases plan with
    | nil => rfl
    | cons representation parameterType head tail =>
        simp [CostStaticArgumentPlan.decorations,
          CostStaticArgumentPlan.abstractPatterns,
          CostStaticRegionPlan.decoration_abstractPattern,
          CostStaticArgumentPlan.decorations_abstractPatterns]

  @[simp]
  theorem CostStaticElementPlan.decorations_abstractPatterns
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType) :
      plan.decorations.map CostStaticPlanDecoration.abstractPattern =
        plan.abstractPatterns := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        simp [CostStaticElementPlan.decorations,
          CostStaticElementPlan.abstractPatterns,
          CostStaticRegionPlan.decoration_abstractPattern,
          CostStaticElementPlan.decorations_abstractPatterns]
end

@[simp]
theorem CostStaticRegionPlan.decoration_boundaries {source : CIGSLT}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.decoration.boundaries =
      (plan.boundaryTable.entries.map fun boundary => boundary.boundary) :=
  by cases plan <;> rfl

/-- Whether an equation-neutral generated application is an ordinary frame or
a reflective quotation frame. -/
inductive CostNeutralFrameKind where
  | ordinary
  | quote
deriving DecidableEq, Repr

mutual
  /-- Nondependent recursive snapshot of one checked Cost region tree.

The compact pattern is retained as an observation alongside the exact typing
fiber; all semantic choices live in `node`. -/
  inductive CostTreeDecoration (source : CIGSLT) where
    | mk (available outer : List TypeExpr) (pattern : Pattern)
        (type : TypeExpr) (node : CostTreeDecorationNode source) :
        CostTreeDecoration source

  /-- Proof-relevant node data erased by compact `Pattern` syntax. -/
  inductive CostTreeDecorationNode (source : CIGSLT) where
    | bvar
    | fvar
    | static (color : CostStaticColor)
        (sourceSort : String)
        (plan : CostStaticPlanDecoration source)
        (boundaries : List (CostRegionBoundary × CostTreeDecoration source))
    | neutralApplication (kind : CostNeutralFrameKind)
        (constructor : source.DeclaredCostConstructor)
        (arguments : List (CostTreeDecoration source))
    | lambda (body : CostTreeDecoration source)
    | multiLambda (body : CostTreeDecoration source)
    | subst (body replacement : CostTreeDecoration source)
    | collection (elements : List (CostTreeDecoration source))
end

namespace CostTreeDecoration

def available {source : CIGSLT} : CostTreeDecoration source → List TypeExpr
  | .mk available _ _ _ _ => available

def outer {source : CIGSLT} : CostTreeDecoration source → List TypeExpr
  | .mk _ outer _ _ _ => outer

def pattern {source : CIGSLT} : CostTreeDecoration source → Pattern
  | .mk _ _ pattern _ _ => pattern

def type {source : CIGSLT} : CostTreeDecoration source → TypeExpr
  | .mk _ _ _ type _ => type

end CostTreeDecoration

mutual
  /-- Forget only proof terms and dependent indices from a checked region
  tree, retaining their complete computational data in a structural snapshot. -/
  def CostRegionTree.decoration {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      CostTreeDecoration source :=
    .mk available outer pattern type <|
      match tree with
      | .bvar _ => .bvar
      | .fvar _ => .fvar
      | @CostRegionTree.static _ _ color _ node children =>
          .static color node.sourceSort.1 node.plan.decoration
            children.decorations
      | .neutralApplicationOrdinary _ _ constructor _ _ _ children =>
          .neutralApplication .ordinary constructor children.decorations
      | .neutralApplicationQuote _ _ constructor _ _ _ children =>
          .neutralApplication .quote constructor children.decorations
      | .lambda bodyTree => .lambda bodyTree.decoration
      | .multiLambda bodyTree => .multiLambda bodyTree.decoration
      | .subst bodyTree replacementTree =>
          .subst bodyTree.decoration replacementTree.decoration
      | .collection children => .collection children.decorations

  /-- Ordered recursive decorations of a neutral constructor's arguments. -/
  def CostRegionArgumentTrees.decorations {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) : List (CostTreeDecoration source) :=
    match trees with
    | .nil => []
    | .cons _ _ head tail => head.decoration :: tail.decorations

  /-- Ordered recursive decorations of a structural collection's elements. -/
  def CostRegionElementTrees.decorations {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer
        elements elementType) : List (CostTreeDecoration source) :=
    match trees with
    | .nil _ _ _ => []
    | .cons head tail => head.decoration :: tail.decorations

  /-- Ordered recursive decorations aligned with the exact finite boundary
  table.  The static plan stores each corresponding typed boundary record. -/
  def CostRegionBoundaryTrees.decorations {source : CIGSLT}
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      List (CostRegionBoundary × CostTreeDecoration source) :=
    match trees with
    | .nil => []
    | @CostRegionBoundaryTrees.cons _ _ _ _ _ boundary _ _ head children =>
        (boundary.boundary, head.decoration) :: children.decorations
end

@[simp]
theorem CostRegionTree.decoration_available {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    tree.decoration.available = available :=
  by cases tree <;> rfl

@[simp]
theorem CostRegionTree.decoration_outer {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    tree.decoration.outer = outer :=
  by cases tree <;> rfl

@[simp]
theorem CostRegionTree.decoration_pattern {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    tree.decoration.pattern = pattern :=
  by cases tree <;> rfl

@[simp]
theorem CostRegionTree.decoration_type {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    tree.decoration.type = type :=
  by cases tree <;> rfl

/-- Extract the complete recursive decoration from an elaborated Cost term. -/
def CostOpenElaboration.decoration {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    CostTreeDecoration source :=
  elaboration.tree.decoration

/-- The complete recursive decoration carried by an intrinsically typed Cost
term. -/
def CostElabTerm.decoration {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    CostTreeDecoration source :=
  term.2.decoration

namespace CIGSLT

/-- Exact structural identity extracted from the complete checked Cost
elaboration.  The eventual semantic lift may transport this decoration along
an authored equation; this identity supplies the strict no-transport baseline
and makes accidental compact collapse testable. -/
def costStructuralDecorationIdentity (source : CIGSLT) :
    ReflectiveOpenElaborationSemantics.Identity
      source.costOpenElaborationCarrier where
  Key := fun _targetFree _targetBound _targetSort => CostTreeDecoration source
  key := CostElabTerm.decoration

/-- Same compact syntax with a different complete Cost decoration is observed
as equal by the compact interface but not by the strict identity-preserving
baseline. -/
theorem compact_but_not_sameCostDecoration (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right)
    (differentDecoration : left.decoration ≠ right.decoration) :
    (source.costOpenElaborationCarrier.compactObservationSetoid
        targetFree targetBound targetSort).r left right ∧
      ¬ (source.costStructuralDecorationIdentity.semantics.relation
        targetFree targetBound targetSort).r left right :=
  source.costStructuralDecorationIdentity.compact_but_not_preserving
    sameErasure differentDecoration

end CIGSLT

end Mettapedia.GSLT.LanguageDef
