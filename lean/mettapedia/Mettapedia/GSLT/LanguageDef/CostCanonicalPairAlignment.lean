import Mettapedia.GSLT.LanguageDef.CostCanonicalStructuralAlignment
import Mettapedia.GSLT.LanguageDef.CostReflectiveRootClassification

/-!
# Paired Cost elaboration under reflective canonical equality

The compact endpoints of a generated reflective step need not choose the
same static decomposition.  The semantic theorem therefore constructs both
proof-relevant region trees together and aligns them hereditarily.  All
structural cases are syntax directed.  The only parameter is the genuinely
semantic case: a pair for which at least one endpoint has a certified static
root shape.

The static premise below is a declaration-derived root certificate, not a
normalization law and not the desired alignment restated without content.
Concrete languages must still construct the restoration bridge for every
such pair.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted
open ReflectionExtension

/-- Compact-syntax evidence that one endpoint must be elaborated as a static
region.  Applications retain the decoded declaration and its exact colour;
a collection is static precisely in a base result fibre. -/
inductive CostStaticRootShape (source : CIGSLT) :
    Pattern → TypeExpr → Prop where
  | application {wireName : String} {arguments : List Pattern}
      {category : String} (color : CostStaticColor)
      (constructor : source.DeclaredCostConstructor)
      (decoded : source.decodeDeclaredCostConstructor wireName =
        some constructor)
      (role : source.declaredCostConstructorRole constructor = .static color) :
      CostStaticRootShape source (.apply wireName arguments) (.base category)
  | baseCollection {collectionType : CollType} {elements : List Pattern}
      {rest : Option String} {category : String} :
      CostStaticRootShape source
        (.collection collectionType elements rest) (.base category)

/-- A collapsing root for one generated static image has a certified static
shape before any planner is run. -/
theorem CostStaticRootShape.of_costStatic_collapsingRoot
    (source : CIGSLT) (declarationColor : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.reflection.1.presentations)
    {pattern : Pattern} {category : String}
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl source declarationColor declaration)
      pattern) :
    CostStaticRootShape source pattern (.base category) := by
  rcases collapsing with ⟨arguments, patternEq⟩ | ⟨elements, patternEq⟩
  · have wrapped :=
      (source.reflectivePresentationsRetypable declaration membership
        ).constructorLabels_mem_wrapped.1
    have staticDecoded :=
      decodeDeclaredCostStaticConstructor_symbols_of_wrappedLabel source
        declarationColor declaration.quoteConstructor wrapped
    obtain ⟨constructor, decoded, role⟩ :=
      exists_declaredCostConstructor_of_static_decode source declarationColor
        ((declarationColor.symbols source).constructor
          declaration.quoteConstructor)
        declaration.quoteConstructor staticDecoded
    have mappedQuote :
        (costStaticReflectivePresentationDecl source declarationColor
          declaration).quoteConstructor =
          (declarationColor.symbols source).constructor
            declaration.quoteConstructor := by
      simp [costStaticReflectivePresentationDecl_eq_map,
        mapReflectivePresentation]
    rw [mappedQuote] at patternEq
    subst pattern
    exact .application declarationColor constructor decoded role
  · subst pattern
    exact .baseCollection

/-- A compact static-shape certificate recovers the exact static colour
retained by any proof-relevant tree at that index. -/
theorem CostStaticRootShape.nonempty_staticRootColor
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (shape : CostStaticRootShape source pattern type)
    (tree : CostRegionTree source targetFree available outer pattern type) :
    Nonempty (Σ color,
      CostRegionTree.StaticRootColor source targetFree tree color) := by
  cases shape with
  | application color constructor decoded role =>
      rcases tree.nonempty_staticRootColor_of_static_application_of_eq rfl rfl
          color constructor decoded role with ⟨root⟩
      exact ⟨⟨color, root⟩⟩
  | baseCollection =>
      exact tree.nonempty_staticRootColor_of_base_collection

/-- Boolean reflection of `CostStaticRootShape.nonempty_staticRootColor`. -/
theorem CostStaticRootShape.rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (shape : CostStaticRootShape source pattern type)
    (tree : CostRegionTree source targetFree available outer pattern type) :
    tree.rootIsStatic = true := by
  rcases shape.nonempty_staticRootColor tree with ⟨⟨color, root⟩⟩
  exact root.rootIsStatic

/-- Every retained static tree exposes the declaration-derived compact root
shape that made the planner stop at that root.  This is the converse of
`CostStaticRootShape.rootIsStatic` on proof-relevant trees; it does not rerun
the planner or choose a colour from syntax. -/
theorem CostRegionTree.staticRootShape_of_rootIsStatic
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (static : tree.rootIsStatic = true) :
    CostStaticRootShape source pattern type := by
  cases tree with
  | bvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | fvar lookup => simp [CostRegionTree.rootIsStatic] at static
  | static node children =>
      rcases node.plan.pattern_shape_of_isStaticRoot node.rootStatic with
          ⟨wireName, arguments, shape⟩ |
          ⟨collectionType, elements, rest, shape⟩
      · obtain ⟨constructor, decoded, role⟩ :=
          node.plan.application_dispatch_of_isStaticRoot node.rootStatic shape
        rw [shape]
        exact .application _ constructor decoded role
      · rw [shape]
        exact .baseCollection
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      simp [CostRegionTree.rootIsStatic] at static
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      simp [CostRegionTree.rootIsStatic] at static
  | lambda body => simp [CostRegionTree.rootIsStatic] at static
  | multiLambda body => simp [CostRegionTree.rootIsStatic] at static
  | subst body replacement => simp [CostRegionTree.rootIsStatic] at static
  | collection children => simp [CostRegionTree.rootIsStatic] at static

/-- Away from the two collapsing reflective roots, structural root agreement
transports a static-root shape to the other endpoint.  In particular, an
aligned application retains the same decoded declaration and static colour,
while an aligned collection stays in the same base result fibre. -/
theorem CostStaticRootShape.of_canonicalRootAligned
    {source : CIGSLT} {declaration : ReflectivePresentationDecl}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (shape : CostStaticRootShape source leftPattern type)
    (aligned : CanonicalRootAligned declaration leftPattern rightPattern) :
    CostStaticRootShape source rightPattern type := by
  cases shape with
  | application color constructor decoded role =>
      cases aligned with
      | apply ne children => exact .application color constructor decoded role
  | baseCollection =>
      cases aligned with
      | collection ne children => exact .baseCollection
      | collectionRest collectionType rest children => exact .baseCollection

/-- A non-collapsing canonical root alignment cannot turn a retained static
tree into a structural tree. -/
theorem CostRegionTree.rootIsStatic_of_canonicalRootAligned
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr} {declaration : ReflectivePresentationDecl}
    (left : CostRegionTree source targetFree available outer leftPattern type)
    (right : CostRegionTree source targetFree available outer rightPattern type)
    (leftStatic : left.rootIsStatic = true)
    (aligned : CanonicalRootAligned declaration leftPattern rightPattern) :
    right.rootIsStatic = true :=
  (left.staticRootShape_of_rootIsStatic leftStatic
    ).of_canonicalRootAligned aligned |>.rootIsStatic right

/-- Two proof-relevant trees for one typed canonical pair, together with the
hereditary alignment that makes their normalized compact patterns equal. -/
structure CostCanonicalPairElaboration
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (targetFree : FreeTypeContext) (available outer : List TypeExpr)
    (leftPattern rightPattern : Pattern) (type : TypeExpr) where
  leftTree : CostRegionTree source targetFree available outer leftPattern type
  rightTree : CostRegionTree source targetFree available outer rightPattern type
  alignment : CostRegionTreeNormalizationAlignment source kernel targetFree
    leftTree rightTree

/-- Paired elaboration of one authored constructor's arguments. -/
structure CostCanonicalArgumentPairElaboration
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (targetFree : FreeTypeContext) (available outer : List TypeExpr)
    (leftArguments rightArguments : List Pattern)
    (parameters : List TermParam) where
  leftTrees : CostRegionArgumentTrees source targetFree available outer
    leftArguments parameters
  rightTrees : CostRegionArgumentTrees source targetFree available outer
    rightArguments parameters
  alignment : CostRegionArgumentTreesNormalizationAlignment source kernel
    targetFree leftTrees rightTrees

/-- Paired elaboration of homogeneous collection elements. -/
structure CostCanonicalElementPairElaboration
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (targetFree : FreeTypeContext) (available outer : List TypeExpr)
    (leftElements rightElements : List Pattern) (elementType : TypeExpr) where
  leftTrees : CostRegionElementTrees source targetFree available outer
    leftElements elementType
  rightTrees : CostRegionElementTrees source targetFree available outer
    rightElements elementType
  alignment : CostRegionElementTreesNormalizationAlignment source kernel
    targetFree leftTrees rightTrees

/-- The sole semantic parameter of paired elaboration: close a canonical pair
when declaration-derived evidence places at least one endpoint at a static
root.  The premise is strictly narrower than arbitrary canonical equality. -/
def CostCanonicalStaticPairClosed
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
      leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
      rightPattern →
    canonicalize declaration leftPattern = canonicalize declaration rightPattern →
    (CostStaticRootShape source leftPattern type ∨
      CostStaticRootShape source rightPattern type) →
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type)

/-- Local closure obligation for the two root-changing forms of reflective
canonicalization: quote/drop absorption and bare-parallel collapse.

This is deliberately separate from `CostCanonicalStaticPairClosed`.  A
non-collapsing static constructor still needs the latter, while a collapsing
root can occur at a non-base collection type in a general language and cannot
be mislabeled as a static region.  Concrete Cost languages may prove that
their reachable collapsing roots are static, but the generic recursion does
not assume it. -/
def CostCanonicalCollapsingPairClosed
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
      leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
      rightPattern →
    canonicalize declaration leftPattern = canonicalize declaration rightPattern →
    (CollapsingRoot declaration leftPattern ∨
      CollapsingRoot declaration rightPattern) →
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type)

/-- Root-bridge formulation of the static obligation.  This is the natural
interface for restoration proofs: the executable compiler supplies endpoint
trees, while the language-specific theorem supplies one of the finite
semantic-atom bridge constructors. -/
def CostCanonicalStaticRootBridgeClosed
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (leftTree : CostRegionTree source targetFree available outer leftPattern type)
    (rightTree : CostRegionTree source targetFree available outer rightPattern type),
    ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
        leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
        rightPattern →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      (CostStaticRootShape source leftPattern type ∨
        CostStaticRootShape source rightPattern type) →
      Nonempty (CostRegionRootNormalizationBridge source kernel targetFree
        leftTree rightTree)

/-- A root-bridge closure discharges paired static elaboration.  Endpoint
trees come from the already-proved total executable compiler; no chooser or
bridge is synthesized by classical choice. -/
theorem CostCanonicalStaticRootBridgeClosed.toPairClosed
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {declaration : ReflectivePresentationDecl}
    (rootClosed : CostCanonicalStaticRootBridgeClosed source kernel declaration) :
    CostCanonicalStaticPairClosed source kernel declaration := by
  intro targetFree available outer leftPattern rightPattern type
    leftWellSorted rightWellSorted canonical staticShape
  let leftResult := CostRegionTree.build? (source := source)
    (targetFree := targetFree) available outer leftPattern type
  let rightResult := CostRegionTree.build? (source := source)
    (targetFree := targetFree) available outer rightPattern type
  have leftSome : leftResult.isSome = true := by
    exact CostRegionTree.build?_isSome_of_wellSorted leftWellSorted
  have rightSome : rightResult.isSome = true := by
    exact CostRegionTree.build?_isSome_of_wellSorted rightWellSorted
  let leftTree := leftResult.get leftSome
  let rightTree := rightResult.get rightSome
  obtain ⟨bridge⟩ := rootClosed leftTree rightTree leftWellSorted
    rightWellSorted canonical staticShape
  exact ⟨⟨leftTree, rightTree, bridge.toTreeAlignment⟩⟩

/-- Forget a paired elaboration down to exact equality of its hereditary
normalized compact patterns. -/
theorem CostCanonicalPairElaboration.normalize_pattern_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (pair : CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) :
    (pair.leftTree.normalize
      (normalizeStatic := kernel.normalize)).pattern =
      (pair.rightTree.normalize
        (normalizeStatic := kernel.normalize)).pattern :=
  pair.alignment.normalize_pattern_eq

/-- Build paired argument forests from the exact child certificates of an
authored rule.  This is the proof-relevant analogue of the single-endpoint
compiler's argument-spine totality theorem. -/
theorem CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl) (parent : Pattern)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          leftPattern →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          rightPattern →
        canonicalize declaration leftPattern = canonicalize declaration rightPattern →
        sizeOf leftPattern < sizeOf parent →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          available outer leftPattern rightPattern type)) :
    ∀ {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam},
      ArgumentsHaveTypes source.costWholeLanguage targetFree available
          leftArguments parameters →
      ArgumentsHaveTypes source.costWholeLanguage targetFree available
          rightArguments parameters →
      Pattern.hasCanonicalBinderMetadataList leftArguments = true →
      Pattern.hasCanonicalBinderMetadataList rightArguments = true →
      isObjectPatternList leftArguments = true →
      isObjectPatternList rightArguments = true →
      (∀ presentation ∈ source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          leftArguments = true) →
      (∀ presentation ∈ source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          rightArguments = true) →
      (∀ argument ∈ leftArguments, sizeOf argument < sizeOf parent) →
      List.Forall₂ (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
        leftArguments rightArguments →
      Nonempty (CostCanonicalArgumentPairElaboration source kernel targetFree
        available outer leftArguments rightArguments parameters) := by
  intro available outer leftArguments rightArguments parameters leftTyped
    rightTyped leftCanonical rightCanonical leftObjects rightObjects leftScope
    rightScope leftArgumentsSmaller canonical
  induction canonical generalizing parameters with
  | nil =>
      cases leftTyped
      cases rightTyped
      exact ⟨⟨.nil, .nil, .nil⟩⟩
  | @cons leftArgument rightArgument leftArguments rightArguments headCanonical
      tailCanonical inductionHypothesis =>
      cases leftTyped with
      | @cons _ _ _ leftParameter leftParameters leftExpected
          leftRepresentation leftParameterType leftHeadTyped leftTailTyped =>
          cases rightTyped with
          | @cons _ _ _ rightParameter rightParameters rightExpected
              rightRepresentation rightParameterType rightHeadTyped
              rightTailTyped =>
              have expectedEq : rightExpected = leftExpected :=
                Option.some.inj (rightParameterType.symm.trans leftParameterType)
              subst rightExpected
              have leftCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadataList] using
                  leftCanonical :
                    leftArgument.hasCanonicalBinderMetadata = true ∧
                      Pattern.hasCanonicalBinderMetadataList leftArguments = true)
              have rightCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadataList] using
                  rightCanonical :
                    rightArgument.hasCanonicalBinderMetadata = true ∧
                      Pattern.hasCanonicalBinderMetadataList rightArguments = true)
              have leftObjectParts := (by
                simpa [isObjectPatternList] using leftObjects :
                  isObjectPattern leftArgument = true ∧
                    isObjectPatternList leftArguments = true)
              have rightObjectParts := (by
                simpa [isObjectPatternList] using rightObjects :
                  isObjectPattern rightArgument = true ∧
                    isObjectPatternList rightArguments = true)
              have leftHeadScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile available.length leftArgument := by
                intro presentation membership
                have spine := leftScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.1
              have rightHeadScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile available.length rightArgument := by
                intro presentation membership
                have spine := rightScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.1
              have leftTailScope : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    available.length leftArguments = true := by
                intro presentation membership
                have spine := leftScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.2
              have rightTailScope : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    available.length rightArguments = true := by
                intro presentation membership
                have spine := rightScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.2
              obtain ⟨headPair⟩ := alignChild
                ⟨⟨leftHeadTyped, leftCanonicalParts.1, leftObjectParts.1,
                    leftHeadTyped.isWellScopedAt⟩, leftHeadScope⟩
                ⟨⟨rightHeadTyped, rightCanonicalParts.1, rightObjectParts.1,
                    rightHeadTyped.isWellScopedAt⟩, rightHeadScope⟩ headCanonical
                (leftArgumentsSmaller leftArgument (by simp))
              obtain ⟨tailPair⟩ := inductionHypothesis leftTailTyped
                rightTailTyped leftCanonicalParts.2 rightCanonicalParts.2
                leftObjectParts.2 rightObjectParts.2 leftTailScope
                rightTailScope (by
                  intro argument membership
                  exact leftArgumentsSmaller argument (by simp [membership]))
              let leftTrees := CostRegionArgumentTrees.cons leftRepresentation
                leftParameterType headPair.leftTree tailPair.leftTrees
              let rightTrees := CostRegionArgumentTrees.cons rightRepresentation
                leftParameterType headPair.rightTree tailPair.rightTrees
              exact ⟨⟨leftTrees, rightTrees,
                .cons leftRepresentation rightRepresentation leftParameterType
                  headPair.leftTree headPair.rightTree tailPair.leftTrees
                  tailPair.rightTrees headPair.alignment tailPair.alignment⟩⟩

/-- Homogeneous-collection companion to paired argument totality. -/
theorem CostCanonicalElementPairElaboration.nonempty_of_wellSorted
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl) (parent : Pattern)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          leftPattern →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          rightPattern →
        canonicalize declaration leftPattern = canonicalize declaration rightPattern →
        sizeOf leftPattern < sizeOf parent →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          available outer leftPattern rightPattern type)) :
    ∀ {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr},
      ElementsHaveType source.costWholeLanguage targetFree available
          leftElements elementType →
      ElementsHaveType source.costWholeLanguage targetFree available
          rightElements elementType →
      Pattern.hasCanonicalBinderMetadataList leftElements = true →
      Pattern.hasCanonicalBinderMetadataList rightElements = true →
      isObjectPatternList leftElements = true →
      isObjectPatternList rightElements = true →
      (∀ presentation ∈ source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          leftElements = true) →
      (∀ presentation ∈ source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          rightElements = true) →
      (∀ element ∈ leftElements, sizeOf element < sizeOf parent) →
      List.Forall₂ (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
        leftElements rightElements →
      Nonempty (CostCanonicalElementPairElaboration source kernel targetFree
        available outer leftElements rightElements elementType) := by
  intro available outer leftElements rightElements elementType leftTyped
    rightTyped leftCanonical rightCanonical leftObjects rightObjects leftScope
    rightScope leftElementsSmaller canonical
  induction canonical generalizing elementType with
  | nil =>
      exact ⟨⟨.nil available outer elementType, .nil available outer elementType,
        .nil available outer elementType⟩⟩
  | @cons leftElement rightElement leftElements rightElements headCanonical
      tailCanonical inductionHypothesis =>
      cases leftTyped with
      | cons leftHeadTyped leftTailTyped =>
          cases rightTyped with
          | cons rightHeadTyped rightTailTyped =>
              have leftCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadataList] using
                  leftCanonical :
                    leftElement.hasCanonicalBinderMetadata = true ∧
                      Pattern.hasCanonicalBinderMetadataList leftElements = true)
              have rightCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadataList] using
                  rightCanonical :
                    rightElement.hasCanonicalBinderMetadata = true ∧
                      Pattern.hasCanonicalBinderMetadataList rightElements = true)
              have leftObjectParts := (by
                simpa [isObjectPatternList] using leftObjects :
                  isObjectPattern leftElement = true ∧
                    isObjectPatternList leftElements = true)
              have rightObjectParts := (by
                simpa [isObjectPatternList] using rightObjects :
                  isObjectPattern rightElement = true ∧
                    isObjectPatternList rightElements = true)
              have leftHeadScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile available.length leftElement := by
                intro presentation membership
                have spine := leftScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.1
              have rightHeadScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile available.length rightElement := by
                intro presentation membership
                have spine := rightScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.1
              have leftTailScope : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    available.length leftElements = true := by
                intro presentation membership
                have spine := leftScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.2
              have rightTailScope : ∀ presentation ∈
                  source.costWholeReflectionProfile.presentations,
                  binderSafeListAt presentation.quoteConstructor
                    available.length rightElements = true := by
                intro presentation membership
                have spine := rightScope presentation membership
                simp only [binderSafeListAt, Bool.and_eq_true] at spine
                exact spine.2
              obtain ⟨headPair⟩ := alignChild
                ⟨⟨leftHeadTyped, leftCanonicalParts.1, leftObjectParts.1,
                    leftHeadTyped.isWellScopedAt⟩, leftHeadScope⟩
                ⟨⟨rightHeadTyped, rightCanonicalParts.1, rightObjectParts.1,
                    rightHeadTyped.isWellScopedAt⟩, rightHeadScope⟩ headCanonical
                (leftElementsSmaller leftElement (by simp))
              obtain ⟨tailPair⟩ := inductionHypothesis leftTailTyped
                rightTailTyped leftCanonicalParts.2 rightCanonicalParts.2
                leftObjectParts.2 rightObjectParts.2 leftTailScope
                rightTailScope (by
                  intro element membership
                  exact leftElementsSmaller element (by simp [membership]))
              exact ⟨⟨.cons headPair.leftTree tailPair.leftTrees,
                .cons headPair.rightTree tailPair.rightTrees,
                .cons headPair.leftTree headPair.rightTree tailPair.leftTrees
                  tailPair.rightTrees headPair.alignment tailPair.alignment⟩⟩

/-- One non-collapsing canonical layer elaborates structurally, delegating
only declaration-certified static roots to the restoration closure.  Child
canonical pairs are supplied recursively by the caller. -/
theorem CostCanonicalPairElaboration.nonempty_of_aligned
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (staticClosed : CostCanonicalStaticPairClosed source kernel declaration)
    (alignChild : ∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType rightChild →
        canonicalize declaration leftChild = canonicalize declaration rightChild →
        sizeOf leftChild < sizeOf leftPattern →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          childAvailable childOuter leftChild rightChild childType))
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize declaration leftPattern =
      canonicalize declaration rightPattern)
    (aligned : CanonicalRootAligned declaration leftPattern rightPattern) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) := by
  cases aligned with
  | bvar index =>
      cases leftWellSorted.1.1 with
      | bvar lookup =>
          have inside : index < available.length :=
            (List.getElem?_eq_some_iff.mp lookup).1
          have extendedLookup : (available ++ outer)[index]? = some type := by
            simpa [List.getElem?_append_left inside] using lookup
          let tree : CostRegionTree source targetFree available outer
              (.bvar index) type := .bvar extendedLookup
          exact ⟨⟨tree, tree, .refl tree⟩⟩
  | fvar name =>
      cases leftWellSorted.1.1 with
      | fvar lookup =>
          let tree : CostRegionTree source targetFree available outer
              (.fvar name) type := .fvar lookup
          exact ⟨⟨tree, tree, .refl tree⟩⟩
  | @apply constructorLabel ne leftArguments rightArguments childrenCanonical =>
      obtain ⟨rule, membership, labelEq, notBare, typeEq, leftArgumentsTyped,
          rightArgumentsTyped⟩ :=
        hasType_apply_pair source.costWholeLanguage_labelDeterministic
          leftWellSorted.1.1 rightWellSorted.1.1
      subst constructorLabel
      subst type
      have coreMembership : rule ∈ source.costCoreLanguage.terms := by
        simpa only [source.costWholeLanguage_terms] using membership
      obtain ⟨constructor, materializes⟩ :=
        source.exists_declaredCostConstructor_of_mem rule coreMembership
      have canonicalLeft :
          Pattern.hasCanonicalBinderMetadataList leftArguments = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using leftWellSorted.1.2.1
      have canonicalRight :
          Pattern.hasCanonicalBinderMetadataList rightArguments = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using rightWellSorted.1.2.1
      have objectsLeft : isObjectPatternList leftArguments = true := by
        simpa [isObjectPattern] using leftWellSorted.1.2.2.1
      have objectsRight : isObjectPatternList rightArguments = true := by
        simpa [isObjectPattern] using rightWellSorted.1.2.2.1
      cases role : source.declaredCostConstructorRole constructor with
      | static color =>
          exact staticClosed leftWellSorted rightWellSorted canonical
            (Or.inl (.application color constructor (by
              rw [← materializes,
                source.materializeDeclaredCostConstructor_label constructor]
              exact source.decodeDeclaredCostConstructor_render constructor)
              role))
      | interactionPrincipal =>
          have neutral : source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨ ∃ kind,
                source.declaredCostConstructorRole constructor =
                  .apparatus kind := Or.inl role
          by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = true
          · have leftAtZero :=
              isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightAtZero :=
              isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    rightArgumentsTyped
                  quoted rightWellSorted.2
            have leftTypedAtZero : ArgumentsHaveTypes
                source.costWholeLanguage targetFree [] leftArguments
                  rule.params := by
              simpa using leftArgumentsTyped.restrictOuterOfScoped
                (inner := []) (outer := available) leftAtZero
            have rightTypedAtZero : ArgumentsHaveTypes
                source.costWholeLanguage targetFree [] rightArguments
                  rule.params := by
              simpa using rightArgumentsTyped.restrictOuterOfScoped
                (inner := []) (outer := available) rightAtZero
            have leftReflectiveAtZero :=
              reflectiveScopeSafeListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightReflectiveAtZero :=
              reflectiveScopeSafeListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    rightArgumentsTyped
                  quoted rightWellSorted.2
            obtain ⟨argumentPair⟩ :=
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted
                (available := []) (outer := available ++ outer)
                declaration (.apply rule.label leftArguments) alignChild
                  leftTypedAtZero rightTypedAtZero
                  canonicalLeft canonicalRight objectsLeft objectsRight
                  leftReflectiveAtZero rightReflectiveAtZero (by
                    intro argument membership
                    have argumentBound := List.sizeOf_lt_of_mem membership
                    simp_wf
                    omega) childrenCanonical
            let leftTree := CostRegionTree.neutralApplicationQuote membership
              notBare constructor materializes neutral quoted
                argumentPair.leftTrees
            let rightTree := CostRegionTree.neutralApplicationQuote membership
              notBare constructor materializes neutral quoted
                argumentPair.rightTrees
            exact ⟨⟨leftTree, rightTree,
              .neutralApplicationQuote membership notBare constructor
                materializes neutral quoted argumentPair.leftTrees
                  argumentPair.rightTrees argumentPair.alignment⟩⟩
          · have ordinary : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = false :=
              Bool.eq_false_of_not_eq_true quoted
            have leftReflective :=
              reflectiveScopeSafeListAt_of_nonquote ordinary
                leftWellSorted.2
            have rightReflective :=
              reflectiveScopeSafeListAt_of_nonquote ordinary
                rightWellSorted.2
            obtain ⟨argumentPair⟩ :=
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted
                (available := available) (outer := outer)
                declaration (.apply rule.label leftArguments) alignChild
                  leftArgumentsTyped rightArgumentsTyped
                  canonicalLeft canonicalRight objectsLeft objectsRight
                  leftReflective rightReflective (by
                    intro argument membership
                    have argumentBound := List.sizeOf_lt_of_mem membership
                    simp_wf
                    omega) childrenCanonical
            let leftTree := CostRegionTree.neutralApplicationOrdinary membership
              notBare constructor materializes neutral ordinary
                argumentPair.leftTrees
            let rightTree := CostRegionTree.neutralApplicationOrdinary membership
              notBare constructor materializes neutral ordinary
                argumentPair.rightTrees
            exact ⟨⟨leftTree, rightTree,
              .neutralApplicationOrdinary membership notBare constructor
                materializes neutral ordinary argumentPair.leftTrees
                  argumentPair.rightTrees argumentPair.alignment⟩⟩
      | apparatus kind =>
          have neutral : source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨ ∃ actualKind,
                source.declaredCostConstructorRole constructor =
                  .apparatus actualKind := Or.inr ⟨kind, role⟩
          by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = true
          · have leftAtZero :=
              isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightAtZero :=
              isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    rightArgumentsTyped
                  quoted rightWellSorted.2
            have leftTypedAtZero : ArgumentsHaveTypes
                source.costWholeLanguage targetFree [] leftArguments
                  rule.params := by
              simpa using leftArgumentsTyped.restrictOuterOfScoped
                (inner := []) (outer := available) leftAtZero
            have rightTypedAtZero : ArgumentsHaveTypes
                source.costWholeLanguage targetFree [] rightArguments
                  rule.params := by
              simpa using rightArgumentsTyped.restrictOuterOfScoped
                (inner := []) (outer := available) rightAtZero
            have leftReflectiveAtZero :=
              reflectiveScopeSafeListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightReflectiveAtZero :=
              reflectiveScopeSafeListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    rightArgumentsTyped
                  quoted rightWellSorted.2
            obtain ⟨argumentPair⟩ :=
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted
                (available := []) (outer := available ++ outer)
                declaration (.apply rule.label leftArguments) alignChild
                  leftTypedAtZero rightTypedAtZero
                  canonicalLeft canonicalRight objectsLeft objectsRight
                  leftReflectiveAtZero rightReflectiveAtZero (by
                    intro argument membership
                    have argumentBound := List.sizeOf_lt_of_mem membership
                    simp_wf
                    omega) childrenCanonical
            let leftTree := CostRegionTree.neutralApplicationQuote membership
              notBare constructor materializes neutral quoted
                argumentPair.leftTrees
            let rightTree := CostRegionTree.neutralApplicationQuote membership
              notBare constructor materializes neutral quoted
                argumentPair.rightTrees
            exact ⟨⟨leftTree, rightTree,
              .neutralApplicationQuote membership notBare constructor
                materializes neutral quoted argumentPair.leftTrees
                  argumentPair.rightTrees argumentPair.alignment⟩⟩
          · have ordinary : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = false :=
              Bool.eq_false_of_not_eq_true quoted
            have leftReflective :=
              reflectiveScopeSafeListAt_of_nonquote ordinary
                leftWellSorted.2
            have rightReflective :=
              reflectiveScopeSafeListAt_of_nonquote ordinary
                rightWellSorted.2
            obtain ⟨argumentPair⟩ :=
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted
                (available := available) (outer := outer)
                declaration (.apply rule.label leftArguments) alignChild
                  leftArgumentsTyped rightArgumentsTyped
                  canonicalLeft canonicalRight objectsLeft objectsRight
                  leftReflective rightReflective (by
                    intro argument membership
                    have argumentBound := List.sizeOf_lt_of_mem membership
                    simp_wf
                    omega) childrenCanonical
            let leftTree := CostRegionTree.neutralApplicationOrdinary membership
              notBare constructor materializes neutral ordinary
                argumentPair.leftTrees
            let rightTree := CostRegionTree.neutralApplicationOrdinary membership
              notBare constructor materializes neutral ordinary
                argumentPair.rightTrees
            exact ⟨⟨leftTree, rightTree,
              .neutralApplicationOrdinary membership notBare constructor
                materializes neutral ordinary argumentPair.leftTrees
                  argumentPair.rightTrees argumentPair.alignment⟩⟩
  | @lambda binder leftBody rightBody bodyCanonical =>
      cases leftWellSorted.1.1 with
      | lambda leftBodyTyped =>
          cases rightWellSorted.1.1 with
          | lambda rightBodyTyped =>
              rename_i domain codomain
              have leftCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftWellSorted.1.2.1 :
                    binder.isNone = true ∧
                      leftBody.hasCanonicalBinderMetadata = true)
              have rightCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightWellSorted.1.2.1 :
                    binder.isNone = true ∧
                      rightBody.hasCanonicalBinderMetadata = true)
              have leftBodyObject : isObjectPattern leftBody = true := by
                simpa [isObjectPattern] using leftWellSorted.1.2.2.1
              have rightBodyObject : isObjectPattern rightBody = true := by
                simpa [isObjectPattern] using rightWellSorted.1.2.2.1
              have leftBodyScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile (domain :: available).length
                    leftBody := by
                intro presentation membership
                have parent := leftWellSorted.2 presentation membership
                simpa [binderSafeAt, Nat.add_comm] using parent
              have rightBodyScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile (domain :: available).length
                    rightBody := by
                intro presentation membership
                have parent := rightWellSorted.2 presentation membership
                simpa [binderSafeAt, Nat.add_comm] using parent
              obtain ⟨bodyPair⟩ := alignChild
                (childAvailable := domain :: available) (childOuter := outer)
                ⟨⟨leftBodyTyped, leftCanonicalParts.2, leftBodyObject,
                    leftBodyTyped.isWellScopedAt⟩, leftBodyScope⟩
                ⟨⟨rightBodyTyped, rightCanonicalParts.2, rightBodyObject,
                    rightBodyTyped.isWellScopedAt⟩, rightBodyScope⟩
                  bodyCanonical (by simp_wf)
              let leftTree := CostRegionTree.lambda (binder := binder)
                bodyPair.leftTree
              let rightTree := CostRegionTree.lambda (binder := binder)
                bodyPair.rightTree
              exact ⟨⟨leftTree, rightTree,
                .lambda bodyPair.leftTree bodyPair.rightTree
                  bodyPair.alignment⟩⟩
  | @multiLambda arity binders leftBody rightBody bodyCanonical =>
      cases leftWellSorted.1.1 with
      | multiLambda leftBodyTyped =>
          cases rightWellSorted.1.1 with
          | multiLambda rightBodyTyped =>
              rename_i binderType codomain
              have leftCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  leftWellSorted.1.2.1 :
                    binders.isEmpty = true ∧
                      leftBody.hasCanonicalBinderMetadata = true)
              have rightCanonicalParts := (by
                simpa [Pattern.hasCanonicalBinderMetadata] using
                  rightWellSorted.1.2.1 :
                    binders.isEmpty = true ∧
                      rightBody.hasCanonicalBinderMetadata = true)
              have leftBodyObject : isObjectPattern leftBody = true := by
                simpa [isObjectPattern] using leftWellSorted.1.2.2.1
              have rightBodyObject : isObjectPattern rightBody = true := by
                simpa [isObjectPattern] using rightWellSorted.1.2.2.1
              have leftBodyScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile
                    (List.replicate arity binderType ++ available).length
                      leftBody := by
                intro presentation membership
                have parent := leftWellSorted.2 presentation membership
                simpa [binderSafeAt, List.length_append, List.length_replicate,
                  Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using parent
              have rightBodyScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
                  source.costWholeReflectionProfile
                    (List.replicate arity binderType ++ available).length
                      rightBody := by
                intro presentation membership
                have parent := rightWellSorted.2 presentation membership
                simpa [binderSafeAt, List.length_append, List.length_replicate,
                  Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using parent
              obtain ⟨bodyPair⟩ := alignChild
                (childAvailable :=
                  List.replicate arity binderType ++ available)
                (childOuter := outer)
                ⟨⟨leftBodyTyped, leftCanonicalParts.2, leftBodyObject,
                    leftBodyTyped.isWellScopedAt⟩, leftBodyScope⟩
                ⟨⟨rightBodyTyped, rightCanonicalParts.2, rightBodyObject,
                    rightBodyTyped.isWellScopedAt⟩, rightBodyScope⟩
                  bodyCanonical (by simp_wf)
              let leftTree := CostRegionTree.multiLambda (arity := arity)
                (binders := binders) bodyPair.leftTree
              let rightTree := CostRegionTree.multiLambda (arity := arity)
                (binders := binders) bodyPair.rightTree
              exact ⟨⟨leftTree, rightTree,
                .multiLambda bodyPair.leftTree bodyPair.rightTree
                  bodyPair.alignment⟩⟩
  | subst bodyCanonical replacementCanonical =>
      have impossible := leftWellSorted.1.2.2.1
      simp [isObjectPattern] at impossible
  | @collection collectionType ne leftElements rightElements
      childrenCanonical =>
      cases type with
      | base category =>
          exact staticClosed leftWellSorted rightWellSorted canonical
            (Or.inl CostStaticRootShape.baseCollection)
      | collection actual elementType =>
          cases leftWellSorted.1.1 with
          | collection leftElementsTyped =>
              cases rightWellSorted.1.1 with
              | collection rightElementsTyped =>
                  have canonicalLeft :
                      Pattern.hasCanonicalBinderMetadataList leftElements = true := by
                    simpa [Pattern.hasCanonicalBinderMetadata] using
                      leftWellSorted.1.2.1
                  have canonicalRight :
                      Pattern.hasCanonicalBinderMetadataList rightElements = true := by
                    simpa [Pattern.hasCanonicalBinderMetadata] using
                      rightWellSorted.1.2.1
                  have objectLeft : isObjectPatternList leftElements = true := by
                    simpa [isObjectPattern] using leftWellSorted.1.2.2.1
                  have objectRight : isObjectPatternList rightElements = true := by
                    simpa [isObjectPattern] using rightWellSorted.1.2.2.1
                  have reflectiveLeft : ∀ presentation ∈
                      source.costWholeReflectionProfile.presentations,
                      binderSafeListAt presentation.quoteConstructor
                        available.length leftElements = true := by
                    intro presentation membership
                    simpa [binderSafeAt] using
                      leftWellSorted.2 presentation membership
                  have reflectiveRight : ∀ presentation ∈
                      source.costWholeReflectionProfile.presentations,
                      binderSafeListAt presentation.quoteConstructor
                        available.length rightElements = true := by
                    intro presentation membership
                    simpa [binderSafeAt] using
                      rightWellSorted.2 presentation membership
                  obtain ⟨elementPair⟩ :=
                    CostCanonicalElementPairElaboration.nonempty_of_wellSorted
                      (available := available) (outer := outer)
                      declaration
                        (.collection collectionType leftElements none)
                        alignChild leftElementsTyped
                        rightElementsTyped
                        canonicalLeft canonicalRight objectLeft objectRight
                        reflectiveLeft reflectiveRight (by
                          intro element membership
                          have elementBound := List.sizeOf_lt_of_mem membership
                          simp_wf
                          omega) childrenCanonical
                  let leftTree := CostRegionTree.collection
                    (collectionType := collectionType) (rest := none)
                      elementPair.leftTrees
                  let rightTree := CostRegionTree.collection
                    (collectionType := collectionType) (rest := none)
                      elementPair.rightTrees
                  exact ⟨⟨leftTree, rightTree,
                    .collection elementPair.leftTrees elementPair.rightTrees
                      elementPair.alignment⟩⟩
      | arrow domain codomain => cases leftWellSorted.1.1
      | multiBinder domain => cases leftWellSorted.1.1
  | collectionRest collectionType rest childrenCanonical =>
      have impossible := leftWellSorted.1.2.2.1
      simp [isObjectPattern] at impossible

/-- Exhaustive one-layer paired elaboration for one generated static image.
Collapsing roots are proved static from the authored reflective declaration;
the remaining arm is the structural theorem above. -/
theorem CostCanonicalPairElaboration.nonempty_of_rootCases
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {category : String}
    (declarationColor : CostStaticColor)
    (sourceDeclaration : ReflectivePresentationDecl)
    (membership : sourceDeclaration ∈
      source.reflection.1.presentations)
    (staticClosed : CostCanonicalStaticPairClosed source kernel
      (costStaticReflectivePresentationDecl source declarationColor
        sourceDeclaration))
    (alignChild : ∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl source declarationColor
              sourceDeclaration) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl source declarationColor
              sourceDeclaration) rightChild →
        sizeOf leftChild < sizeOf leftPattern →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          childAvailable childOuter leftChild rightChild childType))
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (.base category) leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available (.base category) rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) rightPattern) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern (.base category)) := by
  let declaration := costStaticReflectivePresentationDecl source
    declarationColor sourceDeclaration
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · exact staticClosed leftWellSorted rightWellSorted canonical
      (Or.inl (CostStaticRootShape.of_costStatic_collapsingRoot source
        declarationColor sourceDeclaration membership leftCollapsing))
  · exact staticClosed leftWellSorted rightWellSorted canonical
      (Or.inr (CostStaticRootShape.of_costStatic_collapsingRoot source
        declarationColor sourceDeclaration membership rightCollapsing))
  · exact CostCanonicalPairElaboration.nonempty_of_aligned declaration
      staticClosed alignChild leftWellSorted rightWellSorted canonical aligned

/-- Exhaustive one-layer paired elaboration for an arbitrary reflective
declaration.  Static roots and genuinely root-collapsing pairs are the only
local semantic obligations; every rigid constructor, binder, and structural
collection layer is assembled here. -/
theorem CostCanonicalPairElaboration.nonempty_of_cases
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (staticClosed : CostCanonicalStaticPairClosed source kernel declaration)
    (collapsingClosed :
      CostCanonicalCollapsingPairClosed source kernel declaration)
    (alignChild : ∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType rightChild →
        canonicalize declaration leftChild = canonicalize declaration rightChild →
        sizeOf leftChild < sizeOf leftPattern →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          childAvailable childOuter leftChild rightChild childType))
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize declaration leftPattern =
      canonicalize declaration rightPattern) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) := by
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · exact collapsingClosed leftWellSorted rightWellSorted canonical
      (Or.inl leftCollapsing)
  · exact collapsingClosed leftWellSorted rightWellSorted canonical
      (Or.inr rightCollapsing)
  · exact CostCanonicalPairElaboration.nonempty_of_aligned declaration
      staticClosed alignChild leftWellSorted rightWellSorted canonical aligned

/-- Well-founded paired elaboration of every typed canonical pair.

The recursion is purely structural and decreases through the left endpoint.
All language-specific mathematics is concentrated in the two local closure
premises: certified static regions and the two canonicalizer root-collapse
forms.  In particular, this theorem does not assume the final normalized
equality; it constructs both proof-relevant trees and their hereditary
alignment. -/
noncomputable def CostCanonicalPairElaboration.nonempty_of_canonical
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (staticClosed : CostCanonicalStaticPairClosed source kernel declaration)
    (collapsingClosed :
      CostCanonicalCollapsingPairClosed source kernel declaration)
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize declaration leftPattern =
      canonicalize declaration rightPattern) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) := by
  apply CostCanonicalPairElaboration.nonempty_of_cases declaration staticClosed
    collapsingClosed
  · intro childAvailable childOuter leftChild rightChild childType
      childLeftWellSorted childRightWellSorted childCanonical smaller
    exact CostCanonicalPairElaboration.nonempty_of_canonical declaration
      staticClosed collapsingClosed childLeftWellSorted childRightWellSorted
        childCanonical
  · exact leftWellSorted
  · exact rightWellSorted
  · exact canonical
termination_by sizeOf leftPattern

end Mettapedia.GSLT.LanguageDef
