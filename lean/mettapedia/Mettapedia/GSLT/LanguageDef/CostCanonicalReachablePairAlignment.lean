import Mettapedia.GSLT.LanguageDef.CostCanonicalPairAlignment

/-!
# Paired Cost elaboration on a reachable type domain

Unrestricted recursion under reflective canonical equality is too broad for
hereditary Cost normalization.  In particular, a bare parallel collection at
an actual collection type is a structural value whose element order is
preserved by the tree normalizer, even though the reflective canonicalizer
identifies permutations.

The generator theorem starts at a language sort rather than at an arbitrary
type.  This module records the weakest closure data needed to follow that
reachable fragment: base types are admitted, constructor parameters remain in
the fragment, codomains remain in the fragment, and structural collection
types are excluded.  Bare collections at base result types are still handled
by the proof-relevant static-root closure.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- A recursive type domain in which canonical-pair elaboration never exposes
a structural collection.  The constructor-parameter law is tied to the sole
validated generated language; it is not a second typing table. -/
structure CostCanonicalRecursiveTypeDomain (source : CIGSLT) where
  Admissible : TypeExpr → Prop
  base : ∀ category, Admissible (.base category)
  codomain : ∀ {domain codomain}, Admissible (.arrow domain codomain) →
    Admissible codomain
  noCollection : ∀ {collectionType elementType},
    ¬ Admissible (.collection collectionType elementType)
  parameter : ∀ {rule : GrammarRule},
    rule ∈ source.costWholeLanguage.terms →
      ¬ UsesBareCollection rule →
      ∀ {parameter : TermParam}, parameter ∈ rule.params →
        ∀ {expected : TypeExpr}, parameterType? parameter = some expected →
          Admissible expected

namespace CostCanonicalRecursiveTypeDomain

/-- In an admitted recursive domain, a well-sorted collapsing root has a base
result type.  Applications are base-typed by the constructor rule; a raw
collection result is excluded, leaving only its base-typed bare-constructor
interpretation. -/
theorem exists_base_of_collapsingRoot
    {source : CIGSLT} (recursive : CostCanonicalRecursiveTypeDomain source)
    {targetFree : FreeTypeContext} {available : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (admissible : recursive.Admissible type)
    (wellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type pattern)
    {declaration : ReflectivePresentationDecl}
    (collapsing : CollapsingRoot declaration pattern) :
    ∃ category, type = .base category := by
  rcases collapsing with ⟨arguments, patternEq⟩ | ⟨elements, patternEq⟩
  · subst pattern
    obtain ⟨rule, _membership, _label, _notBare, typeEq, _argumentsTyped⟩ :=
      hasType_apply_inversion wellSorted.1.1
    exact ⟨rule.category, typeEq⟩
  · subst pattern
    rcases hasType_collection_inversion wellSorted.1.1 with
      ⟨elementType, typeEq, _elementsTyped⟩ |
        ⟨rule, _parameterName, _elementType, _membership, _shape, typeEq,
          _elementsTyped⟩
    · rw [typeEq] at admissible
      exact (recursive.noCollection admissible).elim
    · exact ⟨rule.category, typeEq⟩

end CostCanonicalRecursiveTypeDomain

/-- Static-root closure restricted to the recursive type domain actually
consumed by reachable paired elaboration.  This avoids requiring a language
to close unrelated collection fibres that recursive generator descent can
never reach. -/
def CostCanonicalStaticPair.IsClosedIn
    {source : CIGSLT} (recursive : CostCanonicalRecursiveTypeDomain source)
    (kernel : CostStaticNormalizationKernel source)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    recursive.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available type rightPattern →
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern →
    (CostStaticRootShape source leftPattern type ∨
      CostStaticRootShape source rightPattern type) →
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type)

namespace CostCanonicalStaticPair.IsClosedIn

/-- An unrestricted static closure restricts to every recursive type domain.
This is the sole compatibility direction needed by existing generic clients. -/
theorem of_unrestricted
    {source : CIGSLT} {recursive : CostCanonicalRecursiveTypeDomain source}
    {kernel : CostStaticNormalizationKernel source}
    {declaration : ReflectivePresentationDecl}
    (closed : CostCanonicalStaticPairClosed source kernel declaration) :
    CostCanonicalStaticPair.IsClosedIn recursive kernel declaration := by
  intro targetFree available outer leftPattern rightPattern type _
    leftWellSorted rightWellSorted canonical staticShape
  exact closed leftWellSorted rightWellSorted canonical staticShape

end CostCanonicalStaticPair.IsClosedIn

/-- One syntax-directed static-root step inside the recursive domain.

Unlike `CostCanonicalStaticPair.IsClosedIn`, this interface does not assume
the complete closure theorem it is intended to construct.  It may consume only
paired elaborations whose two-endpoint size is strictly smaller than the
current pair.  This is the induction interface required by static normalizers
whose collapsing cases recurse into either endpoint. -/
def CostCanonicalStaticPairStepInDomain
    {source : CIGSLT} (recursive : CostCanonicalRecursiveTypeDomain source)
    (kernel : CostStaticNormalizationKernel source)
    (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    recursive.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available type rightPattern →
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern →
    (CostStaticRootShape source leftPattern type ∨
      CostStaticRootShape source rightPattern type) →
    (∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
          source.costWholeReflectionProfile source.costWholeLanguage targetFree
          childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
          source.costWholeReflectionProfile source.costWholeLanguage targetFree
          childAvailable childType rightChild →
      canonicalize declaration leftChild = canonicalize declaration rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      recursive.Admissible childType →
      Nonempty (CostCanonicalPairElaboration source kernel targetFree
        childAvailable childOuter leftChild rightChild childType)) →
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type)

namespace CostCanonicalStaticPairStepInDomain

/-- A completed closure supplies a local step by ignoring the strictly smaller
recursive interface. -/
theorem of_closed
    {source : CIGSLT} {recursive : CostCanonicalRecursiveTypeDomain source}
    {kernel : CostStaticNormalizationKernel source}
    {declaration : ReflectivePresentationDecl}
    (closed : CostCanonicalStaticPair.IsClosedIn recursive kernel
      declaration) :
    CostCanonicalStaticPairStepInDomain recursive kernel declaration := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape _closeSmaller
  exact closed admissible leftWellSorted rightWellSorted canonical staticShape

end CostCanonicalStaticPairStepInDomain

/-- Paired argument elaboration with an explicit proof that every parameter
type lies in the recursive domain.  The domain proof travels with the exact
parameter position, so no global claim about arbitrary child types is needed. -/
theorem CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted_inDomain
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (recursive : CostCanonicalRecursiveTypeDomain source)
    (declaration : ReflectivePresentationDecl)
    (leftParent rightParent : Pattern)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          leftPattern →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree available type
          rightPattern →
        canonicalize declaration leftPattern = canonicalize declaration rightPattern →
        sizeOf leftPattern + sizeOf rightPattern <
          sizeOf leftParent + sizeOf rightParent →
        recursive.Admissible type →
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
      (∀ argument ∈ leftArguments, sizeOf argument < sizeOf leftParent) →
      (∀ argument ∈ rightArguments, sizeOf argument < sizeOf rightParent) →
      (∀ {parameter : TermParam}, parameter ∈ parameters →
        ∀ {expected : TypeExpr}, parameterType? parameter = some expected →
          recursive.Admissible expected) →
      List.Forall₂ (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
        leftArguments rightArguments →
      Nonempty (CostCanonicalArgumentPairElaboration source kernel targetFree
        available outer leftArguments rightArguments parameters) := by
  intro available outer leftArguments rightArguments parameters leftTyped
    rightTyped leftCanonical rightCanonical leftObjects rightObjects leftScope
    rightScope leftArgumentsSmaller rightArgumentsSmaller parametersAdmissible
    canonical
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
              have headAdmissible : recursive.Admissible leftExpected :=
                parametersAdmissible (by simp) leftParameterType
              obtain ⟨headPair⟩ := alignChild
                ⟨⟨leftHeadTyped, leftCanonicalParts.1, leftObjectParts.1,
                    leftHeadTyped.isWellScopedAt⟩, leftHeadScope⟩
                ⟨⟨rightHeadTyped, rightCanonicalParts.1, rightObjectParts.1,
                    rightHeadTyped.isWellScopedAt⟩, rightHeadScope⟩ headCanonical
                (by
                  have leftSmaller := leftArgumentsSmaller leftArgument (by simp)
                  have rightSmaller :=
                    rightArgumentsSmaller rightArgument (by simp)
                  omega)
                headAdmissible
              obtain ⟨tailPair⟩ := inductionHypothesis leftTailTyped
                rightTailTyped leftCanonicalParts.2 rightCanonicalParts.2
                leftObjectParts.2 rightObjectParts.2 leftTailScope
                rightTailScope (by
                  intro argument membership
                  exact leftArgumentsSmaller argument (by simp [membership]))
                (by
                  intro argument membership
                  exact rightArgumentsSmaller argument (by simp [membership]))
                (by
                  intro parameter membership expected parameterType
                  exact parametersAdmissible (by simp [membership]) parameterType)
              let leftTrees := CostRegionArgumentTrees.cons leftRepresentation
                leftParameterType headPair.leftTree tailPair.leftTrees
              let rightTrees := CostRegionArgumentTrees.cons rightRepresentation
                leftParameterType headPair.rightTree tailPair.rightTrees
              exact ⟨⟨leftTrees, rightTrees,
                .cons leftRepresentation rightRepresentation leftParameterType
                  headPair.leftTree headPair.rightTree tailPair.leftTrees
                  tailPair.rightTrees headPair.alignment tailPair.alignment⟩⟩

/-- One non-collapsing canonical layer inside a recursive type domain.  The
collection-typed structural branch is impossible by construction; a
base-typed bare collection remains a static root and is delegated to the
restoration closure. -/
theorem CostCanonicalPairElaboration.nonempty_of_aligned_inDomain
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (recursive : CostCanonicalRecursiveTypeDomain source)
    (declaration : ReflectivePresentationDecl)
    (staticStep : CostCanonicalStaticPairStepInDomain recursive kernel
      declaration)
    (alignChild : ∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree childAvailable
          childType rightChild →
        canonicalize declaration leftChild = canonicalize declaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        recursive.Admissible childType →
        Nonempty (CostCanonicalPairElaboration source kernel targetFree
          childAvailable childOuter leftChild rightChild childType))
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize declaration leftPattern =
      canonicalize declaration rightPattern)
    (admissible : recursive.Admissible type)
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
          exact staticStep admissible leftWellSorted rightWellSorted canonical
            (Or.inl (.application color constructor (by
              rw [← materializes,
                source.materializeDeclaredCostConstructor_label constructor]
              exact source.decodeDeclaredCostConstructor_render constructor)
              role)) alignChild
      | interactionPrincipal =>
          have neutral : source.declaredCostConstructorRole constructor =
              .interactionPrincipal ∨ ∃ kind,
                source.declaredCostConstructorRole constructor =
                  .apparatus kind := Or.inl role
          by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile rule.label = true
          · have leftAtZero := isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightAtZero := isWellScopedListAt_zero_of_typed_quote
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
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted_inDomain
                recursive (available := []) (outer := available ++ outer)
                declaration (.apply rule.label leftArguments)
                  (.apply rule.label rightArguments) alignChild
                  leftTypedAtZero rightTypedAtZero canonicalLeft canonicalRight
                  objectsLeft objectsRight leftReflectiveAtZero
                  rightReflectiveAtZero (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro parameter parameterMembership expected parameterType
                    exact recursive.parameter membership notBare
                      parameterMembership parameterType)
                  childrenCanonical
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
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted_inDomain
                recursive (available := available) (outer := outer)
                declaration (.apply rule.label leftArguments)
                  (.apply rule.label rightArguments) alignChild
                  leftArgumentsTyped rightArgumentsTyped canonicalLeft
                  canonicalRight objectsLeft objectsRight leftReflective
                  rightReflective (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro parameter parameterMembership expected parameterType
                    exact recursive.parameter membership notBare
                      parameterMembership parameterType)
                  childrenCanonical
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
          · have leftAtZero := isWellScopedListAt_zero_of_typed_quote
                source.costWholeLanguage_validate
                  source.costWholeReflectionProfile_validate membership
                    leftArgumentsTyped
                  quoted leftWellSorted.2
            have rightAtZero := isWellScopedListAt_zero_of_typed_quote
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
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted_inDomain
                recursive (available := []) (outer := available ++ outer)
                declaration (.apply rule.label leftArguments)
                  (.apply rule.label rightArguments) alignChild
                  leftTypedAtZero rightTypedAtZero canonicalLeft canonicalRight
                  objectsLeft objectsRight leftReflectiveAtZero
                  rightReflectiveAtZero (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro parameter parameterMembership expected parameterType
                    exact recursive.parameter membership notBare
                      parameterMembership parameterType)
                  childrenCanonical
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
            have leftReflective := reflectiveScopeSafeListAt_of_nonquote
              ordinary leftWellSorted.2
            have rightReflective := reflectiveScopeSafeListAt_of_nonquote
              ordinary rightWellSorted.2
            obtain ⟨argumentPair⟩ :=
              CostCanonicalArgumentPairElaboration.nonempty_of_wellSorted_inDomain
                recursive (available := available) (outer := outer)
                declaration (.apply rule.label leftArguments)
                  (.apply rule.label rightArguments) alignChild
                  leftArgumentsTyped rightArgumentsTyped canonicalLeft
                  canonicalRight objectsLeft objectsRight leftReflective
                  rightReflective (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro argument argumentMembership
                    have argumentBound :=
                      List.sizeOf_lt_of_mem argumentMembership
                    simp_wf
                    omega)
                  (by
                    intro parameter parameterMembership expected parameterType
                    exact recursive.parameter membership notBare
                      parameterMembership parameterType)
                  childrenCanonical
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
                  bodyCanonical (by simp_wf; omega)
                (recursive.codomain admissible)
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
                  bodyCanonical (by simp_wf; omega)
                (recursive.codomain admissible)
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
          exact staticStep admissible leftWellSorted rightWellSorted canonical
            (Or.inl CostStaticRootShape.baseCollection) alignChild
      | collection actual elementType =>
          exact (recursive.noCollection admissible).elim
      | arrow domain codomain => cases leftWellSorted.1.1
      | multiBinder domain => cases leftWellSorted.1.1
  | collectionRest collectionType rest childrenCanonical =>
      have impossible := leftWellSorted.1.2.2.1
      simp [isObjectPattern] at impossible

/-- Identical endpoints close with one checked elaboration and the reflexive
alignment constructor.  This is the genuine base case of paired canonical
descent: it preserves the compiler's proof-relevant tree while avoiding an
unnecessary static-root obligation for a diagonal pair. -/
theorem CostCanonicalPairElaboration.nonempty_of_pattern_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (patternEq : leftPattern = rightPattern) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) := by
  subst rightPattern
  let result := CostRegionTree.build? (source := source)
    (targetFree := targetFree) available outer leftPattern type
  have some : result.isSome = true :=
    CostRegionTree.build?_isSome_of_wellSorted leftWellSorted
  let tree := result.get some
  exact ⟨⟨tree, tree, .refl tree⟩⟩

/-- Well-founded paired elaboration from one syntax-directed static-root step.
The symmetric endpoint measure permits a collapsing static shell on either
side to expose and recursively align a proper child. -/
noncomputable def
    CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (recursive : CostCanonicalRecursiveTypeDomain source)
    (declarationColor : CostStaticColor)
    (sourceDeclaration : ReflectivePresentationDecl)
    (membership : sourceDeclaration ∈
      source.reflection.1.presentations)
    (staticStep : CostCanonicalStaticPairStepInDomain recursive kernel
      (costStaticReflectivePresentationDecl source declarationColor
        sourceDeclaration))
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) rightPattern)
    (admissible : recursive.Admissible type) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) := by
  by_cases patternEq : leftPattern = rightPattern
  · exact CostCanonicalPairElaboration.nonempty_of_pattern_eq
      leftWellSorted patternEq
  let declaration := costStaticReflectivePresentationDecl source
    declarationColor sourceDeclaration
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · obtain ⟨category, typeEq⟩ :=
      recursive.exists_base_of_collapsingRoot admissible leftWellSorted
        leftCollapsing
    subst type
    exact staticStep admissible leftWellSorted rightWellSorted canonical
      (Or.inl (CostStaticRootShape.of_costStatic_collapsingRoot source
        declarationColor sourceDeclaration membership leftCollapsing)) (by
          intro childAvailable childOuter leftChild rightChild childType
            childLeftWellSorted childRightWellSorted childCanonical smaller
            childAdmissible
          exact
            CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
              recursive declarationColor sourceDeclaration membership
              staticStep childLeftWellSorted childRightWellSorted
              childCanonical childAdmissible)
  · obtain ⟨category, typeEq⟩ :=
      recursive.exists_base_of_collapsingRoot admissible rightWellSorted
        rightCollapsing
    subst type
    exact staticStep admissible leftWellSorted rightWellSorted canonical
      (Or.inr (CostStaticRootShape.of_costStatic_collapsingRoot source
        declarationColor sourceDeclaration membership rightCollapsing)) (by
          intro childAvailable childOuter leftChild rightChild childType
            childLeftWellSorted childRightWellSorted childCanonical smaller
            childAdmissible
          exact
            CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
              recursive declarationColor sourceDeclaration membership
              staticStep childLeftWellSorted childRightWellSorted
              childCanonical childAdmissible)
  · apply CostCanonicalPairElaboration.nonempty_of_aligned_inDomain
      recursive declaration staticStep
    · intro childAvailable childOuter leftChild rightChild childType
        childLeftWellSorted childRightWellSorted childCanonical smaller
        childAdmissible
      exact
        CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
          recursive declarationColor sourceDeclaration membership staticStep
          childLeftWellSorted childRightWellSorted childCanonical childAdmissible
    · exact leftWellSorted
    · exact rightWellSorted
    · exact canonical
    · exact admissible
    · exact aligned
termination_by sizeOf leftPattern + sizeOf rightPattern

/-- Well-founded paired elaboration for every canonical pair whose result type
belongs to the recursive domain.  A completed static closure remains accepted
as a compatibility interface; internally it is viewed as a local step. -/
theorem CostCanonicalPairElaboration.nonempty_of_canonical_inDomain
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (recursive : CostCanonicalRecursiveTypeDomain source)
    (declarationColor : CostStaticColor)
    (sourceDeclaration : ReflectivePresentationDecl)
    (membership : sourceDeclaration ∈ source.reflection.1.presentations)
    (staticClosed : CostCanonicalStaticPair.IsClosedIn recursive kernel
      (costStaticReflectivePresentationDecl source declarationColor
        sourceDeclaration))
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl source declarationColor
          sourceDeclaration) rightPattern)
    (admissible : recursive.Admissible type) :
    Nonempty (CostCanonicalPairElaboration source kernel targetFree available
      outer leftPattern rightPattern type) :=
  CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
    recursive declarationColor sourceDeclaration membership
    (CostCanonicalStaticPairStepInDomain.of_closed staticClosed) leftWellSorted
      rightWellSorted canonical admissible

namespace CostCanonicalStaticPair.IsClosedIn

/-- A syntax-directed static step closes the whole recursive domain by the
generic symmetric well-founded elaborator. -/
theorem of_step
    {source : CIGSLT} {recursive : CostCanonicalRecursiveTypeDomain source}
    {kernel : CostStaticNormalizationKernel source}
    {declarationColor : CostStaticColor}
    {sourceDeclaration : ReflectivePresentationDecl}
    (membership : sourceDeclaration ∈ source.reflection.1.presentations)
    (step : CostCanonicalStaticPairStepInDomain recursive kernel
      (costStaticReflectivePresentationDecl source declarationColor
        sourceDeclaration)) :
    CostCanonicalStaticPair.IsClosedIn recursive kernel
      (costStaticReflectivePresentationDecl source declarationColor
        sourceDeclaration) := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape
  exact
    CostCanonicalPairElaboration.nonempty_of_canonical_inDomain_of_staticStep
      recursive declarationColor sourceDeclaration membership step
      leftWellSorted rightWellSorted canonical admissible

end CostCanonicalStaticPair.IsClosedIn

end Mettapedia.GSLT.LanguageDef
