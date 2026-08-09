import Mettapedia.GSLT.LanguageDef.CostElaborationTransport

/-!
# Semantic soundness of proof-relevant Cost transport

This module interprets the structural transport relation in the sole authored
equation semantics.  The static-region case is isolated as the one
substitution/occurrence kernel; every surrounding frame is discharged by
generic typed contextual congruence.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace CostRegionTreeTransport

/-- A tree edge remains inside any authored constructor-argument
representation inhabited by both endpoints.  This strengthens ordinary
fiber soundness exactly where abstraction parameters require lambda syntax
at every intermediate vertex. -/
def ArgumentFiberEquation
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter leftPattern
      leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    (transport : CostRegionTreeTransport source staticLift targetFree left
      right) : Prop :=
  ∀ (parameter : TermParam)
    (leftRepresentation :
      WellSorted.MatchesParameterRepresentation parameter leftPattern)
    (rightRepresentation :
      WellSorted.MatchesParameterRepresentation parameter rightPattern)
    (leftParameterType :
      WellSorted.parameterType? parameter = some leftType)
    (rightParameterType :
      WellSorted.parameterType? parameter = some rightType)
    (leftCanonical : leftPattern.hasCanonicalBinderMetadata = true)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (leftScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      leftAvailable.length leftPattern)
    (rightCanonical : rightPattern.hasCanonicalBinderMetadata = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (rightScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      rightAvailable.length rightPattern),
    let fiber := transport.sameFiber
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree leftAvailable leftOuter parameter
        leftType).r
      (left.originalArgument parameter leftRepresentation leftParameterType
        leftCanonical leftObject leftScope)
      ((right.originalArgument parameter rightRepresentation
        rightParameterType rightCanonical rightObject rightScope
        ).reindexFiber fiber.1.symm fiber.2.1.symm fiber.2.2.symm)

/-- A split-fiber term path automatically preserves a simple authored
parameter, whose representation predicate imposes no additional syntax. -/
theorem simpleArgument_of_fiberEquation
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree source targetFree leftAvailable leftOuter leftPattern
      leftType}
    {right : CostRegionTree source targetFree rightAvailable rightOuter
      rightPattern rightType}
    {transport : CostRegionTreeTransport source staticLift targetFree left
      right}
    (fiberSound : transport.FiberEquation)
    (name : String) (declared : TypeExpr)
    (leftParameterType :
      WellSorted.parameterType? (.simple name declared) = some leftType)
    (rightParameterType :
      WellSorted.parameterType? (.simple name declared) = some rightType)
    (leftCanonical : leftPattern.hasCanonicalBinderMetadata = true)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (leftScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      leftAvailable.length leftPattern)
    (rightCanonical : rightPattern.hasCanonicalBinderMetadata = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (rightScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile
      rightAvailable.length rightPattern) :
    let fiber := transport.sameFiber
    (WellSorted.AvailableOpenArgument.equationSetoid
      source.costWholeLanguage targetFree leftAvailable leftOuter
        (.simple name declared) leftType).r
      (left.originalArgument (.simple name declared) True.intro
        leftParameterType leftCanonical leftObject leftScope)
      ((right.originalArgument (.simple name declared) True.intro
        rightParameterType rightCanonical rightObject rightScope
        ).reindexFiber fiber.1.symm fiber.2.1.symm fiber.2.2.symm) := by
  let fiber := transport.sameFiber
  let pack := fun
      (term : WellSorted.AvailableOpenPattern
        source.costWholeReflectionProfile source.costWholeLanguage
          targetFree leftAvailable leftOuter leftType) =>
    ({ term := term
       representation := True.intro
       parameterType := leftParameterType } :
      WellSorted.AvailableOpenArgument source.costWholeReflectionProfile
        source.costWholeLanguage targetFree leftAvailable leftOuter
          (.simple name declared) leftType)
  have packed :=
    WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
      (by
        intro first second generator
        exact generator)
      (fiberSound leftCanonical leftObject leftScope rightCanonical rightObject
        rightScope)
  have leftEndpoint :
      pack (left.originalAvailableOpenPattern leftCanonical leftObject
        leftScope) =
        left.originalArgument (.simple name declared) True.intro
          leftParameterType leftCanonical leftObject leftScope := by
    apply WellSorted.AvailableOpenArgument.ext
    rfl
  have rightEndpoint :
      pack ((right.originalAvailableOpenPattern rightCanonical rightObject
        rightScope).reindexFiber fiber.1.symm fiber.2.1.symm
          fiber.2.2.symm) =
        (right.originalArgument (.simple name declared) True.intro
          rightParameterType rightCanonical rightObject rightScope
          ).reindexFiber fiber.1.symm fiber.2.1.symm fiber.2.2.symm := by
    apply WellSorted.AvailableOpenArgument.ext
    dsimp only [pack]
    simp only [WellSorted.AvailableOpenArgument.reindexFiber_pattern,
      WellSorted.AvailableOpenPattern.reindexFiber_pattern,
      CostRegionTree.originalArgument_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern]
  rw [leftEndpoint, rightEndpoint] at packed
  exact packed

/-- Reflexive typed transport is semantically reflexive both as a term and
inside every authored parameter representation it inhabits. -/
theorem refl_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    let transport :=
      CostRegionTreeTransport.refl (staticLift := staticLift) tree
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  constructor
  · exact refl_fiberEquation tree
  · intro parameter leftRepresentation rightRepresentation
      leftParameterType rightParameterType leftCanonical leftObject leftScope
      rightCanonical rightObject rightScope
    have endpoints :
        tree.originalArgument parameter leftRepresentation leftParameterType
            leftCanonical leftObject leftScope =
          (tree.originalArgument parameter rightRepresentation
            rightParameterType rightCanonical rightObject rightScope
            ).reindexFiber rfl rfl rfl := by
      apply WellSorted.AvailableOpenArgument.ext
      rfl
    rw [endpoints]
    exact Relation.EqvGen.refl _

end CostRegionTreeTransport

namespace CostRegionArgumentTreesTransport

/-- Pointwise semantic interpretation of a proof-relevant constructor spine. -/
def FiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftArguments rightArguments : List Pattern}
    {parameters : List TermParam}
    {left : CostRegionArgumentTrees source targetFree available outer
      leftArguments parameters}
    {right : CostRegionArgumentTrees source targetFree available outer
      rightArguments parameters}
    (_transport : CostRegionArgumentTreesTransport source staticLift targetFree
      left right) : Prop :=
  ∀ (leftCanonical :
      Pattern.hasCanonicalBinderMetadataList leftArguments = true)
    (leftObjects : WellSorted.isObjectPatternList leftArguments = true)
    (leftScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        leftArguments = true)
    (rightCanonical :
      Pattern.hasCanonicalBinderMetadataList rightArguments = true)
    (rightObjects : WellSorted.isObjectPatternList rightArguments = true)
    (rightScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        rightArguments = true),
    WellSorted.AvailableOpenArguments.EquationForall₂
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available outer
      (left.originalAvailable leftCanonical leftObjects leftScope)
      (right.originalAvailable rightCanonical rightObjects rightScope)

end CostRegionArgumentTreesTransport

namespace CostRegionElementTreesTransport

/-- Pointwise semantic interpretation of a proof-relevant homogeneous
collection spine. -/
def FiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftElements rightElements : List Pattern} {elementType : TypeExpr}
    {left : CostRegionElementTrees source targetFree available outer
      leftElements elementType}
    {right : CostRegionElementTrees source targetFree available outer
      rightElements elementType}
    (_transport : CostRegionElementTreesTransport source staticLift targetFree
      left right) : Prop :=
  ∀ (leftCanonical :
      Pattern.hasCanonicalBinderMetadataList leftElements = true)
    (leftObjects : WellSorted.isObjectPatternList leftElements = true)
    (leftScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        leftElements = true)
    (rightCanonical :
      Pattern.hasCanonicalBinderMetadataList rightElements = true)
    (rightObjects : WellSorted.isObjectPatternList rightElements = true)
    (rightScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        rightElements = true),
    WellSorted.AvailableOpenElements.EquationForall₂
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
        available outer elementType
      (left.originalAvailable leftCanonical leftObjects leftScope)
      (right.originalAvailable rightCanonical rightObjects rightScope)

end CostRegionElementTreesTransport

namespace CostRegionTreeTransport

/-- The static semantic kernel plus recursively interpreted boundary children
discharge both the ordinary typed fiber and every possible authored argument
fiber.  A static root has base type, so abstraction-parameter cases are
definitionally impossible. -/
theorem static_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    (staticSound : source.CostStaticRegionTransportSound staticLift)
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {outer : List TypeExpr}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    (leftChildren : CostRegionBoundaryTrees source targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees source targetFree color
      rightNode.finiteBoundaryTable)
    (sourceSortEq : leftNode.sourceSort = rightNode.sourceSort)
    (planStep : staticLift.Edge leftNode.plan.decoration
      rightNode.plan.decoration leftChildren.decorations
        rightChildren.decorations)
    (children : ∀ targetIndex,
      CostRegionTreeTransport source staticLift targetFree
        (leftChildren.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightChildren.getDecoration targetIndex).tree)
    (childrenSound : ∀ targetIndex,
      (children targetIndex).FiberEquation) :
    let transport := CostRegionTreeTransport.static (outer := outer)
      leftNode rightNode leftChildren rightChildren sourceSortEq planStep
        children
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.static (outer := outer)
    leftNode rightNode leftChildren rightChildren sourceSortEq planStep
      children
  have fiberSound : transport.FiberEquation :=
    staticSound leftNode rightNode leftChildren rightChildren sourceSortEq
      planStep children childrenSound
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      cases declared <;>
        simp [WellSorted.parameterType?] at leftParameterType
  | multiAbstractionNamed binderNames bodyName declared =>
      cases declared with
      | base sort =>
          simp [WellSorted.parameterType?] at leftParameterType
      | arrow domain codomain =>
          cases domain <;>
            simp [WellSorted.parameterType?] at leftParameterType
      | multiBinder domain =>
          simp [WellSorted.parameterType?] at leftParameterType
      | collection collectionType elementType =>
          simp [WellSorted.parameterType?] at leftParameterType

/-- Equation-neutral ordinary application frames preserve typed transport by
pointwise authored argument congruence. -/
theorem neutralApplicationOrdinary_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
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
    (leftChildren : CostRegionArgumentTrees source targetFree available outer
      leftArguments rule.params)
    (rightChildren : CostRegionArgumentTrees source targetFree available outer
      rightArguments rule.params)
    (arguments : CostRegionArgumentTreesTransport source staticLift targetFree
      leftChildren rightChildren)
    (argumentsSound : arguments.FiberEquations) :
    let transport := CostRegionTreeTransport.neutralApplicationOrdinary
      membership notBareCollection constructor materializes neutral ordinary
        leftChildren rightChildren arguments
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.neutralApplicationOrdinary
    membership notBareCollection constructor materializes neutral ordinary
      leftChildren rightChildren arguments
  have fiberSound : transport.FiberEquation := by
    intro leftCanonical leftObject leftScope rightCanonical rightObject
      rightScope
    have leftArgumentCanonical :
        Pattern.hasCanonicalBinderMetadataList leftArguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
    have rightArgumentCanonical :
        Pattern.hasCanonicalBinderMetadataList rightArguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
    have leftArgumentObjects :
        WellSorted.isObjectPatternList leftArguments = true := by
      simpa [WellSorted.isObjectPattern] using leftObject
    have rightArgumentObjects :
        WellSorted.isObjectPatternList rightArguments = true := by
      simpa [WellSorted.isObjectPattern] using rightObject
    have leftArgumentScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          leftArguments = true := by
      intro presentation presentationMembership
      have notThisQuote : rule.label ≠ presentation.quoteConstructor := by
        intro labelEquality
        have detected : ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile rule.label = true := by
          unfold ReflectiveContextSupport.isQuoteConstructor
          rw [List.any_eq_true]
          exact ⟨presentation, presentationMembership,
            by simp [labelEquality]⟩
        rw [detected] at ordinary
        contradiction
      exact binderSafeListAt_of_binderSafeAt_apply_of_ne
        presentation.quoteConstructor rule.label available.length
          leftArguments notThisQuote
            (leftScope presentation presentationMembership)
    have rightArgumentScope : ∀ presentation ∈
        source.costWholeReflectionProfile.presentations,
        binderSafeListAt presentation.quoteConstructor available.length
          rightArguments = true := by
      intro presentation presentationMembership
      have notThisQuote : rule.label ≠ presentation.quoteConstructor := by
        intro labelEquality
        have detected : ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile rule.label = true := by
          unfold ReflectiveContextSupport.isQuoteConstructor
          rw [List.any_eq_true]
          exact ⟨presentation, presentationMembership,
            by simp [labelEquality]⟩
        rw [detected] at ordinary
        contradiction
      exact binderSafeListAt_of_binderSafeAt_apply_of_ne
        presentation.quoteConstructor rule.label available.length
          rightArguments notThisQuote
            (rightScope presentation presentationMembership)
    have assembled :=
      (argumentsSound leftArgumentCanonical leftArgumentObjects
        leftArgumentScope rightArgumentCanonical rightArgumentObjects
        rightArgumentScope).assembleOrdinary membership notBareCollection
          ordinary
    have leftEndpoint :
        (leftChildren.originalAvailable leftArgumentCanonical
          leftArgumentObjects leftArgumentScope).applyOrdinary membership
            notBareCollection ordinary =
          (CostRegionTree.neutralApplicationOrdinary membership
            notBareCollection constructor materializes neutral ordinary
              leftChildren).originalAvailableOpenPattern leftCanonical
                leftObject leftScope := by
      apply WellSorted.AvailableOpenPattern.ext
      rfl
    have rightEndpoint :
        (rightChildren.originalAvailable rightArgumentCanonical
          rightArgumentObjects rightArgumentScope).applyOrdinary membership
            notBareCollection ordinary =
          ((CostRegionTree.neutralApplicationOrdinary membership
            notBareCollection constructor materializes neutral ordinary
              rightChildren).originalAvailableOpenPattern rightCanonical
                rightObject rightScope).reindexFiber
                  transport.sameFiber.1.symm
                  transport.sameFiber.2.1.symm
                  transport.sameFiber.2.2.symm := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [WellSorted.AvailableOpenPattern.reindexFiber_pattern]
      rfl
    rw [leftEndpoint, rightEndpoint] at assembled
    exact assembled
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      cases declared <;>
        simp [WellSorted.parameterType?] at leftParameterType
  | multiAbstractionNamed binderNames bodyName declared =>
      cases declared with
      | base sort =>
          simp [WellSorted.parameterType?] at leftParameterType
      | arrow domain codomain =>
          cases domain <;>
            simp [WellSorted.parameterType?] at leftParameterType
      | multiBinder domain =>
          simp [WellSorted.parameterType?] at leftParameterType
      | collection collectionType elementType =>
          simp [WellSorted.parameterType?] at leftParameterType

/-- Quotation frames use the same pointwise congruence, but their argument
carrier resets the visible binder prefix to zero while retaining the complete
lexical suffix. -/
theorem neutralApplicationQuote_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
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
    (leftChildren : CostRegionArgumentTrees source targetFree []
      (available ++ outer) leftArguments rule.params)
    (rightChildren : CostRegionArgumentTrees source targetFree []
      (available ++ outer) rightArguments rule.params)
    (arguments : CostRegionArgumentTreesTransport source staticLift targetFree
      leftChildren rightChildren)
    (argumentsSound : arguments.FiberEquations) :
    let transport := CostRegionTreeTransport.neutralApplicationQuote
      membership notBareCollection constructor materializes neutral quoted
        leftChildren rightChildren arguments
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.neutralApplicationQuote
    membership notBareCollection constructor materializes neutral quoted
      leftChildren rightChildren arguments
  have fiberSound : transport.FiberEquation := by
    intro leftCanonical leftObject leftScope rightCanonical rightObject
      rightScope
    have leftArgumentCanonical :
        Pattern.hasCanonicalBinderMetadataList leftArguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
    have rightArgumentCanonical :
        Pattern.hasCanonicalBinderMetadataList rightArguments = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
    have leftArgumentObjects :
        WellSorted.isObjectPatternList leftArguments = true := by
      simpa [WellSorted.isObjectPattern] using leftObject
    have rightArgumentObjects :
        WellSorted.isObjectPatternList rightArguments = true := by
      simpa [WellSorted.isObjectPattern] using rightObject
    have leftParentScopeAtBound :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (available ++ outer).length (.apply rule.label leftArguments) := by
      intro presentation presentationMembership
      exact binderSafeAt_mono presentation.quoteConstructor
        (leftScope presentation presentationMembership) (by simp)
    have rightParentScopeAtBound :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (available ++ outer).length (.apply rule.label rightArguments) := by
      intro presentation presentationMembership
      exact binderSafeAt_mono presentation.quoteConstructor
        (rightScope presentation presentationMembership) (by simp)
    have leftArgumentsTyped :
        WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
          (available ++ outer) leftArguments rule.params := by
      simpa only [List.nil_append] using leftChildren.originalTyped
    have rightArgumentsTyped :
        WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
          (available ++ outer) rightArguments rule.params := by
      simpa only [List.nil_append] using rightChildren.originalTyped
    have leftArgumentScope :=
      WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
        source.costWholeLanguage_validate
          source.costWholeReflectionProfile_validate membership
            leftArgumentsTyped quoted leftParentScopeAtBound
    have rightArgumentScope :=
      WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
        source.costWholeLanguage_validate
          source.costWholeReflectionProfile_validate membership
            rightArgumentsTyped quoted rightParentScopeAtBound
    have assembled :=
      (argumentsSound leftArgumentCanonical leftArgumentObjects
        leftArgumentScope rightArgumentCanonical rightArgumentObjects
        rightArgumentScope).assembleQuote membership notBareCollection quoted
    have leftEndpoint :
        (leftChildren.originalAvailable leftArgumentCanonical
          leftArgumentObjects leftArgumentScope).applyQuote membership
            notBareCollection quoted =
          (CostRegionTree.neutralApplicationQuote membership
            notBareCollection constructor materializes neutral quoted
              leftChildren).originalAvailableOpenPattern leftCanonical
                leftObject leftScope := by
      apply WellSorted.AvailableOpenPattern.ext
      rfl
    have rightEndpoint :
        (rightChildren.originalAvailable rightArgumentCanonical
          rightArgumentObjects rightArgumentScope).applyQuote membership
            notBareCollection quoted =
          ((CostRegionTree.neutralApplicationQuote membership
            notBareCollection constructor materializes neutral quoted
              rightChildren).originalAvailableOpenPattern rightCanonical
                rightObject rightScope).reindexFiber
                  transport.sameFiber.1.symm
                  transport.sameFiber.2.1.symm
                  transport.sameFiber.2.2.symm := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [WellSorted.AvailableOpenPattern.reindexFiber_pattern]
      rfl
    rw [leftEndpoint, rightEndpoint] at assembled
    exact assembled
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      cases declared <;>
        simp [WellSorted.parameterType?] at leftParameterType
  | multiAbstractionNamed binderNames bodyName declared =>
      cases declared with
      | base sort =>
          simp [WellSorted.parameterType?] at leftParameterType
      | arrow domain codomain =>
          cases domain <;>
            simp [WellSorted.parameterType?] at leftParameterType
      | multiBinder domain =>
          simp [WellSorted.parameterType?] at leftParameterType
      | collection collectionType elementType =>
          simp [WellSorted.parameterType?] at leftParameterType

/-- Ordinary binders preserve transport by the generic typed lambda
congruence; when the whole lambda is itself an abstraction argument, the same
body path is lifted in the stricter representation-preserving carrier. -/
theorem lambda_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {binder : Option String}
    {leftBody rightBody : Pattern} {domain codomain : TypeExpr}
    (leftTree : CostRegionTree source targetFree (domain :: available) outer
      leftBody codomain)
    (rightTree : CostRegionTree source targetFree (domain :: available) outer
      rightBody codomain)
    (body : CostRegionTreeTransport source staticLift targetFree leftTree
      rightTree)
    (bodySound : body.FiberEquation ∧ body.ArgumentFiberEquation) :
    let transport := CostRegionTreeTransport.lambda (binder := binder)
      leftTree rightTree body
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.lambda (binder := binder)
    leftTree rightTree body
  have fiberSound : transport.FiberEquation := by
    intro leftCanonical leftObject leftScope rightCanonical rightObject
      rightScope
    have leftCanonicalParts :
        binder.isNone = true ∧
          leftBody.hasCanonicalBinderMetadata = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
    have rightCanonicalParts :
        binder.isNone = true ∧
          rightBody.hasCanonicalBinderMetadata = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
    have leftBodyObject : WellSorted.isObjectPattern leftBody = true := by
      simpa [WellSorted.isObjectPattern] using leftObject
    have rightBodyObject : WellSorted.isObjectPattern rightBody = true := by
      simpa [WellSorted.isObjectPattern] using rightObject
    have leftBodyScope :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (domain :: available).length leftBody := by
      intro presentation presentationMembership
      simpa [binderSafeAt, List.length_cons] using
        leftScope presentation presentationMembership
    have rightBodyScope :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (domain :: available).length rightBody := by
      intro presentation presentationMembership
      simpa [binderSafeAt, List.length_cons] using
        rightScope presentation presentationMembership
    have bodyStep := bodySound.1 leftCanonicalParts.2 leftBodyObject
      leftBodyScope rightCanonicalParts.2 rightBodyObject rightBodyScope
    have assembled :=
      WellSorted.AvailableOpenPattern.equationSetoid_lambda_congr binder
        leftCanonicalParts.1 bodyStep
    have leftEndpoint :
        (leftTree.originalAvailableOpenPattern leftCanonicalParts.2
          leftBodyObject leftBodyScope).lambda binder leftCanonicalParts.1 =
          (CostRegionTree.lambda (binder := binder) leftTree
            ).originalAvailableOpenPattern leftCanonical leftObject
              leftScope := by
      apply WellSorted.AvailableOpenPattern.ext
      rfl
    have rightEndpoint :
        ((rightTree.originalAvailableOpenPattern rightCanonicalParts.2
          rightBodyObject rightBodyScope).reindexFiber
            body.sameFiber.1.symm body.sameFiber.2.1.symm
              body.sameFiber.2.2.symm).lambda binder leftCanonicalParts.1 =
          ((CostRegionTree.lambda (binder := binder) rightTree
            ).originalAvailableOpenPattern rightCanonical rightObject
              rightScope).reindexFiber transport.sameFiber.1.symm
                transport.sameFiber.2.1.symm
                transport.sameFiber.2.2.symm := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [WellSorted.AvailableOpenPattern.lambda_pattern,
        WellSorted.AvailableOpenPattern.reindexFiber_pattern,
        CostRegionTree.originalAvailableOpenPattern_pattern]
    rw [leftEndpoint, rightEndpoint] at assembled
    exact assembled
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      cases binder with
      | some display =>
          simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation
      | none =>
          have leftBodyCanonical :
              leftBody.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
          have rightBodyCanonical :
              rightBody.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
          have leftBodyObject :
              WellSorted.isObjectPattern leftBody = true := by
            simpa [WellSorted.isObjectPattern] using leftObject
          have rightBodyObject :
              WellSorted.isObjectPattern rightBody = true := by
            simpa [WellSorted.isObjectPattern] using rightObject
          have leftBodyScope :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                source.costWholeReflectionProfile
                (domain :: available).length leftBody := by
            intro presentation presentationMembership
            simpa [binderSafeAt, List.length_cons] using
              leftScope presentation presentationMembership
          have rightBodyScope :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                source.costWholeReflectionProfile
                (domain :: available).length rightBody := by
            intro presentation presentationMembership
            simpa [binderSafeAt, List.length_cons] using
              rightScope presentation presentationMembership
          have bodyStep := bodySound.1 leftBodyCanonical leftBodyObject
            leftBodyScope rightBodyCanonical rightBodyObject rightBodyScope
          let pack := fun
              (term : WellSorted.AvailableOpenPattern
                source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree (domain :: available) outer codomain) =>
            ({ term := term.lambda none rfl
               representation := True.intro
               parameterType := leftParameterType } :
              WellSorted.AvailableOpenArgument
                source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree available outer
                  (.abstractionNamed binderName bodyName declared)
                    (.arrow domain codomain))
          have packed :=
            WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
              (by
                intro first second generator
                exact EquationSemantics.reflectiveEquationContextStep_fill
                  (.lambda none .hole) generator)
              bodyStep
          have leftEndpoint :
              pack (leftTree.originalAvailableOpenPattern leftBodyCanonical
                leftBodyObject leftBodyScope) =
                (CostRegionTree.lambda (binder := none) leftTree
                  ).originalArgument
                    (.abstractionNamed binderName bodyName declared)
                      leftRepresentation leftParameterType leftCanonical
                        leftObject leftScope := by
            apply WellSorted.AvailableOpenArgument.ext
            rfl
          have rightEndpoint :
              pack ((rightTree.originalAvailableOpenPattern
                rightBodyCanonical rightBodyObject rightBodyScope
                ).reindexFiber body.sameFiber.1.symm
                  body.sameFiber.2.1.symm body.sameFiber.2.2.symm) =
                ((CostRegionTree.lambda (binder := none) rightTree
                  ).originalArgument
                    (.abstractionNamed binderName bodyName declared)
                      rightRepresentation rightParameterType rightCanonical
                        rightObject rightScope).reindexFiber
                          transport.sameFiber.1.symm
                          transport.sameFiber.2.1.symm
                          transport.sameFiber.2.2.symm := by
            apply WellSorted.AvailableOpenArgument.ext
            dsimp only [pack]
            simp only [WellSorted.AvailableOpenPattern.lambda_pattern,
              WellSorted.AvailableOpenPattern.reindexFiber_pattern,
              WellSorted.AvailableOpenArgument.reindexFiber_pattern,
              CostRegionTree.originalArgument_pattern,
              CostRegionTree.originalAvailableOpenPattern_pattern]
          rw [leftEndpoint, rightEndpoint] at packed
          exact packed
  | multiAbstractionNamed binderNames bodyName declared =>
      simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation

/-- Fixed-arity binders preserve transport in both the ordinary typed fiber
and the stricter multi-abstraction argument carrier. -/
theorem multiLambda_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {arity : Nat}
    {binders : List String} {leftBody rightBody : Pattern}
    {domain codomain : TypeExpr}
    (leftTree : CostRegionTree source targetFree
      (List.replicate arity domain ++ available) outer leftBody codomain)
    (rightTree : CostRegionTree source targetFree
      (List.replicate arity domain ++ available) outer rightBody codomain)
    (body : CostRegionTreeTransport source staticLift targetFree leftTree
      rightTree)
    (bodySound : body.FiberEquation ∧ body.ArgumentFiberEquation) :
    let transport := CostRegionTreeTransport.multiLambda
      (arity := arity) (binders := binders) leftTree rightTree body
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.multiLambda
    (arity := arity) (binders := binders) leftTree rightTree body
  have fiberSound : transport.FiberEquation := by
    intro leftCanonical leftObject leftScope rightCanonical rightObject
      rightScope
    have leftCanonicalParts :
        binders.isEmpty = true ∧
          leftBody.hasCanonicalBinderMetadata = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
    have rightCanonicalParts :
        binders.isEmpty = true ∧
          rightBody.hasCanonicalBinderMetadata = true := by
      simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
    have bindersCanonical : binders = [] := by
      simpa using leftCanonicalParts.1
    have leftBodyObject : WellSorted.isObjectPattern leftBody = true := by
      simpa [WellSorted.isObjectPattern] using leftObject
    have rightBodyObject : WellSorted.isObjectPattern rightBody = true := by
      simpa [WellSorted.isObjectPattern] using rightObject
    have leftBodyScope :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (List.replicate arity domain ++ available).length leftBody := by
      intro presentation presentationMembership
      simpa [binderSafeAt, List.length_append, List.length_replicate,
        Nat.add_comm] using leftScope presentation presentationMembership
    have rightBodyScope :
        ReflectiveWellSorted.ReflectiveScopeSafeAt
          source.costWholeReflectionProfile
          (List.replicate arity domain ++ available).length rightBody := by
      intro presentation presentationMembership
      simpa [binderSafeAt, List.length_append, List.length_replicate,
        Nat.add_comm] using rightScope presentation presentationMembership
    have bodyStep := bodySound.1 leftCanonicalParts.2 leftBodyObject
      leftBodyScope rightCanonicalParts.2 rightBodyObject rightBodyScope
    have assembled :=
      WellSorted.AvailableOpenPattern.equationSetoid_multiLambda_congr
        arity binders bindersCanonical bodyStep
    have leftEndpoint :
        (leftTree.originalAvailableOpenPattern leftCanonicalParts.2
          leftBodyObject leftBodyScope).multiLambda arity binders
            bindersCanonical =
          (CostRegionTree.multiLambda (arity := arity) (binders := binders)
            leftTree).originalAvailableOpenPattern leftCanonical leftObject
              leftScope := by
      apply WellSorted.AvailableOpenPattern.ext
      rfl
    have rightEndpoint :
        ((rightTree.originalAvailableOpenPattern rightCanonicalParts.2
          rightBodyObject rightBodyScope).reindexFiber
            body.sameFiber.1.symm body.sameFiber.2.1.symm
              body.sameFiber.2.2.symm).multiLambda arity binders
                bindersCanonical =
          ((CostRegionTree.multiLambda (arity := arity) (binders := binders)
            rightTree).originalAvailableOpenPattern rightCanonical rightObject
              rightScope).reindexFiber transport.sameFiber.1.symm
                transport.sameFiber.2.1.symm
                transport.sameFiber.2.2.symm := by
      apply WellSorted.AvailableOpenPattern.ext
      simp only [WellSorted.AvailableOpenPattern.multiLambda_pattern,
        WellSorted.AvailableOpenPattern.reindexFiber_pattern,
        CostRegionTree.originalAvailableOpenPattern_pattern]
    rw [leftEndpoint, rightEndpoint] at assembled
    exact assembled
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation
  | multiAbstractionNamed binderNames bodyName declared =>
      cases binders with
      | cons display displays =>
          simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation
      | nil =>
          have leftBodyCanonical :
              leftBody.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
          have rightBodyCanonical :
              rightBody.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
          have leftBodyObject :
              WellSorted.isObjectPattern leftBody = true := by
            simpa [WellSorted.isObjectPattern] using leftObject
          have rightBodyObject :
              WellSorted.isObjectPattern rightBody = true := by
            simpa [WellSorted.isObjectPattern] using rightObject
          have leftBodyScope :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                source.costWholeReflectionProfile
                (List.replicate arity domain ++ available).length
                  leftBody := by
            intro presentation presentationMembership
            simpa [binderSafeAt, List.length_append, List.length_replicate,
              Nat.add_comm] using
                leftScope presentation presentationMembership
          have rightBodyScope :
              ReflectiveWellSorted.ReflectiveScopeSafeAt
                source.costWholeReflectionProfile
                (List.replicate arity domain ++ available).length
                  rightBody := by
            intro presentation presentationMembership
            simpa [binderSafeAt, List.length_append, List.length_replicate,
              Nat.add_comm] using
                rightScope presentation presentationMembership
          have bodyStep := bodySound.1 leftBodyCanonical leftBodyObject
            leftBodyScope rightBodyCanonical rightBodyObject rightBodyScope
          let pack := fun
              (term : WellSorted.AvailableOpenPattern
                source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree (List.replicate arity domain ++ available) outer
                    codomain) =>
            ({ term := term.multiLambda arity [] rfl
               representation := True.intro
               parameterType := leftParameterType } :
              WellSorted.AvailableOpenArgument
                source.costWholeReflectionProfile source.costWholeLanguage
                  targetFree available outer
                  (.multiAbstractionNamed binderNames bodyName declared)
                    (.arrow (.multiBinder domain) codomain))
          have packed :=
            WellSorted.AvailableOpenArgument.equationSetoid_of_term_map pack
              (by
                intro first second generator
                exact EquationSemantics.reflectiveEquationContextStep_fill
                  (.multiLambda arity [] .hole) generator)
              bodyStep
          have leftEndpoint :
              pack (leftTree.originalAvailableOpenPattern leftBodyCanonical
                leftBodyObject leftBodyScope) =
                (CostRegionTree.multiLambda (arity := arity) (binders := [])
                  leftTree).originalArgument
                    (.multiAbstractionNamed binderNames bodyName declared)
                      leftRepresentation leftParameterType leftCanonical
                        leftObject leftScope := by
            apply WellSorted.AvailableOpenArgument.ext
            rfl
          have rightEndpoint :
              pack ((rightTree.originalAvailableOpenPattern
                rightBodyCanonical rightBodyObject rightBodyScope
                ).reindexFiber body.sameFiber.1.symm
                  body.sameFiber.2.1.symm body.sameFiber.2.2.symm) =
                ((CostRegionTree.multiLambda (arity := arity) (binders := [])
                  rightTree).originalArgument
                    (.multiAbstractionNamed binderNames bodyName declared)
                      rightRepresentation rightParameterType rightCanonical
                        rightObject rightScope).reindexFiber
                          transport.sameFiber.1.symm
                          transport.sameFiber.2.1.symm
                          transport.sameFiber.2.2.symm := by
            apply WellSorted.AvailableOpenArgument.ext
            dsimp only [pack]
            simp only [WellSorted.AvailableOpenPattern.multiLambda_pattern,
              WellSorted.AvailableOpenPattern.reindexFiber_pattern,
              WellSorted.AvailableOpenArgument.reindexFiber_pattern,
              CostRegionTree.originalArgument_pattern,
              CostRegionTree.originalAvailableOpenPattern_pattern]
          rw [leftEndpoint, rightEndpoint] at packed
          exact packed

/-- Explicit substitution nodes are outside the admitted open-object carrier,
so transport beneath their body is semantically unreachable. -/
theorem substBody_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftBody rightBody replacement : Pattern}
    {domain codomain : TypeExpr}
    (leftTree : CostRegionTree source targetFree (domain :: available)
      outer leftBody codomain)
    (rightTree : CostRegionTree source targetFree (domain :: available)
      outer rightBody codomain)
    (replacementTree : CostRegionTree source targetFree available outer
      replacement domain)
    (body : CostRegionTreeTransport source staticLift targetFree leftTree
      rightTree) :
    let transport := CostRegionTreeTransport.substBody leftTree rightTree
      replacementTree body
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  constructor
  · intro leftCanonical leftObject
    simp [WellSorted.isObjectPattern] at leftObject
  · intro parameter leftRepresentation rightRepresentation leftParameterType
      rightParameterType leftCanonical leftObject
    simp [WellSorted.isObjectPattern] at leftObject

/-- The same carrier exclusion makes transport beneath the replacement arm of
an explicit substitution unreachable. -/
theorem substReplacement_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {bodyPattern leftReplacement rightReplacement : Pattern}
    {domain codomain : TypeExpr}
    (bodyTree : CostRegionTree source targetFree (domain :: available)
      outer bodyPattern codomain)
    (leftTree : CostRegionTree source targetFree available outer
      leftReplacement domain)
    (rightTree : CostRegionTree source targetFree available outer
      rightReplacement domain)
    (replacement : CostRegionTreeTransport source staticLift targetFree
      leftTree rightTree) :
    let transport := CostRegionTreeTransport.substReplacement bodyTree
      leftTree rightTree replacement
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  constructor
  · intro leftCanonical leftObject
    simp [WellSorted.isObjectPattern] at leftObject
  · intro parameter leftRepresentation rightRepresentation leftParameterType
      rightParameterType leftCanonical leftObject
    simp [WellSorted.isObjectPattern] at leftObject

/-- Homogeneous collection frames preserve transport by pointwise authored
element congruence.  Open-object admission removes the rest-variable case. -/
theorem collection_semanticEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    {elementType : TypeExpr}
    (leftChildren : CostRegionElementTrees source targetFree available outer
      leftElements elementType)
    (rightChildren : CostRegionElementTrees source targetFree available outer
      rightElements elementType)
    (elements : CostRegionElementTreesTransport source staticLift targetFree
      leftChildren rightChildren)
    (elementsSound : elements.FiberEquations) :
    let transport := CostRegionTreeTransport.collection
      (collectionType := collectionType) (rest := rest)
        leftChildren rightChildren elements
    transport.FiberEquation ∧ transport.ArgumentFiberEquation := by
  dsimp only
  let transport := CostRegionTreeTransport.collection
    (collectionType := collectionType) (rest := rest)
      leftChildren rightChildren elements
  have fiberSound : transport.FiberEquation := by
    intro leftCanonical leftObject leftScope rightCanonical rightObject
      rightScope
    cases rest with
    | some restName =>
        simp [WellSorted.isObjectPattern] at leftObject
    | none =>
        have leftElementCanonical :
            Pattern.hasCanonicalBinderMetadataList leftElements = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using leftCanonical
        have rightElementCanonical :
            Pattern.hasCanonicalBinderMetadataList rightElements = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using rightCanonical
        have leftElementObjects :
            WellSorted.isObjectPatternList leftElements = true := by
          simpa [WellSorted.isObjectPattern] using leftObject
        have rightElementObjects :
            WellSorted.isObjectPatternList rightElements = true := by
          simpa [WellSorted.isObjectPattern] using rightObject
        have leftElementScope : ∀ presentation ∈
            source.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor available.length
              leftElements = true := by
          intro presentation presentationMembership
          simpa [binderSafeAt] using
            leftScope presentation presentationMembership
        have rightElementScope : ∀ presentation ∈
            source.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor available.length
              rightElements = true := by
          intro presentation presentationMembership
          simpa [binderSafeAt] using
            rightScope presentation presentationMembership
        have assembled :=
          (elementsSound leftElementCanonical leftElementObjects
            leftElementScope rightElementCanonical rightElementObjects
            rightElementScope).assemble collectionType
        have leftEndpoint :
            (leftChildren.originalAvailable leftElementCanonical
              leftElementObjects leftElementScope).collection collectionType =
              (CostRegionTree.collection (collectionType := collectionType)
                (rest := none) leftChildren).originalAvailableOpenPattern
                  leftCanonical leftObject leftScope := by
          apply WellSorted.AvailableOpenPattern.ext
          rfl
        have rightEndpoint :
            (rightChildren.originalAvailable rightElementCanonical
              rightElementObjects rightElementScope).collection collectionType =
              ((CostRegionTree.collection (collectionType := collectionType)
                (rest := none) rightChildren).originalAvailableOpenPattern
                  rightCanonical rightObject rightScope).reindexFiber
                    transport.sameFiber.1.symm
                    transport.sameFiber.2.1.symm
                    transport.sameFiber.2.2.symm := by
          apply WellSorted.AvailableOpenPattern.ext
          simp only [WellSorted.AvailableOpenPattern.reindexFiber_pattern]
          rfl
        rw [leftEndpoint, rightEndpoint] at assembled
        exact assembled
  refine ⟨fiberSound, ?_⟩
  intro parameter leftRepresentation rightRepresentation leftParameterType
    rightParameterType leftCanonical leftObject leftScope rightCanonical
    rightObject rightScope
  cases parameter with
  | simple name declared =>
      exact simpleArgument_of_fiberEquation fiberSound name declared
        leftParameterType rightParameterType leftCanonical leftObject
          leftScope rightCanonical rightObject rightScope
  | abstractionNamed binderName bodyName declared =>
      simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation
  | multiAbstractionNamed binderNames bodyName declared =>
      simp [WellSorted.MatchesParameterRepresentation] at leftRepresentation

end CostRegionTreeTransport

namespace CostRegionArgumentTreesTransport

/-- The empty constructor spine carries the reflexive pointwise equation. -/
theorem nil_fiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} :
    let transport := CostRegionArgumentTreesTransport.nil
      (source := source) (staticLift := staticLift)
      (targetFree := targetFree) (available := available) (outer := outer)
    transport.FiberEquations := by
  dsimp only
  intro leftCanonical leftObjects leftScope rightCanonical rightObjects
    rightScope
  let empty :=
    WellSorted.AvailableOpenArguments.nil
      (profile := source.costWholeReflectionProfile)
        source.costWholeLanguage targetFree available outer
  have leftEndpoint :
      (CostRegionArgumentTrees.nil (source := source)
        (targetFree := targetFree)).originalAvailable leftCanonical leftObjects
          leftScope = empty := by
    apply WellSorted.AvailableOpenArguments.ext
    rfl
  have rightEndpoint :
      (CostRegionArgumentTrees.nil (source := source)
        (targetFree := targetFree)).originalAvailable rightCanonical
          rightObjects rightScope = empty := by
    apply WellSorted.AvailableOpenArguments.ext
    rfl
  rw [leftEndpoint]
  exact WellSorted.AvailableOpenArguments.EquationForall₂.nil

/-- A constructor-spine cons transports pointwise when its head remains in
the authored parameter carrier and its tail transports pointwise. -/
theorem cons_fiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
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
    (leftHead : CostRegionTree source targetFree available outer leftArgument
      expected)
    (rightHead : CostRegionTree source targetFree available outer rightArgument
      expected)
    (leftTail : CostRegionArgumentTrees source targetFree available outer
      leftArguments parameters)
    (rightTail : CostRegionArgumentTrees source targetFree available outer
      rightArguments parameters)
    (head : CostRegionTreeTransport source staticLift targetFree leftHead
      rightHead)
    (tail : CostRegionArgumentTreesTransport source staticLift targetFree
      leftTail rightTail)
    (headSound : head.FiberEquation ∧ head.ArgumentFiberEquation)
    (tailSound : tail.FiberEquations) :
    let transport := CostRegionArgumentTreesTransport.cons
      leftRepresentation rightRepresentation parameterType leftHead rightHead
        leftTail rightTail head tail
    transport.FiberEquations := by
  dsimp only
  intro leftCanonical leftObjects leftScope rightCanonical rightObjects
    rightScope
  have leftCanonicalParts :
      leftArgument.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList leftArguments = true := by
    simpa [Pattern.hasCanonicalBinderMetadataList] using leftCanonical
  have rightCanonicalParts :
      rightArgument.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList rightArguments = true := by
    simpa [Pattern.hasCanonicalBinderMetadataList] using rightCanonical
  have leftObjectParts :
      WellSorted.isObjectPattern leftArgument = true ∧
        WellSorted.isObjectPatternList leftArguments = true := by
    simpa [WellSorted.isObjectPatternList] using leftObjects
  have rightObjectParts :
      WellSorted.isObjectPattern rightArgument = true ∧
        WellSorted.isObjectPatternList rightArguments = true := by
    simpa [WellSorted.isObjectPatternList] using rightObjects
  have leftHeadScope :
      ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length leftArgument := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              leftArgument = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              leftArguments = true := by
      simpa [binderSafeListAt] using
        leftScope presentation presentationMembership
    exact parts.1
  have rightHeadScope :
      ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length rightArgument := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              rightArgument = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              rightArguments = true := by
      simpa [binderSafeListAt] using
        rightScope presentation presentationMembership
    exact parts.1
  have leftTailScope : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        leftArguments = true := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              leftArgument = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              leftArguments = true := by
      simpa [binderSafeListAt] using
        leftScope presentation presentationMembership
    exact parts.2
  have rightTailScope : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        rightArguments = true := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              rightArgument = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              rightArguments = true := by
      simpa [binderSafeListAt] using
        rightScope presentation presentationMembership
    exact parts.2
  have headStep := headSound.2 parameter leftRepresentation
    rightRepresentation parameterType parameterType leftCanonicalParts.1
      leftObjectParts.1 leftHeadScope rightCanonicalParts.1
        rightObjectParts.1 rightHeadScope
  have tailStep := tailSound leftCanonicalParts.2 leftObjectParts.2
    leftTailScope rightCanonicalParts.2 rightObjectParts.2 rightTailScope
  have combined :=
    WellSorted.AvailableOpenArguments.EquationForall₂.cons headStep tailStep
  have leftEndpoint :
      WellSorted.AvailableOpenArguments.cons
          (leftHead.originalArgument parameter leftRepresentation parameterType
            leftCanonicalParts.1 leftObjectParts.1 leftHeadScope)
          (leftTail.originalAvailable leftCanonicalParts.2 leftObjectParts.2
            leftTailScope) =
        (CostRegionArgumentTrees.cons leftRepresentation parameterType
          leftHead leftTail).originalAvailable leftCanonical leftObjects
            leftScope := by
    apply WellSorted.AvailableOpenArguments.ext
    rfl
  have rightEndpoint :
      WellSorted.AvailableOpenArguments.cons
          ((rightHead.originalArgument parameter rightRepresentation
            parameterType rightCanonicalParts.1 rightObjectParts.1
              rightHeadScope).reindexFiber head.sameFiber.1.symm
                head.sameFiber.2.1.symm head.sameFiber.2.2.symm)
          (rightTail.originalAvailable rightCanonicalParts.2 rightObjectParts.2
            rightTailScope) =
        (CostRegionArgumentTrees.cons rightRepresentation parameterType
          rightHead rightTail).originalAvailable rightCanonical rightObjects
            rightScope := by
    apply WellSorted.AvailableOpenArguments.ext
    rfl
  rw [leftEndpoint, rightEndpoint] at combined
  exact combined

end CostRegionArgumentTreesTransport

namespace CostRegionElementTreesTransport

/-- The empty homogeneous spine carries the reflexive pointwise equation. -/
theorem nil_fiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    (available outer : List TypeExpr) (elementType : TypeExpr) :
    let transport := CostRegionElementTreesTransport.nil
      (source := source) (staticLift := staticLift)
      (targetFree := targetFree) available outer elementType
    transport.FiberEquations := by
  dsimp only
  intro leftCanonical leftObjects leftScope rightCanonical rightObjects
    rightScope
  let empty := WellSorted.AvailableOpenElements.nil
    (profile := source.costWholeReflectionProfile)
      source.costWholeLanguage targetFree available outer elementType
  have leftEndpoint :
      (CostRegionElementTrees.nil (source := source) (targetFree := targetFree)
        available outer elementType).originalAvailable leftCanonical
          leftObjects leftScope = empty := by
    apply WellSorted.AvailableOpenElements.ext
    rfl
  have rightEndpoint :
      (CostRegionElementTrees.nil (source := source) (targetFree := targetFree)
        available outer elementType).originalAvailable rightCanonical
          rightObjects rightScope = empty := by
    apply WellSorted.AvailableOpenElements.ext
    rfl
  rw [leftEndpoint]
  exact WellSorted.AvailableOpenElements.EquationForall₂.nil

/-- A homogeneous-spine cons transports pointwise when both the head and tail
do. -/
theorem cons_fiberEquations
    {source : CIGSLT} {staticLift : CostStaticPlanLift source}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftElement rightElement : Pattern}
    {leftElements rightElements : List Pattern} {elementType : TypeExpr}
    (leftHead : CostRegionTree source targetFree available outer leftElement
      elementType)
    (rightHead : CostRegionTree source targetFree available outer rightElement
      elementType)
    (leftTail : CostRegionElementTrees source targetFree available outer
      leftElements elementType)
    (rightTail : CostRegionElementTrees source targetFree available outer
      rightElements elementType)
    (head : CostRegionTreeTransport source staticLift targetFree leftHead
      rightHead)
    (tail : CostRegionElementTreesTransport source staticLift targetFree
      leftTail rightTail)
    (headSound : head.FiberEquation)
    (tailSound : tail.FiberEquations) :
    let transport := CostRegionElementTreesTransport.cons leftHead rightHead
      leftTail rightTail head tail
    transport.FiberEquations := by
  dsimp only
  intro leftCanonical leftObjects leftScope rightCanonical rightObjects
    rightScope
  have leftCanonicalParts :
      leftElement.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList leftElements = true := by
    simpa [Pattern.hasCanonicalBinderMetadataList] using leftCanonical
  have rightCanonicalParts :
      rightElement.hasCanonicalBinderMetadata = true ∧
        Pattern.hasCanonicalBinderMetadataList rightElements = true := by
    simpa [Pattern.hasCanonicalBinderMetadataList] using rightCanonical
  have leftObjectParts :
      WellSorted.isObjectPattern leftElement = true ∧
        WellSorted.isObjectPatternList leftElements = true := by
    simpa [WellSorted.isObjectPatternList] using leftObjects
  have rightObjectParts :
      WellSorted.isObjectPattern rightElement = true ∧
        WellSorted.isObjectPatternList rightElements = true := by
    simpa [WellSorted.isObjectPatternList] using rightObjects
  have leftHeadScope :
      ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length leftElement := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              leftElement = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              leftElements = true := by
      simpa [binderSafeListAt] using
        leftScope presentation presentationMembership
    exact parts.1
  have rightHeadScope :
      ReflectiveWellSorted.ReflectiveScopeSafeAt
        source.costWholeReflectionProfile
        available.length rightElement := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              rightElement = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              rightElements = true := by
      simpa [binderSafeListAt] using
        rightScope presentation presentationMembership
    exact parts.1
  have leftTailScope : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        leftElements = true := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              leftElement = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              leftElements = true := by
      simpa [binderSafeListAt] using
        leftScope presentation presentationMembership
    exact parts.2
  have rightTailScope : ∀ presentation ∈
      source.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor available.length
        rightElements = true := by
    intro presentation presentationMembership
    have parts :
        binderSafeAt presentation.quoteConstructor available.length
              rightElement = true ∧
          binderSafeListAt presentation.quoteConstructor available.length
              rightElements = true := by
      simpa [binderSafeListAt] using
        rightScope presentation presentationMembership
    exact parts.2
  have headStep := headSound leftCanonicalParts.1 leftObjectParts.1
    leftHeadScope rightCanonicalParts.1 rightObjectParts.1 rightHeadScope
  have tailStep := tailSound leftCanonicalParts.2 leftObjectParts.2
    leftTailScope rightCanonicalParts.2 rightObjectParts.2 rightTailScope
  have combined :=
    WellSorted.AvailableOpenElements.EquationForall₂.cons headStep tailStep
  have leftEndpoint :
      WellSorted.AvailableOpenElements.cons
          (leftHead.originalAvailableOpenPattern leftCanonicalParts.1
            leftObjectParts.1 leftHeadScope)
          (leftTail.originalAvailable leftCanonicalParts.2 leftObjectParts.2
            leftTailScope) =
        (CostRegionElementTrees.cons leftHead leftTail).originalAvailable
          leftCanonical leftObjects leftScope := by
    apply WellSorted.AvailableOpenElements.ext
    rfl
  have rightEndpoint :
      WellSorted.AvailableOpenElements.cons
          ((rightHead.originalAvailableOpenPattern rightCanonicalParts.1
            rightObjectParts.1 rightHeadScope).reindexFiber
              head.sameFiber.1.symm head.sameFiber.2.1.symm
                head.sameFiber.2.2.symm)
          (rightTail.originalAvailable rightCanonicalParts.2 rightObjectParts.2
            rightTailScope) =
        (CostRegionElementTrees.cons rightHead rightTail).originalAvailable
          rightCanonical rightObjects rightScope := by
    apply WellSorted.AvailableOpenElements.ext
    rfl
  rw [leftEndpoint, rightEndpoint] at combined
  exact combined

end CostRegionElementTreesTransport

mutual

  /-- Every proof-relevant structural Cost transport is an authored equation
  path once the exact static-region kernel is supplied.  The second conjunct
  records the stronger representation-preserving path needed by constructor
  abstraction parameters. -/
  theorem CostRegionTreeTransport.semanticEquations
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      (staticSound : source.CostStaticRegionTransportSound staticLift)
      {targetFree : WellSorted.FreeTypeContext}
      {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
      {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
      {left : CostRegionTree source targetFree leftAvailable leftOuter
        leftPattern leftType}
      {right : CostRegionTree source targetFree rightAvailable rightOuter
        rightPattern rightType}
      (transport : CostRegionTreeTransport source staticLift targetFree left
        right) :
      transport.FiberEquation ∧ transport.ArgumentFiberEquation :=
    match transport with
    | .refl tree => CostRegionTreeTransport.refl_semanticEquations tree
    | .static leftNode rightNode leftChildren rightChildren sourceSortEq
        planStep children =>
        CostRegionTreeTransport.static_semanticEquations staticSound leftNode
          rightNode leftChildren rightChildren sourceSortEq planStep children
          (fun targetIndex =>
            (CostRegionTreeTransport.semanticEquations staticSound
              (children targetIndex)).1)
    | .neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary leftChildren rightChildren arguments =>
        CostRegionTreeTransport.neutralApplicationOrdinary_semanticEquations
          membership notBareCollection constructor materializes neutral
            ordinary leftChildren rightChildren arguments
              (CostRegionArgumentTreesTransport.semanticEquations staticSound
                arguments)
    | .neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted leftChildren rightChildren arguments =>
        CostRegionTreeTransport.neutralApplicationQuote_semanticEquations
          membership notBareCollection constructor materializes neutral quoted
            leftChildren rightChildren arguments
              (CostRegionArgumentTreesTransport.semanticEquations staticSound
                arguments)
    | .lambda leftTree rightTree body =>
        CostRegionTreeTransport.lambda_semanticEquations leftTree rightTree
          body (CostRegionTreeTransport.semanticEquations staticSound body)
    | .multiLambda leftTree rightTree body =>
        CostRegionTreeTransport.multiLambda_semanticEquations leftTree
          rightTree body
            (CostRegionTreeTransport.semanticEquations staticSound body)
    | .substBody leftTree rightTree replacementTree body =>
        CostRegionTreeTransport.substBody_semanticEquations leftTree rightTree
          replacementTree body
    | .substReplacement bodyTree leftTree rightTree replacement =>
        CostRegionTreeTransport.substReplacement_semanticEquations bodyTree
          leftTree rightTree replacement
    | .collection leftChildren rightChildren elements =>
        CostRegionTreeTransport.collection_semanticEquations leftChildren
          rightChildren elements
            (CostRegionElementTreesTransport.semanticEquations staticSound
              elements)

  /-- Constructor-spine transport is pointwise authored equivalence. -/
  theorem CostRegionArgumentTreesTransport.semanticEquations
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      (staticSound : source.CostStaticRegionTransportSound staticLift)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      {left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters}
      {right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters}
      (transport : CostRegionArgumentTreesTransport source staticLift
        targetFree left right) : transport.FiberEquations :=
    match transport with
    | .nil => CostRegionArgumentTreesTransport.nil_fiberEquations
    | .cons leftRepresentation rightRepresentation parameterType leftHead
        rightHead leftTail rightTail head tail =>
        CostRegionArgumentTreesTransport.cons_fiberEquations
          leftRepresentation rightRepresentation parameterType leftHead
            rightHead leftTail rightTail head tail
              (CostRegionTreeTransport.semanticEquations staticSound head)
              (CostRegionArgumentTreesTransport.semanticEquations staticSound
                tail)

  /-- Homogeneous collection-spine transport is pointwise authored
  equivalence. -/
  theorem CostRegionElementTreesTransport.semanticEquations
      {source : CIGSLT} {staticLift : CostStaticPlanLift source}
      (staticSound : source.CostStaticRegionTransportSound staticLift)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      {left : CostRegionElementTrees source targetFree available outer
        leftElements elementType}
      {right : CostRegionElementTrees source targetFree available outer
        rightElements elementType}
      (transport : CostRegionElementTreesTransport source staticLift
        targetFree left right) : transport.FiberEquations :=
    match transport with
    | .nil available outer elementType =>
        CostRegionElementTreesTransport.nil_fiberEquations available outer
          elementType
    | .cons leftHead rightHead leftTail rightTail head tail =>
        CostRegionElementTreesTransport.cons_fiberEquations leftHead rightHead
          leftTail rightTail head tail
            (CostRegionTreeTransport.semanticEquations staticSound head).1
            (CostRegionElementTreesTransport.semanticEquations staticSound
              tail)

end

namespace CostStaticRegionNode

namespace CostStaticSourceTerm

/-- Proof-only transport of a static source term between equal fibers. -/
def reindex
    {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {firstSourceBound secondSourceBound firstTargetBound secondTargetBound :
      List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support secondSourceBound
      secondTargetBound secondSort)
    (sourceBoundEq : firstSourceBound = secondSourceBound)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort) :
    CostStaticSourceTerm source color free support firstSourceBound
      firstTargetBound firstSort := by
  cases sourceBoundEq
  cases targetBoundEq
  cases sortEq
  exact term

@[simp]
theorem reindex_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {firstSourceBound secondSourceBound firstTargetBound secondTargetBound :
      List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support secondSourceBound
      secondTargetBound secondSort)
    (sourceBoundEq : firstSourceBound = secondSourceBound)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort) :
    (term.reindex sourceBoundEq targetBoundEq sortEq).term.1 = term.term.1 := by
  cases sourceBoundEq
  cases targetBoundEq
  cases sortEq
  rfl

/-- Reindexing along the target context and then using the canonical target
thinning does not alter the acted raw pattern. -/
theorem reindex_act_ofTarget
    {source : CIGSLT} {color : CostStaticColor}
    {free assignmentFree targetFree : WellSorted.FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {firstTargetBound secondTargetBound : List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support
      (CostStaticBinderThinning.sourceContextOfTarget source color
        secondTargetBound) secondTargetBound secondSort)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort)
    (assignment : WellSorted.SupportedOpenAssignment
      source.costWholeReflectionProfile source.costWholeLanguage
        assignmentFree targetFree assignmentSupport) :
    (term.reindex
        (congrArg
          (CostStaticBinderThinning.sourceContextOfTarget source color)
          targetBoundEq)
        targetBoundEq sortEq).act
          (CostStaticBinderThinning.ofTargetThinning source color
            firstTargetBound) assignment =
      term.act
        (CostStaticBinderThinning.ofTargetThinning source color
          secondTargetBound) assignment := by
  cases targetBoundEq
  cases sortEq
  rfl

end CostStaticSourceTerm

/-- Repackage a node's source skeleton in any containing finite boundary
table.  The raw skeleton is unchanged; only its exact free/support evidence
is reconstructed from the checked plan. -/
def sourceActionTermIn
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    CostStaticSourceTerm source color globalTable.sourceFreeContext
      globalTable.sourceSupport node.sourceBound node.targetBound
        node.sourceSort := by
  let supportedSafe :=
    node.plan.abstractPattern_supportedSafe globalTable entriesSubset
  let supported := Classical.choose supportedSafe
  let safe := Classical.choose_spec supportedSafe
  let core : WellSorted.OpenTerm
      source.theory.presentation.presentation.language
      globalTable.sourceFreeContext node.sourceBound node.sourceSort :=
    ⟨node.plan.abstractPattern, supported.toHasType,
      node.plan.abstractPattern_canonicalBinderMetadata node.term.2.2.1,
      node.plan.abstractPattern_object node.term.2.2.2.1,
      supported.toHasType.isWellScopedAt⟩
  exact
    { term := ⟨core.1, core.2,
        node.plan.abstractPattern_reflectiveScopeSafeAt⟩
      supported := supported
      safe := safe }

@[simp]
theorem sourceActionTermIn_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    (node.sourceActionTermIn globalTable entriesSubset).term.1 =
      node.plan.abstractPattern := by
  rfl

/-- Restoring a node through any containing finite table recovers its exact
compact term; enlarging the table changes only proof support. -/
theorem restoreMappedAbstractPatternIn_eq_term
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        globalTable.restorationSupport globalTable.restorationAssignment
        node.targetBound.length
        (node.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source) node.plan.abstractPattern)) =
      node.term.1 := by
  change ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      globalTable.restorationSupport globalTable.restorationAssignment
      node.targetBound.length
      ((CostStaticBinderThinning.ofTargetThinning source color
        node.targetBound).thickenAmbientBVars 0
          (mapPattern (color.symbols source) node.plan.abstractPattern)) =
    node.term.1
  exact (node.plan.restoreMappedAbstractPattern globalTable entriesSubset
    node.term.2.2.2.1).trans node.plan.recomposePattern_eq

end CostStaticRegionNode

namespace CIGSLT

/-- Same-colour action of one authored generator discharges the complete
static-region support-erasure kernel.

The two finite boundary tables are joined before either endpoint is acted
upon.  Their collision-free keys make this one supported assignment restore
both plans exactly.  The proof therefore consumes only the mapped generator
law; recursive child paths retain elaboration provenance but introduce no
additional compact equation authority. -/
theorem costStaticRegionTransportSound_of_mappedGeneratorFiberAction
    (source : CIGSLT) (staticLift : CostStaticPlanLift source)
    (stable : CostStaticMappedGeneratorFiberAction source) :
    source.CostStaticRegionTransportSound staticLift := by
  intro targetFree color outer leftNode rightNode leftChildren rightChildren
    sourceSortEq planStep children childrenSound leftCanonical leftObject
      leftScope rightCanonical rightObject rightScope
  let globalTable := TypedCostRegionBoundaryTable.append
    leftNode.boundaryTable rightNode.boundaryTable
  have leftSubset : leftNode.boundaryTable.entries ⊆ globalTable.entries := by
    intro boundary membership
    simpa only [globalTable, TypedCostRegionBoundaryTable.entries_append] using
      List.mem_append_left rightNode.boundaryTable.entries membership
  have rightSubset :
      rightNode.boundaryTable.entries ⊆ globalTable.entries := by
    intro boundary membership
    simpa only [globalTable, TypedCostRegionBoundaryTable.entries_append] using
      List.mem_append_right leftNode.boundaryTable.entries membership
  have globalCoherent : globalTable.FiberCoherent := by
    exact (TypedCostRegionBoundaryTable.fiberCoherent_append_iff
      leftNode.boundaryTable rightNode.boundaryTable).2
        ⟨leftNode.plan.boundaryTable_fiberCoherent,
          rightNode.plan.boundaryTable_fiberCoherent⟩
  let globalTransport :=
    globalTable.transport_of_fiberCoherent globalCoherent
  let assignment := globalTable.supportedOpenAssignment
  have targetBoundEq : leftNode.targetBound = rightNode.targetBound :=
    leftNode.plan.decoration_targetBound.symm.trans
      ((staticLift.preservesFiber planStep).targetBound_eq.trans
        rightNode.plan.decoration_targetBound)
  let sourceBoundEq : leftNode.sourceBound = rightNode.sourceBound :=
    congrArg (CostStaticBinderThinning.sourceContextOfTarget source color)
      targetBoundEq
  have targetTypeEq :
      TypeExpr.base
          (CostStaticColor.mapLangSort source color leftNode.sourceSort).1 =
        TypeExpr.base
          (CostStaticColor.mapLangSort source color rightNode.sourceSort).1 := by
    simp only [CostStaticColor.mapLangSort_name]
    exact congrArg
      (fun name => TypeExpr.base ((color.symbols source).sort name))
      (congrArg Subtype.val sourceSortEq)
  let leftSource := leftNode.sourceActionTermIn globalTable leftSubset
  let rightSourceRaw := rightNode.sourceActionTermIn globalTable rightSubset
  let rightSource : CostStaticRegionNode.CostStaticSourceTerm source color
      globalTable.sourceFreeContext globalTable.sourceSupport
      leftNode.sourceBound leftNode.targetBound leftNode.sourceSort :=
    rightSourceRaw.reindex sourceBoundEq targetBoundEq sourceSortEq
  have sourceGenerator :
      CostStaticRegionNode.CostStaticSourceTerm.generator leftSource
        rightSource := by
    unfold CostStaticRegionNode.CostStaticSourceTerm.generator
    simpa only [leftSource, rightSource, rightSourceRaw,
      CostStaticRegionNode.CostStaticSourceTerm.reindex_pattern,
      CostStaticRegionNode.sourceActionTermIn_pattern,
      leftNode.plan.decoration_abstractPattern,
      rightNode.plan.decoration_abstractPattern] using
      (staticLift.generatorWitness planStep).erase
  have localPath := stable leftNode.thinning assignment
    globalTransport.freeContext globalTransport.reflectiveSupport sourceGenerator
  have openPathRaw :=
    WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
      localPath
  have openPath :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
    (List.append_nil leftNode.targetBound) openPathRaw
  have lifted :=
    WellSorted.AvailableOpenPattern.reflectiveOpenPatternEquationSetoid_to_availableWithOuter
      outer openPath
  have leftEndpoint :
      WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
          ((leftSource.actAvailable leftNode.thinning assignment
            globalTransport.freeContext globalTransport.reflectiveSupport
            ).toReflectiveOpenPattern.reindexBound
              (List.append_nil leftNode.targetBound)) outer =
        (CostRegionTree.static leftNode leftChildren
          ).originalAvailableOpenPattern leftCanonical leftObject leftScope := by
    apply WellSorted.AvailableOpenPattern.ext
    simp only [WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern]
    simpa [leftSource, CostStaticRegionNode.CostStaticSourceTerm.act,
      assignment, TypedCostRegionBoundaryTable.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.supportedAssignment,
      ReflectiveContextSupport.substitute, globalTransport] using
      leftNode.restoreMappedAbstractPatternIn_eq_term globalTable leftSubset
  have rightEndpoint :
      WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
          ((rightSource.actAvailable leftNode.thinning assignment
            globalTransport.freeContext globalTransport.reflectiveSupport
            ).toReflectiveOpenPattern.reindexBound
              (List.append_nil leftNode.targetBound)) outer =
        ((CostRegionTree.static rightNode rightChildren
          ).originalAvailableOpenPattern rightCanonical rightObject rightScope
          ).reindexFiber targetBoundEq.symm rfl targetTypeEq.symm := by
    apply WellSorted.AvailableOpenPattern.ext
    simp only [WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      WellSorted.AvailableOpenPattern.reindexFiber_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern]
    rw [CostStaticRegionNode.CostStaticSourceTerm.reindex_act_ofTarget
      rightSourceRaw targetBoundEq sourceSortEq assignment]
    simpa [rightSourceRaw,
      CostStaticRegionNode.CostStaticSourceTerm.act,
      assignment, TypedCostRegionBoundaryTable.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.supportedAssignment,
      ReflectiveContextSupport.substitute, globalTransport] using
      rightNode.restoreMappedAbstractPatternIn_eq_term globalTable rightSubset
  rw [leftEndpoint, rightEndpoint] at lifted
  exact lifted

/-- The exact static-region kernel is sufficient for the complete structural
transport erasure law.  All binders, quotations, neutral constructors, and
collection spines are discharged by the generic typed congruence proved
above. -/
theorem costStructuralTransportSound_of_static
    (source : CIGSLT) (staticLift : CostStaticPlanLift source)
    (staticSound : source.CostStaticRegionTransportSound staticLift) :
    source.CostStructuralTransportSound staticLift := by
  intro targetFree targetBound targetSort left right transport
  have splitPath :=
    (CostRegionTreeTransport.semanticEquations staticSound transport).1
      left.1.2.1.2.1 left.1.2.1.2.2.1 left.1.2.2
      right.1.2.1.2.1 right.1.2.1.2.2.1 right.1.2.2
  have openPath :=
    WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
      splitPath
  have transported :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
      (List.append_nil targetBound) openPath
  have leftEndpoint :
      (left.2.tree.originalAvailableOpenPattern left.1.2.1.2.1
        left.1.2.1.2.2.1 left.1.2.2).toReflectiveOpenPattern.reindexBound
          (List.append_nil targetBound) = left.1 := by
    apply Subtype.ext
    simp [CostRegionTree.originalAvailableOpenPattern_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  have rightEndpoint :
      (((right.2.tree.originalAvailableOpenPattern right.1.2.1.2.1
        right.1.2.1.2.2.1 right.1.2.2).reindexFiber
          transport.sameFiber.1.symm transport.sameFiber.2.1.symm
            transport.sameFiber.2.2.symm).toReflectiveOpenPattern.reindexBound
              (List.append_nil targetBound)) = right.1 := by
    apply Subtype.ext
    simp [WellSorted.AvailableOpenPattern.reindexFiber_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  change (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
    source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage targetFree targetBound (.base targetSort.1)).r
        left.1 right.1
  rw [leftEndpoint, rightEndpoint] at transported
  exact transported

/-- A same-colour action for mapped authored generators supplies the entire
structural support-erasure theorem.  This is the public composition point:
the finite-table restoration argument discharges static regions, while the
generic congruence theorem handles every structural constructor. -/
theorem costStructuralTransportSound_of_mappedGeneratorFiberAction
    (source : CIGSLT) (staticLift : CostStaticPlanLift source)
    (stable : CostStaticMappedGeneratorFiberAction source) :
    source.CostStructuralTransportSound staticLift :=
  source.costStructuralTransportSound_of_static staticLift
    (source.costStaticRegionTransportSound_of_mappedGeneratorFiberAction
      staticLift stable)

end CIGSLT

end Mettapedia.GSLT.LanguageDef
