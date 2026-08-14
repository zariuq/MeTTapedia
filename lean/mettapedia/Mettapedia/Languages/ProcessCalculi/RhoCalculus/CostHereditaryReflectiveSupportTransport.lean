import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObject
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryTreeReflectiveSupport

/-!
# Context transport for reflective support, and the supported-executor reduction

Reflective-support safety constrains a typing derivation only through its raw
object, its result type, and the support/available/binder-image data: the one
clause that consults the free context (`fvar`) packages its own lookup, and
its support-shape side condition never mentions the context.  So safety
evidence for an object transports between typing derivations over *different*
free contexts and *different* binder fibres at once.

That transport closes the gap between the two reflective-support endpoints in
this lane:

* the structural theorem
  `rhoCostNormalizeOpenWithStatic_preservesReflectiveSupport` speaks about the
  plain hereditary executor at whatever free context it is given, while
* the live Cost₁ obligation `RhoHereditaryReflectiveSupportPreserving` speaks
  about the finite-support executor, which restricts the caller's free
  context, runs the plain executor, and recontextualizes the result.

Restriction and recontextualization keep the raw pattern and the binder fibre
and change only the free context, so both crossings are instances of the one
transport theorem.  The reduction `rhoHereditaryReflectiveSupportPreserving_of`
therefore leaves exactly one semantic obligation on the support side of the
rho Cost₁ object: the local static-node law
`RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer`.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## Object-only transport between typing contexts -/

/-- On rho's generated Cost language, reflective-support evidence for an
object depends on the selected typing derivation only through its raw object
and result type.  It may therefore be rebuilt over a different free context
*and* a different binder fibre in which the same object has the same type.
Explicit substitution is excluded by the object premise; generated-label and
collection-choice determinism align the remaining potentially ambiguous
typing branches. -/
theorem rhoCostReflectiveSupportSafeAt_recontext_of_object
    {sourceFree : FreeTypeContext} {sourceBound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {sourceTyped : HasType rhoCIGSLT.costWholeLanguage sourceFree sourceBound
      pattern type}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : sourceTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (object : isObjectPattern pattern = true)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    (targetTyped : HasType rhoCIGSLT.costWholeLanguage targetFree targetBound
      pattern type) :
    targetTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCIGSLT.costWholeLanguage sourceFree bound pattern
        type)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPattern pattern = true →
      ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
        (targetTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
          targetBound pattern type),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage sourceFree bound
        arguments parameters)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPatternList arguments = true →
      ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
        (targetTyped : ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage
          targetFree targetBound arguments parameters),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType rhoCIGSLT.costWholeLanguage sourceFree bound
        elements elementType)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPatternList elements = true →
      ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
        (targetTyped : ElementsHaveType rhoCIGSLT.costWholeLanguage targetFree
          targetBound elements elementType),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (by
      intro bound index type lookup currentAvailable currentImage _object
        targetFree targetBound targetTyped
      cases targetTyped with
      | bvar targetLookup => exact .bvar targetLookup currentAvailable)
    (by
      intro bound name type lookup currentAvailable currentImage shape _object
        targetFree targetBound targetTyped
      cases targetTyped with
      | fvar targetLookup => exact .fvar targetLookup currentAvailable shape)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage quoted argumentsSafe argumentsIH object
        targetFree targetBound targetTyped
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using object
      obtain ⟨targetRule, targetMembership, targetLabel, targetNotBare,
          _targetType, targetArguments⟩ := hasType_apply_inversion targetTyped
      have ruleEquality : targetRule = rule :=
        rho_costWholeLanguage_labelDeterministic targetMembership membership
          targetLabel.symm
      subst targetRule
      have targetArgumentsSafe := argumentsIH argumentsObject targetArguments
      exact (HasType.ReflectiveSupportSafeAt.constructorQuote
        (membership := targetMembership) (notBare := targetNotBare)
        quoted targetArgumentsSafe).castTyping)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage ordinary argumentsSafe argumentsIH object
        targetFree targetBound targetTyped
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using object
      obtain ⟨targetRule, targetMembership, targetLabel, targetNotBare,
          _targetType, targetArguments⟩ := hasType_apply_inversion targetTyped
      have ruleEquality : targetRule = rule :=
        rho_costWholeLanguage_labelDeterministic targetMembership membership
          targetLabel.symm
      subst targetRule
      have targetArgumentsSafe := argumentsIH argumentsObject targetArguments
      exact (HasType.ReflectiveSupportSafeAt.constructorOrdinary
        (membership := targetMembership) (notBare := targetNotBare)
        ordinary targetArgumentsSafe).castTyping)
    (by
      intro bound binder body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH object targetFree targetBound targetTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      cases targetTyped with
      | lambda targetBody => exact .lambda (bodyIH bodyObject targetBody))
    (by
      intro bound arity binders body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH object targetFree targetBound targetTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      cases targetTyped with
      | multiLambda targetBody =>
          exact .multiLambda (bodyIH bodyObject targetBody))
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable currentImage bodySafe replacementSafe bodyIH
        replacementIH object targetFree targetBound targetTyped
      simp [isObjectPattern] at object)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        currentAvailable currentImage elementsSafe elementsIH object targetFree
        targetBound targetTyped
      have objectParts : rest.isNone = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPattern] using object
      have elementsObject : isObjectPatternList elements = true := by
        exact objectParts.2
      rcases hasType_collection_inversion targetTyped with
        ⟨targetElementType, targetType, targetElements⟩ |
        ⟨targetRule, targetName, targetElementType, targetMembership,
          targetShape, targetType, targetElements⟩
      · have elementTypeEquality : elementType = targetElementType :=
          (TypeExpr.collection.inj targetType).2
        subst targetElementType
        exact HasType.ReflectiveSupportSafeAt.castTyping
          (target := targetTyped)
          (.collection (elementsIH elementsObject targetElements))
      · simp at targetType)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped currentAvailable currentImage
        elementsSafe elementsIH object targetFree targetBound targetTyped
      have objectParts : rest.isNone = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPattern] using object
      have elementsObject : isObjectPatternList elements = true := by
        exact objectParts.2
      rcases hasType_collection_inversion targetTyped with
        ⟨targetElementType, targetType, targetElements⟩ |
        ⟨targetRule, targetName, targetElementType, targetMembership,
          targetShape, targetType, targetElements⟩
      · simp at targetType
      · have categoryEquality : rule.category = targetRule.category :=
          TypeExpr.base.inj targetType
        have elementTypeEquality : elementType = targetElementType :=
          rho_costWholeLanguage_collectionChoiceDeterministic membership
            targetMembership parameterShape targetShape categoryEquality
        subst targetElementType
        have targetElementsSafe := elementsIH elementsObject targetElements
        have constructedSafe :
            (HasType.collectionConstructor (rest := rest) targetMembership
              targetShape targetElements).ReflectiveSupportSafeAt
                rhoCIGSLT.costWholeReflectionProfile support currentAvailable
                  currentImage :=
          HasType.ReflectiveSupportSafeAt.collectionConstructor
            (membership := targetMembership)
            (parameterShape := targetShape) targetElementsSafe
        have packaged : ∃ constructedTyped :
            HasType rhoCIGSLT.costWholeLanguage targetFree targetBound
              (.collection collectionType elements rest)
                (.base targetRule.category),
            constructedTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support currentAvailable
                currentImage :=
          ⟨_, constructedSafe⟩
        have repackaged : ∃ constructedTyped :
            HasType rhoCIGSLT.costWholeLanguage targetFree targetBound
              (.collection collectionType elements rest) (.base rule.category),
            constructedTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support currentAvailable
                currentImage := by
          rw [categoryEquality]
          exact packaged
        obtain ⟨constructedTyped, finalSafe⟩ := repackaged
        exact HasType.ReflectiveSupportSafeAt.castTyping
          (target := targetTyped) finalSafe)
    (by
      intro bound currentAvailable currentImage _objects targetFree targetBound
        targetTyped
      cases targetTyped
      exact .nil targetBound currentAvailable)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH objects targetFree targetBound targetTyped
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using objects
      cases targetTyped with
      | @cons _ targetArgument targetArguments targetParameter targetParameters
          targetExpected targetRepresentation targetParameterType
          targetArgumentTyped targetArgumentsTyped =>
          have expectedEquality : targetExpected = expected :=
            Option.some.inj (targetParameterType.symm.trans parameterType)
          subst targetExpected
          exact ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := targetRepresentation)
            (parameterType := targetParameterType)
            (argumentIH objectParts.1 targetArgumentTyped)
            (argumentsIH objectParts.2 targetArgumentsTyped))
    (by
      intro bound elementType currentAvailable currentImage _objects targetFree
        targetBound targetTyped
      cases targetTyped
      exact .nil targetBound elementType currentAvailable)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        currentAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH objects targetFree targetBound targetTyped
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using objects
      cases targetTyped with
      | cons targetElement targetElements =>
          exact .cons (elementIH objectParts.1 targetElement)
            (elementsIH objectParts.2 targetElements))
    safe object targetTyped

/-! ## The supported-executor reduction -/

/-- The finite-support hereditary executor preserves every caller-relative
reflective support as soon as the *local static-node law* holds for the
hereditary static kernel.  Restriction to the finite free support and the
final recontextualization keep the raw pattern and the binder fibre, so both
context crossings are object-only transports; the plain-executor middle leg
is the already-proved structural tree theorem. -/
theorem rhoHereditaryReflectiveSupportPreserving_of
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    RhoHereditaryReflectiveSupportPreserving := by
  intro free bound sort term support available binderImage safe
  have restrictedSafe :
      term.restrictFreeContext.2.1.1.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage :=
    rhoCostReflectiveSupportSafeAt_recontext_of_object safe term.2.1.2.2.1
      term.restrictFreeContext.2.1.1
  have normalizedRestrictedSafe :=
    rhoCostNormalizeOpenWithStatic_preservesReflectiveSupport
      rhoHereditaryStaticNormalizer staticPreserves term.restrictFreeContext
      support available binderImage restrictedSafe
  exact rhoCostReflectiveSupportSafeAt_recontext_of_object
    normalizedRestrictedSafe
    (rhoCIGSLT.costNormalizeOpenWithStatic rhoHereditaryStaticNormalizer
      term.restrictFreeContext).2.1.2.2.1
    (rhoCostNormalizeOpenHereditarySupported term).2.1.1

/-! ## The rho Cost₁ object over the reduced obligations -/

/-- The rho Cost₁ object laws, assembled from generator tree alignability and
the local static-node reflective-support law alone.  The whole-tree and
supported-executor layers of the support obligation are discharged by the
structural theorem and the context transport above. -/
def rhoHereditaryCostOneObjectLaws_ofStaticLaw
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneObjectLaws_of alignable
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

/-- The normalizer-indexed rho Cost₁ domain object over the same reduced
obligations. -/
def rhoHereditaryCostOneDomainObject_ofStaticLaw
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_of alignable
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
