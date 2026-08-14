import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryOccurrenceSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostFillDeterminism

/-!
# Reflective support through rho Cost region trees

This module isolates the structural part of reflective-support preservation
for hereditary rho Cost normalization.  A local premise covers exactly one
static node after its boundary children have been normalized.  The mutually
recursive outer proof then transports that premise through region trees,
constructor arguments, collection elements, and finite boundary values.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## Object-only transport between binder fibres -/

/-- On rho's generated Cost language, reflective-support evidence for an
object depends on the selected typing derivation only through its raw object
and result type.  In particular, it may be rebuilt in another binder fibre
where the same object has the same type.  Explicit substitution is excluded
by the object premise; generated-label and collection-choice determinism
align the remaining potentially ambiguous typing branches. -/
theorem rhoCostReflectiveSupportSafeAt_retype_of_object
    {free : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {sourceTyped : HasType rhoCIGSLT.costWholeLanguage free sourceBound
      pattern type}
    {targetTyped : HasType rhoCIGSLT.costWholeLanguage free targetBound
      pattern type}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : sourceTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (object : isObjectPattern pattern = true) :
    targetTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern type)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPattern pattern = true →
      ∀ {targetBound : List TypeExpr}
        (targetTyped : HasType rhoCIGSLT.costWholeLanguage free targetBound
          pattern type),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage free bound
        arguments parameters)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPatternList arguments = true →
      ∀ {targetBound : List TypeExpr}
        (targetTyped : ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage free
          targetBound arguments parameters),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
        elements elementType)
      available binderImage
      (_ : typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support available binderImage) =>
      isObjectPatternList elements = true →
      ∀ {targetBound : List TypeExpr}
        (targetTyped : ElementsHaveType rhoCIGSLT.costWholeLanguage free
          targetBound elements elementType),
        targetTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (by
      intro bound index type lookup currentAvailable currentImage _object
        targetBound targetTyped
      cases targetTyped with
      | bvar targetLookup => exact .bvar targetLookup currentAvailable)
    (by
      intro bound name type lookup currentAvailable currentImage shape _object
        targetBound targetTyped
      cases targetTyped with
      | fvar targetLookup => exact .fvar targetLookup currentAvailable shape)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage quoted argumentsSafe argumentsIH object
        targetBound targetTyped
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
        targetBound targetTyped
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
        currentImage bodySafe bodyIH object targetBound targetTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      cases targetTyped with
      | lambda targetBody => exact .lambda (bodyIH bodyObject targetBody))
    (by
      intro bound arity binders body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH object targetBound targetTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      cases targetTyped with
      | multiLambda targetBody =>
          exact .multiLambda (bodyIH bodyObject targetBody))
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable currentImage bodySafe replacementSafe bodyIH
        replacementIH object targetBound targetTyped
      simp [isObjectPattern] at object)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        currentAvailable currentImage elementsSafe elementsIH object targetBound
        targetTyped
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
        elementsSafe elementsIH object targetBound targetTyped
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
            HasType rhoCIGSLT.costWholeLanguage free targetBound
              (.collection collectionType elements rest)
                (.base targetRule.category),
            constructedTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support currentAvailable
                currentImage :=
          ⟨_, constructedSafe⟩
        have repackaged : ∃ constructedTyped :
            HasType rhoCIGSLT.costWholeLanguage free targetBound
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
      intro bound currentAvailable currentImage _objects targetBound targetTyped
      cases targetTyped
      exact .nil targetBound currentAvailable)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH objects targetBound targetTyped
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using objects
      cases targetTyped with
      | @cons _ targetArgument targetArguments targetParameter targetParameters
          targetExpected targetRepresentation targetParameterType targetArgumentTyped
          targetArgumentsTyped =>
          have expectedEquality : targetExpected = expected :=
            Option.some.inj (targetParameterType.symm.trans parameterType)
          subst targetExpected
          exact ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := targetRepresentation)
            (parameterType := targetParameterType)
            (argumentIH objectParts.1 targetArgumentTyped)
            (argumentsIH objectParts.2 targetArgumentsTyped))
    (by
      intro bound elementType currentAvailable currentImage _objects
        targetBound targetTyped
      cases targetTyped
      exact .nil targetBound elementType currentAvailable)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        currentAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH objects targetBound targetTyped
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using objects
      cases targetTyped with
      | cons targetElement targetElements =>
          exact .cons (elementIH objectParts.1 targetElement)
            (elementsIH objectParts.2 targetElements))
    safe object targetTyped

/-- Transport support evidence together with an explicit equality of the raw
pattern.  Typing proofs remain proof-irrelevant after the syntax indices have
been aligned. -/
private theorem reflectiveSupportSafeAt_castPattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sourcePattern targetPattern : Pattern}
    {type : TypeExpr} {sourceTyped : HasType language free bound sourcePattern type}
    {targetTyped : HasType language free bound targetPattern type}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (patternEquality : sourcePattern = targetPattern)
    (safe : sourceTyped.ReflectiveSupportSafeAt profile support available
      binderImage) :
    targetTyped.ReflectiveSupportSafeAt profile support available
      binderImage := by
  subst targetPattern
  exact safe.castTyping

/-- Invert support safety at a multi-lambda without exposing dependent
constructor equalities to the caller's termination proof. -/
private theorem reflectiveSupportSafeAt_multiLambda_inversion
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arity : Nat} {binders : List String}
    {body : Pattern} {domain codomain : TypeExpr}
    {typed : HasType language free bound (.multiLambda arity binders body)
      (.arrow (.multiBinder domain) codomain)}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ∃ bodyTyped : HasType language free
        (List.replicate arity domain ++ bound) body codomain,
      bodyTyped.ReflectiveSupportSafeAt profile support
        (List.replicate arity (binderImage domain) ++ available)
          binderImage := by
  cases safe with
  | multiLambda bodySafe => exact ⟨_, bodySafe⟩

private theorem reflectiveSupportSafeAt_lambda_inversion
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {binder : Option String} {body : Pattern}
    {domain codomain : TypeExpr}
    {typed : HasType language free bound (.lambda binder body)
      (.arrow domain codomain)}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ∃ bodyTyped : HasType language free (domain :: bound) body codomain,
      bodyTyped.ReflectiveSupportSafeAt profile support
        (binderImage domain :: available) binderImage := by
  cases safe with
  | lambda bodySafe => exact ⟨_, bodySafe⟩

private theorem reflectiveSupportSafeAt_collection_inversion
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {elementType : TypeExpr}
    {typed : HasType language free bound
      (.collection collectionType elements rest)
        (.collection collectionType elementType)}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ∃ elementsTyped : ElementsHaveType language free bound elements elementType,
      elementsTyped.ReflectiveSupportSafeAt profile support available
        binderImage := by
  cases safe with
  | collection elementsSafe => exact ⟨_, elementsSafe⟩

/-- Proof-relevant inversion of support safety at an application.  The
actual authored rule is retained because raw label/category indices alone do
not definitionally determine its parameter spine. -/
private inductive ApplicationReflectiveSupportView
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (language : LanguageDef) (free : FreeTypeContext)
    (support : ContextSupport.Support) (bound : List TypeExpr)
    (label : String) (arguments : List Pattern) (type : TypeExpr)
    (available : List TypeExpr) (binderImage : TypeExpr → TypeExpr) : Prop where
  | quote {rule : GrammarRule}
      (membership : rule ∈ language.terms)
      (labelEquality : label = rule.label)
      (typeEquality : type = .base rule.category)
      {argumentsTyped : ArgumentsHaveTypes language free bound arguments
        rule.params}
      (quoted : ReflectiveContextSupport.isQuoteConstructor profile
        rule.label = true)
      (argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt profile support
        [] binderImage) :
      ApplicationReflectiveSupportView profile language free support bound label
        arguments type available binderImage
  | ordinary {rule : GrammarRule}
      (membership : rule ∈ language.terms)
      (labelEquality : label = rule.label)
      (typeEquality : type = .base rule.category)
      {argumentsTyped : ArgumentsHaveTypes language free bound arguments
        rule.params}
      (ordinary : ReflectiveContextSupport.isQuoteConstructor profile
        rule.label = false)
      (argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt profile support
        available binderImage) :
      ApplicationReflectiveSupportView profile language free support bound label
        arguments type available binderImage

private theorem applicationReflectiveSupportView
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    {typed : HasType language free bound (.apply label arguments) type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ApplicationReflectiveSupportView profile language free support bound label
      arguments type available binderImage := by
  cases safe with
  | @constructorQuote bound rule arguments membership notBare argumentsTyped
      available binderImage quoted argumentsSafe =>
      exact .quote membership rfl rfl quoted argumentsSafe
  | @constructorOrdinary bound rule arguments membership notBare argumentsTyped
      available binderImage ordinary argumentsSafe =>
      exact .ordinary membership rfl rfl ordinary argumentsSafe

/-! ## The exact local static-node premise -/

/-- One static normalization step preserves an arbitrary caller-relative
reflective support whenever every recursively normalized boundary value does.
This is the only semantic premise used by the structural tree theorem. -/
def RhoCostStaticReflectiveSupportPreserving
    (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT) : Prop :=
  ∀ {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr),
    CostStaticBoundaryChildReflectiveSupportPreserving node.boundaryTable
      values support binderImage →
    node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage →
    (normalizeStatic node values).2.1.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage

/-! ## Mutual preservation through the alternating tree -/

mutual
  /-- Child-first normalization preserves reflective support through one
  complete rho Cost region tree, assuming only the exact local static law. -/
  theorem CostRegionTree.normalize_preservesReflectiveSupport
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type)
      (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
      (staticPreserves :
        RhoCostStaticReflectiveSupportPreserving normalizeStatic)
      (support : ContextSupport.Support) (reflectiveAvailable : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr)
      (object : isObjectPattern pattern = true)
      (safe : tree.originalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage) :
      (tree.normalize
        (normalizeStatic := normalizeStatic)).typed.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
            binderImage :=
    match tree with
    | CostRegionTree.bvar lookup => by
        simpa only [CostRegionTree.originalTyped,
          CostRegionTree.normalize] using safe
    | CostRegionTree.fvar lookup => by
        simpa only [CostRegionTree.originalTyped,
          CostRegionTree.normalize] using safe
    | @CostRegionTree.static _ _ color outer node children => by
        let values := children.normalizeValues
          (normalizeStatic := normalizeStatic)
        have childrenPreserve :
            CostStaticBoundaryChildReflectiveSupportPreserving
              node.boundaryTable values support binderImage :=
          CostRegionBoundaryTrees.normalizeValues_preservesReflectiveSupport
            children normalizeStatic staticPreserves support binderImage
        have exactInputSafe : node.term.2.1.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
              binderImage :=
          rhoCostReflectiveSupportSafeAt_retype_of_object safe
            node.term.2.2.2.1
        have normalizedSafe := staticPreserves node values support
          reflectiveAvailable binderImage childrenPreserve exactInputSafe
        obtain ⟨extendedTyped, extendedSafe⟩ := normalizedSafe.extendOuter outer
        have patternEquality :
            (normalizeStatic node values).1 =
              ((CostRegionTree.static (outer := outer) node children).normalize
                (normalizeStatic := normalizeStatic)).pattern :=
          (CostRegionTree.normalize_static_pattern normalizeStatic node
            children).symm
        exact reflectiveSupportSafeAt_castPattern patternEquality extendedSafe
    | @CostRegionTree.neutralApplicationOrdinary _ _ available outer rule arguments membership
        notBare constructor materializes neutral ordinary children => by
        have argumentsObject : isObjectPatternList arguments = true := by
          simpa [isObjectPattern] using object
        have view := applicationReflectiveSupportView safe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped quoted argumentsSafe =>
            have ruleEquality : actualRule = rule :=
              rho_costWholeLanguage_labelDeterministic actualMembership
                membership labelEquality.symm
            subst actualRule
            rw [ordinary] at quoted
            contradiction
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped _viewOrdinary argumentsSafe =>
            have ruleEquality : actualRule = rule :=
              rho_costWholeLanguage_labelDeterministic actualMembership
                membership labelEquality.symm
            subst actualRule
            have exactArgumentsSafe :
              children.originalTyped.ReflectiveSupportSafeAt
                rhoCIGSLT.costWholeReflectionProfile support
                  reflectiveAvailable binderImage :=
              argumentsSafe.castTyping
            let normalizedArguments := children.normalize
              (normalizeStatic := normalizeStatic)
            have normalizedArgumentsSafe :
                normalizedArguments.typed.ReflectiveSupportSafeAt
                  rhoCIGSLT.costWholeReflectionProfile support
                    reflectiveAvailable binderImage :=
              CostRegionArgumentTrees.normalize_preservesReflectiveSupport
                children normalizeStatic staticPreserves support
                  reflectiveAvailable binderImage argumentsObject
                    exactArgumentsSafe
            have rebuiltSafe :
                (HasType.constructor membership notBare
                  normalizedArguments.typed).ReflectiveSupportSafeAt
                    rhoCIGSLT.costWholeReflectionProfile support
                      reflectiveAvailable binderImage :=
              .constructorOrdinary (membership := membership)
                (notBare := notBare) ordinary normalizedArgumentsSafe
            simpa only [CostRegionTree.normalize] using
              (HasType.ReflectiveSupportSafeAt.castTyping rebuiltSafe)
    | @CostRegionTree.neutralApplicationQuote _ _ available outer rule arguments membership
        notBare constructor materializes neutral quoted children => by
        have argumentsObject : isObjectPatternList arguments = true := by
          simpa [isObjectPattern] using object
        have view := applicationReflectiveSupportView safe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped _viewQuoted argumentsSafe =>
            have ruleEquality : actualRule = rule :=
              rho_costWholeLanguage_labelDeterministic actualMembership
                membership labelEquality.symm
            subst actualRule
            have exactArgumentsSafe :
              children.originalTyped.ReflectiveSupportSafeAt
                rhoCIGSLT.costWholeReflectionProfile support [] binderImage :=
              argumentsSafe.castTyping
            let normalizedArguments := children.normalize
              (normalizeStatic := normalizeStatic)
            have normalizedArgumentsSafe :
                normalizedArguments.typed.ReflectiveSupportSafeAt
                  rhoCIGSLT.costWholeReflectionProfile support [] binderImage :=
              CostRegionArgumentTrees.normalize_preservesReflectiveSupport
                children normalizeStatic staticPreserves support [] binderImage
                  argumentsObject exactArgumentsSafe
            let sourceRootTyped :=
              HasType.constructor membership notBare normalizedArguments.typed
            have sourceRootSafe :
                sourceRootTyped.ReflectiveSupportSafeAt
                  rhoCIGSLT.costWholeReflectionProfile support
                    reflectiveAvailable binderImage :=
              .constructorQuote (membership := membership)
                (notBare := notBare) quoted normalizedArgumentsSafe
            let targetRootTyped :
                HasType rhoCIGSLT.costWholeLanguage targetFree
                  (available ++ outer) (.apply rule.label
                    normalizedArguments.patterns) (.base rule.category) := by
              simpa only [List.nil_append] using sourceRootTyped
            have targetRootSafe :
                targetRootTyped.ReflectiveSupportSafeAt
                  rhoCIGSLT.costWholeReflectionProfile support
                    reflectiveAvailable binderImage :=
              HasType.ReflectiveSupportSafeAt.castBound
                (source := sourceRootTyped) (target := targetRootTyped)
                  (List.nil_append _) sourceRootSafe
            simpa only [CostRegionTree.normalize] using
              (HasType.ReflectiveSupportSafeAt.castTyping targetRootSafe)
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped ordinary argumentsSafe =>
            have ruleEquality : actualRule = rule :=
              rho_costWholeLanguage_labelDeterministic actualMembership
                membership labelEquality.symm
            subst actualRule
            rw [quoted] at ordinary
            contradiction
    | @CostRegionTree.lambda _ _ available outer binder body domain codomain bodyTree => by
        have bodyObject : isObjectPattern body = true := by
          simpa [isObjectPattern] using object
        obtain ⟨rootBodyTyped, rootBodySafe⟩ :=
          reflectiveSupportSafeAt_lambda_inversion safe
        have bodySafe' : bodyTree.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              (binderImage domain :: reflectiveAvailable) binderImage := by
          simpa only [List.cons_append] using rootBodySafe.castTyping
        let normalizedBody := bodyTree.normalize
          (normalizeStatic := normalizeStatic)
        have normalizedBodySafe :
            normalizedBody.typed.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                (binderImage domain :: reflectiveAvailable) binderImage :=
          CostRegionTree.normalize_preservesReflectiveSupport bodyTree
            normalizeStatic staticPreserves support
              (binderImage domain :: reflectiveAvailable) binderImage
                bodyObject bodySafe'
        have rebuiltSafe :
            (HasType.lambda (binder := binder)
              normalizedBody.typed).ReflectiveSupportSafeAt
                rhoCIGSLT.costWholeReflectionProfile support
                  reflectiveAvailable binderImage :=
          .lambda normalizedBodySafe
        simpa only [CostRegionTree.normalize] using
          (HasType.ReflectiveSupportSafeAt.castTyping rebuiltSafe)
    | @CostRegionTree.multiLambda _ _ available outer arity binders body domain codomain bodyTree => by
        have bodyObject : isObjectPattern body = true := by
          simpa [isObjectPattern] using object
        obtain ⟨rootBodyTyped, rootBodySafe⟩ :=
          reflectiveSupportSafeAt_multiLambda_inversion safe
        have bodySafe' : bodyTree.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              (List.replicate arity (binderImage domain) ++
                reflectiveAvailable) binderImage :=
          HasType.ReflectiveSupportSafeAt.castBound
            (source := rootBodyTyped) (target := bodyTree.originalTyped)
              (List.append_assoc _ _ _).symm rootBodySafe
        let normalizedBody := bodyTree.normalize
          (normalizeStatic := normalizeStatic)
        have recursiveBodySafe :
            normalizedBody.typed.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                (List.replicate arity (binderImage domain) ++
                  reflectiveAvailable) binderImage :=
          CostRegionTree.normalize_preservesReflectiveSupport bodyTree
            normalizeStatic staticPreserves support
              (List.replicate arity (binderImage domain) ++
                reflectiveAvailable)
              binderImage bodyObject bodySafe'
        have targetBodyTyped :
            HasType rhoCIGSLT.costWholeLanguage targetFree
              (List.replicate arity domain ++ (available ++ outer))
                normalizedBody.pattern codomain := by
          simpa only [List.append_assoc] using normalizedBody.typed
        have targetBodySafe :
            targetBodyTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                (List.replicate arity (binderImage domain) ++
                  reflectiveAvailable) binderImage :=
          HasType.ReflectiveSupportSafeAt.castBound
            (source := normalizedBody.typed) (target := targetBodyTyped)
              (List.append_assoc _ _ _) recursiveBodySafe
        have rebuiltSafe :=
          HasType.ReflectiveSupportSafeAt.multiLambda
            (profile := rhoCIGSLT.costWholeReflectionProfile)
            (support := support) (available := reflectiveAvailable)
            (binderImage := binderImage)
            (arity := arity) (binders := binders) (domain := domain)
            (bodyTyped := targetBodyTyped) targetBodySafe
        simpa only [CostRegionTree.normalize] using
          (HasType.ReflectiveSupportSafeAt.castTyping rebuiltSafe)
    | CostRegionTree.subst bodyTree replacementTree => by
        simp [isObjectPattern] at object
    | @CostRegionTree.collection _ _ available outer collectionType elements rest elementType children => by
        have elementsObject : isObjectPatternList elements = true := by
          have objectParts := object
          simp only [isObjectPattern, Bool.and_eq_true] at objectParts
          exact objectParts.2
        obtain ⟨rootElementsTyped, rootElementsSafe⟩ :=
          reflectiveSupportSafeAt_collection_inversion safe
        have exactElementsSafe :
            children.originalTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                reflectiveAvailable binderImage :=
          rootElementsSafe.castTyping
        let normalizedElements := children.normalize
          (normalizeStatic := normalizeStatic)
        have normalizedElementsSafe :
            normalizedElements.typed.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                reflectiveAvailable binderImage :=
          CostRegionElementTrees.normalize_preservesReflectiveSupport
            children normalizeStatic staticPreserves support
              reflectiveAvailable binderImage elementsObject exactElementsSafe
        have rebuiltSafe :
            (HasType.collection (collectionType := collectionType)
              (rest := rest) normalizedElements.typed
            ).ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support
                reflectiveAvailable binderImage :=
          .collection normalizedElementsSafe
        simpa only [CostRegionTree.normalize] using
          (HasType.ReflectiveSupportSafeAt.castTyping rebuiltSafe)
  termination_by 4 * tree.weight + 3
  decreasing_by
    all_goals subst_vars
    all_goals try simp only [CostRegionTree.weight]
    all_goals omega

  /-- Argument-spine companion to whole-tree reflective-support
  preservation. -/
  theorem CostRegionArgumentTrees.normalize_preservesReflectiveSupport
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (trees : CostRegionArgumentTrees rhoCIGSLT targetFree available outer
        arguments parameters)
      (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
      (staticPreserves :
        RhoCostStaticReflectiveSupportPreserving normalizeStatic)
      (support : ContextSupport.Support) (reflectiveAvailable : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr)
      (objects : isObjectPatternList arguments = true)
      (safe : trees.originalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage) :
      (trees.normalize
        (normalizeStatic := normalizeStatic)).typed.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
            binderImage :=
    match trees with
    | CostRegionArgumentTrees.nil => by
        simpa only [CostRegionArgumentTrees.originalTyped,
          CostRegionArgumentTrees.normalize] using safe
    | @CostRegionArgumentTrees.cons _ _ available outer argument arguments parameter parameters expected
        representation parameterType head tail => by
        have objectParts : isObjectPattern argument = true ∧
            isObjectPatternList arguments = true := by
          simpa [isObjectPatternList] using objects
        let exactInput := ArgumentsHaveTypes.cons representation parameterType
          head.originalTyped tail.originalTyped
        have exactInputSafe : exactInput.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
              binderImage := by
          apply ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
          simpa only [CostRegionArgumentTrees.originalTyped] using safe
        have exactHeadSafe : head.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
            (representation := representation) (parameterType := parameterType)
            (argumentTyped := head.originalTyped)
            (argumentsTyped := tail.originalTyped) exactInputSafe
        have exactTailSafe : tail.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage := by
          cases exactInputSafe with
          | cons _ tailSafe => exact tailSafe.castTyping
        let normalizedHead := head.normalize
          (normalizeStatic := normalizeStatic)
        let normalizedTail := tail.normalize
          (normalizeStatic := normalizeStatic)
        have normalizedHeadSafe : normalizedHead.typed.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage :=
          CostRegionTree.normalize_preservesReflectiveSupport head
            normalizeStatic staticPreserves support reflectiveAvailable
              binderImage objectParts.1 exactHeadSafe
        have normalizedTailSafe : normalizedTail.typed.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage :=
          CostRegionArgumentTrees.normalize_preservesReflectiveSupport
            tail normalizeStatic staticPreserves support reflectiveAvailable
              binderImage objectParts.2 exactTailSafe
        have outputSafe :
            (ArgumentsHaveTypes.cons
              (normalizedHead.matchesParameterRepresentation parameter
                representation)
              parameterType
              normalizedHead.typed normalizedTail.typed
            ).ReflectiveSupportSafeAt rhoCIGSLT.costWholeReflectionProfile
              support reflectiveAvailable binderImage :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := normalizedHead.matchesParameterRepresentation
              parameter representation)
            (parameterType := parameterType) normalizedHeadSafe
              normalizedTailSafe
        simpa only [CostRegionArgumentTrees.normalize] using outputSafe
  termination_by 4 * trees.weight + 2
  decreasing_by
    all_goals simp only [CostRegionArgumentTrees.weight]
    all_goals omega

  /-- Homogeneous-element companion to whole-tree reflective-support
  preservation. -/
  theorem CostRegionElementTrees.normalize_preservesReflectiveSupport
      {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (trees : CostRegionElementTrees rhoCIGSLT targetFree available outer
        elements elementType)
      (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
      (staticPreserves :
        RhoCostStaticReflectiveSupportPreserving normalizeStatic)
      (support : ContextSupport.Support) (reflectiveAvailable : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr)
      (objects : isObjectPatternList elements = true)
      (safe : trees.originalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage) :
      (trees.normalize
        (normalizeStatic := normalizeStatic)).typed.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
            binderImage :=
    match trees with
    | CostRegionElementTrees.nil available outer elementType => by
        simpa only [CostRegionElementTrees.originalTyped,
          CostRegionElementTrees.normalize] using safe
    | @CostRegionElementTrees.cons _ _ available outer element elements elementType head tail => by
        have objectParts : isObjectPattern element = true ∧
            isObjectPatternList elements = true := by
          simpa [isObjectPatternList] using objects
        let exactInput := ElementsHaveType.cons head.originalTyped
          tail.originalTyped
        have exactInputSafe : exactInput.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
              binderImage := by
          apply ElementsHaveType.ReflectiveSupportSafeAt.castTyping
          simpa only [CostRegionElementTrees.originalTyped] using safe
        have exactHeadSafe : head.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage := by
          cases exactInputSafe with
          | cons headSafe _ => exact headSafe.castTyping
        have exactTailSafe : tail.originalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage := by
          cases exactInputSafe with
          | cons _ tailSafe => exact tailSafe.castTyping
        let normalizedHead := head.normalize
          (normalizeStatic := normalizeStatic)
        let normalizedTail := tail.normalize
          (normalizeStatic := normalizeStatic)
        have normalizedHeadSafe : normalizedHead.typed.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage :=
          CostRegionTree.normalize_preservesReflectiveSupport head
            normalizeStatic staticPreserves support reflectiveAvailable
              binderImage objectParts.1 exactHeadSafe
        have normalizedTailSafe : normalizedTail.typed.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support
              reflectiveAvailable binderImage :=
          CostRegionElementTrees.normalize_preservesReflectiveSupport
            tail normalizeStatic staticPreserves support reflectiveAvailable
              binderImage objectParts.2 exactTailSafe
        have outputSafe :
            (ElementsHaveType.cons normalizedHead.typed normalizedTail.typed
            ).ReflectiveSupportSafeAt rhoCIGSLT.costWholeReflectionProfile
              support reflectiveAvailable binderImage :=
          .cons normalizedHeadSafe normalizedTailSafe
        simpa only [CostRegionElementTrees.normalize] using outputSafe
  termination_by 4 * trees.weight + 1
  decreasing_by
    all_goals simp only [CostRegionElementTrees.weight]
    all_goals omega

  /-- Normalizing a finite boundary forest supplies exactly the child
  preservation premise required by its enclosing static node. -/
  theorem CostRegionBoundaryTrees.normalizeValues_preservesReflectiveSupport
      {targetFree : FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        occurrences}
      (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color table)
      (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
      (staticPreserves :
        RhoCostStaticReflectiveSupportPreserving normalizeStatic)
      (support : ContextSupport.Support)
      (binderImage : TypeExpr → TypeExpr) :
      CostStaticBoundaryChildReflectiveSupportPreserving table
        (trees.normalizeValues (normalizeStatic := normalizeStatic)) support
          binderImage := fun {name} {resolved} selected {inputBound available}
            {inputTyped} inputSafe =>
    match (motive :=
        ∀ (color : CostStaticColor)
          (occurrences : List CostRegionOccurrence)
          (table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
            occurrences)
          (forest : CostRegionBoundaryTrees rhoCIGSLT targetFree color table)
          (resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
            color targetFree)
          (_selected : TypedCostRegionBoundaryTable.Values.resolve table
            (forest.normalizeValues (normalizeStatic := normalizeStatic)) name =
              some resolved)
          (inputBound available : List TypeExpr)
          (inputTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
            inputBound resolved.1.boundary.content
              resolved.1.boundary.targetType)
          (_inputSafe : inputTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support available
                binderImage),
        resolved.2.2.1.1.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support available binderImage)
      color, occurrences, table, trees, resolved, selected, inputBound,
        available, inputTyped, inputSafe with
    | _, _, _, @CostRegionBoundaryTrees.nil _ _ color, _, selected, _, _, _, _ => by
        simp [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.resolve] at selected
    | _, _, _, @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences
        boundary content tail head children, resolved, selected, inputBound,
          reflectiveAvailable, inputTyped, inputSafe => by
        simp only [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.resolve] at selected
        split at selected
        · have resolvedEquality := Option.some.inj selected
          cases resolvedEquality
          have headInputSafe : head.originalTyped.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
                binderImage :=
            rhoCostReflectiveSupportSafeAt_retype_of_object inputSafe
              boundary.contentObjectPattern
          apply HasType.ReflectiveSupportSafeAt.castBound
            (source := (head.normalize
              (normalizeStatic := normalizeStatic)).typed)
            (boundEquality := List.append_nil _)
          exact CostRegionTree.normalize_preservesReflectiveSupport head
              normalizeStatic staticPreserves support reflectiveAvailable
                binderImage boundary.contentObjectPattern headInputSafe
        · exact
            CostRegionBoundaryTrees.normalizeValues_preservesReflectiveSupport
              children normalizeStatic staticPreserves support binderImage
                selected inputSafe
  termination_by 4 * trees.weight
  decreasing_by
    all_goals simp only [CostRegionBoundaryTrees.weight]
    all_goals omega
end

/-! ## Compact-executor endpoint -/

/-- The structural theorem reaches the checked compact executor selected by
`CostOpenElaboration.compile`.  Thus the only remaining semantic obligation
for reflective-support preservation is the exact local static-node law. -/
theorem rhoCostNormalizeOpenWithStatic_preservesReflectiveSupport
    (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving normalizeStatic)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree targetBound targetSort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (safe : term.2.1.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    (rhoCIGSLT.costNormalizeOpenWithStatic normalizeStatic term).2.1.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support
        available binderImage := by
  let elaboration := CostOpenElaboration.compile rhoCIGSLT term
  have treeInputSafe : elaboration.tree.originalTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage :=
    HasType.ReflectiveSupportSafeAt.castBound
      (source := term.2.1.1) (target := elaboration.tree.originalTyped)
        (List.append_nil targetBound).symm safe
  have normalizedSafe :=
    CostRegionTree.normalize_preservesReflectiveSupport elaboration.tree
      normalizeStatic staticPreserves support available binderImage
        term.2.1.2.2.1 treeInputSafe
  exact HasType.ReflectiveSupportSafeAt.castBound
    (source := (elaboration.tree.normalize
      (normalizeStatic := normalizeStatic)).typed)
    (target := (rhoCIGSLT.costNormalizeOpenWithStatic normalizeStatic term
      ).2.1.1)
    (List.append_nil targetBound) normalizedSafe

/-! ## Boundary canaries -/

/-- The empty boundary forest supplies a genuine preservation function: every
lookup is rejected by the finite table rather than discharged by an arbitrary
fallback value. -/
theorem rhoCostEmptyBoundaryTrees_preserveReflectiveSupport
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
    (support : ContextSupport.Support) (binderImage : TypeExpr → TypeExpr) :
    CostStaticBoundaryChildReflectiveSupportPreserving
      (TypedCostRegionBoundaryTable.nil :
        TypedCostRegionBoundaryTable rhoCIGSLT color targetFree [])
      ((CostRegionBoundaryTrees.nil : CostRegionBoundaryTrees rhoCIGSLT
        targetFree color .nil).normalizeValues
          (normalizeStatic := normalizeStatic)) support binderImage :=
  by
    intro name resolved selected
    simp [CostRegionBoundaryTrees.normalizeValues,
      TypedCostRegionBoundaryTable.Values.resolve] at selected

/-- A one-entry boundary forest turns a preservation theorem for its actual
child into the finite-lookup preservation interface consumed by a static
node.  The selected branch is inhabited; the rejected branch terminates in
the empty tail. -/
theorem rhoCostSingletonBoundary_preservesReflectiveSupport_of_head
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {occurrence : CostRegionOccurrence}
    {boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree}
    {content : boundary.boundary.content = occurrence.content}
    (head : CostRegionTree rhoCIGSLT targetFree
      boundary.boundary.targetSupport [] boundary.boundary.content
        boundary.boundary.targetType)
    (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
    (support : ContextSupport.Support) (binderImage : TypeExpr → TypeExpr)
    (headPreserves :
      ∀ {inputBound reflectiveAvailable : List TypeExpr}
        {inputTyped : HasType rhoCIGSLT.costWholeLanguage targetFree inputBound
          boundary.boundary.content boundary.boundary.targetType},
        inputTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
              binderImage →
          (head.normalize
            (normalizeStatic := normalizeStatic)).typed.ReflectiveSupportSafeAt
              rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
                binderImage) :
    let table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        [occurrence] := .cons boundary content .nil
    let trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color table :=
      .cons head .nil
    CostStaticBoundaryChildReflectiveSupportPreserving table
      (trees.normalizeValues (normalizeStatic := normalizeStatic)) support
        binderImage := by
  dsimp
  intro name resolved selected inputBound reflectiveAvailable inputTyped
    inputSafe
  simp only [CostRegionBoundaryTrees.normalizeValues,
    TypedCostRegionBoundaryTable.Values.resolve] at selected
  split at selected
  · have resolvedEquality := Option.some.inj selected
    cases resolvedEquality
    apply HasType.ReflectiveSupportSafeAt.castBound
      (source := (head.normalize (normalizeStatic := normalizeStatic)).typed)
      (boundEquality := List.append_nil _)
    exact headPreserves inputSafe
  · simp at selected

/-- A free-variable structural leaf preserves reflective support without
consulting the static normalizer.  This is the positive non-static boundary
of the mutual theorem. -/
theorem rhoCostFVarTree_normalize_preservesReflectiveSupport
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {name : String} {type : TypeExpr} (lookup : targetFree name = some type)
    (normalizeStatic : CostStaticRegionNormalizer rhoCIGSLT)
    (support : ContextSupport.Support) (reflectiveAvailable : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (shape : ∃ inner, reflectiveAvailable = inner ++ support name) :
    let tree : CostRegionTree rhoCIGSLT targetFree available outer
        (.fvar name) type := .fvar lookup
    (tree.normalize
      (normalizeStatic := normalizeStatic)).typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage := by
  dsimp
  have leafSafe :
      (HasType.fvar (language := rhoCIGSLT.costWholeLanguage)
        (free := targetFree) (bound := available ++ outer)
          lookup).ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage :=
    HasType.ReflectiveSupportSafeAt.fvar
    (profile := rhoCIGSLT.costWholeReflectionProfile)
    (binderImage := binderImage) lookup reflectiveAvailable shape
  simpa only [CostRegionTree.normalize] using leafSafe

/-- Explicit substitution is outside the object-language domain of the
retyping and whole-tree preservation theorems. -/
theorem rhoCostSubst_not_object (body replacement : Pattern) :
    isObjectPattern (.subst body replacement) ≠ true := by
  simp [isObjectPattern]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
