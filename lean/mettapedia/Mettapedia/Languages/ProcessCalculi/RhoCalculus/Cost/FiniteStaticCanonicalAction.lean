import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticAction
import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalAction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventorySubstitution
import Mettapedia.GSLT.LanguageDef.ReflectiveConstructorSupport

/-!
# Source-typed canonical action for finite rho Cost profiles

The source inventory controls normalization. Target values may contain every
admitted finite constructor, including synchronous output. The proof uses
Name-result sealing in the target, not the false claim that arbitrary mixed
Cost normalization preserves a target Drop argument's typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.FiniteStaticCanonicalAction
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open ReflectionExtension ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- The chosen member of the two existing transported declaration lists. -/
def declaration (theory : IGSLT) (color : CostStaticColor) : ReflectivePresentationDecl :=
  match color with
  | .base => costBaseReflectivePresentationDecl rhoReflectivePresentation
  | .wrapped => costWrappedReflectivePresentationDecl theory rhoReflectivePresentation

theorem declaration_mem (profile : ContinuationDecorationProfile cut) (color : CostStaticColor) :
    declaration theory color ∈
      (profile.costWholeReflectionProfile rhoReflectionProfile).presentations := by
  cases color <;> simp [declaration, costWholeReflectionProfile,
    costStaticReflectivePresentations, rhoReflectionProfile]

/-- The literal static action at a source local-binder prefix and an
independently recorded target-visible support context. -/
def actionAt (profile : ContinuationDecorationProfile cut) (color : CostStaticColor)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    {free targetFree : FreeTypeContext} {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment (profile.costWholeReflectionProfile rhoReflectionProfile)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support)
    (inner available : List TypeExpr) (pattern : Pattern) : Pattern :=
  ReflectiveContextSupport.substituteAt (profile.costWholeReflectionProfile rhoReflectionProfile)
    support assignment.assignment available.length
    (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex inner.length
      (mapPattern (color.symbolsOf theory) pattern))

/-- Local cancellation after the actual finite static action. The target
Name-result condition licenses arbitrary admitted assignment values. -/
theorem quoteDrop
    (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (quotedResults : ReflectiveNameResultsQuoted
      (profile := profile.costWholeReflectionProfile rhoReflectionProfile) profile.costWholeLanguage)
    {color : CostStaticColor} {free targetFree : FreeTypeContext}
    {support : ContextSupport.Support} {sourceBound targetBound inner : List TypeExpr}
    {name : Pattern}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    (assignment : SupportedOpenAssignment (profile.costWholeReflectionProfile rhoReflectionProfile)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support)
    (typed : HasType theory.presentation.presentation.language free (inner ++ sourceBound)
      name (.base "Name"))
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      (mapTypeExpr (color.symbolsOf theory)))
    (supported : ConstructorsWithin (· ∈ profile.wrappedLabels) name)
    (object : isObjectPattern name = true) (available : List TypeExpr) :
    canonicalize (declaration theory color)
      (actionAt profile color thinning assignment inner available
        (.apply "NQuote" [.apply "PDrop" [name]])) =
      canonicalize (declaration theory color)
        (actionAt profile color thinning assignment inner available name) := by
  let fragment := typed.withConstructors supported bareAllowed
  have mappedTyped := profile.mapStatic_hasType nonprincipal color fragment
  have mappedSafe := profile.mapStatic_reflectiveSupport nonprincipal bareAllowed
    rhoReflectionProfile color fragment safe.castTyping
  have casted : ∃ mapped : HasType profile.costWholeLanguage
      (free.map (color.symbolsOf theory))
      (inner.map (mapTypeExpr (color.symbolsOf theory)) ++
        sourceBound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) name)
      (mapTypeExpr (color.symbolsOf theory) (.base "Name")),
      mapped.ReflectiveSupportSafeAt (profile.costWholeReflectionProfile rhoReflectionProfile)
        support [] id := by
    rw [← List.map_append]
    exact ⟨mappedTyped, mappedSafe⟩
  obtain ⟨mappedTyped, mappedSafe⟩ := casted
  have renamedTyped := thinning.hasType_renameAmbient
    (inner := inner.map (mapTypeExpr (color.symbolsOf theory))) mappedTyped
  have renamedSafe := mappedSafe.renameAmbientBVarsAt thinning.toTargetIndex
    thinning.preservesBoundTypes
  have cancellation := quoteDrop_substituteAt_canonicalize_eq_of_resultsQuoted
    quotedResults assignment (declaration theory color) (declaration_mem profile color)
    (by
      have quoteField : (declaration theory color).quoteConstructor =
          (color.symbolsOf theory).constructor "NQuote" := by cases color <;> rfl
      have dropField : (declaration theory color).dropConstructor =
          (color.symbolsOf theory).constructor "PDrop" := by cases color <;> rfl
      rw [quoteField, dropField]
      exact fun equality => (by decide : "NQuote" ≠ "PDrop")
        (CostStaticColor.symbolsOf_constructor_injective theory color equality)) renamedTyped
    (by cases color <;> rfl) renamedSafe.castTyping
    (by simpa only [ContextSubstitution.isObjectPattern_renameAmbientBVarsAt,
      isObjectPattern_mapPattern] using object) available.length
  cases color <;>
    simpa only [actionAt, declaration, costBaseReflectivePresentationDecl,
      costWrappedReflectivePresentationDecl, mapReflectivePresentation,
      costBaseStaticReflectiveSymbols, costWrappedStaticReflectiveSymbols,
      costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      CostStaticColor.symbolsOf, costWrappedStaticSymbols, rhoReflectivePresentation,
      mapPattern, mapPatternList_eq_map, ContextSubstitution.renameAmbientBVarsAt,
      List.map_cons, List.map_nil, List.length_map] using cancellation

/-- Canonicalizing a supported typed source frame before restoration does
not change its target canonical representative. Target values may contain
principal constructors and apparatus outside the source static fragment. -/
theorem canonicalize_action
    (profile : ContinuationDecorationProfile cut)
    (inventory : CanonicalInventory theory.presentation.presentation.language)
    (sourceReflectionValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate
      theory.presentation.presentation.language rhoReflectionProfile = [])
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (reflectiveAllowed : ReflectiveConstructorsAllowed (· ∈ profile.wrappedLabels)
      rhoReflectivePresentation)
    (quotedResults : ReflectiveNameResultsQuoted
      (profile := profile.costWholeReflectionProfile rhoReflectionProfile) profile.costWholeLanguage)
    {color : CostStaticColor} {free targetFree : FreeTypeContext}
    {support : ContextSupport.Support} {sourceBound targetBound inner available : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    (assignment : SupportedOpenAssignment (profile.costWholeReflectionProfile rhoReflectionProfile)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support)
    (typed : HasType theory.presentation.presentation.language free (inner ++ sourceBound) pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
      (mapTypeExpr (color.symbolsOf theory)))
    (supported : ConstructorsWithin (· ∈ profile.wrappedLabels) pattern)
    (object : isObjectPattern pattern = true) :
    canonicalize (declaration theory color)
      (actionAt profile color thinning assignment inner available pattern) =
      canonicalize (declaration theory color)
        (actionAt profile color thinning assignment inner available
          (canonicalize rhoReflectivePresentation pattern)) := by
  let targetDeclaration := declaration theory color
  have sourceMembership : rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoReflectionProfile.presentations := by simp [rhoReflectionProfile]
  have targetQuoteStatus : ReflectiveContextSupport.isQuoteConstructor
      (profile.costWholeReflectionProfile rhoReflectionProfile)
      ((color.symbolsOf theory).constructor rhoReflectivePresentation.quoteConstructor) = true := by
    rw [profile.reflectiveIsQuoteConstructor_mapStatic]
    simp [rhoReflectionProfile, ReflectiveContextSupport.isQuoteConstructor,
      rhoReflectivePresentation]
  have targetDeclarationQuote : targetDeclaration.quoteConstructor =
      (color.symbolsOf theory).constructor rhoReflectivePresentation.quoteConstructor := by
    cases color <;> rfl
  have targetQuoteStatusTag : ReflectiveContextSupport.isQuoteConstructor
      (profile.costWholeReflectionProfile rhoReflectionProfile)
      (color.constructorTag ++ rhoReflectivePresentation.quoteConstructor) = true := by
    rw [← CostStaticColor.symbolsOf_constructor]
    exact targetQuoteStatus
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType theory.presentation.presentation.language free bound pattern type)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbolsOf theory) →
        ConstructorsWithin
          (· ∈ profile.wrappedLabels) pattern →
        isObjectPattern pattern = true →
        canonicalize
            targetDeclaration
            (actionAt profile color thinning assignment currentInner
              currentAvailable pattern) =
          canonicalize
            targetDeclaration
            (actionAt profile color thinning assignment currentInner
              currentAvailable
              (canonicalize
                rhoReflectivePresentation pattern)))
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes theory.presentation.presentation.language free bound arguments parameters)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbolsOf theory) →
        ConstructorListWithin
          (· ∈ profile.wrappedLabels) arguments →
        isObjectPatternList arguments = true →
        canonicalizeList
            targetDeclaration
            (arguments.map
              (actionAt profile color thinning assignment currentInner
                currentAvailable)) =
          canonicalizeList
            targetDeclaration
            ((canonicalizeList
              rhoReflectivePresentation arguments).map
                (actionAt profile color thinning assignment currentInner
                  currentAvailable)))
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType theory.presentation.presentation.language free bound elements elementType)
      (currentAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support
        currentAvailable currentImage) =>
      ∀ (currentInner : List TypeExpr),
        bound = currentInner ++ sourceBound →
        currentImage = mapTypeExpr (color.symbolsOf theory) →
        ConstructorListWithin
          (· ∈ profile.wrappedLabels) elements →
        isObjectPatternList elements = true →
        canonicalizeList
            targetDeclaration
            (elements.map
              (actionAt profile color thinning assignment currentInner
                currentAvailable)) =
          canonicalizeList
            targetDeclaration
            ((canonicalizeList
              rhoReflectivePresentation elements).map
                (actionAt profile color thinning assignment currentInner
                  currentAvailable)))
    (by
      intro bound index resultType lookup currentAvailable currentImage
        currentInner boundEquality imageEquality resultSupported resultObject
      rfl)
    (by
      intro bound freeName resultType lookup currentAvailable currentImage shape
        currentInner boundEquality imageEquality resultSupported resultObject
      rfl)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage quoted argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ profile.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have selectedByQuote :
          rule.label = rhoReflectivePresentation.quoteConstructor := by
        unfold ReflectiveContextSupport.isQuoteConstructor at quoted
        rw [List.any_eq_true] at quoted
        obtain ⟨declaration, declarationMembership, quoteLabel⟩ := quoted
        have declarationEquality : declaration =
            rhoReflectivePresentation.toReflectivePresentationDecl := by
          simpa [rhoReflectionProfile] using declarationMembership
        subst declaration
        have quoteLabel' :
            rhoReflectivePresentation.quoteConstructor = rule.label := by
          simpa using quoteLabel
        exact quoteLabel'.symm
      obtain ⟨argument, argumentTyped, rfl, argumentSafe⟩ :=
        argumentsTyped.selectedQuoteArgument
          theory.presentation.presentation.valid
            sourceReflectionValid sourceMembership
            membership selectedByQuote
            argumentsSafe
      have argumentSupported : ConstructorsWithin
          (· ∈ profile.wrappedLabels) argument :=
        argumentsSupported.1
      have argumentObject : isObjectPattern argument = true := by
        simpa [isObjectPatternList] using argumentsObject
      have argumentEquality :
          canonicalize
              targetDeclaration
              (actionAt profile color thinning assignment currentInner []
                argument) =
            canonicalize
              targetDeclaration
              (actionAt profile color thinning assignment currentInner []
                (canonicalize
                  rhoReflectivePresentation argument)) := by
        simpa [canonicalizeList]
          using argumentsIH currentInner boundEquality imageEquality
            argumentsSupported argumentsObject
      have quoteAction (payload : Pattern) :
          actionAt profile color thinning assignment currentInner
              currentAvailable
              (.apply rhoReflectivePresentation.quoteConstructor [payload]) =
            .apply targetDeclaration.quoteConstructor
              [actionAt profile color thinning assignment currentInner []
                payload] := by
        rw [targetDeclarationQuote]
        simp [actionAt,
          ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern,
          targetQuoteStatusTag]
      rw [selectedByQuote]
      apply ReflectiveCanonicalAction.quote rhoReflectivePresentation targetDeclaration
        (actionAt profile color thinning assignment currentInner currentAvailable)
        (actionAt profile color thinning assignment currentInner []) argument
        quoteAction argumentEquality
      intro name canonicalEquality
      obtain ⟨nameTyped, nameSafe, nameObject⟩ := inventory.dropCanonicalSupportStable
        rhoReflectivePresentation sourceMembership argumentTyped argumentSafe
        argumentObject canonicalEquality
      have canonicalSupported := (constructorsWithin_canonicalize_iff
        rhoReflectivePresentation reflectiveAllowed argument).2 argumentSupported
      rw [canonicalEquality] at canonicalSupported
      have nameSupported : ConstructorsWithin (· ∈ profile.wrappedLabels) name :=
        canonicalSupported.2.1
      have nameTypedSafe : ∃ nameTyped' : HasType theory.presentation.presentation.language free
          (currentInner ++ sourceBound) name (.base rhoReflectivePresentation.nameSort),
          nameTyped'.ReflectiveSupportSafeAt rhoReflectionProfile support []
            (mapTypeExpr (color.symbolsOf theory)) := by
        rw [← boundEquality]
        exact ⟨nameTyped, by simpa only [imageEquality] using nameSafe⟩
      obtain ⟨nameTyped, nameSafe⟩ := nameTypedSafe
      exact quoteDrop profile nonprincipal bareAllowed quotedResults thinning assignment
        nameTyped nameSafe nameSupported nameObject currentAvailable)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        currentAvailable currentImage ordinary argumentsSafe argumentsIH
        currentInner boundEquality imageEquality resultSupported resultObject
      have argumentsSupported : ConstructorListWithin
          (· ∈ profile.wrappedLabels) arguments :=
        resultSupported.2
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have listEquality := argumentsIH currentInner boundEquality imageEquality
        argumentsSupported argumentsObject
      have selected :
          rule.label ≠ rhoReflectivePresentation.quoteConstructor := by
        intro equality
        have sourceQuote : ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
            rhoReflectivePresentation.quoteConstructor = true := by
          simp only [ReflectiveContextSupport.isQuoteConstructor,
            List.any_eq_true]
          exact ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
            sourceMembership, by simp⟩
        rw [equality] at ordinary
        exact Bool.noConfusion (ordinary.symm.trans sourceQuote)
      have selectedFalse :
          (rule.label == rhoReflectivePresentation.quoteConstructor) = false :=
        by simp [selected]
      have targetOrdinaryStatus :
          ReflectiveContextSupport.isQuoteConstructor (profile.costWholeReflectionProfile rhoReflectionProfile)
              ((color.symbolsOf theory).constructor rule.label) = false := by
        rw [profile.reflectiveIsQuoteConstructor_mapStatic]
        exact ordinary
      have targetOrdinaryStatusTag :
          ReflectiveContextSupport.isQuoteConstructor (profile.costWholeReflectionProfile rhoReflectionProfile)
              (color.constructorTag ++ rule.label) = false := by
        rw [← CostStaticColor.symbolsOf_constructor]
        exact targetOrdinaryStatus
      have applicationAction (patterns : List Pattern) :
          actionAt profile color thinning assignment currentInner
              currentAvailable (.apply rule.label patterns) =
            .apply ((color.symbolsOf theory).constructor rule.label)
              (patterns.map (actionAt profile color thinning assignment
                currentInner currentAvailable)) := by
        simp [actionAt,
          ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern,
          targetOrdinaryStatusTag, List.map_map, Function.comp_def]
      have canonicalApplication :
          canonicalize
              rhoReflectivePresentation (.apply rule.label arguments) =
            .apply rule.label
              (canonicalizeList
                rhoReflectivePresentation arguments) := by
        simp [canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          selectedFalse]
      rw [canonicalApplication, applicationAction, applicationAction]
      simp only [canonicalize]
      rw [listEquality])
    (by
      intro bound binder body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : domain :: bound =
          (domain :: currentInner) ++ sourceBound := by
        simp [boundEquality]
      have bodyEquality := bodyIH (domain :: currentInner) bodyBound
        imageEquality resultSupported bodyObject
      simpa [actionAt,
        ReflectiveContextSupport.substituteAt,
        canonicalize,
        ContextSubstitution.renameAmbientBVarsAt, mapPattern]
        using congrArg (Pattern.lambda binder) bodyEquality)
    (by
      intro bound arity binders body domain codomain bodyTyped currentAvailable
        currentImage bodySafe bodyIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have bodyBound : List.replicate arity domain ++ bound =
          (List.replicate arity domain ++ currentInner) ++ sourceBound := by
        simp [boundEquality, List.append_assoc]
      have bodyEquality := bodyIH
        (List.replicate arity domain ++ currentInner) bodyBound imageEquality
          resultSupported bodyObject
      simpa [actionAt,
        ReflectiveContextSupport.substituteAt,
        canonicalize,
        ContextSubstitution.renameAmbientBVarsAt, mapPattern,
        List.length_append, List.length_replicate,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using congrArg (Pattern.multiLambda arity binders) bodyEquality)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        currentInner boundEquality imageEquality resultSupported resultObject
      simp [isObjectPattern] at resultObject)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        currentAvailable currentImage elementsSafe elementsIH currentInner
        boundEquality imageEquality resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have listEquality := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      apply ReflectiveCanonicalAction.collection rhoReflectivePresentation targetDeclaration
        (actionAt profile color thinning assignment currentInner currentAvailable)
        (by cases color <;> rfl) ?_ ?_ collectionType elements listEquality
      · intro kind patterns
        simp [actionAt, ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern,
          List.map_map, Function.comp_def]
      · have unitField : targetDeclaration.parallelUnitConstructor =
            (color.symbolsOf theory).constructor rhoReflectivePresentation.parallelUnitConstructor := by
          cases color <;> rfl
        rw [unitField]
        simp [actionAt, ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern])
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped currentAvailable currentImage
        elementsSafe elementsIH currentInner boundEquality imageEquality
        resultSupported resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have listEquality := elementsIH currentInner boundEquality imageEquality
        resultSupported elementsObject
      apply ReflectiveCanonicalAction.collection rhoReflectivePresentation targetDeclaration
        (actionAt profile color thinning assignment currentInner currentAvailable)
        (by cases color <;> rfl) ?_ ?_ collectionType elements listEquality
      · intro kind patterns
        simp [actionAt, ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern,
          List.map_map, Function.comp_def]
      · have unitField : targetDeclaration.parallelUnitConstructor =
            (color.symbolsOf theory).constructor rhoReflectivePresentation.parallelUnitConstructor := by
          cases color <;> rfl
        rw [unitField]
        simp [actionAt, ReflectiveContextSupport.substituteAt,
          ContextSubstitution.renameAmbientBVarsAt, mapPattern])
    (by
      intro bound currentAvailable currentImage currentInner boundEquality
        imageEquality argumentsSupported argumentsObject
      rfl)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH currentInner boundEquality imageEquality argumentsSupported
        argumentsObject
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using argumentsObject
      simp only [canonicalizeList,
        List.map_cons]
      rw [argumentIH currentInner boundEquality imageEquality
          argumentsSupported.1 objectParts.1,
        argumentsIH currentInner boundEquality imageEquality
          argumentsSupported.2 objectParts.2])
    (by
      intro bound elementType currentAvailable currentImage currentInner
        boundEquality imageEquality elementsSupported elementsObject
      rfl)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        currentAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH currentInner boundEquality imageEquality elementsSupported
        elementsObject
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using elementsObject
      simp only [canonicalizeList,
        List.map_cons]
      rw [elementIH currentInner boundEquality imageEquality
          elementsSupported.1 objectParts.1,
        elementsIH currentInner boundEquality imageEquality
          elementsSupported.2 objectParts.2])
    safe inner rfl rfl supported object


end Mettapedia.Languages.ProcessCalculi.RhoCalculus.FiniteStaticCanonicalAction
