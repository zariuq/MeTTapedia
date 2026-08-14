import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceRecursive
import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportOccurrenceSubstitutionComposition
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Reflective substitution with two availabilities

For a binder-free frame, caller-relative support availability and the
executor's quote-local substitution availability can be tracked independently.
The first controls the result's support certificate. The second controls the
de Bruijn shift and is justified by a support certificate for the assignment's
typing support.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Reflection

namespace WellSorted

mutual
  def ReflectiveSubstitutionBinderFree : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => ReflectiveSubstitutionBinderFreeList arguments
    | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => false
    | .collection _ elements _ => ReflectiveSubstitutionBinderFreeList elements

  def ReflectiveSubstitutionBinderFreeList : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        ReflectiveSubstitutionBinderFree pattern &&
          ReflectiveSubstitutionBinderFreeList patterns
end

@[simp]
theorem reflectiveSubstitutionBinderFree_fvar (name : String) :
    ReflectiveSubstitutionBinderFree (.fvar name) = true :=
  rfl

@[simp]
theorem reflectiveSubstitutionBinderFree_lambda
    (binder : Option String) (body : Pattern) :
    ReflectiveSubstitutionBinderFree (.lambda binder body) = false :=
  rfl

/-! ## Binder-image irrelevance for binder-free frames -/

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- A binder-free frame never consults the interpretation chosen for binder
  types in its reflective-support certificate. -/
  theorem HasType.ReflectiveSupportSafeAt.changeBinderImage_of_binderFree
      {language : LanguageDef} {free : FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language free bound pattern type}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : ReflectiveSubstitutionBinderFree pattern = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | bvar lookup => exact .bvar lookup available
    | fvar lookup _ shape =>
        exact .fvar lookup available shape
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        have argumentsFree : ReflectiveSubstitutionBinderFreeList arguments = true := by
          simpa [ReflectiveSubstitutionBinderFree] using frameFree
        exact .constructorQuote (membership := membership)
          (notBare := notBare) quoted
          (argumentsSafe.changeBinderImage_of_binderFree argumentsFree
            targetImage)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        have argumentsFree : ReflectiveSubstitutionBinderFreeList arguments = true := by
          simpa [ReflectiveSubstitutionBinderFree] using frameFree
        exact .constructorOrdinary (membership := membership)
          (notBare := notBare) ordinary
          (argumentsSafe.changeBinderImage_of_binderFree argumentsFree
            targetImage)
    | lambda bodySafe =>
        simp [ReflectiveSubstitutionBinderFree] at frameFree
    | multiLambda bodySafe =>
        simp [ReflectiveSubstitutionBinderFree] at frameFree
    | subst bodySafe replacementSafe =>
        simp [ReflectiveSubstitutionBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : ReflectiveSubstitutionBinderFreeList elements = true := by
          simpa [ReflectiveSubstitutionBinderFree] using frameFree
        exact .collection
          (elementsSafe.changeBinderImage_of_binderFree elementsFree
            targetImage)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        have elementsFree : ReflectiveSubstitutionBinderFreeList elements = true := by
          simpa [ReflectiveSubstitutionBinderFree] using frameFree
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (elementsSafe.changeBinderImage_of_binderFree elementsFree
            targetImage)
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to binder-image irrelevance. -/
  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.changeBinderImage_of_binderFree
      {language : LanguageDef} {free : FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language free bound arguments parameters}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList arguments = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | nil => exact .nil bound available
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        have freeParts : ReflectiveSubstitutionBinderFree argument = true ∧
            ReflectiveSubstitutionBinderFreeList arguments = true := by
          simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (argumentSafe.changeBinderImage_of_binderFree freeParts.1
            targetImage)
          (argumentsSafe.changeBinderImage_of_binderFree freeParts.2
            targetImage)
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-element companion to binder-image irrelevance. -/
  theorem ElementsHaveType.ReflectiveSupportSafeAt.changeBinderImage_of_binderFree
      {language : LanguageDef} {free : FreeTypeContext}
      {profile : ReflectionProfile} {support : ContextSupport.Support}
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : ElementsHaveType language free bound elements elementType}
      {sourceImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available
        sourceImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList elements = true)
      (targetImage : TypeExpr → TypeExpr) :
      typed.ReflectiveSupportSafeAt profile support available targetImage := by
    cases safe with
    | nil => exact .nil bound elementType available
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        have freeParts : ReflectiveSubstitutionBinderFree element = true ∧
            ReflectiveSubstitutionBinderFreeList elements = true := by
          simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
        exact .cons
          (elementSafe.changeBinderImage_of_binderFree freeParts.1
            targetImage)
          (elementsSafe.changeBinderImage_of_binderFree freeParts.2
            targetImage)
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

inductive ApplicationSupportView
    (profile : ReflectionProfile) (language : LanguageDef)
    (free : FreeTypeContext) (support : ContextSupport.Support)
    (bound : List TypeExpr) (label : String) (arguments : List Pattern)
    (type : TypeExpr) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr) : Prop where
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
      ApplicationSupportView profile language free support bound label
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
      ApplicationSupportView profile language free support bound label
        arguments type available binderImage

theorem applicationSupportView
    {profile : ReflectionProfile} {language : LanguageDef}
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    {type : TypeExpr}
    {typed : HasType language free bound (.apply label arguments) type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ApplicationSupportView profile language free support bound label arguments
      type available binderImage := by
  cases safe with
  | @constructorQuote bound rule arguments membership notBare argumentsTyped
      available binderImage quoted argumentsSafe =>
      exact .quote membership rfl rfl quoted argumentsSafe
  | @constructorOrdinary bound rule arguments membership notBare argumentsTyped
      available binderImage ordinary argumentsSafe =>
      exact .ordinary membership rfl rfl ordinary argumentsSafe

inductive CollectionSupportView
    (profile : ReflectionProfile) (language : LanguageDef)
    (free : FreeTypeContext) (support : ContextSupport.Support)
    (bound : List TypeExpr) (collectionType : CollType)
    (elements : List Pattern) (rest : Option String) (type : TypeExpr)
    (available : List TypeExpr) (binderImage : TypeExpr → TypeExpr) : Prop where
  | collection {elementType : TypeExpr}
      (typeEquality : type = .collection collectionType elementType)
      {elementsTyped : ElementsHaveType language free bound elements
        elementType}
      (elementsSafe : elementsTyped.ReflectiveSupportSafeAt profile support
        available binderImage) :
      CollectionSupportView profile language free support bound collectionType
        elements rest type available binderImage
  | collectionConstructor {rule : GrammarRule} {parameterName : String}
      {elementType : TypeExpr}
      (membership : rule ∈ language.terms)
      (parameterShape : rule.params =
        [.simple parameterName (.collection collectionType elementType)])
      (typeEquality : type = .base rule.category)
      {elementsTyped : ElementsHaveType language free bound elements
        elementType}
      (elementsSafe : elementsTyped.ReflectiveSupportSafeAt profile support
        available binderImage) :
      CollectionSupportView profile language free support bound collectionType
        elements rest type available binderImage

theorem collectionSupportView
    {profile : ReflectionProfile} {language : LanguageDef}
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {type : TypeExpr}
    {typed : HasType language free bound
      (.collection collectionType elements rest) type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    CollectionSupportView profile language free support bound collectionType
      elements rest type available binderImage := by
  cases safe with
  | @collection bound collectionType elements rest elementType elementsTyped
      available binderImage elementsSafe =>
      exact .collection rfl elementsSafe
  | @collectionConstructor bound rule parameterName collectionType elements
      rest elementType membership parameterShape elementsTyped available
      binderImage elementsSafe =>
      exact .collectionConstructor membership parameterShape rfl elementsSafe

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  theorem HasType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtTwoAvailabilities
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound callerAvailable actualAvailable : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        callerAvailable callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        actualAvailable actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFree pattern = true)
      (sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      {Root : Type}
      (embed : CostStaticFVarOccurrence pattern → Root)
      (valueSafe : ∀ {name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available callerBinderImage) :
      ∃ outputTyped : HasType language target bound
          (ReflectiveContextSupport.substituteAt profile typingSupport
            assignment.assignment actualAvailable.length pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          callerAvailable callerBinderImage := by
    cases callerSafe with
    | @bvar bound index type lookup currentAvailable callerBinderImage =>
        let outputTyped : HasType language target bound (.bvar index) type :=
          .bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := callerBinderImage) lookup callerAvailable⟩)
    | @fvar bound name type lookup currentAvailable callerBinderImage
        callerShape =>
        cases actualSafe with
        | fvar _ _ actualShape =>
            let point : CostStaticFVarOccurrence (.fvar name) :=
              ⟨name, .hole, .here⟩
            obtain ⟨active, actualShape⟩ := actualShape
            have assignedSafe := valueSafe (lookup := lookup)
              (available := callerAvailable) (embed point)
            obtain ⟨liftedTyped, liftedSafe⟩ :=
              assignedSafe.liftBVars_insert [] (typingSupport name) active rfl
            let liftedTyped' : HasType language target
                (active ++ typingSupport name)
                (liftBVars 0 active.length
                  (assignment.assignment name)) type := by
              simpa only [List.nil_append, List.length_nil] using liftedTyped
            have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt profile
                outputSupport callerAvailable callerBinderImage := by
              apply HasType.ReflectiveSupportSafeAt.castTyping
              simpa only [List.nil_append, List.length_nil] using liftedSafe
            obtain ⟨extendedTyped, extendedSafe⟩ :=
              liftedSafe'.extendOuter sealed
            have shiftEquality :
                actualAvailable.length - (typingSupport name).length =
                  active.length := by
              rw [actualShape]
              simp only [List.length_append]
              omega
            have packaged : ∃ outputTyped : HasType language target
                ((active ++ typingSupport name) ++ sealed)
                (ReflectiveContextSupport.substituteAt profile typingSupport
                  assignment.assignment actualAvailable.length
                    (.fvar name)) type,
              outputTyped.ReflectiveSupportSafeAt profile outputSupport
                callerAvailable callerBinderImage := by
              simpa only [ReflectiveContextSupport.substituteAt,
                shiftEquality] using (⟨extendedTyped, extendedSafe⟩)
            rw [actualShape] at boundShape
            simpa only [boundShape] using packaged
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable callerBinderImage quoted argumentsCallerSafe =>
        have view := applicationSupportView actualSafe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualQuoted argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  [] actualBinderImage :=
              argumentsActualSafe.castTyping
            have argumentsFree :
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputArguments, outputSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree bound (by simp)
                  (fun occurrence => embed
                    (occurrence.inApply rule.label))
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputTyped := HasType.constructor membership notBare
              outputArguments
            simpa [ReflectiveContextSupport.substituteAt, quoted] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.constructorQuote
                  (membership := membership) (notBare := notBare) quoted
                  outputSafe⟩)
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualOrdinary argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            rw [quoted] at actualOrdinary
            contradiction
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable callerBinderImage ordinary
        argumentsCallerSafe =>
        have view := applicationSupportView actualSafe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualQuoted argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            rw [ordinary] at actualQuoted
            contradiction
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualOrdinary argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              argumentsActualSafe.castTyping
            have argumentsFree :
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputArguments, outputSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree sealed boundShape
                  (fun occurrence => embed
                    (occurrence.inApply rule.label))
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputTyped := HasType.constructor membership notBare
              outputArguments
            simpa [ReflectiveContextSupport.substituteAt, ordinary] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.constructorOrdinary
                  (membership := membership) (notBare := notBare) ordinary
                  outputSafe⟩)
    | lambda => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | multiLambda => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | subst => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable callerBinderImage elementsCallerSafe =>
        have view := collectionSupportView actualSafe
        cases view with
        | @collection actualElementType typeEquality actualElementsTyped
            elementsActualSafe =>
            have elementTypeEquality : elementType = actualElementType :=
              (TypeExpr.collection.inj typeEquality).2
            subst actualElementType
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              elementsActualSafe.castTyping
            have elementsFree :
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputElements, outputSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  (fun occurrence => embed
                    (occurrence.inCollection collectionType rest))
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputTyped := HasType.collection
              (collectionType := collectionType) (rest := rest) outputElements
            simpa only [ReflectiveContextSupport.substituteAt] using
              (⟨outputTyped, HasType.ReflectiveSupportSafeAt.collection
                outputSafe⟩)
        | collectionConstructor _ _ typeEquality _ =>
            simp at typeEquality
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable callerBinderImage elementsCallerSafe =>
        have view := collectionSupportView actualSafe
        cases view with
        | collection typeEquality _ =>
            simp at typeEquality
        | @collectionConstructor actualRule actualParameterName
            actualElementType actualMembership actualParameterShape
            typeEquality actualElementsTyped elementsActualSafe =>
            have categoriesEquality : rule.category = actualRule.category :=
              TypeExpr.base.inj typeEquality
            have elementTypeEquality : elementType = actualElementType :=
              collectionDeterministic membership actualMembership
                parameterShape actualParameterShape categoriesEquality
            subst actualElementType
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              elementsActualSafe.castTyping
            have elementsFree :
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputElements, outputSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  (fun occurrence => embed
                    (occurrence.inCollection collectionType rest))
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputTyped := HasType.collectionConstructor (rest := rest)
              membership parameterShape outputElements
            simpa only [ReflectiveContextSupport.substituteAt] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.collectionConstructor
                  (membership := membership) (parameterShape := parameterShape)
                  outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtTwoAvailabilities
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound callerAvailable actualAvailable : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        callerAvailable callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        actualAvailable actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList arguments = true)
      (sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence arguments → Root)
      (valueSafe : ∀ {name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available callerBinderImage) :
      ∃ outputTyped : ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualAvailable.length))
          parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          callerAvailable callerBinderImage := by
    cases callerSafe with
    | nil =>
        let outputTyped := ArgumentsHaveTypes.nil
          (language := language) (free := target) (bound := bound)
        exact ⟨outputTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable callerBinderImage argumentCallerSafe
        argumentsCallerSafe =>
        have actualSafe' :
            (ArgumentsHaveTypes.cons representation parameterType
              argumentTyped argumentsTyped).ReflectiveSupportSafeAt profile
                typingSupport actualAvailable actualBinderImage :=
          actualSafe.castTyping
        have argumentActualSafeExact :
            argumentTyped.ReflectiveSupportSafeAt profile typingSupport
              actualAvailable actualBinderImage :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
            (representation := representation)
            (parameterType := parameterType)
            (argumentTyped := argumentTyped)
            (argumentsTyped := argumentsTyped) actualSafe'
        cases actualSafe' with
        | cons argumentActualSafe argumentsActualSafe =>
            have argumentActualSafe' :
                argumentTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              argumentActualSafeExact
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              argumentsActualSafe.castTyping
            have freeParts : ReflectiveSubstitutionBinderFree argument = true ∧
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
            let embedHead : CostStaticFVarOccurrence argument → Root :=
              fun occurrence => embed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTail : CostStaticFVarListOccurrence arguments → Root :=
              fun occurrence => embed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            obtain ⟨outputArgument, outputArgumentSafe⟩ :=
              argumentCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  argumentActualSafe' freeParts.1 sealed boundShape embedHead
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' freeParts.2 sealed boundShape embedTail
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputRepresentation := representation.substituteReflectiveAt
              profile parameter argument typingSupport assignment.assignment
                actualAvailable.length
            let outputTyped := ArgumentsHaveTypes.cons outputRepresentation
              parameterType outputArgument outputArguments
            exact ⟨outputTyped, .cons
              (representation := outputRepresentation)
              (parameterType := parameterType) outputArgumentSafe
              outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtTwoAvailabilities
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound callerAvailable actualAvailable : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        callerAvailable callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        actualAvailable actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList elements = true)
      (sealed : List TypeExpr)
      (boundShape : bound = actualAvailable ++ sealed)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence elements → Root)
      (valueSafe : ∀ {name type}
        {lookup : source name = some type} {available : List TypeExpr},
        Root →
          (assignment.typed lookup).ReflectiveSupportSafeAt profile
            outputSupport available callerBinderImage) :
      ∃ outputTyped : ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualAvailable.length))
          elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          callerAvailable callerBinderImage := by
    cases callerSafe with
    | nil =>
        let outputTyped := ElementsHaveType.nil
          (language := language) (free := target) bound elementType
        exact ⟨outputTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable callerBinderImage elementCallerSafe
        elementsCallerSafe =>
        have actualSafe' :
            (ElementsHaveType.cons elementTyped
              elementsTyped).ReflectiveSupportSafeAt profile typingSupport
                actualAvailable actualBinderImage :=
          actualSafe.castTyping
        cases actualSafe' with
        | cons elementActualSafe elementsActualSafe =>
            have elementActualSafe' :
                elementTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              elementActualSafe.castTyping
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  actualAvailable actualBinderImage :=
              elementsActualSafe.castTyping
            have freeParts : ReflectiveSubstitutionBinderFree element = true ∧
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
            let embedHead : CostStaticFVarOccurrence element → Root :=
              fun occurrence => embed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTail : CostStaticFVarListOccurrence elements → Root :=
              fun occurrence => embed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            obtain ⟨outputElement, outputElementSafe⟩ :=
              elementCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  elementActualSafe' freeParts.1 sealed boundShape embedHead
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            obtain ⟨outputElements, outputElementsSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtTwoAvailabilities
                assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' freeParts.2 sealed boundShape embedTail
                  (fun {name type} {lookup} {available} root =>
                    valueSafe (name := name) (type := type)
                      (lookup := lookup) (available := available) root)
            let outputTyped := ElementsHaveType.cons outputElement
              outputElements
            exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-! ## Binder-free exposed/sealed regimes

The fully positional theorem above deliberately allows arbitrary syntax.  Its
callback is consequently quantified over every ambient availability, which is
too strong for a restored free variable whose support is nonempty.  Canonical
rho frames are binder-free, so their only two substitution regimes are the
root frame and the quote-local sealed frame.  This interface records those
regimes explicitly and gives each one its own occurrence callback.
-/

inductive ReflectiveSubstitutionRegime where
  | exposed
  | sealed

namespace ReflectiveSubstitutionRegime

def available : ReflectiveSubstitutionRegime → List TypeExpr → List TypeExpr
  | .exposed, rootAvailable => rootAvailable
  | .sealed, _ => []

@[simp]
theorem available_exposed (rootAvailable : List TypeExpr) :
    available .exposed rootAvailable = rootAvailable := rfl

@[simp]
theorem available_sealed (rootAvailable : List TypeExpr) :
    available .sealed rootAvailable = [] := rfl

end ReflectiveSubstitutionRegime

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Binder-free substitution with separate exposed and sealed occurrence
  callbacks.  A quoted constructor switches to the sealed regime; ordinary
  constructors preserve the current regime. -/
  theorem HasType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtBinderFreeRegimes
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (regime : ReflectiveSubstitutionRegime)
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound rootCallerAvailable rootActualAvailable : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
        callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
        actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFree pattern = true)
      (sealed : List TypeExpr)
      (boundShape : bound =
        ReflectiveSubstitutionRegime.available regime rootActualAvailable ++ sealed)
      {RootExposed RootSealed : String → Type}
      (embedExposed : (occurrence : CostStaticFVarOccurrence pattern) →
        RootExposed occurrence.name)
      (embedSealed : (occurrence : CostStaticFVarOccurrence pattern) →
        RootSealed occurrence.name)
      (valueSafeExposed : ∀ {name type}
        (lookup : source name = some type), RootExposed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          rootCallerAvailable callerBinderImage)
      (valueSafeSealed : ∀ {name type}
        (lookup : source name = some type), RootSealed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          [] callerBinderImage) :
      ∃ outputTyped : HasType language target bound
          (ReflectiveContextSupport.substituteAt profile typingSupport
            assignment.assignment
            (ReflectiveSubstitutionRegime.available regime rootActualAvailable).length
            pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
          callerBinderImage := by
    cases callerSafe with
    | @bvar bound index type lookup currentAvailable callerBinderImage =>
        let outputTyped : HasType language target bound (.bvar index) type :=
          .bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := callerBinderImage) lookup
            (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)⟩)
    | @fvar bound name type lookup currentAvailable callerBinderImage callerShape =>
        cases regime with
        | exposed =>
            cases actualSafe with
            | fvar _ _ actualShape =>
                let point : CostStaticFVarOccurrence (.fvar name) :=
                  ⟨name, .hole, .here⟩
                obtain ⟨active, actualShape⟩ := actualShape
                have assignedSafe :=
                  valueSafeExposed (lookup := lookup) (embedExposed point)
                obtain ⟨liftedTyped, liftedSafe⟩ :=
                  assignedSafe.liftBVars_insert [] (typingSupport name) active rfl
                let liftedTyped' : HasType language target
                    (active ++ typingSupport name)
                    (liftBVars 0 active.length
                      (assignment.assignment name)) type := by
                  simpa only [List.nil_append, List.length_nil] using liftedTyped
                have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt profile
                    outputSupport rootCallerAvailable callerBinderImage := by
                  apply HasType.ReflectiveSupportSafeAt.castTyping
                  simpa only [List.nil_append, List.length_nil] using liftedSafe
                obtain ⟨extendedTyped, extendedSafe⟩ :=
                  liftedSafe'.extendOuter sealed
                have actualShape' : rootActualAvailable =
                    active ++ typingSupport name := by
                  simpa only [ReflectiveSubstitutionRegime.available] using
                    actualShape
                have shiftEquality :
                    rootActualAvailable.length - (typingSupport name).length =
                      active.length := by
                  rw [actualShape']
                  simp only [List.length_append]
                  omega
                have packaged : ∃ outputTyped : HasType language target
                    ((active ++ typingSupport name) ++ sealed)
                    (ReflectiveContextSupport.substituteAt profile typingSupport
                      assignment.assignment rootActualAvailable.length
                        (.fvar name)) type,
                  outputTyped.ReflectiveSupportSafeAt profile outputSupport
                    rootCallerAvailable callerBinderImage := by
                    simpa only [ReflectiveContextSupport.substituteAt,
                      shiftEquality] using (⟨extendedTyped, extendedSafe⟩)
                rw [actualShape'] at boundShape
                simpa only [ReflectiveSubstitutionRegime.available, boundShape]
                  using packaged
        | sealed =>
            cases actualSafe with
            | fvar _ _ actualShape =>
                let point : CostStaticFVarOccurrence (.fvar name) :=
                  ⟨name, .hole, .here⟩
                obtain ⟨active, actualShape⟩ := actualShape
                have assignedSafe :=
                  valueSafeSealed (lookup := lookup) (embedSealed point)
                obtain ⟨liftedTyped, liftedSafe⟩ :=
                  assignedSafe.liftBVars_insert [] (typingSupport name) active rfl
                let liftedTyped' : HasType language target
                    (active ++ typingSupport name)
                    (liftBVars 0 active.length
                      (assignment.assignment name)) type := by
                  simpa only [List.nil_append, List.length_nil] using liftedTyped
                have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt profile
                    outputSupport [] callerBinderImage := by
                  apply HasType.ReflectiveSupportSafeAt.castTyping
                  simpa only [List.nil_append, List.length_nil] using liftedSafe
                obtain ⟨extendedTyped, extendedSafe⟩ :=
                  liftedSafe'.extendOuter sealed
                have shiftEquality :
                    0 - (typingSupport name).length = active.length := by
                  have actualShape' : [] = active ++ typingSupport name := by
                    simpa only [ReflectiveSubstitutionRegime.available] using
                      actualShape
                  have lengths := congrArg List.length actualShape'
                  simp only [List.length_nil, List.length_append] at lengths
                  omega
                have packaged : ∃ outputTyped : HasType language target
                    ((active ++ typingSupport name) ++ sealed)
                    (ReflectiveContextSupport.substituteAt profile typingSupport
                      assignment.assignment 0 (.fvar name)) type,
                  outputTyped.ReflectiveSupportSafeAt profile outputSupport
                    [] callerBinderImage := by
                    simpa only [ReflectiveContextSupport.substituteAt,
                      shiftEquality] using (⟨extendedTyped, extendedSafe⟩)
                have actualShape' : [] = active ++ typingSupport name := by
                  simpa only [ReflectiveSubstitutionRegime.available] using
                    actualShape
                have boundShape' := boundShape
                rw [show ReflectiveSubstitutionRegime.available
                    .sealed rootActualAvailable = [] by rfl] at boundShape'
                rw [actualShape'] at boundShape'
                simpa only [ReflectiveSubstitutionRegime.available,
                  List.length_nil, boundShape']
                  using packaged
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable callerBinderImage quoted argumentsCallerSafe =>
        have view := applicationSupportView actualSafe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualQuoted argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  [] actualBinderImage := argumentsActualSafe.castTyping
            have argumentsFree :
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputArguments, outputSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                (regime := .sealed) (arguments := arguments)
                (rootCallerAvailable := rootCallerAvailable)
                (rootActualAvailable := rootActualAvailable)
                (RootExposed := RootExposed) (RootSealed := RootSealed)
                assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree bound (by simp)
                  (fun occurrence => embedExposed
                    (occurrence.inApply rule.label))
                  (fun occurrence => embedSealed
                    (occurrence.inApply rule.label))
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputTyped := HasType.constructor membership notBare
              outputArguments
            simpa [ReflectiveContextSupport.substituteAt, quoted] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.constructorQuote
                  (membership := membership) (notBare := notBare) quoted
                  outputSafe⟩)
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualOrdinary argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            rw [quoted] at actualOrdinary
            contradiction
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable callerBinderImage ordinary
        argumentsCallerSafe =>
        have view := applicationSupportView actualSafe
        cases view with
        | @quote actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualQuoted argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            rw [ordinary] at actualQuoted
            contradiction
        | @ordinary actualRule actualMembership labelEquality typeEquality
            actualArgumentsTyped actualOrdinary argumentsActualSafe =>
            have ruleEquality : actualRule = rule :=
              labelDeterministic actualMembership membership labelEquality.symm
            subst actualRule
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime
                    rootActualAvailable) actualBinderImage :=
              argumentsActualSafe.castTyping
            have argumentsFree :
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputArguments, outputSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree sealed boundShape
                  (fun occurrence => embedExposed
                    (occurrence.inApply rule.label))
                  (fun occurrence => embedSealed
                    (occurrence.inApply rule.label))
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputTyped := HasType.constructor membership notBare
              outputArguments
            simpa [ReflectiveContextSupport.substituteAt, ordinary] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.constructorOrdinary
                  (membership := membership) (notBare := notBare) ordinary
                  outputSafe⟩)
    | lambda => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | multiLambda => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | subst => simp [ReflectiveSubstitutionBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable callerBinderImage elementsCallerSafe =>
        have view := collectionSupportView actualSafe
        cases view with
        | @collection actualElementType typeEquality actualElementsTyped
            elementsActualSafe =>
            have elementTypeEquality : elementType = actualElementType :=
              (TypeExpr.collection.inj typeEquality).2
            subst actualElementType
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime
                    rootActualAvailable) actualBinderImage :=
              elementsActualSafe.castTyping
            have elementsFree :
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputElements, outputSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  (fun occurrence => embedExposed
                    (occurrence.inCollection collectionType rest))
                  (fun occurrence => embedSealed
                    (occurrence.inCollection collectionType rest))
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputTyped := HasType.collection
              (collectionType := collectionType) (rest := rest) outputElements
            simpa only [ReflectiveContextSupport.substituteAt] using
              (⟨outputTyped, HasType.ReflectiveSupportSafeAt.collection
                outputSafe⟩)
        | collectionConstructor _ _ typeEquality _ =>
            simp at typeEquality
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable callerBinderImage elementsCallerSafe =>
        have view := collectionSupportView actualSafe
        cases view with
        | collection typeEquality _ =>
            simp at typeEquality
        | @collectionConstructor actualRule actualParameterName
            actualElementType actualMembership actualParameterShape
            typeEquality actualElementsTyped elementsActualSafe =>
            have categoriesEquality : rule.category = actualRule.category :=
              TypeExpr.base.inj typeEquality
            have elementTypeEquality : elementType = actualElementType :=
              collectionDeterministic membership actualMembership
                parameterShape actualParameterShape categoriesEquality
            subst actualElementType
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime
                    rootActualAvailable) actualBinderImage :=
              elementsActualSafe.castTyping
            have elementsFree :
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFree] using frameFree
            obtain ⟨outputElements, outputSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  (fun occurrence => embedExposed
                    (occurrence.inCollection collectionType rest))
                  (fun occurrence => embedSealed
                    (occurrence.inCollection collectionType rest))
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputTyped := HasType.collectionConstructor (rest := rest)
              membership parameterShape outputElements
            simpa only [ReflectiveContextSupport.substituteAt] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.collectionConstructor
                  (membership := membership) (parameterShape := parameterShape)
                  outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtBinderFreeRegimes
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (regime : ReflectiveSubstitutionRegime)
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound rootCallerAvailable rootActualAvailable : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
        callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
        actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList arguments = true)
      (sealed : List TypeExpr)
      (boundShape : bound =
        ReflectiveSubstitutionRegime.available regime rootActualAvailable ++ sealed)
      {RootExposed RootSealed : String → Type}
      (embedExposed : (occurrence : CostStaticFVarListOccurrence arguments) →
        RootExposed occurrence.occurrence.name)
      (embedSealed : (occurrence : CostStaticFVarListOccurrence arguments) →
        RootSealed occurrence.occurrence.name)
      (valueSafeExposed : ∀ {name type}
        (lookup : source name = some type), RootExposed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          rootCallerAvailable callerBinderImage)
      (valueSafeSealed : ∀ {name type}
        (lookup : source name = some type), RootSealed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          [] callerBinderImage) :
      ∃ outputTyped : ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment
            (ReflectiveSubstitutionRegime.available regime
              rootActualAvailable).length)) parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
          callerBinderImage := by
    cases callerSafe with
    | nil =>
        let outputTyped := ArgumentsHaveTypes.nil
          (language := language) (free := target) (bound := bound)
        exact ⟨outputTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable callerBinderImage argumentCallerSafe
        argumentsCallerSafe =>
        have actualSafe' :
            (ArgumentsHaveTypes.cons representation parameterType
              argumentTyped argumentsTyped).ReflectiveSupportSafeAt profile
                typingSupport (ReflectiveSubstitutionRegime.available regime
                  rootActualAvailable) actualBinderImage := actualSafe.castTyping
        have argumentActualSafeExact :
            argumentTyped.ReflectiveSupportSafeAt profile typingSupport
              (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
              actualBinderImage :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
            (representation := representation) (parameterType := parameterType)
            (argumentTyped := argumentTyped) (argumentsTyped := argumentsTyped)
            actualSafe'
        cases actualSafe' with
        | cons argumentActualSafe argumentsActualSafe =>
            have argumentActualSafe' := argumentActualSafeExact
            have argumentsActualSafe' :
                argumentsTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime
                    rootActualAvailable) actualBinderImage :=
              argumentsActualSafe.castTyping
            have freeParts : ReflectiveSubstitutionBinderFree argument = true ∧
                ReflectiveSubstitutionBinderFreeList arguments = true := by
              simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
            let embedHeadExposed : (occurrence : CostStaticFVarOccurrence argument) →
                RootExposed occurrence.name :=
              fun occurrence => embedExposed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTailExposed :
                (occurrence : CostStaticFVarListOccurrence arguments) →
                  RootExposed occurrence.occurrence.name :=
              fun occurrence => embedExposed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            let embedHeadSealed : (occurrence : CostStaticFVarOccurrence argument) →
                RootSealed occurrence.name :=
              fun occurrence => embedSealed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTailSealed :
                (occurrence : CostStaticFVarListOccurrence arguments) →
                  RootSealed occurrence.occurrence.name :=
              fun occurrence => embedSealed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            obtain ⟨outputArgument, outputArgumentSafe⟩ :=
              argumentCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  argumentActualSafe' freeParts.1 sealed boundShape
                  embedHeadExposed embedHeadSealed
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' freeParts.2 sealed boundShape
                  embedTailExposed embedTailSealed
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputRepresentation := representation.substituteReflectiveAt
              profile parameter argument typingSupport assignment.assignment
                (ReflectiveSubstitutionRegime.available regime
                  rootActualAvailable).length
            let outputTyped := ArgumentsHaveTypes.cons outputRepresentation
              parameterType outputArgument outputArguments
            exact ⟨outputTyped, .cons
              (representation := outputRepresentation)
              (parameterType := parameterType) outputArgumentSafe
              outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtBinderFreeRegimes
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (regime : ReflectiveSubstitutionRegime)
      (assignment : SupportedAssignment language source target typingSupport)
      (labelDeterministic : LabelDeterministic language)
      (collectionDeterministic : CollectionChoiceDeterministic language)
      {bound rootCallerAvailable rootActualAvailable : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {callerBinderImage actualBinderImage : TypeExpr → TypeExpr}
      (callerSafe : typed.ReflectiveSupportSafeAt profile inputSupport
        (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
        callerBinderImage)
      (actualSafe : typed.ReflectiveSupportSafeAt profile typingSupport
        (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
        actualBinderImage)
      (frameFree : ReflectiveSubstitutionBinderFreeList elements = true)
      (sealed : List TypeExpr)
      (boundShape : bound =
        ReflectiveSubstitutionRegime.available regime rootActualAvailable ++ sealed)
      {RootExposed RootSealed : String → Type}
      (embedExposed : (occurrence : CostStaticFVarListOccurrence elements) →
        RootExposed occurrence.occurrence.name)
      (embedSealed : (occurrence : CostStaticFVarListOccurrence elements) →
        RootSealed occurrence.occurrence.name)
      (valueSafeExposed : ∀ {name type}
        (lookup : source name = some type), RootExposed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          rootCallerAvailable callerBinderImage)
      (valueSafeSealed : ∀ {name type}
        (lookup : source name = some type), RootSealed name →
        (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
          [] callerBinderImage) :
      ∃ outputTyped : ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment
            (ReflectiveSubstitutionRegime.available regime
              rootActualAvailable).length)) elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport
          (ReflectiveSubstitutionRegime.available regime rootCallerAvailable)
          callerBinderImage := by
    cases callerSafe with
    | nil =>
        let outputTyped := ElementsHaveType.nil
          (language := language) (free := target) bound elementType
        exact ⟨outputTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable callerBinderImage elementCallerSafe elementsCallerSafe =>
        have actualSafe' :
            (ElementsHaveType.cons elementTyped elementsTyped).ReflectiveSupportSafeAt
              profile typingSupport (ReflectiveSubstitutionRegime.available regime
                rootActualAvailable) actualBinderImage := actualSafe.castTyping
        cases actualSafe' with
        | cons elementActualSafe elementsActualSafe =>
            have elementActualSafe' :
                elementTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
                  actualBinderImage := elementActualSafe.castTyping
            have elementsActualSafe' :
                elementsTyped.ReflectiveSupportSafeAt profile typingSupport
                  (ReflectiveSubstitutionRegime.available regime rootActualAvailable)
                  actualBinderImage := elementsActualSafe.castTyping
            have freeParts : ReflectiveSubstitutionBinderFree element = true ∧
                ReflectiveSubstitutionBinderFreeList elements = true := by
              simpa [ReflectiveSubstitutionBinderFreeList] using frameFree
            let embedHeadExposed : (occurrence : CostStaticFVarOccurrence element) →
                RootExposed occurrence.name :=
              fun occurrence => embedExposed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTailExposed :
                (occurrence : CostStaticFVarListOccurrence elements) →
                  RootExposed occurrence.occurrence.name :=
              fun occurrence => embedExposed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            let embedHeadSealed : (occurrence : CostStaticFVarOccurrence element) →
                RootSealed occurrence.name :=
              fun occurrence => embedSealed
                { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTailSealed :
                (occurrence : CostStaticFVarListOccurrence elements) →
                  RootSealed occurrence.occurrence.name :=
              fun occurrence => embedSealed
                { position := ⟨occurrence.position.val + 1, by
                    have positionBound := occurrence.position.isLt
                    simp only [List.length_cons]
                    omega⟩
                  occurrence := occurrence.occurrence }
            obtain ⟨outputElement, outputElementSafe⟩ :=
              elementCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  elementActualSafe' freeParts.1 sealed boundShape
                  embedHeadExposed embedHeadSealed
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            obtain ⟨outputElements, outputElementsSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtBinderFreeRegimes
                regime assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' freeParts.2 sealed boundShape
                  embedTailExposed embedTailSealed
                  (fun {name type} {lookup} root =>
                    valueSafeExposed (name := name) (type := type)
                      (lookup := lookup) root)
                  (fun {name type} {lookup} root =>
                    valueSafeSealed (name := name) (type := type)
                      (lookup := lookup) root)
            let outputTyped := ElementsHaveType.cons outputElement outputElements
            exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

end WellSorted

end Mettapedia.GSLT.LanguageDef
