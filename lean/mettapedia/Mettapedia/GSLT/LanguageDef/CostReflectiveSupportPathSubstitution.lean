import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportTwoAvailabilitySubstitution

/-!
# Path-indexed reflective substitution

For a binder-free term, a free-variable occurrence's support availability is
determined by its exact path through quote constructors.  This module records
that path in the substitution callback, avoiding a global root-footprint
condition and avoiding a total exposed/sealed callback that could be applied
to an occurrence in the wrong regime.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace WellSorted

/-- Reflective availability at an exact selected occurrence.  Only quote
constructors reset the ambient availability. -/
def reflectiveOccurrenceAvailable
    (profile : ReflectionProfile) (ambient : List TypeExpr) :
    OneHoleContext → List TypeExpr
  | .hole => ambient
  | .apply constructor _ inner _ =>
      reflectiveOccurrenceAvailable profile
        (if ReflectiveContextSupport.isQuoteConstructor profile constructor
          then [] else ambient) inner
  | .lambda _ inner => reflectiveOccurrenceAvailable profile ambient inner
  | .multiLambda _ _ inner =>
      reflectiveOccurrenceAvailable profile ambient inner
  | .substBody inner _ =>
      reflectiveOccurrenceAvailable profile ambient inner
  | .substReplacement _ inner =>
      reflectiveOccurrenceAvailable profile ambient inner
  | .collection _ _ inner _ _ =>
      reflectiveOccurrenceAvailable profile ambient inner

@[simp]
theorem reflectiveOccurrenceAvailable_hole
    (profile : ReflectionProfile) (ambient : List TypeExpr) :
    reflectiveOccurrenceAvailable profile ambient .hole = ambient :=
  rfl

theorem reflectiveOccurrenceAvailable_inApply
    (profile : ReflectionProfile) (ambient : List TypeExpr)
    (constructor : String) {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    reflectiveOccurrenceAvailable profile ambient
        (occurrence.inApply constructor).context =
      reflectiveOccurrenceAvailable profile
        (if ReflectiveContextSupport.isQuoteConstructor profile constructor
          then [] else ambient) occurrence.occurrence.context := by
  cases occurrence
  rfl

theorem reflectiveOccurrenceAvailable_inCollection
    (profile : ReflectionProfile) (ambient : List TypeExpr)
    (collectionType : CollType) (rest : Option String)
    {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    reflectiveOccurrenceAvailable profile ambient
        (occurrence.inCollection collectionType rest).context =
      reflectiveOccurrenceAvailable profile ambient
        occurrence.occurrence.context := by
  cases occurrence
  rfl

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Binder-free reflective substitution whose assignment callback is indexed
  by an exact root occurrence.  The token fixes both the restored name and
  the quote-local availability at which its value is required to be safe. -/
  theorem HasType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtPaths
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
      {Root : String → Type}
      (rootAvailable : {name : String} → Root name → List TypeExpr)
      (embed : (occurrence : CostStaticFVarOccurrence pattern) →
        Root occurrence.name)
      (embedAvailable : ∀ occurrence,
        rootAvailable (embed occurrence) =
          reflectiveOccurrenceAvailable profile callerAvailable
            occurrence.context)
      (valueSafe : ∀ {name type} (lookup : source name = some type)
        (root : Root name),
        (assignment.typed lookup).ReflectiveSupportSafeAt profile
          outputSupport (rootAvailable root) callerBinderImage) :
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
            have assignedSafeRoot := valueSafe lookup (embed point)
            have assignedSafe :
                (assignment.typed lookup).ReflectiveSupportSafeAt profile
                  outputSupport callerAvailable callerBinderImage := by
              rw [embedAvailable point] at assignedSafeRoot
              simpa [point, reflectiveOccurrenceAvailable] using assignedSafeRoot
            obtain ⟨active, actualShape⟩ := actualShape
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
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree bound (by simp)
                  rootAvailable
                  (fun occurrence => embed (occurrence.inApply rule.label))
                  (fun occurrence => by
                    simpa [reflectiveOccurrenceAvailable_inApply, quoted]
                      using embedAvailable (occurrence.inApply rule.label))
                  valueSafe
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
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' argumentsFree sealed boundShape
                  rootAvailable
                  (fun occurrence => embed (occurrence.inApply rule.label))
                  (fun occurrence => by
                    simpa [reflectiveOccurrenceAvailable_inApply, ordinary]
                      using embedAvailable (occurrence.inApply rule.label))
                  valueSafe
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
              elementsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  rootAvailable
                  (fun occurrence =>
                    embed (occurrence.inCollection collectionType rest))
                  (fun occurrence => by
                    change rootAvailable
                        (embed (occurrence.inCollection collectionType rest)) =
                      reflectiveOccurrenceAvailable profile callerAvailable
                        occurrence.occurrence.context
                    exact embedAvailable
                      (occurrence.inCollection collectionType rest))
                  valueSafe
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
              elementsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' elementsFree sealed boundShape
                  rootAvailable
                  (fun occurrence =>
                    embed (occurrence.inCollection collectionType rest))
                  (fun occurrence => by
                    change rootAvailable
                        (embed (occurrence.inCollection collectionType rest)) =
                      reflectiveOccurrenceAvailable profile callerAvailable
                        occurrence.occurrence.context
                    exact embedAvailable
                      (occurrence.inCollection collectionType rest))
                  valueSafe
            let outputTyped := HasType.collectionConstructor (rest := rest)
              membership parameterShape outputElements
            simpa only [ReflectiveContextSupport.substituteAt] using
              (⟨outputTyped,
                HasType.ReflectiveSupportSafeAt.collectionConstructor
                  (membership := membership) (parameterShape := parameterShape)
                  outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtPaths
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
      {Root : String → Type}
      (rootAvailable : {name : String} → Root name → List TypeExpr)
      (embed : (occurrence : CostStaticFVarListOccurrence arguments) →
        Root occurrence.occurrence.name)
      (embedAvailable : ∀ occurrence,
        rootAvailable (embed occurrence) =
          reflectiveOccurrenceAvailable profile callerAvailable
            occurrence.occurrence.context)
      (valueSafe : ∀ {name type} (lookup : source name = some type)
        (root : Root name),
        (assignment.typed lookup).ReflectiveSupportSafeAt profile
          outputSupport (rootAvailable root) callerBinderImage) :
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
            (representation := representation) (parameterType := parameterType)
            (argumentTyped := argumentTyped) (argumentsTyped := argumentsTyped)
            actualSafe'
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
            let embedHead : (occurrence : CostStaticFVarOccurrence argument) →
                Root occurrence.name := fun occurrence => embed
              { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTail :
                (occurrence : CostStaticFVarListOccurrence arguments) →
                  Root occurrence.occurrence.name := fun occurrence => embed
              { position := ⟨occurrence.position.val + 1, by
                  have positionBound := occurrence.position.isLt
                  simp only [List.length_cons]
                  omega⟩
                occurrence := occurrence.occurrence }
            obtain ⟨outputArgument, outputArgumentSafe⟩ :=
              argumentCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  argumentActualSafe' freeParts.1 sealed boundShape
                  rootAvailable embedHead
                  (fun occurrence => by
                    exact embedAvailable
                      { position := ⟨0, by simp⟩, occurrence := occurrence })
                  valueSafe
            obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
              argumentsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  argumentsActualSafe' freeParts.2 sealed boundShape
                  rootAvailable embedTail
                  (fun occurrence => by
                    exact embedAvailable
                      { position := ⟨occurrence.position.val + 1, by
                          have positionBound := occurrence.position.isLt
                          simp only [List.length_cons]
                          omega⟩
                        occurrence := occurrence.occurrence })
                  valueSafe
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

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtPaths
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
      {Root : String → Type}
      (rootAvailable : {name : String} → Root name → List TypeExpr)
      (embed : (occurrence : CostStaticFVarListOccurrence elements) →
        Root occurrence.occurrence.name)
      (embedAvailable : ∀ occurrence,
        rootAvailable (embed occurrence) =
          reflectiveOccurrenceAvailable profile callerAvailable
            occurrence.occurrence.context)
      (valueSafe : ∀ {name type} (lookup : source name = some type)
        (root : Root name),
        (assignment.typed lookup).ReflectiveSupportSafeAt profile
          outputSupport (rootAvailable root) callerBinderImage) :
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
            let embedHead : (occurrence : CostStaticFVarOccurrence element) →
                Root occurrence.name := fun occurrence => embed
              { position := ⟨0, by simp⟩, occurrence := occurrence }
            let embedTail :
                (occurrence : CostStaticFVarListOccurrence elements) →
                  Root occurrence.occurrence.name := fun occurrence => embed
              { position := ⟨occurrence.position.val + 1, by
                  have positionBound := occurrence.position.isLt
                  simp only [List.length_cons]
                  omega⟩
                occurrence := occurrence.occurrence }
            obtain ⟨outputElement, outputElementSafe⟩ :=
              elementCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  elementActualSafe' freeParts.1 sealed boundShape
                  rootAvailable embedHead
                  (fun occurrence => by
                    exact embedAvailable
                      { position := ⟨0, by simp⟩, occurrence := occurrence })
                  valueSafe
            obtain ⟨outputElements, outputElementsSafe⟩ :=
              elementsCallerSafe.substitutePreservingReflectiveSupportAtPaths
                  assignment labelDeterministic collectionDeterministic
                  elementsActualSafe' freeParts.2 sealed boundShape
                  rootAvailable embedTail
                  (fun occurrence => by
                    exact embedAvailable
                      { position := ⟨occurrence.position.val + 1, by
                          have positionBound := occurrence.position.isLt
                          simp only [List.length_cons]
                          omega⟩
                        occurrence := occurrence.occurrence })
                  valueSafe
            let outputTyped := ElementsHaveType.cons outputElement outputElements
            exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

end WellSorted

end Mettapedia.GSLT.LanguageDef
