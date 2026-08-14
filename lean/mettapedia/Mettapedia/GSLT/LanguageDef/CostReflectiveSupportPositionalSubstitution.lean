import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportOccurrenceSubstitutionComposition
import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceRecursive

/-!
# Positional reflective-support substitution

Reflective support and substitution depth measure different things.  Support
is relative to the caller's visible binder context, while substitution depth
is determined by the executor's path through quotes and binders.  This module
keeps those indices independent and asks for the exact replacement theorem at
each proof-relevant free-variable occurrence.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Reflection

namespace WellSorted

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Substitute at an executor-supplied depth while preserving support at an
  independent caller availability.  The leaf callback receives both the exact
  source occurrence and the actual local substitution depth. -/
  theorem HasType.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarOccurrence pattern → Nat → Root)
      (valueSafe : ∀ {bound name type} {available : List TypeExpr},
        source name = some type → Root → (depth : Nat) →
          ∃ outputTyped : HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : HasType language target bound
          (ReflectiveContextSupport.substituteAt profile typingSupport
            assignment.assignment actualDepth pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | @bvar bound index type lookup currentAvailable binderImage =>
        let outputTyped : HasType language target bound (.bvar index) type :=
          .bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := binderImage) lookup available⟩)
    | @fvar bound name type lookup currentAvailable binderImage shape =>
        let point : CostStaticFVarOccurrence (.fvar name) :=
          ⟨name, .hole, .here⟩
        exact valueSafe lookup (embed point actualDepth) actualDepth
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment 0
              (fun occurrence depth =>
                embed (occurrence.inApply rule.label) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := membership) (notBare := notBare) quoted
              outputSafe⟩)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth =>
                embed (occurrence.inApply rule.label) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.constructor membership notBare
          outputArguments
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := membership) (notBare := notBare) ordinary
              outputSafe⟩)
    | @lambda bound binder body domain codomain bodyTyped currentAvailable
        binderImage bodySafe =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + 1)
              (fun occurrence depth => embed
                (occurrence.inContext (.lambda binder .hole)) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.lambda (binder := binder) outputBody
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.lambda outputSafe⟩)
    | @multiLambda bound arity binders body domain codomain bodyTyped
        currentAvailable binderImage bodySafe =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + arity)
              (fun occurrence depth => embed
                (occurrence.inContext
                  (.multiLambda arity binders .hole)) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let rawOutputTyped := HasType.multiLambda (binders := binders)
          outputBody
        let outputTyped : HasType language target bound
            (ReflectiveContextSupport.substituteAt profile typingSupport
              assignment.assignment actualDepth
                (.multiLambda arity binders body))
            (.arrow (.multiBinder domain) codomain) := by
          simpa only [ReflectiveContextSupport.substituteAt, Nat.add_comm]
            using rawOutputTyped
        have rawOutputSafe := HasType.ReflectiveSupportSafeAt.multiLambda
          (binders := binders) outputSafe
        have outputSafe' : outputTyped.ReflectiveSupportSafeAt profile
            outputSupport available binderImage := by
          apply HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [ReflectiveContextSupport.substituteAt, Nat.add_comm]
            using rawOutputSafe
          exact outputTyped
        exact ⟨outputTyped, outputSafe'⟩
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable binderImage bodySafe replacementSafe =>
        obtain ⟨outputBody, outputBodySafe⟩ :=
          bodySafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment (actualDepth + 1)
              (fun occurrence depth => embed
                (occurrence.inContext
                  (.substBody .hole replacement)) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        obtain ⟨outputReplacement, outputReplacementSafe⟩ :=
          replacementSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed
                (occurrence.inContext
                  (.substReplacement body .hole)) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.subst outputBody outputReplacement
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.subst
            outputBodySafe outputReplacementSafe⟩)
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed
                (occurrence.inCollection collectionType rest) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.collection
          (collectionType := collectionType) (rest := rest) outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.collection
            outputSafe⟩)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth
              (fun occurrence depth => embed
                (occurrence.inCollection collectionType rest) depth)
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := HasType.collectionConstructor (rest := rest)
          membership parameterShape outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
              outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      {bound available : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence arguments → Nat → Root)
      (valueSafe : ∀ {bound name type} {available : List TypeExpr},
        source name = some type → Root → (depth : Nat) →
          ∃ outputTyped : HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualDepth)) parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | nil =>
        let outputTyped := ArgumentsHaveTypes.nil
          (language := language) (free := target) (bound := bound)
        exact ⟨outputTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe =>
        let embedHead : CostStaticFVarOccurrence argument → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨0, by simp⟩, occurrence := occurrence } depth
        let embedTail : CostStaticFVarListOccurrence arguments → Nat →
            Root :=
          fun occurrence depth => embed
            { position := ⟨occurrence.position.val + 1, by
                have positionBound := occurrence.position.isLt
                simp only [List.length_cons]
                omega⟩
              occurrence := occurrence.occurrence } depth
        obtain ⟨outputArgument, outputArgumentSafe⟩ :=
          argumentSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedHead
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
          argumentsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedTail
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputRepresentation := representation.substituteReflectiveAt
          profile parameter argument typingSupport assignment.assignment
            actualDepth
        let outputTyped := ArgumentsHaveTypes.cons outputRepresentation
          parameterType outputArgument outputArguments
        exact ⟨outputTyped, .cons (representation := outputRepresentation)
          (parameterType := parameterType) outputArgumentSafe
          outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substituteAtPreservingReflectiveSupportFromOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      (assignment : SupportedAssignment language source target typingSupport)
      {bound available : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {binderImage : TypeExpr → TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (actualDepth : Nat)
      {Root : Type}
      (embed : CostStaticFVarListOccurrence elements → Nat → Root)
      (valueSafe : ∀ {bound name type} {available : List TypeExpr},
        source name = some type → Root → (depth : Nat) →
          ∃ outputTyped : HasType language target bound
              (ReflectiveContextSupport.substituteAt profile typingSupport
                assignment.assignment depth (.fvar name)) type,
            outputTyped.ReflectiveSupportSafeAt profile outputSupport
              available binderImage) :
      ∃ outputTyped : ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            typingSupport assignment.assignment actualDepth)) elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases safe with
    | nil =>
        let outputTyped := ElementsHaveType.nil
          (language := language) (free := target) bound elementType
        exact ⟨outputTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe =>
        let embedHead : CostStaticFVarOccurrence element → Nat → Root :=
          fun occurrence depth => embed
            { position := ⟨0, by simp⟩, occurrence := occurrence } depth
        let embedTail : CostStaticFVarListOccurrence elements → Nat →
            Root :=
          fun occurrence depth => embed
            { position := ⟨occurrence.position.val + 1, by
                have positionBound := occurrence.position.isLt
                simp only [List.length_cons]
                omega⟩
              occurrence := occurrence.occurrence } depth
        obtain ⟨outputElement, outputElementSafe⟩ :=
          elementSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedHead
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        obtain ⟨outputElements, outputElementsSafe⟩ :=
          elementsSafe.substituteAtPreservingReflectiveSupportFromOccurrences
            assignment actualDepth embedTail
              (fun {bound name type available} lookup root depth =>
                valueSafe (bound := bound) (name := name) (type := type)
                  (available := available) lookup root depth)
        let outputTyped := ElementsHaveType.cons outputElement outputElements
        exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

end WellSorted

end Mettapedia.GSLT.LanguageDef
