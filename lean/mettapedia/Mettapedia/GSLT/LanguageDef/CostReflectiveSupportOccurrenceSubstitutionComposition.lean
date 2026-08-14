import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportSubstitutionComposition

/-!
# Occurrence-local reflective support under substitution

The class-level reflective substitution interface asks one assignment value to
support every ambient prefix through a root-footprint suffix law.  That law is
sufficient, but not necessary: a free variable inside an assigned lambda may
be protected by the lambda's own binder even when its support is not a suffix
of the assignment value's root availability.

This module records the exact weaker condition.  Each proof-relevant source
occurrence carries safety of its assigned value at that occurrence's actual
reflective availability.  Repeated occurrences of one source name may
therefore carry different safety derivations without changing the assignment
or its typing authority.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Reflection

namespace WellSorted

mutual
  /-- Assigned values are support-safe at each exact term occurrence selected
  by a substitution-alignment derivation.  The free-variable constructor is
  the only non-structural field: it retains safety at the current `available`,
  rather than asking for a class-wide root-footprint law. -/
  inductive ReflectiveSupportOccurrenceValuesSafeAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (outputSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {pattern : Pattern} → {type : TypeExpr} →
      {typed : HasType language source bound pattern type} →
      {available : List TypeExpr} →
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage} →
      (aligned : ReflectiveSupportSubstitutionAlignedAt typingSupport safe) →
      Prop where
    | bvar {bound index type} {lookup : bound[index]? = some type}
        {available} :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.bvar
            (typingSupport := typingSupport)
            (binderImage := binderImage) (available := available)
            (lookup := lookup))
    | fvar {bound name type} {lookup : source name = some type}
        {available}
        {shape : ∃ inner, available = inner ++ inputSupport name}
        {contextShape : ∃ active sealed,
          bound = (active ++ typingSupport name) ++ sealed ∧
            active.length = available.length - (inputSupport name).length}
        (valueSafe : (assignment.typed lookup).ReflectiveSupportSafeAt
          profile outputSupport available binderImage) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.fvar
            (typingSupport := typingSupport) (lookup := lookup)
            (binderImage := binderImage) (shape := shape) contextShape)
    | constructorQuote {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language source bound
          arguments rule.params}
        {available}
        {quoted : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = true}
        {argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile inputSupport argumentsTyped [] binderImage}
        {argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe}
        (argumentsValues : ReflectiveArgumentsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport argumentsAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.constructorQuote
            (membership := membership) (notBare := notBare)
            (available := available) (quoted := quoted) argumentsAligned)
    | constructorOrdinary {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language source bound
          arguments rule.params}
        {available}
        {ordinary : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = false}
        {argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile inputSupport argumentsTyped available binderImage}
        {argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe}
        (argumentsValues : ReflectiveArgumentsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport argumentsAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.constructorOrdinary
            (membership := membership) (notBare := notBare)
            (ordinary := ordinary) argumentsAligned)
    | lambda {bound binder body domain codomain}
        {bodyTyped : HasType language source (domain :: bound) body codomain}
        {available}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (binderImage domain :: available) binderImage}
        {bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe}
        (bodyValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport bodyAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.lambda
            (binder := binder) bodyAligned)
    | multiLambda {bound arity binders body domain codomain}
        {bodyTyped : HasType language source
          (List.replicate arity domain ++ bound) body codomain}
        {available}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (List.replicate arity (binderImage domain) ++ available) binderImage}
        {bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe}
        (bodyValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport bodyAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.multiLambda
            (binders := binders) bodyAligned)
    | subst {bound body replacement domain codomain}
        {bodyTyped : HasType language source (domain :: bound) body codomain}
        {replacementTyped : HasType language source bound replacement domain}
        {available}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (binderImage domain :: available) binderImage}
        {replacementSafe : replacementTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe}
        {replacementAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport replacementSafe}
        (bodyValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport bodyAligned)
        (replacementValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport replacementAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.subst bodyAligned
            replacementAligned)
    | collection {bound collectionType elements rest elementType}
        {elementsTyped : ElementsHaveType language source bound elements
          elementType}
        {available}
        {elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile inputSupport elementsTyped available binderImage}
        {elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe}
        (elementsValues : ReflectiveElementsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport elementsAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.collection
            (collectionType := collectionType) (rest := rest) elementsAligned)
    | collectionConstructor
        {bound rule parameterName collectionType elements rest elementType}
        {membership : rule ∈ language.terms}
        {parameterShape : rule.params =
          [.simple parameterName (.collection collectionType elementType)]}
        {elementsTyped : ElementsHaveType language source bound elements
          elementType}
        {available}
        {elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile inputSupport elementsTyped available binderImage}
        {elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe}
        (elementsValues : ReflectiveElementsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport elementsAligned) :
        ReflectiveSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveSupportSubstitutionAlignedAt.collectionConstructor
            (membership := membership) (parameterShape := parameterShape)
            (rest := rest) elementsAligned)

  /-- Argument-spine companion to occurrence-local assignment safety. -/
  inductive ReflectiveArgumentsSupportOccurrenceValuesSafeAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (outputSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {arguments : List Pattern} →
      {parameters : List TermParam} →
      {typed : ArgumentsHaveTypes language source bound arguments parameters} →
      {available : List TypeExpr} →
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage} →
      (aligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
        typingSupport safe) →
        Prop where
    | nil (bound available : List TypeExpr) :
        ReflectiveArgumentsSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment
          outputSupport
          (ReflectiveArgumentsSupportSubstitutionAlignedAt.nil
            (typingSupport := typingSupport)
            (binderImage := binderImage) bound available)
    | cons {bound argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language source bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language source bound arguments
          parameters}
        {available}
        {argumentSafe : argumentTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {argumentAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport argumentSafe}
        {argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe}
        (argumentValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport argumentAligned)
        (argumentsValues : ReflectiveArgumentsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport argumentsAligned) :
        ReflectiveArgumentsSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment
          outputSupport
          (ReflectiveArgumentsSupportSubstitutionAlignedAt.cons
            (representation := representation) (parameterType := parameterType)
            argumentAligned argumentsAligned)

  /-- Collection-spine companion to occurrence-local assignment safety. -/
  inductive ReflectiveElementsSupportOccurrenceValuesSafeAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport : ContextSupport.Support}
      {profile : ReflectionProfile}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (outputSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {elements : List Pattern} →
      {elementType : TypeExpr} →
      {typed : ElementsHaveType language source bound elements elementType} →
      {available : List TypeExpr} →
      {safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage} →
      (aligned : ReflectiveElementsSupportSubstitutionAlignedAt
        typingSupport safe) →
        Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr)
        (available : List TypeExpr) :
        ReflectiveElementsSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveElementsSupportSubstitutionAlignedAt.nil
            (typingSupport := typingSupport)
            (binderImage := binderImage) bound elementType available)
    | cons {bound element elements elementType}
        {elementTyped : HasType language source bound element elementType}
        {elementsTyped : ElementsHaveType language source bound elements
          elementType}
        {available}
        {elementSafe : elementTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {elementsSafe : elementsTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {elementAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport elementSafe}
        {elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe}
        (elementValues : ReflectiveSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport elementAligned)
        (elementsValues : ReflectiveElementsSupportOccurrenceValuesSafeAt
          (profile := profile) (binderImage := binderImage)
          assignment outputSupport elementsAligned) :
        ReflectiveElementsSupportOccurrenceValuesSafeAt (profile := profile)
          (binderImage := binderImage) assignment outputSupport
          (ReflectiveElementsSupportSubstitutionAlignedAt.cons elementAligned
            elementsAligned)
end

/-- A free-variable occurrence exposes assignment safety at the carrier's
exact reflection profile.  In particular, evidence indexed by one profile
cannot launder a value-safety certificate produced for another profile. -/
theorem ReflectiveSupportOccurrenceValuesSafeAt.fvar_valueSafe_at_carrierProfile
    {language : LanguageDef} {source target : FreeTypeContext}
    {typingSupport inputSupport outputSupport : ContextSupport.Support}
    {profile : ReflectionProfile}
    (assignment : SupportedAssignment language source target typingSupport)
    {bound : List TypeExpr} {name : String} {type : TypeExpr}
    {lookup : source name = some type} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    {shape : ∃ inner, available = inner ++ inputSupport name}
    {contextShape : ∃ active sealed,
      bound = (active ++ typingSupport name) ++ sealed ∧
        active.length = available.length - (inputSupport name).length}
    (values : ReflectiveSupportOccurrenceValuesSafeAt
      (profile := profile) (binderImage := binderImage)
        assignment outputSupport
        (ReflectiveSupportSubstitutionAlignedAt.fvar
          (typingSupport := typingSupport) (lookup := lookup)
          (binderImage := binderImage) (shape := shape) contextShape)) :
    (assignment.typed lookup).ReflectiveSupportSafeAt profile outputSupport
      available binderImage := by
  cases values with
  | fvar valueSafe => exact valueSafe

mutual
  /-- Occurrence-local assignment safety is sufficient for reflective
  substitution.  Unlike the class-level theorem, this result never inserts an
  unverified ambient coeffect prefix into an assignment value. -/
  theorem HasType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveSupportSubstitutionAlignedAt typingSupport safe)
      (occurrenceValues : ReflectiveSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage)
        assignment outputSupport aligned) :
      ∃ outputTyped : HasType language target bound
          (ReflectiveContextSupport.substituteAt profile inputSupport
            assignment.assignment available.length pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases occurrenceValues with
    | @bvar bound index type lookup currentAvailable =>
        let outputTyped : HasType language target bound (.bvar index) type :=
          HasType.bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := binderImage) lookup available⟩)
    | @fvar bound name type lookup currentAvailable shape contextShape
        valueSafe =>
        obtain ⟨active, sealed, boundShape, activeLength⟩ := contextShape
        subst bound
        obtain ⟨liftedTyped, liftedSafe⟩ := valueSafe.liftBVars_insert
          [] (typingSupport name) active rfl
        let liftedTyped' : HasType language target
            (active ++ typingSupport name)
            (liftBVars 0 active.length (assignment.assignment name)) type := by
          simpa only [List.nil_append, List.length_nil] using liftedTyped
        have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt
            profile outputSupport available binderImage := by
          apply HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [List.nil_append, List.length_nil] using liftedSafe
        obtain ⟨extendedTyped, extendedSafe⟩ := liftedSafe'.extendOuter sealed
        have activePair :
            ∃ reflectedTyped : HasType language target
                ((active ++ typingSupport name) ++ sealed)
                (liftBVars 0 active.length (assignment.assignment name)) type,
              reflectedTyped.ReflectiveSupportSafeAt profile outputSupport
                available binderImage :=
          ⟨extendedTyped, extendedSafe⟩
        have liftEquality :
            liftBVars 0 active.length (assignment.assignment name) =
              liftBVars 0 (available.length - (inputSupport name).length)
                (assignment.assignment name) :=
          congrArg (fun shift => liftBVars 0 shift (assignment.assignment name))
            activeLength
        rw [liftEquality] at activePair
        simpa only [ReflectiveContextSupport.substituteAt] using activePair
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable quoted argumentsSafe argumentsAligned
        argumentsValues =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment argumentsAligned argumentsValues
        let outputTyped := HasType.constructor membership notBare outputArguments
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := membership) (notBare := notBare) quoted
              outputSafe⟩)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable ordinary argumentsSafe
        argumentsAligned argumentsValues =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment argumentsAligned argumentsValues
        let outputTyped := HasType.constructor membership notBare outputArguments
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := membership) (notBare := notBare) ordinary
              outputSafe⟩)
    | @lambda bound binder body domain codomain bodyTyped currentAvailable
        bodySafe bodyAligned bodyValues =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupportAtOccurrences assignment
            bodyAligned bodyValues
        let outputTyped := HasType.lambda (binder := binder) outputBody
        simpa [ReflectiveContextSupport.substituteAt, List.length_cons] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.lambda outputSafe⟩)
    | @multiLambda bound arity binders body domain codomain bodyTyped
        currentAvailable bodySafe bodyAligned bodyValues =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupportAtOccurrences assignment
            bodyAligned bodyValues
        let rawOutputTyped := HasType.multiLambda (binders := binders) outputBody
        let outputTyped : HasType language target bound
            (ReflectiveContextSupport.substituteAt profile inputSupport
              assignment.assignment available.length
              (.multiLambda arity binders body))
            (.arrow (.multiBinder domain) codomain) := by
          simpa only [ReflectiveContextSupport.substituteAt,
            List.length_append, List.length_replicate, Nat.add_comm] using
              rawOutputTyped
        have rawOutputSafe := HasType.ReflectiveSupportSafeAt.multiLambda
          (binders := binders) outputSafe
        have outputSafe' : outputTyped.ReflectiveSupportSafeAt
            profile outputSupport available binderImage := by
          apply HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [ReflectiveContextSupport.substituteAt,
            List.length_append, List.length_replicate, Nat.add_comm] using
              rawOutputSafe
          exact outputTyped
        exact ⟨outputTyped, outputSafe'⟩
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        currentAvailable bodySafe replacementSafe bodyAligned
        replacementAligned bodyValues replacementValues =>
        obtain ⟨outputBody, outputBodySafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupportAtOccurrences assignment
            bodyAligned bodyValues
        obtain ⟨outputReplacement, outputReplacementSafe⟩ :=
          replacementSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment replacementAligned replacementValues
        let outputTyped := HasType.subst outputBody outputReplacement
        simpa [ReflectiveContextSupport.substituteAt, List.length_cons] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.subst outputBodySafe
            outputReplacementSafe⟩)
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable elementsSafe elementsAligned
        elementsValues =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment elementsAligned elementsValues
        let outputTyped := HasType.collection (collectionType := collectionType)
          (rest := rest) outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.collection outputSafe⟩)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable elementsSafe elementsAligned
        elementsValues =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment elementsAligned elementsValues
        let outputTyped := HasType.collectionConstructor (rest := rest)
          membership parameterShape outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
              outputSafe⟩)
  termination_by 3 * sizeOf pattern + 2

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
        typingSupport safe)
      (occurrenceValues : ReflectiveArgumentsSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage)
        assignment outputSupport aligned) :
      ∃ outputTyped : ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            inputSupport assignment.assignment available.length)) parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases occurrenceValues with
    | @nil bound currentAvailable =>
        let outputTyped := ArgumentsHaveTypes.nil
          (language := language) (free := target) (bound := bound)
        exact ⟨outputTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable argumentSafe argumentsSafe
        argumentAligned argumentsAligned argumentValues argumentsValues =>
        obtain ⟨outputArgument, outputArgumentSafe⟩ :=
          argumentSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment argumentAligned argumentValues
        obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment argumentsAligned argumentsValues
        let outputRepresentation := representation.substituteReflectiveAt
          profile parameter argument inputSupport assignment.assignment
            available.length
        let outputTyped := ArgumentsHaveTypes.cons outputRepresentation
          parameterType outputArgument outputArguments
        exact ⟨outputTyped, .cons (representation := outputRepresentation)
          (parameterType := parameterType) outputArgumentSafe
          outputArgumentsSafe⟩
  termination_by 3 * sizeOf arguments + 1

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupportAtOccurrences
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : SupportedAssignment language source target typingSupport)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveElementsSupportSubstitutionAlignedAt
        typingSupport safe)
      (occurrenceValues : ReflectiveElementsSupportOccurrenceValuesSafeAt
        (profile := profile) (binderImage := binderImage)
        assignment outputSupport aligned) :
      ∃ outputTyped : ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            inputSupport assignment.assignment available.length)) elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases occurrenceValues with
    | @nil bound elementType currentAvailable =>
        let outputTyped := ElementsHaveType.nil
          (language := language) (free := target) bound elementType
        exact ⟨outputTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable elementSafe elementsSafe elementAligned
        elementsAligned elementValues elementsValues =>
        obtain ⟨outputElement, outputElementSafe⟩ :=
          elementSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment elementAligned elementValues
        obtain ⟨outputElements, outputElementsSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupportAtOccurrences
            assignment elementsAligned elementsValues
        let outputTyped := ElementsHaveType.cons outputElement outputElements
        exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-! ## Sharp occurrence-local canaries -/

private def occurrenceCanarySourceFree (valueType : TypeExpr) :
    FreeTypeContext := fun name =>
  if name = "source" then some (.arrow valueType valueType) else none

private def occurrenceCanaryTargetFree (valueType : TypeExpr) :
    FreeTypeContext := fun name =>
  if name = "target" then some valueType else none

private def occurrenceCanaryTypingSupport : ContextSupport.Support := fun _ => []

private def occurrenceCanaryInputSupport : ContextSupport.Support := fun _ => []

private def occurrenceCanaryOutputSupport (valueType : TypeExpr) :
    ContextSupport.Support := fun name =>
  if name = "target" then [valueType] else []

private def occurrenceCanaryTooLargeOutputSupport
    (marker valueType : TypeExpr) : ContextSupport.Support := fun name =>
  if name = "target" then [marker, valueType] else []

private def occurrenceCanaryAssignmentPattern : ContextSupport.Assignment :=
  fun _ => .lambda none (.fvar "target")

private theorem occurrenceCanarySourceLookup (valueType : TypeExpr) :
    occurrenceCanarySourceFree valueType "source" =
      some (.arrow valueType valueType) := by
  simp [occurrenceCanarySourceFree]

private def occurrenceCanaryAssignment (language : LanguageDef)
    (valueType : TypeExpr) : SupportedAssignment language
      (occurrenceCanarySourceFree valueType)
      (occurrenceCanaryTargetFree valueType) occurrenceCanaryTypingSupport where
  assignment := occurrenceCanaryAssignmentPattern
  typed := by
    intro name type lookup
    by_cases selected : name = "source"
    · subst name
      simp [occurrenceCanarySourceFree] at lookup
      subst type
      change HasType language (occurrenceCanaryTargetFree valueType) []
        (.lambda none (.fvar "target")) (.arrow valueType valueType)
      exact .lambda (.fvar (by simp [occurrenceCanaryTargetFree]))
    · simp [occurrenceCanarySourceFree, selected] at lookup

private def occurrenceCanarySourceTyped (language : LanguageDef)
    (valueType : TypeExpr) :
    HasType language (occurrenceCanarySourceFree valueType) []
      (.fvar "source") (.arrow valueType valueType) :=
  .fvar (occurrenceCanarySourceLookup valueType)

private def occurrenceCanarySourceSafe (profile : ReflectionProfile)
    (language : LanguageDef) (valueType : TypeExpr) :
    (occurrenceCanarySourceTyped language valueType).ReflectiveSupportSafeAt
      profile occurrenceCanaryInputSupport [] id :=
  .fvar (by simp [occurrenceCanarySourceFree]) []
    ⟨[], by simp [occurrenceCanaryInputSupport]⟩

private def occurrenceCanaryAligned (profile : ReflectionProfile)
    (language : LanguageDef) (valueType : TypeExpr) :
    ReflectiveSupportSubstitutionAlignedAt occurrenceCanaryTypingSupport
      (occurrenceCanarySourceSafe profile language valueType) :=
  .fvar (lookup := occurrenceCanarySourceLookup valueType)
    (shape := ⟨[], by simp [occurrenceCanaryInputSupport]⟩)
    ⟨[], [], by simp [occurrenceCanaryTypingSupport,
      occurrenceCanaryInputSupport]⟩

private theorem occurrenceCanaryValueSafe (profile : ReflectionProfile)
    (language : LanguageDef) (valueType : TypeExpr) :
    ((occurrenceCanaryAssignment language valueType).typed
      (by simp [occurrenceCanarySourceFree] :
        occurrenceCanarySourceFree valueType "source" =
          some (.arrow valueType valueType))).ReflectiveSupportSafeAt
      profile (occurrenceCanaryOutputSupport valueType) [] id := by
  let bodyTyped : HasType language (occurrenceCanaryTargetFree valueType)
      [valueType] (.fvar "target") valueType :=
    .fvar (by simp [occurrenceCanaryTargetFree])
  let lambdaTyped : HasType language (occurrenceCanaryTargetFree valueType) []
      (.lambda none (.fvar "target")) (.arrow valueType valueType) :=
    .lambda bodyTyped
  have bodySafe : bodyTyped.ReflectiveSupportSafeAt profile
      (occurrenceCanaryOutputSupport valueType) [valueType] id :=
    .fvar (by simp [occurrenceCanaryTargetFree]) [valueType]
      ⟨[], by simp [occurrenceCanaryOutputSupport]⟩
  have lambdaSafe : lambdaTyped.ReflectiveSupportSafeAt profile
      (occurrenceCanaryOutputSupport valueType) [] id := .lambda bodySafe
  exact lambdaSafe.castTyping

/-- Positive canary: a lambda-valued assignment is safe at this exact source
occurrence even though the lambda's free target name has nonempty support and
that support is not a suffix of the assignment value's root availability. -/
theorem lambdaValue_substitution_succeeds_without_rootFootprint
    (profile : ReflectionProfile) (language : LanguageDef)
    (valueType : TypeExpr) :
    (∃ outputTyped : HasType language (occurrenceCanaryTargetFree valueType) []
        (ReflectiveContextSupport.substituteAt profile
          occurrenceCanaryInputSupport occurrenceCanaryAssignmentPattern 0
            (.fvar "source")) (.arrow valueType valueType),
      outputTyped.ReflectiveSupportSafeAt profile
        (occurrenceCanaryOutputSupport valueType) [] id) ∧
      ¬ ∃ inner,
        occurrenceCanaryInputSupport "source" =
          inner ++ occurrenceCanaryOutputSupport valueType "target" := by
  constructor
  · apply
      (occurrenceCanarySourceSafe profile language valueType
        ).substitutePreservingReflectiveSupportAtOccurrences
          (occurrenceCanaryAssignment language valueType)
          (occurrenceCanaryAligned profile language valueType)
    exact .fvar (lookup := occurrenceCanarySourceLookup valueType)
      (shape := ⟨[], by simp [occurrenceCanaryInputSupport]⟩)
      (contextShape := ⟨[], [], by simp [occurrenceCanaryTypingSupport,
        occurrenceCanaryInputSupport]⟩)
      (occurrenceCanaryValueSafe profile language valueType)
  · rintro ⟨inner, impossible⟩
    have lengths := congrArg List.length impossible
    simp [occurrenceCanaryInputSupport, occurrenceCanaryOutputSupport] at lengths

private theorem lambdaValue_not_safe_when_localSupport_tooLarge
    (profile : ReflectionProfile) (language : LanguageDef)
    (marker valueType : TypeExpr) :
    ¬ ((occurrenceCanaryAssignment language valueType).typed
      (occurrenceCanarySourceLookup valueType)).ReflectiveSupportSafeAt
        profile (occurrenceCanaryTooLargeOutputSupport marker valueType)
          [] id := by
  intro alleged
  let bodyTyped : HasType language (occurrenceCanaryTargetFree valueType)
      [valueType] (.fvar "target") valueType :=
    .fvar (by simp [occurrenceCanaryTargetFree])
  let lambdaTyped : HasType language (occurrenceCanaryTargetFree valueType) []
      (.lambda none (.fvar "target")) (.arrow valueType valueType) :=
    .lambda bodyTyped
  have explicitSafe : lambdaTyped.ReflectiveSupportSafeAt profile
      (occurrenceCanaryTooLargeOutputSupport marker valueType) [] id :=
    alleged.castTyping
  cases explicitSafe with
  | lambda bodySafe =>
      cases bodySafe with
      | fvar _ _ shape =>
          obtain ⟨inner, impossible⟩ := shape
          have lengths := congrArg List.length impossible
          simp [occurrenceCanaryTooLargeOutputSupport] at lengths

/-- Negative locality and profile-indexing canary: the same lambda value
cannot carry an output support longer than the one binder actually available
at its inner free-name occurrence.  The carrier projection exposes safety at
the carrier's own profile, so evidence from another profile cannot be used to
fill this gap. -/
theorem lambdaValue_not_occurrenceSafe_when_localSupport_tooLarge
    (profile : ReflectionProfile) (language : LanguageDef)
    (marker valueType : TypeExpr) :
    ¬ ReflectiveSupportOccurrenceValuesSafeAt
      (profile := profile) (binderImage := id)
      (occurrenceCanaryAssignment language valueType)
      (occurrenceCanaryTooLargeOutputSupport marker valueType)
      (occurrenceCanaryAligned profile language valueType) := by
  intro values
  apply lambdaValue_not_safe_when_localSupport_tooLarge profile language
    marker valueType
  exact
    ReflectiveSupportOccurrenceValuesSafeAt.fvar_valueSafe_at_carrierProfile
      (lookup := occurrenceCanarySourceLookup valueType)
      (shape := ⟨[], by simp [occurrenceCanaryInputSupport]⟩)
      (contextShape := ⟨[], [], by simp [occurrenceCanaryTypingSupport,
        occurrenceCanaryInputSupport]⟩)
      (occurrenceCanaryAssignment language valueType) values

end WellSorted

end Mettapedia.GSLT.LanguageDef
