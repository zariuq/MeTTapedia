import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Proof-relevant reflective support under substitution

This module separates the proof-only composition infrastructure from the
core context-support definitions.  It aligns lexical typing support with
reflective availability, preserves arbitrary binder interpretations, and
composes independently selected input and output coeffects.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

namespace WellSorted

/-- A typed supported assignment whose values carry a second, independent
reflective coeffect.  `typingSupport` controls typing, `inputSupport` controls
the reflective insertion depth at source occurrences, and `outputSupport` is
the coeffect retained after substitution.  The suffix field is deliberately
finite: it is required only for free names that the selected assignment value
actually contains. -/
structure ReflectiveSupportSafeAssignment (profile : ReflectionProfile)
    (language : LanguageDef) (source target : FreeTypeContext)
    (typingSupport inputSupport outputSupport : ContextSupport.Support)
    (binderImage : TypeExpr → TypeExpr := id)
    extends SupportedAssignment language source target typingSupport where
  valueSafe : ∀ {name type} (lookup : source name = some type),
    (toSupportedAssignment.typed lookup).ReflectiveSupportSafeAt
      profile outputSupport (inputSupport name) binderImage
  outputSupportSuffix : ∀ {name type}, source name = some type →
    ∀ targetName, targetName ∈ (assignment name).freeFvarNames →
      ∃ inner, inputSupport name = inner ++ outputSupport targetName

mutual
  /-- A reflective safety derivation is aligned with an independent typing
  support when every free-variable leaf admits the exact decomposition used
  by supported substitution.  `active` is the syntactic binder prefix through
  which the assigned value is lifted; `sealed` is retained only by typing
  (for example, outside a reflective quotation).  Only prefix lengths are
  identified, so the reflective binder interpretation remains arbitrary. -/
  inductive ReflectiveSupportSubstitutionAlignedAt
      {language : LanguageDef} {free : FreeTypeContext}
      {inputSupport : ContextSupport.Support}
      (typingSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {pattern : Pattern} → {type : TypeExpr} →
      {typed : HasType language free bound pattern type} →
      {available : List TypeExpr} →
      {binderImage : TypeExpr → TypeExpr} →
      typed.ReflectiveSupportSafeAt profile inputSupport available binderImage →
      Prop where
    | bvar {bound index type} {lookup : bound[index]? = some type}
        {available binderImage} :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.bvar
            (binderImage := binderImage) lookup available)
    | fvar {bound name type} {lookup : free name = some type}
        {available binderImage}
        {shape : ∃ inner, available = inner ++ inputSupport name}
        (contextShape : ∃ active sealed,
          bound = (active ++ typingSupport name) ++ sealed ∧
            active.length = available.length - (inputSupport name).length) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.fvar (bound := bound)
            (binderImage := binderImage) lookup available shape)
    | constructorQuote {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available binderImage}
        {quoted : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = true}
        {argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile inputSupport argumentsTyped [] binderImage}
        (argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.constructorQuote
            (membership := membership) (notBare := notBare)
            (available := available) quoted argumentsSafe)
    | constructorOrdinary {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available binderImage}
        {ordinary : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = false}
        {argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile inputSupport argumentsTyped available binderImage}
        (argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.constructorOrdinary
            (membership := membership) (notBare := notBare)
            ordinary argumentsSafe)
    | lambda {bound binder body domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {available binderImage}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (binderImage domain :: available) binderImage}
        (bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.lambda (binder := binder) bodySafe)
    | multiLambda {bound arity binders body domain codomain}
        {bodyTyped : HasType language free
          (List.replicate arity domain ++ bound) body codomain}
        {available binderImage}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (List.replicate arity (binderImage domain) ++ available)
          binderImage}
        (bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.multiLambda
            (binders := binders) bodySafe)
    | subst {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {available binderImage}
        {bodySafe : bodyTyped.ReflectiveSupportSafeAt profile inputSupport
          (binderImage domain :: available) binderImage}
        {replacementSafe : replacementTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        (bodyAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport bodySafe)
        (replacementAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport replacementSafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.subst bodySafe replacementSafe)
    | collection {bound collectionType elements rest elementType}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available binderImage}
        {elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile inputSupport elementsTyped available binderImage}
        (elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.collection
            (collectionType := collectionType) (rest := rest) elementsSafe)
    | collectionConstructor
        {bound rule parameterName collectionType elements rest elementType}
        {membership : rule ∈ language.terms}
        {parameterShape : rule.params =
          [.simple parameterName (.collection collectionType elementType)]}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available binderImage}
        {elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile inputSupport elementsTyped available binderImage}
        (elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe) :
        ReflectiveSupportSubstitutionAlignedAt typingSupport
          (HasType.ReflectiveSupportSafeAt.collectionConstructor
            (membership := membership) (parameterShape := parameterShape)
            (rest := rest) elementsSafe)

  /-- Argument-spine companion to substitution alignment. -/
  inductive ReflectiveArgumentsSupportSubstitutionAlignedAt
      {language : LanguageDef} {free : FreeTypeContext}
      {inputSupport : ContextSupport.Support}
      (typingSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {arguments : List Pattern} →
      {parameters : List TermParam} →
      {typed : ArgumentsHaveTypes language free bound arguments parameters} →
      {available : List TypeExpr} →
      {binderImage : TypeExpr → TypeExpr} →
      typed.ReflectiveSupportSafeAt profile inputSupport available binderImage →
      Prop where
    | nil (bound available : List TypeExpr) {binderImage} :
        ReflectiveArgumentsSupportSubstitutionAlignedAt typingSupport
          (ArgumentsHaveTypes.ReflectiveSupportSafeAt.nil
            (binderImage := binderImage) bound available)
    | cons {bound argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {available binderImage}
        {argumentSafe : argumentTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        (argumentAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport argumentSafe)
        (argumentsAligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
          typingSupport argumentsSafe) :
        ReflectiveArgumentsSupportSubstitutionAlignedAt typingSupport
          (ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := representation) (parameterType := parameterType)
            argumentSafe argumentsSafe)

  /-- Collection-spine companion to substitution alignment. -/
  inductive ReflectiveElementsSupportSubstitutionAlignedAt
      {language : LanguageDef} {free : FreeTypeContext}
      {inputSupport : ContextSupport.Support}
      (typingSupport : ContextSupport.Support) :
      {bound : List TypeExpr} → {elements : List Pattern} →
      {elementType : TypeExpr} →
      {typed : ElementsHaveType language free bound elements elementType} →
      {available : List TypeExpr} →
      {binderImage : TypeExpr → TypeExpr} →
      typed.ReflectiveSupportSafeAt profile inputSupport available binderImage →
      Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr)
        (available : List TypeExpr) {binderImage} :
        ReflectiveElementsSupportSubstitutionAlignedAt typingSupport
          (ElementsHaveType.ReflectiveSupportSafeAt.nil
            (binderImage := binderImage) bound elementType available)
    | cons {bound element elements elementType}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available binderImage}
        {elementSafe : elementTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        {elementsSafe : elementsTyped.ReflectiveSupportSafeAt
          profile inputSupport available binderImage}
        (elementAligned : ReflectiveSupportSubstitutionAlignedAt
          typingSupport elementSafe)
        (elementsAligned : ReflectiveElementsSupportSubstitutionAlignedAt
          typingSupport elementsSafe) :
        ReflectiveElementsSupportSubstitutionAlignedAt typingSupport
          (ElementsHaveType.ReflectiveSupportSafeAt.cons
            elementSafe elementsSafe)
end

/-- Positive boundary canary: a variable whose typing and reflective supports
are exact needs neither active insertion nor a sealed outer context. -/
theorem HasType.ReflectiveSupportSafeAt.fvar_substitutionAligned_exact
    {language : LanguageDef} {free : FreeTypeContext}
    {inputSupport : ContextSupport.Support}
    {name : String} {type : TypeExpr}
    (lookup : free name = some type)
    (binderImage : TypeExpr → TypeExpr) :
    let safe :
        (HasType.fvar (language := language) (bound := inputSupport name)
          lookup).ReflectiveSupportSafeAt profile inputSupport
            (inputSupport name) binderImage :=
      HasType.ReflectiveSupportSafeAt.fvar lookup (inputSupport name)
        ⟨[], by simp⟩
    ReflectiveSupportSubstitutionAlignedAt inputSupport safe := by
  dsimp
  exact ReflectiveSupportSubstitutionAlignedAt.fvar
    (lookup := lookup) (shape := ⟨[], by simp⟩)
    ⟨[], [], by simp⟩

/-- Negative boundary canary: reflective insertion depth cannot exceed the
active typing prefix.  A coeffect with one extra active binder cannot be
aligned with an unchanged exact typing context. -/
theorem HasType.ReflectiveSupportSafeAt.fvar_not_substitutionAligned_extra
    {language : LanguageDef} {free : FreeTypeContext}
    {inputSupport : ContextSupport.Support}
    {name : String} {type marker : TypeExpr}
    (lookup : free name = some type)
    (binderImage : TypeExpr → TypeExpr) :
    ReflectiveSupportSubstitutionAlignedAt inputSupport
      (HasType.ReflectiveSupportSafeAt.fvar
        (profile := profile) (language := language) (free := free)
        (support := inputSupport)
        (bound := inputSupport name) (binderImage := binderImage) lookup
        (marker :: inputSupport name) ⟨[marker], by simp⟩) → False := by
  intro aligned
  cases aligned with
  | fvar contextShape =>
      obtain ⟨active, sealed, boundShape, activeLength⟩ := contextShape
      have lengths := congrArg List.length boundShape
      simp only [List.length_append, List.length_cons] at lengths activeLength
      omega


end WellSorted

end Mettapedia.GSLT.LanguageDef
