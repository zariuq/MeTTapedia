import Mettapedia.GSLT.LanguageDef.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

/-!
# Binder-context support for open structural parameters

An ordinary free pattern variable records its result type but not the bound
context on which its eventual filling may depend.  That distinction matters
for a syntax transformer: a canonicalizer may move an opaque parameter under
additional binders only when the parameter is weakened accordingly, and may
not move it out of binders on which it depends.

This file refines the existing declaration-derived typing derivations with
their actual free-variable occurrence contexts.  It does not introduce a
second typing judgment.  A support assignment chooses one suffix of the
bound context for each free variable; structural substitution then weakens
the chosen filling by exactly the remaining prefix.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

namespace ContextSupport

/-- The bound-variable context on which each structural parameter depends. -/
abbrev Support := String → List TypeExpr

/-- Simultaneous fillings for structural parameters. -/
abbrev Assignment := String → Pattern

/-- Instantiate a supported parameter at its occurrence depth.  The support
length is the number of outer de Bruijn levels retained by the filling; all
additional inner binders are inserted by weakening. -/
def substituteAt (support : Support) (assignment : Assignment) (depth : Nat) :
    Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name =>
      liftBVars 0 (depth - (support name).length) (assignment name)
  | .apply constructor arguments =>
      .apply constructor (arguments.map (substituteAt support assignment depth))
  | .lambda binderName body =>
      .lambda binderName (substituteAt support assignment (depth + 1) body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames
        (substituteAt support assignment (depth + arity) body)
  | .subst body replacement =>
      .subst (substituteAt support assignment (depth + 1) body)
        (substituteAt support assignment depth replacement)
  | .collection collectionType elements rest =>
      .collection collectionType
        (elements.map (substituteAt support assignment depth)) rest
termination_by pattern => sizeOf pattern

/-- Top-level supported substitution in one authored bound context. -/
def substitute (support : Support) (assignment : Assignment)
    (bound : List TypeExpr) (pattern : Pattern) : Pattern :=
  substituteAt support assignment bound.length pattern

end ContextSupport

/-! ## Reflective support action

Ordinary typing retains every surrounding binder below a reflective quote,
while reflective scope deliberately seals the quoted body from those outer
binders.  Consequently the number used to weaken a structural parameter is
not always the length of the typing context.  The following action tracks the
binders available since the nearest authored quotation boundary. -/

namespace ReflectiveContextSupport

/-- Whether a constructor is selected as a reflective quotation boundary by
an explicit reflection profile. -/
def isQuoteConstructor (profile : ReflectionProfile)
    (constructor : String) : Bool :=
  profile.presentations.any
    (fun presentation => presentation.quoteConstructor == constructor)

/-- Capture-avoiding structural substitution indexed by the binder support
available since the nearest reflective quote.  Every authored quote resets
that support to zero; ordinary constructors preserve it. -/
def substituteAt (profile : ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (availableDepth : Nat) :
    Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name =>
      liftBVars 0 (availableDepth - (support name).length) (assignment name)
  | .apply constructor arguments =>
      let childDepth :=
        if isQuoteConstructor profile constructor then 0 else availableDepth
      .apply constructor
        (arguments.map (substituteAt profile support assignment childDepth))
  | .lambda binderName body =>
      .lambda binderName
        (substituteAt profile support assignment (availableDepth + 1) body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames
        (substituteAt profile support assignment
          (availableDepth + arity) body)
  | .subst body replacement =>
      .subst
        (substituteAt profile support assignment (availableDepth + 1) body)
        (substituteAt profile support assignment availableDepth replacement)
  | .collection collectionType elements rest =>
      .collection collectionType
        (elements.map
          (substituteAt profile support assignment availableDepth)) rest
termination_by pattern => sizeOf pattern

/-- Top-level reflective structural substitution in an authored bound
context. -/
def substitute (profile : ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (bound : List TypeExpr)
    (pattern : Pattern) : Pattern :=
  substituteAt profile support assignment bound.length pattern

/-- Two reflective substitution environments agree on every free name that
the given pattern can inspect.  Entries outside this finite syntactic support
are deliberately irrelevant. -/
def SubstitutionInputsAgreeOn (pattern : Pattern)
    (firstSupport secondSupport : ContextSupport.Support)
    (firstAssignment secondAssignment : ContextSupport.Assignment) : Prop :=
  ∀ name, name ∈ pattern.freeFvarNames →
    firstSupport name = secondSupport name ∧
      firstAssignment name = secondAssignment name

/-- Reflective substitution is exactly extensional on the finite set of free
names read by its input pattern.  This permits independently assembled finite
environments to agree on a skeleton without requiring unused entries to be
definitionally equal. -/
theorem substituteAt_eq_of_inputsAgreeOn
    (profile : ReflectionProfile)
    {firstSupport secondSupport : ContextSupport.Support}
    {firstAssignment secondAssignment : ContextSupport.Assignment}
    (availableDepth : Nat) (pattern : Pattern)
    (agree : SubstitutionInputsAgreeOn pattern firstSupport secondSupport
      firstAssignment secondAssignment) :
    substituteAt profile firstSupport firstAssignment availableDepth pattern =
      substituteAt profile secondSupport secondAssignment availableDepth
        pattern := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index => simp [substituteAt]
  | hfvar name =>
      obtain ⟨supportEquality, assignmentEquality⟩ :=
        agree name (by simp [Pattern.freeFvarNames])
      simp [substituteAt, supportEquality, assignmentEquality]
  | happly constructor arguments inductionHypothesis =>
      simp only [substituteAt]
      congr 1
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      apply agree name
      simp only [Pattern.freeFvarNames, List.mem_flatMap]
      exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      simp only [substituteAt]
      congr 1
      apply inductionHypothesis
      intro name membership
      apply agree name
      simpa [Pattern.freeFvarNames] using membership
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [substituteAt]
      congr 1
      apply inductionHypothesis
      intro name membership
      apply agree name
      simpa [Pattern.freeFvarNames] using membership
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [substituteAt]
      congr 1
      · apply bodyInduction
        intro name membership
        apply agree name
        simp [Pattern.freeFvarNames, membership]
      · apply replacementInduction
        intro name membership
        apply agree name
        simp [Pattern.freeFvarNames, membership]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [substituteAt]
      congr 1
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership
      apply agree name
      simp only [Pattern.freeFvarNames, List.mem_append,
        List.mem_flatMap]
      exact Or.inl ⟨element, membership, nameMembership⟩

/-- Top-level form of finite-support extensionality. -/
theorem substitute_eq_of_inputsAgreeOn
    (profile : ReflectionProfile)
    {firstSupport secondSupport : ContextSupport.Support}
    {firstAssignment secondAssignment : ContextSupport.Assignment}
    (bound : List TypeExpr) (pattern : Pattern)
    (agree : SubstitutionInputsAgreeOn pattern firstSupport secondSupport
      firstAssignment secondAssignment) :
    substitute profile firstSupport firstAssignment bound pattern =
      substitute profile secondSupport secondAssignment bound pattern := by
  exact substituteAt_eq_of_inputsAgreeOn profile bound.length pattern agree

end ReflectiveContextSupport

namespace WellSorted

open ContextSupport
open Mettapedia.OSLF.Framework.ConstructorCategory

/-! ## Occurrence contexts derived from typing evidence -/

mutual
  /-- A free variable occurs at an exact bound context in the existing typing
  derivation.  The relation is a refinement of that proof and extracts no
  proof-irrelevant data from it. -/
  inductive FreeVariableOccursAt
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {pattern : Pattern} → {type : TypeExpr} →
      HasType language free bound pattern type →
      String → List TypeExpr → Prop where
    | here {bound name type} {lookup : free name = some type} :
        FreeVariableOccursAt (HasType.fvar lookup) name bound
    | constructor {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {name occurrenceBound}
        (occurs : ArgumentsFreeVariableOccursAt argumentsTyped
          name occurrenceBound) :
        FreeVariableOccursAt
          (HasType.constructor membership notBare argumentsTyped)
          name occurrenceBound
    | lambda {bound binder body domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt bodyTyped name occurrenceBound) :
        FreeVariableOccursAt (HasType.lambda (binder := binder) bodyTyped)
          name occurrenceBound
    | multiLambda {bound arity binders body domain codomain}
        {bodyTyped : HasType language free
          (List.replicate arity domain ++ bound) body codomain}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt bodyTyped name occurrenceBound) :
        FreeVariableOccursAt
          (HasType.multiLambda (binders := binders) bodyTyped)
          name occurrenceBound
    | substBody {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt bodyTyped name occurrenceBound) :
        FreeVariableOccursAt (HasType.subst bodyTyped replacementTyped)
          name occurrenceBound
    | substReplacement {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt replacementTyped name occurrenceBound) :
        FreeVariableOccursAt (HasType.subst bodyTyped replacementTyped)
          name occurrenceBound
    | collection {bound collectionType elements rest elementType}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {name occurrenceBound}
        (occurs : ElementsFreeVariableOccursAt elementsTyped
          name occurrenceBound) :
        FreeVariableOccursAt
          (HasType.collection (collectionType := collectionType)
            (rest := rest) elementsTyped) name occurrenceBound
    | collectionConstructor
        {bound rule parameterName collectionType elements rest elementType}
        {membership : rule ∈ language.terms}
        {parameterShape : rule.params =
          [.simple parameterName (.collection collectionType elementType)]}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {name occurrenceBound}
        (occurs : ElementsFreeVariableOccursAt elementsTyped
          name occurrenceBound) :
        FreeVariableOccursAt
          (HasType.collectionConstructor (rest := rest)
            membership parameterShape elementsTyped)
          name occurrenceBound

  /-- Free-variable occurrence in an authored constructor argument spine. -/
  inductive ArgumentsFreeVariableOccursAt
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {arguments : List Pattern} →
      {parameters : List TermParam} →
      ArgumentsHaveTypes language free bound arguments parameters →
      String → List TypeExpr → Prop where
    | head {argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt argumentTyped name occurrenceBound) :
        ArgumentsFreeVariableOccursAt
          (ArgumentsHaveTypes.cons representation parameterType
            argumentTyped argumentsTyped) name occurrenceBound
    | tail {argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {name occurrenceBound}
        (occurs : ArgumentsFreeVariableOccursAt argumentsTyped
          name occurrenceBound) :
        ArgumentsFreeVariableOccursAt
          (ArgumentsHaveTypes.cons representation parameterType
            argumentTyped argumentsTyped) name occurrenceBound

  /-- Free-variable occurrence in a collection element spine. -/
  inductive ElementsFreeVariableOccursAt
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {elementType : TypeExpr} →
      {elements : List Pattern} →
      ElementsHaveType language free bound elements elementType →
      String → List TypeExpr → Prop where
    | head {element elements}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound
          elements elementType}
        {name occurrenceBound}
        (occurs : FreeVariableOccursAt elementTyped name occurrenceBound) :
        ElementsFreeVariableOccursAt
          (ElementsHaveType.cons elementTyped elementsTyped)
          name occurrenceBound
    | tail {element elements}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound
          elements elementType}
        {name occurrenceBound}
        (occurs : ElementsFreeVariableOccursAt elementsTyped
          name occurrenceBound) :
        ElementsFreeVariableOccursAt
          (ElementsHaveType.cons elementTyped elementsTyped)
          name occurrenceBound
end

/-! ## Occurrence support across reflective boundaries -/

mutual
  /-- A free-variable occurrence together with the binder support available
  since the nearest authored reflective quote.  The underlying typing proof
  retains the full lexical context; this additional index records exactly
  the context through which an opaque filling may be weakened. -/
  inductive ReflectiveFreeVariableOccursAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {pattern : Pattern} → {type : TypeExpr} →
      HasType language free bound pattern type →
      List TypeExpr → String → List TypeExpr → Prop where
    | here {name type} {lookup : free name = some type}
        (bound available : List TypeExpr) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.fvar (bound := bound) lookup)
          available name available
    | constructorQuote {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available name occurrenceSupport}
        (quoted : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = true)
        (occurs : ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
          [] name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.constructor membership notBare argumentsTyped)
          available name occurrenceSupport
    | constructorOrdinary {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available name occurrenceSupport}
        (ordinary : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = false)
        (occurs : ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
          available name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.constructor membership notBare argumentsTyped)
          available name occurrenceSupport
    | lambda {bound binder body domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile bodyTyped
          (domain :: available) name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.lambda (binder := binder) bodyTyped)
          available name occurrenceSupport
    | multiLambda {bound arity binders body domain codomain}
        {bodyTyped : HasType language free
          (List.replicate arity domain ++ bound) body codomain}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile bodyTyped
          (List.replicate arity domain ++ available) name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.multiLambda (binders := binders) bodyTyped)
          available name occurrenceSupport
    | substBody {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile bodyTyped
          (domain :: available) name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.subst bodyTyped replacementTyped)
          available name occurrenceSupport
    | substReplacement {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile replacementTyped
          available name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.subst bodyTyped replacementTyped)
          available name occurrenceSupport
    | collection {bound collectionType elements rest elementType}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available name occurrenceSupport}
        (occurs : ReflectiveElementsFreeVariableOccursAt profile elementsTyped
          available name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.collection (collectionType := collectionType)
            (rest := rest) elementsTyped)
          available name occurrenceSupport
    | collectionConstructor
        {bound rule parameterName collectionType elements rest elementType}
        {membership : rule ∈ language.terms}
        {parameterShape : rule.params =
          [.simple parameterName (.collection collectionType elementType)]}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available name occurrenceSupport}
        (occurs : ReflectiveElementsFreeVariableOccursAt profile elementsTyped
          available name occurrenceSupport) :
        ReflectiveFreeVariableOccursAt profile
          (HasType.collectionConstructor (rest := rest)
            membership parameterShape elementsTyped)
          available name occurrenceSupport

  /-- Reflective-support occurrence in an authored constructor spine. -/
  inductive ReflectiveArgumentsFreeVariableOccursAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {arguments : List Pattern} →
      {parameters : List TermParam} →
      ArgumentsHaveTypes language free bound arguments parameters →
      List TypeExpr → String → List TypeExpr → Prop where
    | head {argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile argumentTyped
          available name occurrenceSupport) :
        ReflectiveArgumentsFreeVariableOccursAt profile
          (ArgumentsHaveTypes.cons representation parameterType
            argumentTyped argumentsTyped)
          available name occurrenceSupport
    | tail {argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {available name occurrenceSupport}
        (occurs : ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
          available name occurrenceSupport) :
        ReflectiveArgumentsFreeVariableOccursAt profile
          (ArgumentsHaveTypes.cons representation parameterType
            argumentTyped argumentsTyped)
          available name occurrenceSupport

  /-- Reflective-support occurrence in a collection element spine. -/
  inductive ReflectiveElementsFreeVariableOccursAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext} :
      {bound : List TypeExpr} → {elementType : TypeExpr} →
      {elements : List Pattern} →
      ElementsHaveType language free bound elements elementType →
      List TypeExpr → String → List TypeExpr → Prop where
    | head {element elements}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound
          elements elementType}
        {available name occurrenceSupport}
        (occurs : ReflectiveFreeVariableOccursAt profile elementTyped
          available name occurrenceSupport) :
        ReflectiveElementsFreeVariableOccursAt profile
          (ElementsHaveType.cons elementTyped elementsTyped)
          available name occurrenceSupport
    | tail {element elements}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound
          elements elementType}
        {available name occurrenceSupport}
        (occurs : ReflectiveElementsFreeVariableOccursAt profile elementsTyped
          available name occurrenceSupport) :
        ReflectiveElementsFreeVariableOccursAt profile
          (ElementsHaveType.cons elementTyped elementsTyped)
          available name occurrenceSupport
end

/-- Every reflective occurrence support extends the parameter's declared
support by an inner prefix.  At the root, `available` is the authored bound
context; quotation resets it to the empty context. -/
def HasType.RespectsReflectiveSupportAt
    (profile : ReflectionProfile)
    {language : LanguageDef} {free : FreeTypeContext}
    (available : List TypeExpr) (support : ContextSupport.Support)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type) : Prop :=
  ∀ name occurrenceSupport,
    ReflectiveFreeVariableOccursAt profile typed available name occurrenceSupport →
      ∃ inner, occurrenceSupport = inner ++ support name

/-- Pointwise reflective-support discipline for an authored constructor
argument spine. -/
def ArgumentsHaveTypes.RespectsReflectiveSupportAt
    (profile : ReflectionProfile)
    {language : LanguageDef} {free : FreeTypeContext}
    (available : List TypeExpr) (support : ContextSupport.Support)
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters) : Prop :=
  ∀ name occurrenceSupport,
    ReflectiveArgumentsFreeVariableOccursAt profile typed
        available name occurrenceSupport →
      ∃ inner, occurrenceSupport = inner ++ support name

/-- Pointwise reflective-support discipline for a collection element spine. -/
def ElementsHaveType.RespectsReflectiveSupportAt
    (profile : ReflectionProfile)
    {language : LanguageDef} {free : FreeTypeContext}
    (available : List TypeExpr) (support : ContextSupport.Support)
    {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType language free bound elements elementType) : Prop :=
  ∀ name occurrenceSupport,
    ReflectiveElementsFreeVariableOccursAt profile typed
        available name occurrenceSupport →
      ∃ inner, occurrenceSupport = inner ++ support name

/-! The occurrence relation above is useful for extensional statements and
counterexamples.  The following mutually inductive judgment is the
constructor-facing form used by canonicalizer proofs: it carries the same
support discipline, but exposes one proof constructor per authored typing
constructor instead of requiring dependent inversion on an occurrence. -/

mutual
  /-- Every free parameter in a typing derivation is used within its declared
  reflective binder support. -/
  inductive HasType.ReflectiveSupportSafeAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext}
      (support : ContextSupport.Support) :
      {bound : List TypeExpr} → {pattern : Pattern} → {type : TypeExpr} →
      HasType language free bound pattern type → List TypeExpr →
      (binderImage : TypeExpr → TypeExpr := id) → Prop where
    | bvar {bound index type} (lookup : bound[index]? = some type)
        (available : List TypeExpr) {binderImage : TypeExpr → TypeExpr} :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.bvar (free := free) lookup) available binderImage
    | fvar {bound name type} (lookup : free name = some type)
        (available : List TypeExpr) {binderImage : TypeExpr → TypeExpr}
        (shape : ∃ inner, available = inner ++ support name) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.fvar (bound := bound) lookup) available binderImage
    | constructorQuote {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (quoted : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = true)
        (argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile support argumentsTyped [] binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.constructor membership notBare argumentsTyped) available
          binderImage
    | constructorOrdinary {bound rule arguments}
        {membership : rule ∈ language.terms}
        {notBare : ¬ UsesBareCollection rule}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments rule.params}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (ordinary : ReflectiveContextSupport.isQuoteConstructor
          profile rule.label = false)
        (argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile support argumentsTyped available binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.constructor membership notBare argumentsTyped) available
          binderImage
    | lambda {bound binder body domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (bodySafe : HasType.ReflectiveSupportSafeAt profile support bodyTyped
          (binderImage domain :: available) binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.lambda (binder := binder) bodyTyped) available binderImage
    | multiLambda {bound arity binders body domain codomain}
        {bodyTyped : HasType language free
          (List.replicate arity domain ++ bound) body codomain}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (bodySafe : HasType.ReflectiveSupportSafeAt profile support bodyTyped
          (List.replicate arity (binderImage domain) ++ available)
          binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.multiLambda (binders := binders) bodyTyped) available
          binderImage
    | subst {bound body replacement domain codomain}
        {bodyTyped : HasType language free (domain :: bound) body codomain}
        {replacementTyped : HasType language free bound replacement domain}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (bodySafe : HasType.ReflectiveSupportSafeAt profile support bodyTyped
          (binderImage domain :: available) binderImage)
        (replacementSafe : HasType.ReflectiveSupportSafeAt profile support replacementTyped
          available binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.subst bodyTyped replacementTyped) available binderImage
    | collection {bound collectionType elements rest elementType}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile support elementsTyped available binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.collection (collectionType := collectionType)
            (rest := rest) elementsTyped) available binderImage
    | collectionConstructor
        {bound rule parameterName collectionType elements rest elementType}
        {membership : rule ∈ language.terms}
        {parameterShape : rule.params =
          [.simple parameterName (.collection collectionType elementType)]}
        {elementsTyped : ElementsHaveType language free bound elements elementType}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile support elementsTyped available binderImage) :
        HasType.ReflectiveSupportSafeAt profile support
          (HasType.collectionConstructor (rest := rest)
            membership parameterShape elementsTyped) available binderImage

  /-- Reflective support safety for an authored constructor spine. -/
  inductive ArgumentsHaveTypes.ReflectiveSupportSafeAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext}
      (support : ContextSupport.Support) :
      {bound : List TypeExpr} → {arguments : List Pattern} →
      {parameters : List TermParam} →
      ArgumentsHaveTypes language free bound arguments parameters →
      List TypeExpr → (binderImage : TypeExpr → TypeExpr := id) → Prop where
    | nil (bound available : List TypeExpr)
        {binderImage : TypeExpr → TypeExpr} :
        ArgumentsHaveTypes.ReflectiveSupportSafeAt profile support
          (ArgumentsHaveTypes.nil (language := language) (free := free)
            (bound := bound)) available binderImage
    | cons {bound argument arguments parameter parameters expected}
        {representation : MatchesParameterRepresentation parameter argument}
        {parameterType : parameterType? parameter = some expected}
        {argumentTyped : HasType language free bound argument expected}
        {argumentsTyped : ArgumentsHaveTypes language free bound
          arguments parameters}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (argumentSafe : HasType.ReflectiveSupportSafeAt
          profile support argumentTyped available binderImage)
        (argumentsSafe : ArgumentsHaveTypes.ReflectiveSupportSafeAt
          profile support argumentsTyped available binderImage) :
        ArgumentsHaveTypes.ReflectiveSupportSafeAt profile support
          (ArgumentsHaveTypes.cons representation parameterType
            argumentTyped argumentsTyped) available binderImage

  /-- Reflective support safety for collection elements. -/
  inductive ElementsHaveType.ReflectiveSupportSafeAt
      (profile : ReflectionProfile)
      {language : LanguageDef} {free : FreeTypeContext}
      (support : ContextSupport.Support) :
      {bound : List TypeExpr} → {elements : List Pattern} →
      {elementType : TypeExpr} →
      ElementsHaveType language free bound elements elementType →
      List TypeExpr → (binderImage : TypeExpr → TypeExpr := id) → Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr)
        (available : List TypeExpr) {binderImage : TypeExpr → TypeExpr} :
        ElementsHaveType.ReflectiveSupportSafeAt profile support
          (ElementsHaveType.nil (language := language) (free := free)
            bound elementType) available binderImage
    | cons {bound element elements elementType}
        {elementTyped : HasType language free bound element elementType}
        {elementsTyped : ElementsHaveType language free bound
          elements elementType}
        {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
        (elementSafe : HasType.ReflectiveSupportSafeAt
          profile support elementTyped available binderImage)
        (elementsSafe : ElementsHaveType.ReflectiveSupportSafeAt
          profile support elementsTyped available binderImage) :
        ElementsHaveType.ReflectiveSupportSafeAt profile support
          (ElementsHaveType.cons elementTyped elementsTyped) available
          binderImage
end

/-- Reflective-support safety depends on the typing derivation only through
its judgment.  Transport between proof-irrelevant derivations of that same
judgment is therefore lossless. -/
theorem HasType.ReflectiveSupportSafeAt.castTyping
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {source target : HasType language free bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : source.ReflectiveSupportSafeAt profile support available binderImage) :
    target.ReflectiveSupportSafeAt profile support available binderImage := by
  have proofEquality : source = target := Subsingleton.elim _ _
  cases proofEquality
  exact safe

/-- Transport reflective-support evidence across an equality of complete
binder contexts.  The typing derivation is proof-irrelevant once the
judgment indices agree; keeping this transport explicit avoids dependent
rewrites through the support derivation. -/
theorem HasType.ReflectiveSupportSafeAt.castBound
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr}
    {source : HasType language free sourceBound pattern type}
    {target : HasType language free targetBound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (boundEquality : sourceBound = targetBound)
    (safe : source.ReflectiveSupportSafeAt profile support available binderImage) :
    target.ReflectiveSupportSafeAt profile support available binderImage := by
  cases boundEquality
  exact safe.castTyping

/-- Proof-irrelevant transport for support-safe constructor spines. -/
theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    {source target :
      ArgumentsHaveTypes language free bound arguments parameters}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : source.ReflectiveSupportSafeAt profile support available binderImage) :
    target.ReflectiveSupportSafeAt profile support available binderImage := by
  have proofEquality : source = target := Subsingleton.elim _ _
  cases proofEquality
  exact safe

/-- The head of a support-safe constructor spine is support-safe.  The
explicit proof transport hides only proof-irrelevant choices of the same
authored parameter type. -/
theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {argument : Pattern} {arguments : List Pattern}
    {parameter : TermParam} {parameters : List TermParam}
    {expected : TypeExpr}
    {representation : MatchesParameterRepresentation parameter argument}
    {parameterType : parameterType? parameter = some expected}
    {argumentTyped : HasType language free bound argument expected}
    {argumentsTyped : ArgumentsHaveTypes language free bound
      arguments parameters}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : (ArgumentsHaveTypes.cons representation parameterType
      argumentTyped argumentsTyped).ReflectiveSupportSafeAt
        profile support available binderImage) :
    argumentTyped.ReflectiveSupportSafeAt profile support available binderImage := by
  cases safe with
  | @cons bound' argument' arguments' parameter' parameters' expected'
      representation' parameterType' argumentTyped' argumentsTyped' available'
      binderImage' argumentSafe argumentsSafe =>
      have expectedEquality : expected' = expected := by
        have someEquality : some expected' = some expected :=
          parameterType'.symm.trans parameterType
        exact Option.some.inj someEquality
      subst expected'
      have proofEquality : argumentTyped' = argumentTyped :=
        Subsingleton.elim _ _
      cases proofEquality
      exact argumentSafe

/-- Proof-irrelevant transport for support-safe collection elements. -/
theorem ElementsHaveType.ReflectiveSupportSafeAt.castTyping
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    {source target : ElementsHaveType language free bound elements elementType}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : source.ReflectiveSupportSafeAt profile support available binderImage) :
    target.ReflectiveSupportSafeAt profile support available binderImage := by
  have proofEquality : source = target := Subsingleton.elim _ _
  cases proofEquality
  exact safe

/-- Every member of a support-safe collection spine has a typing derivation
with the same reflective support discipline. -/
theorem ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    {typed : ElementsHaveType language free bound elements elementType}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ element ∈ elements,
      ∃ elementTyped : HasType language free bound element elementType,
        elementTyped.ReflectiveSupportSafeAt profile support available binderImage := by
  exact ElementsHaveType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun {bound} {elements} {elementType} _ available
        binderImage _ =>
      ∀ element ∈ elements,
        ∃ elementTyped : HasType language free bound element elementType,
          elementTyped.ReflectiveSupportSafeAt profile support available binderImage)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; simp_all)
    (by
      intro bound head tail elementType headTyped tailTyped available
        binderImage headSafe tailSafe headIH tailIH candidate membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact ⟨headTyped, headSafe⟩
      · exact tailIH candidate membership)
    safe

/-- Pointwise support-safe typed elements assemble into one support-safe
collection spine. -/
theorem ElementsHaveType.ReflectiveSupportSafeAt.of_forall_mem
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (pointwise : ∀ element ∈ elements,
      ∃ elementTyped : HasType language free bound element elementType,
        elementTyped.ReflectiveSupportSafeAt profile support available binderImage) :
    ∃ typed : ElementsHaveType language free bound elements elementType,
      typed.ReflectiveSupportSafeAt profile support available binderImage := by
  induction elements with
  | nil =>
      let typed := ElementsHaveType.nil (language := language) (free := free)
        bound elementType
      exact ⟨typed, .nil bound elementType available⟩
  | cons head tail inductionHypothesis =>
      obtain ⟨headTyped, headSafe⟩ := pointwise head (by simp)
      have tailPointwise : ∀ element ∈ tail,
          ∃ elementTyped : HasType language free bound element elementType,
            elementTyped.ReflectiveSupportSafeAt profile support available
              binderImage := by
        intro element membership
        exact pointwise element (by simp [membership])
      obtain ⟨tailTyped, tailSafe⟩ := inductionHypothesis tailPointwise
      let typed := ElementsHaveType.cons headTyped tailTyped
      exact ⟨typed, .cons headSafe tailSafe⟩

namespace HasType

/-- A bound variable carries no free-variable support obligation. -/
theorem bvar_respectsReflectiveSupportAt
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {index : Nat} {type : TypeExpr}
    (lookup : bound[index]? = some type)
    (available : List TypeExpr) (support : ContextSupport.Support) :
    (HasType.bvar (language := language) (free := free) lookup).RespectsReflectiveSupportAt
      profile available support := by
  intro name occurrenceSupport occurs
  cases occurs

/-- A free variable respects exactly the support suffix supplied at its
occurrence. -/
theorem fvar_respectsReflectiveSupportAt
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {name : String} {type : TypeExpr}
    (lookup : free name = some type)
    {available : List TypeExpr} {support : ContextSupport.Support}
    (shape : ∃ inner, available = inner ++ support name) :
    (HasType.fvar (language := language) (bound := bound) lookup).RespectsReflectiveSupportAt
      profile available support := by
  intro occurrenceName occurrenceSupport occurs
  cases occurs
  exact shape

/-- Assemble support preservation through one ordinary binder. -/
theorem lambda_respectsReflectiveSupportAt
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {binder : Option String} {body : Pattern}
    {domain codomain : TypeExpr}
    {bodyTyped : HasType language free (domain :: bound) body codomain}
    {available : List TypeExpr} {support : ContextSupport.Support}
    (bodySupported : bodyTyped.RespectsReflectiveSupportAt
      profile (domain :: available) support) :
    (HasType.lambda (binder := binder) bodyTyped).RespectsReflectiveSupportAt
      profile available support := by
  intro name occurrenceSupport occurs
  cases occurs with
  | lambda child => exact bodySupported _ _ child

/-- Assemble support preservation through a multi-binder. -/
theorem multiLambda_respectsReflectiveSupportAt
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arity : Nat} {binders : List String}
    {body : Pattern} {domain codomain : TypeExpr}
    {bodyTyped : HasType language free
      (List.replicate arity domain ++ bound) body codomain}
    {available : List TypeExpr} {support : ContextSupport.Support}
    (bodySupported : bodyTyped.RespectsReflectiveSupportAt
      profile (List.replicate arity domain ++ available) support) :
    (HasType.multiLambda (binders := binders) bodyTyped).RespectsReflectiveSupportAt
      profile available support := by
  intro name occurrenceSupport occurs
  cases occurs with
  | multiLambda child => exact bodySupported _ _ child

end HasType

/-- Each occurrence context extends the parameter's declared support by an
inner prefix.  Thus a filling can be weakened into every place where the
parameter occurs, while a canonicalizer that preserves this predicate cannot
move a parameter out of binders on which it depends. -/
def HasType.RespectsSupport
    {language : LanguageDef} {free : FreeTypeContext}
    (support : ContextSupport.Support)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type) : Prop :=
  ∀ name occurrenceBound,
    FreeVariableOccursAt typed name occurrenceBound →
      ∃ inner, occurrenceBound = inner ++ support name

/-- A support-indexed assignment is typed at the exact outer context declared
for every source parameter. -/
structure SupportedAssignment (language : LanguageDef)
    (source target : FreeTypeContext)
    (support : ContextSupport.Support) where
  assignment : ContextSupport.Assignment
  typed : ∀ {name type}, source name = some type →
    HasType language target (support name) (assignment name) type

/-- A support-indexed assignment whose values are open object-language
terms, not merely sorted raw patterns.  These three proof fields are exactly
the non-typing components of `OpenTermWellSorted`; keeping them beside the
existing `SupportedAssignment` lets reflective restoration return the real
open carrier without introducing another syntax or typing judgment. -/
structure SupportedOpenAssignment (profile : ReflectionProfile)
    (language : LanguageDef)
    (source target : FreeTypeContext)
    (support : ContextSupport.Support)
    extends SupportedAssignment language source target support where
  canonicalBinderMetadata : ∀ {name type}, source name = some type →
    (assignment name).hasCanonicalBinderMetadata = true
  objectPattern : ∀ {name type}, source name = some type →
    isObjectPattern (assignment name) = true
  reflectiveScopeSafe : ∀ {name type}, source name = some type →
    ReflectiveScopeSafeAt profile (support name).length (assignment name)

private theorem canonicalBinderMetadataList_liftBVars
    (cutoff shift : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      (liftBVars cutoff shift pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata) :
    Pattern.hasCanonicalBinderMetadataList
        (patterns.map (liftBVars cutoff shift)) =
      Pattern.hasCanonicalBinderMetadataList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, Pattern.hasCanonicalBinderMetadataList]
      rw [pointwise pattern (by simp)]
      rw [inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- Lifting de Bruijn indices changes neither locally nameless display
metadata nor its canonicality. -/
@[simp]
theorem hasCanonicalBinderMetadata_liftBVars
    (cutoff shift : Nat) (pattern : Pattern) :
    (liftBVars cutoff shift pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [liftBVars, Pattern.hasCanonicalBinderMetadata, shifted]
  | hfvar name => simp [liftBVars, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_liftBVars cutoff shift arguments
        (fun member membership => inductionHypothesis member membership cutoff)
  | hlambda binder body inductionHypothesis =>
      simp only [liftBVars, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [liftBVars, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [liftBVars, Pattern.hasCanonicalBinderMetadata]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_liftBVars cutoff shift elements
        (fun member membership => inductionHypothesis member membership cutoff)

private theorem isObjectPatternList_liftBVars
    (cutoff shift : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      isObjectPattern (liftBVars cutoff shift pattern) =
        isObjectPattern pattern) :
    isObjectPatternList (patterns.map (liftBVars cutoff shift)) =
      isObjectPatternList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, isObjectPatternList]
      rw [pointwise pattern (by simp)]
      rw [inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- De Bruijn weakening preserves the object-language boundary. -/
@[simp]
theorem isObjectPattern_liftBVars
    (cutoff shift : Nat) (pattern : Pattern) :
    isObjectPattern (liftBVars cutoff shift pattern) =
      isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [liftBVars, isObjectPattern, shifted]
  | hfvar name => simp [liftBVars, isObjectPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, isObjectPattern]
      exact isObjectPatternList_liftBVars cutoff shift arguments
        (fun member membership => inductionHypothesis member membership cutoff)
  | hlambda binder body inductionHypothesis =>
      simpa [liftBVars, isObjectPattern] using
        inductionHypothesis (cutoff + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [liftBVars, isObjectPattern] using
        inductionHypothesis (cutoff + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [liftBVars, isObjectPattern]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, isObjectPattern]
      rw [isObjectPatternList_liftBVars cutoff shift elements
        (fun member membership => inductionHypothesis member membership cutoff)]

mutual
  /-- Reflective supported substitution preserves canonical locally nameless
  binder metadata when every assigned open term has canonical metadata. -/
  theorem HasType.ReflectiveSupportSafeAt.substituteCanonicalBinderMetadata
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (canonical : pattern.hasCanonicalBinderMetadata = true) :
      Pattern.hasCanonicalBinderMetadata
        (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length pattern) = true := by
    cases safe with
    | bvar lookup available =>
        simpa [ReflectiveContextSupport.substituteAt] using canonical
    | fvar lookup available shape =>
        simp only [ReflectiveContextSupport.substituteAt,
          hasCanonicalBinderMetadata_liftBVars]
        exact assignment.canonicalBinderMetadata lookup
    | constructorQuote quoted argumentsSafe =>
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simpa [ReflectiveContextSupport.substituteAt, quoted,
          Pattern.hasCanonicalBinderMetadata] using
          argumentsSafe.substituteCanonicalBinderMetadata assignment canonical
    | constructorOrdinary ordinary argumentsSafe =>
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simpa [ReflectiveContextSupport.substituteAt, ordinary,
          Pattern.hasCanonicalBinderMetadata] using
          argumentsSafe.substituteCanonicalBinderMetadata assignment canonical
    | lambda bodySafe =>
        simp only [Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true] at canonical
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
        refine ⟨canonical.1, ?_⟩
        simpa only [List.length_cons] using
          bodySafe.substituteCanonicalBinderMetadata assignment canonical.2
    | multiLambda bodySafe =>
        simp only [Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true] at canonical
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
        refine ⟨canonical.1, ?_⟩
        simpa only [List.length_append, List.length_replicate, Nat.add_comm]
          using bodySafe.substituteCanonicalBinderMetadata assignment canonical.2
    | subst bodySafe replacementSafe =>
        simp only [Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true] at canonical
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
        constructor
        · simpa [ReflectiveContextSupport.substituteAt, List.length_cons]
            using bodySafe.substituteCanonicalBinderMetadata assignment
              canonical.1
        · simpa [ReflectiveContextSupport.substituteAt]
            using replacementSafe.substituteCanonicalBinderMetadata assignment
              canonical.2
    | collection elementsSafe =>
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simpa only [ReflectiveContextSupport.substituteAt,
          Pattern.hasCanonicalBinderMetadata] using
          elementsSafe.substituteCanonicalBinderMetadata assignment canonical
    | collectionConstructor elementsSafe =>
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simpa only [ReflectiveContextSupport.substituteAt,
          Pattern.hasCanonicalBinderMetadata] using
          elementsSafe.substituteCanonicalBinderMetadata assignment canonical

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substituteCanonicalBinderMetadata
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (canonical : Pattern.hasCanonicalBinderMetadataList arguments = true) :
      Pattern.hasCanonicalBinderMetadataList
        (arguments.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons argumentSafe argumentsSafe =>
        simp only [List.map, Pattern.hasCanonicalBinderMetadataList,
          Bool.and_eq_true] at canonical ⊢
        exact ⟨argumentSafe.substituteCanonicalBinderMetadata assignment
            canonical.1,
          argumentsSafe.substituteCanonicalBinderMetadata assignment
            canonical.2⟩

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substituteCanonicalBinderMetadata
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (canonical : Pattern.hasCanonicalBinderMetadataList elements = true) :
      Pattern.hasCanonicalBinderMetadataList
        (elements.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons elementSafe elementsSafe =>
        simp only [List.map, Pattern.hasCanonicalBinderMetadataList,
          Bool.and_eq_true] at canonical ⊢
        exact ⟨elementSafe.substituteCanonicalBinderMetadata assignment
            canonical.1,
          elementsSafe.substituteCanonicalBinderMetadata assignment
            canonical.2⟩
end

mutual
  /-- Reflective supported substitution preserves the object-language
  boundary when every assigned value is itself an object term. -/
  theorem HasType.ReflectiveSupportSafeAt.substituteObjectPattern
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (object : isObjectPattern pattern = true) :
      isObjectPattern
        (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length pattern) = true := by
    cases safe with
    | bvar lookup available =>
        simp [ReflectiveContextSupport.substituteAt, isObjectPattern]
    | fvar lookup available shape =>
        simp only [ReflectiveContextSupport.substituteAt,
          isObjectPattern_liftBVars]
        exact assignment.objectPattern lookup
    | constructorQuote quoted argumentsSafe =>
        simp only [isObjectPattern] at object
        simpa [ReflectiveContextSupport.substituteAt, quoted,
          isObjectPattern] using
          argumentsSafe.substituteObjectPattern assignment object
    | constructorOrdinary ordinary argumentsSafe =>
        simp only [isObjectPattern] at object
        simpa [ReflectiveContextSupport.substituteAt, ordinary,
          isObjectPattern] using
          argumentsSafe.substituteObjectPattern assignment object
    | lambda bodySafe =>
        simp only [isObjectPattern] at object
        simp only [ReflectiveContextSupport.substituteAt, isObjectPattern]
        simpa only [List.length_cons] using
          bodySafe.substituteObjectPattern assignment object
    | multiLambda bodySafe =>
        simp only [isObjectPattern] at object
        simp only [ReflectiveContextSupport.substituteAt, isObjectPattern]
        simpa only [List.length_append, List.length_replicate, Nat.add_comm]
          using bodySafe.substituteObjectPattern assignment object
    | subst bodySafe replacementSafe =>
        simp [isObjectPattern] at object
    | collection elementsSafe =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        simp only [ReflectiveContextSupport.substituteAt, isObjectPattern,
          Bool.and_eq_true]
        exact ⟨object.1,
          elementsSafe.substituteObjectPattern assignment object.2⟩
    | collectionConstructor elementsSafe =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        simp only [ReflectiveContextSupport.substituteAt, isObjectPattern,
          Bool.and_eq_true]
        exact ⟨object.1,
          elementsSafe.substituteObjectPattern assignment object.2⟩

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substituteObjectPattern
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (object : isObjectPatternList arguments = true) :
      isObjectPatternList
        (arguments.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons argumentSafe argumentsSafe =>
        simp only [List.map, isObjectPatternList, Bool.and_eq_true] at object ⊢
        exact ⟨argumentSafe.substituteObjectPattern assignment object.1,
          argumentsSafe.substituteObjectPattern assignment object.2⟩

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substituteObjectPattern
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (object : isObjectPatternList elements = true) :
      isObjectPatternList
        (elements.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons elementSafe elementsSafe =>
        simp only [List.map, isObjectPatternList, Bool.and_eq_true] at object ⊢
        exact ⟨elementSafe.substituteObjectPattern assignment object.1,
          elementsSafe.substituteObjectPattern assignment object.2⟩
end

mutual
  /-- Supported substitution preserves one chosen reflective scope check.
  `available` controls weakening of inserted parameters, while `scopeDepth`
  controls the surrounding scope check.  Separating them is essential below
  a quote: substitution support resets to zero even when another reflective
  presentation is being checked at a larger ambient depth. -/
  theorem HasType.ReflectiveSupportSafeAt.substituteBinderSafeAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (presentation : ReflectivePresentationDecl)
      (membership : presentation ∈ profile.presentations)
      {scopeDepth : Nat} (availableWithin : available.length ≤ scopeDepth)
      (scope : binderSafeAt presentation.quoteConstructor scopeDepth pattern = true) :
      binderSafeAt presentation.quoteConstructor scopeDepth
        (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length pattern) = true := by
    cases safe with
    | bvar lookup available =>
        simpa [ReflectiveContextSupport.substituteAt] using scope
    | @fvar bound name type lookup available _binderImage shape =>
        have assignmentSafe :=
          assignment.reflectiveScopeSafe lookup presentation membership
        have lifted := ContextSubstitution.binderSafeAt_liftBVars
          presentation.quoteConstructor
          (ambient := (support name).length) (cutoff := 0)
          (shift := available.length - (support name).length)
          (by simpa using assignmentSafe)
        have atAvailable :
            binderSafeAt presentation.quoteConstructor available.length
              (liftBVars 0 (available.length - (support name).length)
                (assignment.assignment name)) = true := by
          obtain ⟨inner, rfl⟩ := shape
          simpa [List.length_append, Nat.add_comm] using lifted
        simpa only [ReflectiveContextSupport.substituteAt] using
          binderSafeAt_mono presentation.quoteConstructor atAvailable
            availableWithin
    | @constructorQuote bound rule arguments membershipRule notBare
        argumentsTyped available _binderImage quoted argumentsSafe =>
        cases arguments with
        | nil =>
            simp [ReflectiveContextSupport.substituteAt, binderSafeAt,
              binderSafeListAt]
        | cons argument remainder =>
            cases remainder with
            | nil =>
                by_cases same : rule.label = presentation.quoteConstructor
                · have inputList :
                      binderSafeListAt presentation.quoteConstructor 0
                        [argument] = true := by
                    simpa [binderSafeAt, same, binderSafeListAt] using scope
                  have selectedQuote :
                      ReflectiveContextSupport.isQuoteConstructor profile
                        presentation.quoteConstructor = true := by
                    simpa [same] using quoted
                  have outputList :=
                    argumentsSafe.substituteBinderSafeListAt assignment
                      presentation membership (Nat.le_refl 0) inputList
                  simpa [ReflectiveContextSupport.substituteAt, selectedQuote,
                    binderSafeAt, same, binderSafeListAt] using outputList
                · have inputList :
                      binderSafeListAt presentation.quoteConstructor scopeDepth
                        [argument] = true := by
                    simpa [binderSafeAt, same, binderSafeListAt] using scope
                  have outputList :=
                    argumentsSafe.substituteBinderSafeListAt assignment
                      presentation membership (Nat.zero_le scopeDepth) inputList
                  simpa [ReflectiveContextSupport.substituteAt, quoted,
                    binderSafeAt, same, binderSafeListAt] using outputList
            | cons second remainder =>
                have inputList :
                    binderSafeListAt presentation.quoteConstructor scopeDepth
                      (argument :: second :: remainder) = true := by
                  simpa [binderSafeAt] using scope
                have outputList :=
                  argumentsSafe.substituteBinderSafeListAt assignment
                    presentation membership (Nat.zero_le scopeDepth) inputList
                simpa [ReflectiveContextSupport.substituteAt, quoted,
                  binderSafeAt] using outputList
    | @constructorOrdinary bound rule arguments membershipRule notBare
        argumentsTyped available _binderImage ordinary argumentsSafe =>
        have notThisQuote :
            rule.label ≠ presentation.quoteConstructor := by
          intro same
          have quoted : ReflectiveContextSupport.isQuoteConstructor
              profile rule.label = true := by
            unfold ReflectiveContextSupport.isQuoteConstructor
            rw [List.any_eq_true]
            exact ⟨presentation, membership, by simp [same]⟩
          rw [quoted] at ordinary
          contradiction
        have inputList :
            binderSafeListAt presentation.quoteConstructor scopeDepth
              arguments = true := by
          cases arguments with
          | nil => simp [binderSafeListAt]
          | cons argument remainder =>
              cases remainder with
              | nil => simpa [binderSafeAt, notThisQuote] using scope
              | cons second remainder => simpa [binderSafeAt] using scope
        have outputList :=
          argumentsSafe.substituteBinderSafeListAt assignment presentation
            membership availableWithin inputList
        cases arguments with
        | nil =>
            simp [ReflectiveContextSupport.substituteAt, ordinary,
              binderSafeAt, binderSafeListAt]
        | cons argument remainder =>
            cases remainder with
            | nil =>
                simpa [ReflectiveContextSupport.substituteAt, ordinary,
                  binderSafeAt, notThisQuote] using outputList
            | cons second remainder =>
                simpa [ReflectiveContextSupport.substituteAt, ordinary,
                  binderSafeAt] using outputList
    | @lambda bound binder body domain codomain bodyTyped available _binderImage
        bodySafe =>
        have bodyScope :
            binderSafeAt presentation.quoteConstructor (scopeDepth + 1) body =
              true := by
          simpa [binderSafeAt] using scope
        have bodyWithin : (domain :: available).length ≤ scopeDepth + 1 := by
          simpa [List.length_cons] using Nat.add_le_add_right availableWithin 1
        have bodyResult := bodySafe.substituteBinderSafeAt assignment
          presentation membership bodyWithin bodyScope
        simpa [ReflectiveContextSupport.substituteAt, binderSafeAt,
          List.length_cons] using bodyResult
    | @multiLambda bound arity binders body domain codomain bodyTyped available
        _binderImage bodySafe =>
        have bodyScope :
            binderSafeAt presentation.quoteConstructor (scopeDepth + arity)
              body = true := by
          simpa [binderSafeAt] using scope
        have bodyWithin :
            (List.replicate arity domain ++ available).length ≤
              scopeDepth + arity := by
          simp only [List.length_append, List.length_replicate]
          omega
        have bodyResult := bodySafe.substituteBinderSafeAt assignment
          presentation membership bodyWithin bodyScope
        simpa [ReflectiveContextSupport.substituteAt, binderSafeAt,
          List.length_append, List.length_replicate, Nat.add_comm] using bodyResult
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        available _binderImage bodySafe replacementSafe =>
        have componentScope :
            binderSafeAt presentation.quoteConstructor (scopeDepth + 1) body =
                true ∧
              binderSafeAt presentation.quoteConstructor scopeDepth replacement =
                true := by
          simpa [binderSafeAt, Bool.and_eq_true] using scope
        have bodyWithin : (domain :: available).length ≤ scopeDepth + 1 := by
          simpa [List.length_cons] using Nat.add_le_add_right availableWithin 1
        have bodyResult := bodySafe.substituteBinderSafeAt assignment
          presentation membership bodyWithin componentScope.1
        have replacementResult := replacementSafe.substituteBinderSafeAt
          assignment presentation membership availableWithin componentScope.2
        simpa [ReflectiveContextSupport.substituteAt, binderSafeAt,
          Bool.and_eq_true, List.length_cons] using
            And.intro bodyResult replacementResult
    | @collection bound collectionType elements rest elementType elementsTyped
        available _binderImage elementsSafe =>
        have inputList :
            binderSafeListAt presentation.quoteConstructor scopeDepth elements =
              true := by
          simpa [binderSafeAt] using scope
        have outputList :=
          elementsSafe.substituteBinderSafeListAt assignment presentation
            membership availableWithin inputList
        simpa [ReflectiveContextSupport.substituteAt, binderSafeAt] using
          outputList
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membershipRule parameterShape elementsTyped available
        _binderImage elementsSafe =>
        have inputList :
            binderSafeListAt presentation.quoteConstructor scopeDepth elements =
              true := by
          simpa [binderSafeAt] using scope
        have outputList :=
          elementsSafe.substituteBinderSafeListAt assignment presentation
            membership availableWithin inputList
        simpa [ReflectiveContextSupport.substituteAt, binderSafeAt] using
          outputList

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substituteBinderSafeListAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (presentation : ReflectivePresentationDecl)
      (membership : presentation ∈ profile.presentations)
      {scopeDepth : Nat} (availableWithin : available.length ≤ scopeDepth)
      (scope : binderSafeListAt presentation.quoteConstructor scopeDepth
        arguments = true) :
      binderSafeListAt presentation.quoteConstructor scopeDepth
        (arguments.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons argumentSafe argumentsSafe =>
        simp only [List.map, binderSafeListAt, Bool.and_eq_true] at scope ⊢
        exact ⟨argumentSafe.substituteBinderSafeAt assignment presentation
            membership availableWithin scope.1,
          argumentsSafe.substituteBinderSafeListAt assignment presentation
            membership availableWithin scope.2⟩

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substituteBinderSafeListAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {available : List TypeExpr}
      (assignment : SupportedOpenAssignment profile language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available)
      (presentation : ReflectivePresentationDecl)
      (membership : presentation ∈ profile.presentations)
      {scopeDepth : Nat} (availableWithin : available.length ≤ scopeDepth)
      (scope : binderSafeListAt presentation.quoteConstructor scopeDepth
        elements = true) :
      binderSafeListAt presentation.quoteConstructor scopeDepth
        (elements.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) = true := by
    cases safe with
    | nil => rfl
    | cons elementSafe elementsSafe =>
        simp only [List.map, binderSafeListAt, Bool.and_eq_true] at scope ⊢
        exact ⟨elementSafe.substituteBinderSafeAt assignment presentation
            membership availableWithin scope.1,
          elementsSafe.substituteBinderSafeListAt assignment presentation
            membership availableWithin scope.2⟩
end

/-- Root-level supported substitution preserves every authored reflective
scope boundary. -/
theorem HasType.ReflectiveSupportSafeAt.substituteReflectiveScopeSafe
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language source bound pattern type}
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : typed.ReflectiveSupportSafeAt profile support bound)
    (scope : ReflectiveScopeSafeAt profile bound.length pattern) :
    ReflectiveScopeSafeAt profile bound.length
      (ReflectiveContextSupport.substitute profile support
        assignment.assignment bound pattern) := by
  intro presentation membership
  simpa only [ReflectiveContextSupport.substitute] using
    safe.substituteBinderSafeAt assignment presentation membership
      (Nat.le_refl bound.length) (scope presentation membership)

/-- A sorted term may be placed in a larger outer binder context without
changing its de Bruijn indices.  The new binders are less local than every
index already present in the term. -/
theorem HasType.extendOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (outer : List TypeExpr) :
    HasType language free (bound ++ outer) pattern type := by
  have typed' : HasType language free (bound ++ []) pattern type := by
    simpa only [List.append_nil] using typed
  have lifted := typed'.liftBVars_insert
    (inner := bound) (outer := []) (inserted := outer)
  have inert : liftBVars bound.length outer.length pattern = pattern :=
    liftBVars_eq_self_of_isWellScopedAt typed.isWellScopedAt
  simpa only [List.append_nil, inert] using lifted

/-- Supported substitution preserves the concrete binder representation
selected by an authored constructor parameter. -/
private theorem matchesParameterRepresentation_substituteSupportedAt
    (parameter : TermParam) (pattern : Pattern)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (depth : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (ContextSupport.substituteAt support assignment depth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, ContextSupport.substituteAt]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, ContextSupport.substituteAt]
      case multiLambda arity binders body => cases binders <;> simp

/-- Reflective supported substitution preserves the concrete binder
representation selected by an authored constructor parameter. -/
theorem MatchesParameterRepresentation.substituteReflectiveAt
    (profile : ReflectionProfile) (parameter : TermParam) (pattern : Pattern)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (availableDepth : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (ReflectiveContextSupport.substituteAt profile support assignment
          availableDepth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          ReflectiveContextSupport.substituteAt]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          ReflectiveContextSupport.substituteAt]
      case multiLambda arity binders body => cases binders <;> simp

mutual
  /-- Reflective support substitution preserves typing while retaining the
  full lexical context.  `available` is the binder prefix since the nearest
  quote and `sealed` is the lexically present suffix hidden by that quote. -/
  theorem HasType.substituteReflectiveSupportedAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (typed : HasType language source bound pattern type)
      (supported : typed.RespectsReflectiveSupportAt profile available support) :
      HasType language target bound
        (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length pattern) type := by
    cases typed with
    | @bvar bound index type lookup =>
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.bvar (free := target) lookup)
    | @fvar bound name type lookup =>
        obtain ⟨inner, availableShape⟩ := supported name available
          (ReflectiveFreeVariableOccursAt.here
            (lookup := lookup) bound available)
        have replacementTyped := assignment.typed lookup
        have lifted := replacementTyped.liftBVars_insert
          (inner := []) (outer := support name) (inserted := inner)
        have extended := lifted.extendOuter sealed
        have shiftEquality :
            (inner ++ support name).length - (support name).length =
              inner.length := by
          simp only [List.length_append]
          omega
        simpa only [boundShape, ReflectiveContextSupport.substituteAt,
          availableShape, List.nil_append, List.length_nil, shiftEquality]
          using extended
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        cases quoteStatus : ReflectiveContextSupport.isQuoteConstructor
            profile rule.label with
        | false =>
            have argumentsSupported : ∀ name occurrenceSupport,
                ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
                    available name occurrenceSupport →
                  ∃ inner, occurrenceSupport = inner ++ support name := by
              intro name occurrenceSupport occurs
              exact supported name occurrenceSupport
                (ReflectiveFreeVariableOccursAt.constructorOrdinary
                  (membership := membership) (notBare := notBare)
                  quoteStatus occurs)
            simpa [ReflectiveContextSupport.substituteAt, quoteStatus] using
              (HasType.constructor membership notBare
                (argumentsTyped.substituteReflectiveSupportedAt boundShape
                  assignment argumentsSupported))
        | true =>
            have argumentsSupported : ∀ name occurrenceSupport,
                ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
                    [] name occurrenceSupport →
                  ∃ inner, occurrenceSupport = inner ++ support name := by
              intro name occurrenceSupport occurs
              exact supported name occurrenceSupport
                (ReflectiveFreeVariableOccursAt.constructorQuote
                  (membership := membership) (notBare := notBare)
                  quoteStatus occurs)
            have substitutedArguments :=
              ArgumentsHaveTypes.substituteReflectiveSupportedAt
                (available := []) (sealed := bound) (by simp)
                assignment argumentsTyped argumentsSupported
            simpa [ReflectiveContextSupport.substituteAt, quoteStatus] using
              (HasType.constructor membership notBare substitutedArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have bodySupported : bodyTyped.RespectsReflectiveSupportAt
            profile (domain :: available) support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.lambda occurs)
        have substituted :=
          HasType.substituteReflectiveSupportedAt
            (available := domain :: available) (sealed := sealed)
            (by simp only [boundShape, List.cons_append])
            assignment bodyTyped bodySupported
        convert HasType.lambda (binder := binder) substituted using 1
        all_goals
          simp [ReflectiveContextSupport.substituteAt, List.length_cons]
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have bodySupported : bodyTyped.RespectsReflectiveSupportAt
            profile (List.replicate arity domain ++ available) support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.multiLambda occurs)
        have substituted :=
          HasType.substituteReflectiveSupportedAt
            (available := List.replicate arity domain ++ available)
            (sealed := sealed)
            (by simp only [boundShape, List.append_assoc])
            assignment bodyTyped bodySupported
        simpa only [ReflectiveContextSupport.substituteAt,
          List.length_append, List.length_replicate, Nat.add_comm,
          List.append_assoc] using
            (HasType.multiLambda (binders := binders) substituted)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have bodySupported : bodyTyped.RespectsReflectiveSupportAt
            profile (domain :: available) support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.substBody
              (replacementTyped := replacementTyped) occurs)
        have replacementSupported :
            replacementTyped.RespectsReflectiveSupportAt profile available support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.substReplacement
              (bodyTyped := bodyTyped) occurs)
        have substitutedBody :=
          HasType.substituteReflectiveSupportedAt
            (available := domain :: available) (sealed := sealed)
            (by simp only [boundShape, List.cons_append])
            assignment bodyTyped bodySupported
        have substitutedReplacement :=
          HasType.substituteReflectiveSupportedAt
            (available := available) (sealed := sealed)
            boundShape assignment replacementTyped replacementSupported
        convert HasType.subst substitutedBody substitutedReplacement using 1
        all_goals
          simp [ReflectiveContextSupport.substituteAt, List.length_cons]
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have elementsSupported : ∀ name occurrenceSupport,
            ReflectiveElementsFreeVariableOccursAt profile elementsTyped
                available name occurrenceSupport →
              ∃ inner, occurrenceSupport = inner ++ support name := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.collection occurs)
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.collection (rest := rest)
            (elementsTyped.substituteReflectiveSupportedAt boundShape
              assignment elementsSupported))
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        have elementsSupported : ∀ name occurrenceSupport,
            ReflectiveElementsFreeVariableOccursAt profile elementsTyped
                available name occurrenceSupport →
              ∃ inner, occurrenceSupport = inner ++ support name := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveFreeVariableOccursAt.collectionConstructor
              (parameterName := parameterName)
              (membership := membership)
              (parameterShape := parameterShape) occurs)
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.collectionConstructor membership parameterShape
            (elementsTyped.substituteReflectiveSupportedAt boundShape
              assignment elementsSupported))

  theorem ArgumentsHaveTypes.substituteReflectiveSupportedAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (typed : ArgumentsHaveTypes language source bound arguments parameters)
      (supported : ∀ name occurrenceSupport,
        ReflectiveArgumentsFreeVariableOccursAt profile typed
            available name occurrenceSupport →
          ∃ inner, occurrenceSupport = inner ++ support name) :
      ArgumentsHaveTypes language target bound
        (arguments.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        have argumentSupported : argumentTyped.RespectsReflectiveSupportAt
            profile available support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveArgumentsFreeVariableOccursAt.head
              (representation := representation)
              (parameterType := parameterType)
              (argumentsTyped := argumentsTyped) occurs)
        have argumentsSupported : ∀ name occurrenceSupport,
            ReflectiveArgumentsFreeVariableOccursAt profile argumentsTyped
                available name occurrenceSupport →
              ∃ inner, occurrenceSupport = inner ++ support name := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveArgumentsFreeVariableOccursAt.tail
              (representation := representation)
              (parameterType := parameterType)
              (argumentTyped := argumentTyped) occurs)
        exact .cons
          (MatchesParameterRepresentation.substituteReflectiveAt
            _ _ _ _ _ _ representation)
          parameterType
          (argumentTyped.substituteReflectiveSupportedAt
            boundShape assignment argumentSupported)
          (ArgumentsHaveTypes.substituteReflectiveSupportedAt
            (available := available) (sealed := sealed)
            boundShape assignment argumentsTyped argumentsSupported)

  theorem ElementsHaveType.substituteReflectiveSupportedAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (typed : ElementsHaveType language source bound elements elementType)
      (supported : ∀ name occurrenceSupport,
        ReflectiveElementsFreeVariableOccursAt profile typed
            available name occurrenceSupport →
          ∃ inner, occurrenceSupport = inner ++ support name) :
      ElementsHaveType language target bound
        (elements.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        have elementSupported : elementTyped.RespectsReflectiveSupportAt
            profile available support := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveElementsFreeVariableOccursAt.head
              (elementsTyped := elementsTyped) occurs)
        have elementsSupported : ∀ name occurrenceSupport,
            ReflectiveElementsFreeVariableOccursAt profile elementsTyped
                available name occurrenceSupport →
              ∃ inner, occurrenceSupport = inner ++ support name := by
          intro name occurrenceSupport occurs
          exact supported name occurrenceSupport
            (ReflectiveElementsFreeVariableOccursAt.tail
              (elementTyped := elementTyped) occurs)
        exact .cons
          (elementTyped.substituteReflectiveSupportedAt
            boundShape assignment elementSupported)
          (ElementsHaveType.substituteReflectiveSupportedAt
            (available := available) (sealed := sealed)
            boundShape assignment elementsTyped elementsSupported)
end

/-- Root-level reflective substitution preserves typing.  The initial
available support is the complete authored binder context and no suffix is
sealed yet. -/
theorem HasType.substituteReflectiveSupported
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (assignment : SupportedAssignment language source target support)
    (typed : HasType language source bound pattern type)
    (supported : typed.RespectsReflectiveSupportAt profile bound support) :
    HasType language target bound
      (ReflectiveContextSupport.substitute profile support
        assignment.assignment bound pattern) type := by
  simpa only [ReflectiveContextSupport.substitute] using
    HasType.substituteReflectiveSupportedAt
      (available := bound) (sealed := []) (by simp)
      assignment typed supported

mutual
  /-- Reflective supported substitution preserves typing directly from the
  constructor-facing safety certificate emitted by an open canonical
  section.  This avoids flattening the certificate to an occurrence
  predicate and then reconstructing its constructor cases. -/
  theorem HasType.ReflectiveSupportSafeAt.substitute
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      HasType language target bound
        (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length pattern) type := by
    cases safe with
    | @bvar bound index type lookup available _binderImage =>
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.bvar (free := target) lookup)
    | @fvar bound name type lookup available _binderImage shape =>
        obtain ⟨inner, availableShape⟩ := shape
        have replacementTyped := assignment.typed lookup
        have lifted := replacementTyped.liftBVars_insert
          (inner := []) (outer := support name) (inserted := inner)
        have extended := lifted.extendOuter sealed
        have shiftEquality :
            (inner ++ support name).length - (support name).length =
              inner.length := by
          simp only [List.length_append]
          omega
        simpa only [boundShape, ReflectiveContextSupport.substituteAt,
          availableShape, List.nil_append, List.length_nil, shiftEquality]
          using extended
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        available _binderImage quoted argumentsSafe =>
        have substitutedArguments :=
          argumentsSafe.substitute (available := []) (sealed := bound)
            (by simp) assignment
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (HasType.constructor membership notBare substitutedArguments)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped available _binderImage ordinary argumentsSafe =>
        have substitutedArguments :=
          argumentsSafe.substitute boundShape assignment
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (HasType.constructor membership notBare substitutedArguments)
    | @lambda bound binder body domain codomain bodyTyped available _binderImage
        bodySafe =>
        have substituted := bodySafe.substitute
          (available := domain :: available) (sealed := sealed)
          (by simp only [boundShape, List.cons_append]) assignment
        convert HasType.lambda (binder := binder) substituted using 1
        all_goals
          simp [ReflectiveContextSupport.substituteAt, List.length_cons]
    | @multiLambda bound arity binders body domain codomain bodyTyped available
        _binderImage bodySafe =>
        have substituted := bodySafe.substitute
          (available := List.replicate arity domain ++ available)
          (sealed := sealed) (by simp only [boundShape, List.append_assoc])
          assignment
        simpa only [ReflectiveContextSupport.substituteAt,
          List.length_append, List.length_replicate, Nat.add_comm,
          List.append_assoc] using
            (HasType.multiLambda (binders := binders) substituted)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        available _binderImage bodySafe replacementSafe =>
        have substitutedBody := bodySafe.substitute
          (available := domain :: available) (sealed := sealed)
          (by simp only [boundShape, List.cons_append]) assignment
        have substitutedReplacement := replacementSafe.substitute
          (available := available) (sealed := sealed) boundShape assignment
        convert HasType.subst substitutedBody substitutedReplacement using 1
        all_goals
          simp [ReflectiveContextSupport.substituteAt, List.length_cons]
    | @collection bound collectionType elements rest elementType elementsTyped
        available _binderImage elementsSafe =>
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.collection (rest := rest)
            (elementsSafe.substitute boundShape assignment))
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped available
        _binderImage elementsSafe =>
        simpa only [ReflectiveContextSupport.substituteAt] using
          (HasType.collectionConstructor membership parameterShape
            (elementsSafe.substitute boundShape assignment))

  /-- Argument-spine companion to direct support-safe substitution. -/
  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitute
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      ArgumentsHaveTypes language target bound
        (arguments.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) parameters := by
    cases safe with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        _binderImage argumentSafe argumentsSafe =>
        exact .cons
          (MatchesParameterRepresentation.substituteReflectiveAt
            _ _ _ _ _ _ representation)
          parameterType
          (argumentSafe.substitute boundShape assignment)
          (argumentsSafe.substitute boundShape assignment)

  /-- Collection-spine companion to direct support-safe substitution. -/
  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitute
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound available sealed : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      (boundShape : bound = available ++ sealed)
      (assignment : SupportedAssignment language source target support)
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      ElementsHaveType language target bound
        (elements.map (ReflectiveContextSupport.substituteAt profile support
          assignment.assignment available.length)) elementType := by
    cases safe with
    | nil => exact .nil _ _
    | @cons bound element elements elementType elementTyped elementsTyped
        available _binderImage elementSafe elementsSafe =>
        exact .cons
          (elementSafe.substitute boundShape assignment)
          (elementsSafe.substitute boundShape assignment)
end

/-- Root-level direct support-safe substitution. -/
theorem HasType.ReflectiveSupportSafeAt.substituteRoot
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language source bound pattern type}
    (assignment : SupportedAssignment language source target support)
    (safe : typed.ReflectiveSupportSafeAt profile support bound) :
    HasType language target bound
      (ReflectiveContextSupport.substitute profile support
        assignment.assignment bound pattern) type := by
  simpa only [ReflectiveContextSupport.substitute] using
    safe.substitute (available := bound) (sealed := []) (by simp) assignment

/-- Supported reflective substitution maps a genuine open object term to a
genuine open object term in the target free-variable context.  Typing,
locally nameless binder metadata, object-pattern admissibility, and every
authored reflective quotation boundary are preserved by the same operation. -/
theorem HasType.ReflectiveSupportSafeAt.substituteOpenTermWellSorted
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern}
    {sort : LangSort language}
    {typed : HasSort language source bound pattern sort.1}
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : typed.ReflectiveSupportSafeAt profile support bound)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (objectPattern : isObjectPattern pattern = true)
    (scope : ReflectiveScopeSafeAt profile bound.length pattern) :
    ReflectiveWellSorted.OpenTermWellSorted profile language target bound sort
      (ReflectiveContextSupport.substitute profile support
        assignment.assignment bound pattern) := by
  let outputTyped := safe.substituteRoot assignment.toSupportedAssignment
  exact ⟨
    ⟨outputTyped,
      safe.substituteCanonicalBinderMetadata assignment canonical,
      safe.substituteObjectPattern assignment objectPattern,
      outputTyped.isWellScopedAt⟩,
    safe.substituteReflectiveScopeSafe assignment scope⟩

/-- Apply one support-certified structural assignment to an open object at
an arbitrary authored type.  This is the general typed carrier action;
`OpenTerm.substituteReflectiveSupported` below is its base-sort
specialization. -/
def ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (pattern : ReflectiveWellSorted.OpenPattern profile language source bound type)
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : pattern.2.1.1.ReflectiveSupportSafeAt profile support bound) :
    ReflectiveWellSorted.OpenPattern profile language target bound type :=
  let outputTyped := safe.substituteRoot assignment.toSupportedAssignment
  ⟨ReflectiveContextSupport.substitute profile support
      assignment.assignment bound pattern.1,
    ⟨outputTyped,
      safe.substituteCanonicalBinderMetadata assignment pattern.2.1.2.1,
      safe.substituteObjectPattern assignment pattern.2.1.2.2.1,
      outputTyped.isWellScopedAt⟩,
    safe.substituteReflectiveScopeSafe assignment pattern.2.2⟩

@[simp]
theorem ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (pattern : ReflectiveWellSorted.OpenPattern profile language source bound type)
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : pattern.2.1.1.ReflectiveSupportSafeAt profile support bound) :
    (ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported
      pattern assignment safe).1 =
      ReflectiveContextSupport.substitute profile support
        assignment.assignment bound pattern.1 :=
  rfl

/-- Apply one support-certified structural assignment to a genuine typed open
term.  The source and target share the sole authored `LanguageDef`; only the
free-variable context changes.  Reflective quotation safety is supplied by
the source typing derivation and preserved by the existing substitution
theorem, so this construction introduces no raw-pattern side channel. -/
def ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {sort : LangSort language}
    (term : ReflectiveWellSorted.OpenTerm profile language source bound sort)
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : term.2.1.1.ReflectiveSupportSafeAt profile support bound) :
    ReflectiveWellSorted.OpenTerm profile language target bound sort :=
  ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported
    term assignment safe

@[simp]
theorem ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {sort : LangSort language}
    (term : ReflectiveWellSorted.OpenTerm profile language source bound sort)
    (assignment : SupportedOpenAssignment profile language source target support)
    (safe : term.2.1.1.ReflectiveSupportSafeAt profile support bound) :
    (ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported
      term assignment safe).1 =
      ReflectiveContextSupport.substitute profile support
        assignment.assignment bound term.1 :=
  rfl

/-- A parameter that occurs immediately below a reflective quote cannot
depend on any binder outside that quote. -/
theorem HasType.support_eq_nil_of_reflective_occurrence
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language free bound pattern type}
    {available : List TypeExpr} {name : String}
    (supported : typed.RespectsReflectiveSupportAt profile available support)
    (occurs : ReflectiveFreeVariableOccursAt profile typed available name []) :
    support name = [] := by
  obtain ⟨inner, empty⟩ := supported name [] occurs
  exact (List.append_eq_nil_iff.mp empty.symm).2

/-- A typed application of an authored quotation constructor has a unary
argument spine, as certified by the validated reflective presentation. -/
theorem ArgumentsHaveTypes.length_eq_one_of_quote
    {language : LanguageDef} (valid : language.validate = [])
    (profileValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate language profile = [])
    {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {arguments : List Pattern}
    (membership : rule ∈ language.terms)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (quoted : ReflectiveContextSupport.isQuoteConstructor profile
      rule.label = true) :
    arguments.length = 1 := by
  unfold ReflectiveContextSupport.isQuoteConstructor at quoted
  rw [List.any_eq_true] at quoted
  obtain ⟨presentation, presentationMembership, quoteLabel⟩ := quoted
  have quoteLabel' : presentation.quoteConstructor = rule.label := by
    simpa using quoteLabel
  have presentationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      profileValid presentationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil language
      presentation presentationValid
  have quoteMembership : witness.quote ∈ language.terms := by
    have filtered : witness.quote ∈ language.terms.filter
        (fun candidate => candidate.label == presentation.quoteConstructor) := by
      rw [witness.quoteUnique]
      simp
    exact (List.mem_filter.mp filtered).1
  have quoteRuleLabel : witness.quote.label = rule.label := by
    have filtered : witness.quote ∈ language.terms.filter
        (fun candidate => candidate.label == presentation.quoteConstructor) := by
      rw [witness.quoteUnique]
      simp
    exact (beq_iff_eq.mp (List.mem_filter.mp filtered).2).trans quoteLabel'
  have ruleEquality : witness.quote = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
      quoteMembership membership quoteRuleLabel
  calc
    arguments.length = rule.params.length := typed.length_eq
    _ = witness.quote.params.length := by rw [ruleEquality]
    _ = 1 := by simp [witness.quoteParameters]

/-- Quote-aware binder safety for a typed unary quotation gives ordinary
scope for its argument at the reset depth. -/
theorem isWellScopedListAt_zero_of_typed_quote
    {language : LanguageDef} (valid : language.validate = [])
    (profileValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate language profile = [])
    {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {arguments : List Pattern}
    (membership : rule ∈ language.terms)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (quoted : ReflectiveContextSupport.isQuoteConstructor profile
      rule.label = true)
    (scope : ReflectiveScopeSafeAt profile bound.length
      (.apply rule.label arguments)) :
    Pattern.isWellScopedListAt 0 arguments = true := by
  have argumentLength := typed.length_eq_one_of_quote
    valid profileValid membership quoted
  obtain ⟨argument, argumentsShape⟩ := List.length_eq_one_iff.mp argumentLength
  subst arguments
  unfold ReflectiveContextSupport.isQuoteConstructor at quoted
  rw [List.any_eq_true] at quoted
  obtain ⟨presentation, presentationMembership, quoteLabel⟩ := quoted
  have quoteLabel' : presentation.quoteConstructor = rule.label := by
    simpa using quoteLabel
  have quotationSafe := scope presentation presentationMembership
  have argumentSafe :
      binderSafeAt presentation.quoteConstructor 0 argument = true := by
    simpa [binderSafeAt, quoteLabel'] using quotationSafe
  have ordinaryScope : argument.isWellScopedAt 0 = true :=
    isWellScopedAt_of_binderSafeAt presentation.quoteConstructor argumentSafe
  simpa [Pattern.isWellScopedListAt] using ordinaryScope

/-- Lowering the ambient binder depth preserves one quotation check whenever
ordinary local scope is already known at the smaller depth.  The quotation
case itself is independent of the ambient depth; the local-scope premise
controls every non-quotation path. -/
theorem binderSafeAt_of_isWellScopedAt_of_binderSafeAt
    (quoteConstructor : String) {small large : Nat} {pattern : Pattern}
    (scopedAtSmall : pattern.isWellScopedAt small = true)
    (safeAtLarge : binderSafeAt quoteConstructor large pattern = true)
    (depthOrder : small ≤ large) :
    binderSafeAt quoteConstructor small pattern = true := by
  induction pattern using Pattern.inductionOn generalizing small large with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at scopedAtSmall
      simpa [binderSafeAt] using scopedAtSmall
  | hfvar name => simp [binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil => simp [binderSafeAt, binderSafeListAt]
      | cons argument remainder =>
          cases remainder with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                simpa [binderSafeAt] using safeAtLarge
              · have argumentScoped :
                    argument.isWellScopedAt small = true := by
                  simpa [Pattern.isWellScopedAt,
                    Pattern.isWellScopedListAt] using scopedAtSmall
                have argumentSafe :
                    binderSafeAt quoteConstructor large argument = true := by
                  simpa [binderSafeAt, quoted, binderSafeListAt] using
                    safeAtLarge
                simpa [binderSafeAt, quoted, binderSafeListAt] using
                  inductionHypothesis argument (by simp) argumentScoped
                    argumentSafe depthOrder
          | cons second tail =>
              have scopedList :
                  Pattern.isWellScopedListAt small
                    (argument :: second :: tail) = true := by
                simpa [Pattern.isWellScopedAt] using scopedAtSmall
              have safeList :
                  binderSafeListAt quoteConstructor large
                    (argument :: second :: tail) = true := by
                simpa [binderSafeAt] using safeAtLarge
              rw [show binderSafeAt quoteConstructor small
                  (.apply constructor (argument :: second :: tail)) =
                    binderSafeListAt quoteConstructor small
                      (argument :: second :: tail) by rfl]
              rw [binderSafeListAt_eq_true_iff]
              rw [isWellScopedListAt_eq_true_iff] at scopedList
              rw [binderSafeListAt_eq_true_iff] at safeList
              intro member membership
              exact inductionHypothesis member (by simp_all)
                (scopedList member membership) (safeList member membership)
                depthOrder
  | hlambda binder body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at scopedAtSmall
      simp only [binderSafeAt] at safeAtLarge ⊢
      exact inductionHypothesis scopedAtSmall safeAtLarge
        (Nat.add_le_add_right depthOrder 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at scopedAtSmall
      simp only [binderSafeAt] at safeAtLarge ⊢
      exact inductionHypothesis scopedAtSmall safeAtLarge
        (Nat.add_le_add_right depthOrder arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at scopedAtSmall
      simp only [binderSafeAt, Bool.and_eq_true] at safeAtLarge ⊢
      exact ⟨
        bodyInduction scopedAtSmall.1 safeAtLarge.1
          (Nat.add_le_add_right depthOrder 1),
        replacementInduction scopedAtSmall.2 safeAtLarge.2 depthOrder⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at scopedAtSmall
      simp only [binderSafeAt] at safeAtLarge ⊢
      rw [binderSafeListAt_eq_true_iff]
      rw [isWellScopedListAt_eq_true_iff] at scopedAtSmall
      rw [binderSafeListAt_eq_true_iff] at safeAtLarge
      intro element membership
      exact inductionHypothesis element membership
        (scopedAtSmall element membership) (safeAtLarge element membership)
        depthOrder

/-- Every authored reflective presentation sees the contents of a typed
quotation safely at depth zero.  For the selected quotation this is the
direct reset rule; all other presentations are lowered using ordinary scope
of the same unary argument. -/
theorem reflectiveScopeSafeListAt_zero_of_typed_quote
    {language : LanguageDef} (valid : language.validate = [])
    (profileValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate language profile = [])
    {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {arguments : List Pattern}
    (membership : rule ∈ language.terms)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (quoted : ReflectiveContextSupport.isQuoteConstructor profile
      rule.label = true)
    (scope : ReflectiveScopeSafeAt profile bound.length
      (.apply rule.label arguments)) :
    ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor 0 arguments = true := by
  have argumentLength := typed.length_eq_one_of_quote
    valid profileValid membership quoted
  obtain ⟨argument, argumentsShape⟩ := List.length_eq_one_iff.mp argumentLength
  subst arguments
  have ordinaryScope :=
    isWellScopedListAt_zero_of_typed_quote
      valid profileValid membership typed quoted scope
  intro presentation presentationMembership
  have parentSafe := scope presentation presentationMembership
  by_cases selected : rule.label = presentation.quoteConstructor
  · have argumentSafe :
        binderSafeAt presentation.quoteConstructor 0 argument = true := by
      simpa [binderSafeAt, selected] using parentSafe
    simpa [binderSafeListAt] using argumentSafe
  · have argumentSafeAtBound :
        binderSafeAt presentation.quoteConstructor bound.length argument =
          true := by
      simpa [binderSafeAt, binderSafeListAt, selected] using parentSafe
    have argumentScoped : argument.isWellScopedAt 0 = true := by
      simpa [Pattern.isWellScopedListAt] using ordinaryScope
    have argumentSafe := binderSafeAt_of_isWellScopedAt_of_binderSafeAt
      presentation.quoteConstructor argumentScoped argumentSafeAtBound
        (Nat.zero_le _)
    simpa [binderSafeListAt] using argumentSafe

/-- An ordinary authored constructor preserves the ambient reflective scope
of its entire argument spine.  This is the negative companion to the reset
lemma above. -/
theorem reflectiveScopeSafeListAt_of_nonquote
    {bound : List TypeExpr}
    {rule : GrammarRule} {arguments : List Pattern}
    (ordinary : ReflectiveContextSupport.isQuoteConstructor profile
      rule.label = false)
    (scope : ReflectiveScopeSafeAt profile bound.length
      (.apply rule.label arguments)) :
    ∀ presentation ∈ profile.presentations,
      binderSafeListAt presentation.quoteConstructor bound.length
        arguments = true := by
  intro presentation presentationMembership
  have notSelected : rule.label ≠ presentation.quoteConstructor := by
    intro selected
    have selectedByLanguage :
        ReflectiveContextSupport.isQuoteConstructor profile rule.label =
          true := by
      unfold ReflectiveContextSupport.isQuoteConstructor
      rw [List.any_eq_true]
      exact ⟨presentation, presentationMembership, by simp [selected]⟩
    rw [ordinary] at selectedByLanguage
    cases selectedByLanguage
  have parentSafe := scope presentation presentationMembership
  cases arguments with
  | nil => simp [binderSafeListAt]
  | cons argument arguments =>
      cases arguments with
      | nil =>
          simpa [binderSafeAt, binderSafeListAt, notSelected] using parentSafe
      | cons next rest =>
          simpa [binderSafeAt] using parentSafe

mutual
  /-- Supported structural substitution preserves the authored typing
  judgment.  This is the dependent-context form of weakening: each free
  variable is instantiated at its declared support and lifted through the
  exact inner prefix recorded by the source derivation. -/
  theorem HasType.substituteSupported
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (assignment : SupportedAssignment language source target support)
      (typed : HasType language source bound pattern type)
      (supported : typed.RespectsSupport support) :
      HasType language target bound
        (ContextSupport.substituteAt support assignment.assignment
          bound.length pattern) type := by
    cases typed with
    | @bvar bound index type lookup =>
        simpa only [ContextSupport.substituteAt] using
          (HasType.bvar (free := target) lookup)
    | @fvar bound name type lookup =>
        obtain ⟨inner, boundShape⟩ := supported name bound
          (FreeVariableOccursAt.here (lookup := lookup))
        have replacementTyped := assignment.typed lookup
        have lifted := replacementTyped.liftBVars_insert
          (inner := []) (outer := support name) (inserted := inner)
        have shiftEquality :
            (inner ++ support name).length - (support name).length =
              inner.length := by
          simp only [List.length_append]
          omega
        simpa only [ContextSupport.substituteAt, boundShape,
          List.nil_append, List.length_nil, shiftEquality] using lifted
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        have argumentsSupported : ∀ name occurrenceBound,
            ArgumentsFreeVariableOccursAt argumentsTyped name occurrenceBound →
              ∃ inner, occurrenceBound = inner ++ support name := by
          intro name occurrenceBound occurs
          exact supported name occurrenceBound
            (FreeVariableOccursAt.constructor
              (membership := membership) (notBare := notBare) occurs)
        simpa only [ContextSupport.substituteAt] using
          (HasType.constructor membership notBare
            (argumentsTyped.substituteSupported assignment argumentsSupported))
    | @lambda bound binder body domain codomain bodyTyped =>
        have bodySupported : bodyTyped.RespectsSupport support := by
          intro name occurrenceBound membership
          exact supported name occurrenceBound
            (FreeVariableOccursAt.lambda membership)
        have substituted := bodyTyped.substituteSupported assignment bodySupported
        simpa only [ContextSupport.substituteAt, List.length_cons,
          Nat.add_comm] using
            (HasType.lambda (binder := binder) substituted)
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have bodySupported : bodyTyped.RespectsSupport support := by
          intro name occurrenceBound membership
          exact supported name occurrenceBound
            (FreeVariableOccursAt.multiLambda membership)
        have substituted := bodyTyped.substituteSupported assignment bodySupported
        simpa only [ContextSupport.substituteAt, List.length_append,
          List.length_replicate, Nat.add_comm] using
            (HasType.multiLambda (binders := binders) substituted)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have supportedParts :
            bodyTyped.RespectsSupport support ∧
              replacementTyped.RespectsSupport support := by
          constructor
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (FreeVariableOccursAt.substBody
                (replacementTyped := replacementTyped) membership)
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (FreeVariableOccursAt.substReplacement
                (bodyTyped := bodyTyped) membership)
        have substitutedBody := bodyTyped.substituteSupported assignment
          supportedParts.1
        have substitutedReplacement :=
          replacementTyped.substituteSupported assignment supportedParts.2
        simpa only [ContextSupport.substituteAt, List.length_cons,
          Nat.add_comm] using
            HasType.subst substitutedBody substitutedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have elementsSupported : ∀ name occurrenceBound,
            ElementsFreeVariableOccursAt elementsTyped name occurrenceBound →
              ∃ inner, occurrenceBound = inner ++ support name := by
          intro name occurrenceBound occurs
          exact supported name occurrenceBound
            (FreeVariableOccursAt.collection occurs)
        simpa only [ContextSupport.substituteAt] using
          (HasType.collection (rest := rest)
            (elementsTyped.substituteSupported assignment elementsSupported))
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        have elementsSupported : ∀ name occurrenceBound,
            ElementsFreeVariableOccursAt elementsTyped name occurrenceBound →
              ∃ inner, occurrenceBound = inner ++ support name := by
          intro name occurrenceBound occurs
          exact supported name occurrenceBound
            (FreeVariableOccursAt.collectionConstructor
              (parameterName := parameterName)
              (membership := membership)
              (parameterShape := parameterShape) occurs)
        simpa only [ContextSupport.substituteAt] using
          (HasType.collectionConstructor membership parameterShape
            (elementsTyped.substituteSupported assignment elementsSupported))

  theorem ArgumentsHaveTypes.substituteSupported
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (assignment : SupportedAssignment language source target support)
      (typed : ArgumentsHaveTypes language source bound arguments parameters)
      (supported : ∀ name occurrenceBound,
        ArgumentsFreeVariableOccursAt typed name occurrenceBound →
          ∃ inner, occurrenceBound = inner ++ support name) :
      ArgumentsHaveTypes language target bound
        (arguments.map (ContextSupport.substituteAt support
          assignment.assignment bound.length)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        have supportedParts :
            argumentTyped.RespectsSupport support ∧
              (∀ name occurrenceBound,
                ArgumentsFreeVariableOccursAt argumentsTyped
                    name occurrenceBound →
                  ∃ inner, occurrenceBound = inner ++ support name) := by
          constructor
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (ArgumentsFreeVariableOccursAt.head
                (representation := representation)
                (parameterType := parameterType)
                (argumentsTyped := argumentsTyped) membership)
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (ArgumentsFreeVariableOccursAt.tail
                (representation := representation)
                (parameterType := parameterType)
                (argumentTyped := argumentTyped) membership)
        exact .cons
          (matchesParameterRepresentation_substituteSupportedAt
            _ _ _ _ _ representation)
          parameterType
          (argumentTyped.substituteSupported assignment supportedParts.1)
          (ArgumentsHaveTypes.substituteSupported
            (bound := bound) assignment argumentsTyped supportedParts.2)

  theorem ElementsHaveType.substituteSupported
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (assignment : SupportedAssignment language source target support)
      (typed : ElementsHaveType language source bound elements elementType)
      (supported : ∀ name occurrenceBound,
        ElementsFreeVariableOccursAt typed name occurrenceBound →
          ∃ inner, occurrenceBound = inner ++ support name) :
      ElementsHaveType language target bound
        (elements.map (ContextSupport.substituteAt support
          assignment.assignment bound.length)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        have supportedParts :
            elementTyped.RespectsSupport support ∧
              (∀ name occurrenceBound,
                ElementsFreeVariableOccursAt elementsTyped
                    name occurrenceBound →
                  ∃ inner, occurrenceBound = inner ++ support name) := by
          constructor
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (ElementsFreeVariableOccursAt.head
                (elementsTyped := elementsTyped) membership)
          · intro name occurrenceBound membership
            exact supported name occurrenceBound
              (ElementsFreeVariableOccursAt.tail
                (elementTyped := elementTyped) membership)
        exact .cons
          (elementTyped.substituteSupported assignment supportedParts.1)
          (ElementsHaveType.substituteSupported
            (bound := bound) assignment elementsTyped supportedParts.2)
end

end WellSorted

end Mettapedia.GSLT.LanguageDef
