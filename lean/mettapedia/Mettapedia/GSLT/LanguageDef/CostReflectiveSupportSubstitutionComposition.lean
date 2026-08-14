import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportSubstitution

/-!
# Structural composition for reflective support substitution

This module supplies binder weakening, ambient coeffect extension, and the
structural composition theorem over the proof-relevant alignment algebra.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

namespace WellSorted

/-- De Bruijn lifting preserves the representation form selected by an
authored constructor parameter. -/
private theorem matchesParameterRepresentation_reflectiveSupport_liftBVars
    (parameter : TermParam) (pattern : Pattern) (cutoff shift : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (liftBVars cutoff shift pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, liftBVars]
      case lambda binder body =>
        cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, liftBVars]
      case multiLambda arity binders body =>
        cases binders <;> simp

/-- Inserting binders and lifting their de Bruijn indices preserves a
reflective-support certificate without changing its coeffect.  The generated
mutual recursor quantifies the certificate's actual `binderImage` index. -/
theorem HasType.ReflectiveSupportSafeAt.liftBVars_insert
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language free bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ (inner outer inserted : List TypeExpr), bound = inner ++ outer →
      ∃ liftedTyped : HasType language free ((inner ++ inserted) ++ outer)
          (liftBVars inner.length inserted.length pattern) type,
        liftedTyped.ReflectiveSupportSafeAt profile support available
          binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound} {pattern} {type} _ available binderImage _ =>
      ∀ inner outer inserted, bound = inner ++ outer →
        ∃ liftedTyped : HasType language free ((inner ++ inserted) ++ outer)
            (liftBVars inner.length inserted.length pattern) type,
          liftedTyped.ReflectiveSupportSafeAt profile support available
            binderImage)
    (motive_2 := fun {bound} {arguments} {parameters} _ available binderImage _ =>
      ∀ inner outer inserted, bound = inner ++ outer →
        ∃ liftedTyped : ArgumentsHaveTypes language free
            ((inner ++ inserted) ++ outer)
            (arguments.map (liftBVars inner.length inserted.length)) parameters,
          liftedTyped.ReflectiveSupportSafeAt profile support available
            binderImage)
    (motive_3 := fun {bound} {elements} {elementType} _ available binderImage _ =>
      ∀ inner outer inserted, bound = inner ++ outer →
        ∃ liftedTyped : ElementsHaveType language free
            ((inner ++ inserted) ++ outer)
            (elements.map (liftBVars inner.length inserted.length)) elementType,
          liftedTyped.ReflectiveSupportSafeAt profile support available
            binderImage)
    (by
      intro bound index type lookup available binderImage inner outer inserted
        boundEquality
      subst bound
      by_cases beyond : index ≥ inner.length
      · have liftedTyped : HasType language free ((inner ++ inserted) ++ outer)
            (.bvar (index + inserted.length)) type := by
          simpa [liftBVars, beyond] using
            (HasType.bvar (free := free) lookup).liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)
        cases liftedTyped with
        | bvar lookup' =>
            have lookup'' :
                (inner ++ (inserted ++ outer))[index + inserted.length]? =
                  some type := by
              simpa only [List.append_assoc] using lookup'
            simpa [liftBVars, beyond] using
              (⟨HasType.bvar (free := free) lookup'',
                HasType.ReflectiveSupportSafeAt.bvar
                  (profile := profile) (support := support)
                  (binderImage := binderImage) lookup'' available⟩)
      · have liftedTyped : HasType language free ((inner ++ inserted) ++ outer)
            (.bvar index) type := by
          simpa [liftBVars, beyond] using
            (HasType.bvar (free := free) lookup).liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)
        cases liftedTyped with
        | bvar lookup' =>
            have lookup'' : (inner ++ (inserted ++ outer))[index]? =
                some type := by
              simpa only [List.append_assoc] using lookup'
            simpa [liftBVars, beyond] using
              (⟨HasType.bvar (free := free) lookup'',
                HasType.ReflectiveSupportSafeAt.bvar
                  (profile := profile) (support := support)
                  (binderImage := binderImage) lookup'' available⟩))
    (by
      intro bound name type lookup available binderImage shape inner outer
        inserted boundEquality
      subst bound
      let liftedTyped : HasType language free ((inner ++ inserted) ++ outer)
          (.fvar name) type := HasType.fvar lookup
      simpa only [liftBVars] using
        (⟨liftedTyped, HasType.ReflectiveSupportSafeAt.fvar
          (binderImage := binderImage) lookup available shape⟩))
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        binderImage quoted argumentsSafe argumentsIH inner outer inserted
        boundEquality
      subst bound
      obtain ⟨liftedArguments, liftedSafe⟩ :=
        argumentsIH inner outer inserted rfl
      let liftedTyped := HasType.constructor membership notBare liftedArguments
      simpa only [liftBVars] using
        (⟨liftedTyped, HasType.ReflectiveSupportSafeAt.constructorQuote
          (membership := membership) (notBare := notBare) quoted liftedSafe⟩))
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        binderImage ordinary argumentsSafe argumentsIH inner outer inserted
        boundEquality
      subst bound
      obtain ⟨liftedArguments, liftedSafe⟩ :=
        argumentsIH inner outer inserted rfl
      let liftedTyped := HasType.constructor membership notBare liftedArguments
      simpa only [liftBVars] using
        (⟨liftedTyped, HasType.ReflectiveSupportSafeAt.constructorOrdinary
          (membership := membership) (notBare := notBare) ordinary liftedSafe⟩))
    (by
      intro bound binder body domain codomain bodyTyped available binderImage
        bodySafe bodyIH inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedBody, liftedBodySafe⟩ :=
        bodyIH (domain :: inner) outer inserted rfl
      let finalBodyTyped : HasType language free
          (domain :: ((inner ++ inserted) ++ outer))
          (liftBVars (inner.length + 1) inserted.length body) codomain := by
        simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
          liftedBody
      have finalBodySafe : finalBodyTyped.ReflectiveSupportSafeAt
          profile support (binderImage domain :: available) binderImage := by
        apply HasType.ReflectiveSupportSafeAt.castTyping
        simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
          liftedBodySafe
      let liftedTyped := HasType.lambda (binder := binder) finalBodyTyped
      have liftedSafe : liftedTyped.ReflectiveSupportSafeAt profile support
          available binderImage := .lambda finalBodySafe
      simpa only [liftBVars] using (⟨liftedTyped, liftedSafe⟩))
    (by
      intro bound arity binders body domain codomain bodyTyped available
        binderImage bodySafe bodyIH inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedBody, liftedBodySafe⟩ :=
        bodyIH (List.replicate arity domain ++ inner) outer inserted (by
          simp only [List.append_assoc])
      have finalBodyTyped : HasType language free
          (List.replicate arity domain ++ ((inner ++ inserted) ++ outer))
          (liftBVars (inner.length + arity) inserted.length body) codomain := by
        simpa only [List.append_assoc, List.length_append,
          List.length_replicate, Nat.add_comm] using liftedBody
      have finalBodySafe : finalBodyTyped.ReflectiveSupportSafeAt profile support
          (List.replicate arity (binderImage domain) ++ available)
          binderImage := by
        apply HasType.ReflectiveSupportSafeAt.castTyping
        simpa only [List.append_assoc, List.length_append,
          List.length_replicate, Nat.add_comm] using liftedBodySafe
        exact finalBodyTyped
      let liftedTyped := HasType.multiLambda (binders := binders) finalBodyTyped
      have liftedSafe : liftedTyped.ReflectiveSupportSafeAt profile support
          available binderImage := .multiLambda finalBodySafe
      simpa only [liftBVars] using (⟨liftedTyped, liftedSafe⟩))
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        available binderImage bodySafe replacementSafe bodyIH replacementIH
        inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedBody, liftedBodySafe⟩ :=
        bodyIH (domain :: inner) outer inserted rfl
      obtain ⟨liftedReplacement, liftedReplacementSafe⟩ :=
        replacementIH inner outer inserted rfl
      have liftedBody' : HasType language free
          (domain :: ((inner ++ inserted) ++ outer))
          (liftBVars (inner.length + 1) inserted.length body) codomain := by
        simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
          liftedBody
      have liftedBodySafe' : liftedBody'.ReflectiveSupportSafeAt profile support
          (binderImage domain :: available) binderImage := by
        apply HasType.ReflectiveSupportSafeAt.castTyping
        simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
          liftedBodySafe
      let liftedTyped := HasType.subst liftedBody' liftedReplacement
      have liftedSafe : liftedTyped.ReflectiveSupportSafeAt profile support
          available binderImage := .subst liftedBodySafe' liftedReplacementSafe
      simpa only [liftBVars, List.length_cons, Nat.add_comm] using
        (⟨liftedTyped, liftedSafe⟩))
    (by
      intro bound collectionType elements rest elementType elementsTyped
        available binderImage elementsSafe elementsIH inner outer inserted
        boundEquality
      subst bound
      obtain ⟨liftedElements, liftedSafe⟩ :=
        elementsIH inner outer inserted rfl
      let liftedTyped := HasType.collection (collectionType := collectionType)
        (rest := rest) liftedElements
      simpa only [liftBVars] using
        (⟨liftedTyped, HasType.ReflectiveSupportSafeAt.collection liftedSafe⟩))
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available binderImage
        elementsSafe elementsIH inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedElements, liftedSafe⟩ :=
        elementsIH inner outer inserted rfl
      let liftedTyped := HasType.collectionConstructor (rest := rest)
        membership parameterShape liftedElements
      simpa only [liftBVars] using
        (⟨liftedTyped, HasType.ReflectiveSupportSafeAt.collectionConstructor
          (membership := membership) (parameterShape := parameterShape)
          liftedSafe⟩))
    (by
      intro bound available binderImage inner outer inserted boundEquality
      subst bound
      let liftedTyped := ArgumentsHaveTypes.nil
        (language := language) (free := free)
        (bound := ((inner ++ inserted) ++ outer))
      exact ⟨liftedTyped, .nil _ _⟩)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        binderImage argumentSafe argumentsSafe argumentIH argumentsIH
        inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedArgument, liftedArgumentSafe⟩ :=
        argumentIH inner outer inserted rfl
      obtain ⟨liftedArguments, liftedArgumentsSafe⟩ :=
        argumentsIH inner outer inserted rfl
      let liftedRepresentation :=
        matchesParameterRepresentation_reflectiveSupport_liftBVars
          parameter argument inner.length inserted.length representation
      let liftedTyped := ArgumentsHaveTypes.cons liftedRepresentation
        parameterType liftedArgument liftedArguments
      exact ⟨liftedTyped, .cons (representation := liftedRepresentation)
        (parameterType := parameterType) liftedArgumentSafe
        liftedArgumentsSafe⟩)
    (by
      intro bound elementType available binderImage inner outer inserted
        boundEquality
      subst bound
      let liftedTyped := ElementsHaveType.nil
        (language := language) (free := free)
        ((inner ++ inserted) ++ outer) elementType
      exact ⟨liftedTyped, .nil _ _ _⟩)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available binderImage elementSafe elementsSafe elementIH elementsIH
        inner outer inserted boundEquality
      subst bound
      obtain ⟨liftedElement, liftedElementSafe⟩ :=
        elementIH inner outer inserted rfl
      obtain ⟨liftedElements, liftedElementsSafe⟩ :=
        elementsIH inner outer inserted rfl
      let liftedTyped := ElementsHaveType.cons liftedElement liftedElements
      exact ⟨liftedTyped, .cons liftedElementSafe liftedElementsSafe⟩)
    safe

/-- Argument-spine companion to proof-relevant binder insertion. -/
theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.liftBVars_insert
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    {typed : ArgumentsHaveTypes language free bound arguments parameters}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ (inner outer inserted : List TypeExpr), bound = inner ++ outer →
      ∃ liftedTyped : ArgumentsHaveTypes language free
          ((inner ++ inserted) ++ outer)
          (arguments.map (liftBVars inner.length inserted.length)) parameters,
        liftedTyped.ReflectiveSupportSafeAt profile support available
          binderImage := by
  exact ArgumentsHaveTypes.ReflectiveSupportSafeAt.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun {bound} {arguments} {parameters} _ available binderImage _ =>
      ∀ inner outer inserted, bound = inner ++ outer →
        ∃ liftedTyped : ArgumentsHaveTypes language free
            ((inner ++ inserted) ++ outer)
            (arguments.map (liftBVars inner.length inserted.length)) parameters,
          liftedTyped.ReflectiveSupportSafeAt profile support available
            binderImage)
    (motive_3 := fun _ _ _ _ => True)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by
      intro bound available binderImage inner outer inserted boundEquality
      subst bound
      let liftedTyped := ArgumentsHaveTypes.nil
        (language := language) (free := free)
        (bound := ((inner ++ inserted) ++ outer))
      exact ⟨liftedTyped, .nil _ _⟩)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        binderImage argumentSafe argumentsSafe _ argumentsIH inner outer
        inserted boundEquality
      subst bound
      obtain ⟨liftedArgument, liftedArgumentSafe⟩ :=
        argumentSafe.liftBVars_insert inner outer inserted rfl
      obtain ⟨liftedArguments, liftedArgumentsSafe⟩ :=
        argumentsIH inner outer inserted rfl
      let liftedRepresentation :=
        matchesParameterRepresentation_reflectiveSupport_liftBVars
          parameter argument inner.length inserted.length representation
      let liftedTyped := ArgumentsHaveTypes.cons liftedRepresentation
        parameterType liftedArgument liftedArguments
      exact ⟨liftedTyped, .cons (representation := liftedRepresentation)
        (parameterType := parameterType) liftedArgumentSafe
        liftedArgumentsSafe⟩)
    (by intros; trivial) (by intros; trivial) safe

/-- Collection-spine companion to proof-relevant binder insertion. -/
theorem ElementsHaveType.ReflectiveSupportSafeAt.liftBVars_insert
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    {typed : ElementsHaveType language free bound elements elementType}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ (inner outer inserted : List TypeExpr), bound = inner ++ outer →
      ∃ liftedTyped : ElementsHaveType language free
          ((inner ++ inserted) ++ outer)
          (elements.map (liftBVars inner.length inserted.length)) elementType,
        liftedTyped.ReflectiveSupportSafeAt profile support available
          binderImage := by
  exact ElementsHaveType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun {bound} {elements} {elementType} _ available binderImage _ =>
      ∀ inner outer inserted, bound = inner ++ outer →
        ∃ liftedTyped : ElementsHaveType language free
            ((inner ++ inserted) ++ outer)
            (elements.map (liftBVars inner.length inserted.length)) elementType,
          liftedTyped.ReflectiveSupportSafeAt profile support available
            binderImage)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (by
      intro bound elementType available binderImage inner outer inserted
        boundEquality
      subst bound
      let liftedTyped := ElementsHaveType.nil
        (language := language) (free := free)
        ((inner ++ inserted) ++ outer) elementType
      exact ⟨liftedTyped, .nil _ _ _⟩)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available binderImage elementSafe elementsSafe _ elementsIH inner outer
        inserted boundEquality
      subst bound
      obtain ⟨liftedElement, liftedElementSafe⟩ :=
        elementSafe.liftBVars_insert inner outer inserted rfl
      obtain ⟨liftedElements, liftedElementsSafe⟩ :=
        elementsIH inner outer inserted rfl
      let liftedTyped := ElementsHaveType.cons liftedElement liftedElements
      exact ⟨liftedTyped, .cons liftedElementSafe liftedElementsSafe⟩)
    safe

/-- Adding an unused outer typing context preserves reflective support safety.
The syntax is unchanged because a well-scoped term has no de Bruijn index at
or beyond the old context length. -/
theorem HasType.ReflectiveSupportSafeAt.extendOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language free bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage)
    (outer : List TypeExpr) :
    ∃ extendedTyped : HasType language free (bound ++ outer) pattern type,
      extendedTyped.ReflectiveSupportSafeAt profile support available
        binderImage := by
  have typed' : HasType language free (bound ++ []) pattern type := by
    simpa only [List.append_nil] using typed
  have safe' : typed'.ReflectiveSupportSafeAt profile support available
      binderImage := by
    apply HasType.ReflectiveSupportSafeAt.castBound
      (source := typed) (target := typed')
    · simp only [List.append_nil]
    · exact safe
  obtain ⟨liftedTyped, liftedSafe⟩ :=
    HasType.ReflectiveSupportSafeAt.liftBVars_insert
      (profile := profile) (language := language) (free := free)
      (support := support) (pattern := pattern) (type := type)
      (typed := typed') (available := available)
      (binderImage := binderImage) safe' bound [] outer rfl
  have inert : liftBVars bound.length outer.length pattern = pattern :=
    liftBVars_eq_self_of_isWellScopedAt typed.isWellScopedAt
  let finalTyped : HasType language free (bound ++ outer) pattern type := by
    simpa only [List.append_nil, inert] using liftedTyped
  have finalSafe : finalTyped.ReflectiveSupportSafeAt profile support available
      binderImage := by
    apply HasType.ReflectiveSupportSafeAt.castTyping
    simpa only [List.append_nil, inert] using liftedSafe
  exact ⟨finalTyped, finalSafe⟩

/-- De Bruijn lifting changes no free-variable name. -/
theorem mem_freeFvarNames_liftBVars_iff
    (name : String) (cutoff shift : Nat) (pattern : Pattern) :
    name ∈ (liftBVars cutoff shift pattern).freeFvarNames ↔
      name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [liftBVars, Pattern.freeFvarNames, shifted]
  | hfvar variableName => simp [liftBVars, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, Pattern.freeFvarNames, List.mem_flatMap,
        List.mem_map]
      constructor
      · rintro ⟨normalized, ⟨argument, membership, rfl⟩, support⟩
        exact ⟨argument, membership,
          (inductionHypothesis argument membership cutoff).mp support⟩
      · rintro ⟨argument, membership, support⟩
        exact ⟨liftBVars cutoff shift argument,
          ⟨argument, membership, rfl⟩,
          (inductionHypothesis argument membership cutoff).mpr support⟩
  | hlambda binder body inductionHypothesis =>
      simpa [liftBVars, Pattern.freeFvarNames] using
        inductionHypothesis (cutoff + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [liftBVars, Pattern.freeFvarNames] using
        inductionHypothesis (cutoff + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [liftBVars, Pattern.freeFvarNames,
        bodyInduction (cutoff + 1), replacementInduction cutoff]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, Pattern.freeFvarNames, List.mem_append,
        List.mem_flatMap, List.mem_map]
      constructor
      · rintro (⟨normalized, ⟨element, membership, rfl⟩, support⟩ | support)
        · exact Or.inl ⟨element, membership,
            (inductionHypothesis element membership cutoff).mp support⟩
        · exact Or.inr support
      · rintro (⟨element, membership, support⟩ | support)
        · exact Or.inl ⟨liftBVars cutoff shift element,
            ⟨element, membership, rfl⟩,
            (inductionHypothesis element membership cutoff).mpr support⟩
        · exact Or.inr support

/-- Insert one ambient coeffect prefix after the binders introduced by the
current syntax.  The finite `suffixes` premise is the sharp condition. -/
private theorem HasType.ReflectiveSupportSafeAt.insertAvailablePrefixAt
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language free bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ (inside root inserted : List TypeExpr), available = inside ++ root →
      (∀ name, name ∈ pattern.freeFvarNames →
        ∃ inner, root = inner ++ support name) →
      typed.ReflectiveSupportSafeAt profile support
        ((inside ++ inserted) ++ root) binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {_} {pattern} {_} typed available binderImage _ =>
      ∀ inside root inserted, available = inside ++ root →
        (∀ name, name ∈ pattern.freeFvarNames →
          ∃ inner, root = inner ++ support name) →
        typed.ReflectiveSupportSafeAt profile support
          ((inside ++ inserted) ++ root) binderImage)
    (motive_2 := fun {_} {arguments} {_} typed available binderImage _ =>
      ∀ inside root inserted, available = inside ++ root →
        (∀ name, name ∈ arguments.flatMap Pattern.freeFvarNames →
          ∃ inner, root = inner ++ support name) →
        typed.ReflectiveSupportSafeAt profile support
          ((inside ++ inserted) ++ root) binderImage)
    (motive_3 := fun {_} {elements} {_} typed available binderImage _ =>
      ∀ inside root inserted, available = inside ++ root →
        (∀ name, name ∈ elements.flatMap Pattern.freeFvarNames →
          ∃ inner, root = inner ++ support name) →
        typed.ReflectiveSupportSafeAt profile support
          ((inside ++ inserted) ++ root) binderImage)
    (by
      intro bound index type lookup available binderImage inside root inserted
        availableShape suffixes
      exact .bvar lookup _)
    (by
      intro bound name type lookup available binderImage shape inside root
        inserted availableShape suffixes
      obtain ⟨inner, rootShape⟩ := suffixes name (by
        simp [Pattern.freeFvarNames])
      exact .fvar lookup _ ⟨inside ++ inserted ++ inner, by
        simp [rootShape, List.append_assoc]⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        binderImage quoted argumentsSafe argumentsIH inside root inserted
        availableShape suffixes
      exact .constructorQuote (membership := membership) (notBare := notBare)
        quoted argumentsSafe)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        binderImage ordinary argumentsSafe argumentsIH inside root inserted
        availableShape suffixes
      exact .constructorOrdinary (membership := membership) (notBare := notBare)
        ordinary (argumentsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simpa only [Pattern.freeFvarNames] using nameMembership)))
    (by
      intro bound binder body domain codomain bodyTyped available binderImage
        bodySafe bodyIH inside root inserted availableShape suffixes
      have bodyAvailableShape : binderImage domain :: available =
          (binderImage domain :: inside) ++ root := by
        simp only [List.cons_append, availableShape]
      exact .lambda (by
        simpa only [List.cons_append] using
          bodyIH (binderImage domain :: inside) root inserted
            bodyAvailableShape (by
              intro name nameMembership
              apply suffixes name
              simpa only [Pattern.freeFvarNames] using nameMembership)))
    (by
      intro bound arity binders body domain codomain bodyTyped available
        binderImage bodySafe bodyIH inside root inserted availableShape suffixes
      have bodyAvailableShape :
          List.replicate arity (binderImage domain) ++ available =
            (List.replicate arity (binderImage domain) ++ inside) ++ root := by
        simp only [availableShape, List.append_assoc]
      have prefixedBody := bodyIH
        (List.replicate arity (binderImage domain) ++ inside) root inserted
        bodyAvailableShape (by
          intro name nameMembership
          apply suffixes name
          simpa only [Pattern.freeFvarNames] using nameMembership)
      exact .multiLambda (by
        simpa only [List.append_assoc] using prefixedBody))
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        available binderImage bodySafe replacementSafe bodyIH replacementIH
        inside root inserted availableShape suffixes
      have bodyAvailableShape : binderImage domain :: available =
          (binderImage domain :: inside) ++ root := by
        simp only [List.cons_append, availableShape]
      exact .subst
        (by
          simpa only [List.cons_append] using
            bodyIH (binderImage domain :: inside) root inserted
              bodyAvailableShape (by
                intro name nameMembership
                apply suffixes name
                simp only [Pattern.freeFvarNames, List.mem_append]
                exact Or.inl nameMembership))
        (replacementIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [Pattern.freeFvarNames, List.mem_append]
          exact Or.inr nameMembership)))
    (by
      intro bound collectionType elements rest elementType elementsTyped
        available binderImage elementsSafe elementsIH inside root inserted
        availableShape suffixes
      exact .collection (elementsIH inside root inserted availableShape (by
        intro name nameMembership
        apply suffixes name
        simp only [Pattern.freeFvarNames, List.mem_append]
        exact Or.inl nameMembership)))
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available binderImage
        elementsSafe elementsIH inside root inserted availableShape suffixes
      exact .collectionConstructor (membership := membership)
        (parameterShape := parameterShape)
        (elementsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [Pattern.freeFvarNames, List.mem_append]
          exact Or.inl nameMembership)))
    (by
      intro bound available binderImage inside root inserted availableShape
        suffixes
      exact .nil _ _)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        binderImage argumentSafe argumentsSafe argumentIH argumentsIH inside
        root inserted availableShape suffixes
      exact .cons (representation := representation)
        (parameterType := parameterType)
        (argumentIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inl nameMembership))
        (argumentsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr nameMembership)))
    (by
      intro bound elementType available binderImage inside root inserted
        availableShape suffixes
      exact .nil _ _ _)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available binderImage elementSafe elementsSafe elementIH elementsIH
        inside root inserted availableShape suffixes
      exact .cons
        (elementIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inl nameMembership))
        (elementsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr nameMembership)))
    safe

private theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.insertAvailablePrefixAt
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    {typed : ArgumentsHaveTypes language free bound arguments parameters}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ inside root inserted, available = inside ++ root →
      (∀ name, name ∈ arguments.flatMap Pattern.freeFvarNames →
        ∃ inner, root = inner ++ support name) →
      typed.ReflectiveSupportSafeAt profile support
        ((inside ++ inserted) ++ root) binderImage := by
  exact ArgumentsHaveTypes.ReflectiveSupportSafeAt.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun {_} {arguments} {_} typed available binderImage _ =>
      ∀ inside root inserted, available = inside ++ root →
        (∀ name, name ∈ arguments.flatMap Pattern.freeFvarNames →
          ∃ inner, root = inner ++ support name) →
        typed.ReflectiveSupportSafeAt profile support
          ((inside ++ inserted) ++ root) binderImage)
    (motive_3 := fun _ _ _ _ => True)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by
      intro bound available binderImage inside root inserted availableShape
        suffixes
      exact .nil _ _)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        binderImage argumentSafe argumentsSafe _ argumentsIH inside root
        inserted availableShape suffixes
      exact .cons (representation := representation)
        (parameterType := parameterType)
        (argumentSafe.insertAvailablePrefixAt inside root inserted
          availableShape (by
            intro name nameMembership
            apply suffixes name
            simp only [List.flatMap_cons, List.mem_append]
            exact Or.inl nameMembership))
        (argumentsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr nameMembership)))
    (by intros; trivial) (by intros; trivial) safe

private theorem ElementsHaveType.ReflectiveSupportSafeAt.insertAvailablePrefixAt
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    {typed : ElementsHaveType language free bound elements elementType}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage) :
    ∀ inside root inserted, available = inside ++ root →
      (∀ name, name ∈ elements.flatMap Pattern.freeFvarNames →
        ∃ inner, root = inner ++ support name) →
      typed.ReflectiveSupportSafeAt profile support
        ((inside ++ inserted) ++ root) binderImage := by
  exact ElementsHaveType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun {_} {elements} {_} typed available binderImage _ =>
      ∀ inside root inserted, available = inside ++ root →
        (∀ name, name ∈ elements.flatMap Pattern.freeFvarNames →
          ∃ inner, root = inner ++ support name) →
        typed.ReflectiveSupportSafeAt profile support
          ((inside ++ inserted) ++ root) binderImage)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (by
      intro bound elementType available binderImage inside root inserted
        availableShape suffixes
      exact .nil _ _ _)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available binderImage elementSafe elementsSafe _ elementsIH inside root
        inserted availableShape suffixes
      exact .cons
        (elementSafe.insertAvailablePrefixAt inside root inserted availableShape
          (by
            intro name nameMembership
            apply suffixes name
            simp only [List.flatMap_cons, List.mem_append]
            exact Or.inl nameMembership))
        (elementsIH inside root inserted availableShape (by
          intro name nameMembership
          apply suffixes name
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr nameMembership)))
    safe

/-- Public root form of ambient coeffect insertion. -/
theorem HasType.ReflectiveSupportSafeAt.insertAvailablePrefix
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language free bound pattern type}
    {available inserted : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available binderImage)
    (suffixes : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ inner, available = inner ++ support name) :
    typed.ReflectiveSupportSafeAt profile support
      (inserted ++ available) binderImage := by
  simpa only [List.nil_append] using
    safe.insertAvailablePrefixAt [] available inserted (by simp) suffixes


mutual
  /-- Reflective supported substitution composes independent typing, input,
  and output supports.  The alignment derivation is the exact
  variable-placement law: it separates active binders from sealed outer
  binders and equates only the active prefix lengths.  Consequently this
  theorem preserves an arbitrary reflective binder interpretation. -/
  theorem HasType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupport
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source bound pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : ReflectiveSupportSafeAssignment profile language source
        target typingSupport inputSupport outputSupport binderImage)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveSupportSubstitutionAlignedAt typingSupport safe) :
      ∃ outputTyped : HasType language target bound
          (ReflectiveContextSupport.substituteAt profile inputSupport
            assignment.assignment available.length pattern) type,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases aligned with
    | @bvar bound index type lookup currentAvailable binderImage =>
        let outputTyped : HasType language target bound (.bvar index) type :=
          HasType.bvar lookup
        simpa [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.bvar
              (binderImage := binderImage) lookup available⟩)
    | @fvar bound name type lookup currentAvailable binderImage shape
        contextShape =>
        obtain ⟨active, sealed, boundShape, activeLength⟩ := contextShape
        obtain ⟨reflectivePrefix, availableShape⟩ := shape
        subst bound
        subst available
        have activePrefixLength : active.length = reflectivePrefix.length := by
          simpa only [List.length_append, Nat.add_sub_cancel_right] using
            activeLength
        have valueSafe := assignment.valueSafe lookup
        obtain ⟨liftedTyped, liftedSafe⟩ := valueSafe.liftBVars_insert
          [] (typingSupport name) active rfl
        let liftedTyped' : HasType language target
            (active ++ typingSupport name)
            (liftBVars 0 active.length (assignment.assignment name)) type := by
          simpa only [List.nil_append, List.length_nil] using liftedTyped
        have liftedSafe' : liftedTyped'.ReflectiveSupportSafeAt
            profile outputSupport (inputSupport name) binderImage := by
          apply HasType.ReflectiveSupportSafeAt.castTyping
          simpa only [List.nil_append, List.length_nil] using liftedSafe
        obtain ⟨extendedTyped, extendedSafe⟩ := liftedSafe'.extendOuter sealed
        have prefixedSafe := extendedSafe.insertAvailablePrefix
          (inserted := reflectivePrefix)
          (by
            intro targetName targetMembership
            apply assignment.outputSupportSuffix lookup targetName
            exact (mem_freeFvarNames_liftBVars_iff targetName 0
              active.length (assignment.assignment name)).mp targetMembership)
        have activePair :
            ∃ reflectedTyped : HasType language target
            ((active ++ typingSupport name) ++ sealed)
              (liftBVars 0 active.length (assignment.assignment name)) type,
              reflectedTyped.ReflectiveSupportSafeAt profile outputSupport
                (reflectivePrefix ++ inputSupport name) binderImage :=
          ⟨extendedTyped, prefixedSafe⟩
        have liftEquality :
            liftBVars 0 active.length (assignment.assignment name) =
              liftBVars 0 reflectivePrefix.length
                (assignment.assignment name) :=
          congrArg (fun shift =>
            liftBVars 0 shift (assignment.assignment name)) activePrefixLength
        rw [liftEquality] at activePair
        simpa only [ReflectiveContextSupport.substituteAt,
          List.length_append, Nat.add_sub_cancel_right] using activePair
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        currentAvailable binderImage quoted argumentsSafe argumentsAligned =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupport assignment
            argumentsAligned
        let outputTyped := HasType.constructor membership notBare outputArguments
        simpa [ReflectiveContextSupport.substituteAt, quoted] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := membership) (notBare := notBare)
              quoted outputSafe⟩)
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped currentAvailable binderImage ordinary argumentsSafe
        argumentsAligned =>
        obtain ⟨outputArguments, outputSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupport assignment
            argumentsAligned
        let outputTyped := HasType.constructor membership notBare outputArguments
        simpa [ReflectiveContextSupport.substituteAt, ordinary] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := membership) (notBare := notBare)
              ordinary outputSafe⟩)
    | @lambda bound binder body domain codomain bodyTyped currentAvailable
        binderImage bodySafe bodyAligned =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupport assignment
            bodyAligned
        let outputTyped := HasType.lambda (binder := binder) outputBody
        simpa [ReflectiveContextSupport.substituteAt, List.length_cons] using
          (⟨outputTyped, HasType.ReflectiveSupportSafeAt.lambda outputSafe⟩)
    | @multiLambda bound arity binders body domain codomain bodyTyped
        currentAvailable binderImage bodySafe bodyAligned =>
        obtain ⟨outputBody, outputSafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupport assignment
            bodyAligned
        let rawOutputTyped := HasType.multiLambda (binders := binders) outputBody
        let outputTyped : HasType language target bound
            (ReflectiveContextSupport.substituteAt profile inputSupport
              assignment.assignment available.length
              (.multiLambda arity binders body))
            (.arrow (.multiBinder domain) codomain) := by
          simpa only [ReflectiveContextSupport.substituteAt,
            List.length_append, List.length_replicate, Nat.add_comm] using
              rawOutputTyped
        have rawOutputSafe :=
          HasType.ReflectiveSupportSafeAt.multiLambda
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
        currentAvailable binderImage bodySafe replacementSafe bodyAligned
        replacementAligned =>
        obtain ⟨outputBody, outputBodySafe⟩ :=
          bodySafe.substitutePreservingReflectiveSupport assignment
            bodyAligned
        obtain ⟨outputReplacement, outputReplacementSafe⟩ :=
          replacementSafe.substitutePreservingReflectiveSupport assignment
            replacementAligned
        let outputTyped := HasType.subst outputBody outputReplacement
        simpa [ReflectiveContextSupport.substituteAt, List.length_cons] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.subst outputBodySafe
              outputReplacementSafe⟩)
    | @collection bound collectionType elements rest elementType elementsTyped
        currentAvailable binderImage elementsSafe elementsAligned =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupport assignment
            elementsAligned
        let outputTyped := HasType.collection (collectionType := collectionType)
          (rest := rest) outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.collection outputSafe⟩)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped
        currentAvailable binderImage elementsSafe elementsAligned =>
        obtain ⟨outputElements, outputSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupport assignment
            elementsAligned
        let outputTyped := HasType.collectionConstructor (rest := rest)
          membership parameterShape outputElements
        simpa only [ReflectiveContextSupport.substituteAt] using
          (⟨outputTyped,
            HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
              outputSafe⟩)

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupport
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source bound arguments parameters}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : ReflectiveSupportSafeAssignment profile language source
        target typingSupport inputSupport outputSupport binderImage)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveArgumentsSupportSubstitutionAlignedAt
        typingSupport safe) :
      ∃ outputTyped : ArgumentsHaveTypes language target bound
          (arguments.map (ReflectiveContextSupport.substituteAt profile
            inputSupport assignment.assignment available.length)) parameters,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases aligned with
    | @nil bound currentAvailable binderImage =>
        let outputTyped := ArgumentsHaveTypes.nil
          (language := language) (free := target) (bound := bound)
        exact ⟨outputTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        currentAvailable binderImage argumentSafe argumentsSafe
        argumentAligned argumentsAligned =>
        obtain ⟨outputArgument, outputArgumentSafe⟩ :=
          argumentSafe.substitutePreservingReflectiveSupport assignment
            argumentAligned
        obtain ⟨outputArguments, outputArgumentsSafe⟩ :=
          argumentsSafe.substitutePreservingReflectiveSupport assignment
            argumentsAligned
        let outputRepresentation := representation.substituteReflectiveAt
          profile parameter argument inputSupport assignment.assignment
            available.length
        let outputTyped := ArgumentsHaveTypes.cons outputRepresentation
          parameterType outputArgument outputArguments
        exact ⟨outputTyped, .cons
          (representation := outputRepresentation)
          (parameterType := parameterType)
          outputArgumentSafe outputArgumentsSafe⟩

  theorem ElementsHaveType.ReflectiveSupportSafeAt.substitutePreservingReflectiveSupport
      {language : LanguageDef} {source target : FreeTypeContext}
      {typingSupport inputSupport outputSupport : ContextSupport.Support}
      {bound available : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : ElementsHaveType language source bound elements elementType}
      {binderImage : TypeExpr → TypeExpr}
      (assignment : ReflectiveSupportSafeAssignment profile language source
        target typingSupport inputSupport outputSupport binderImage)
      (safe : typed.ReflectiveSupportSafeAt profile inputSupport available
        binderImage)
      (aligned : ReflectiveElementsSupportSubstitutionAlignedAt
        typingSupport safe) :
      ∃ outputTyped : ElementsHaveType language target bound
          (elements.map (ReflectiveContextSupport.substituteAt profile
            inputSupport assignment.assignment available.length)) elementType,
        outputTyped.ReflectiveSupportSafeAt profile outputSupport available
          binderImage := by
    cases aligned with
    | @nil bound elementType currentAvailable binderImage =>
        let outputTyped := ElementsHaveType.nil
          (language := language) (free := target) bound elementType
        exact ⟨outputTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        currentAvailable binderImage elementSafe elementsSafe elementAligned
        elementsAligned =>
        obtain ⟨outputElement, outputElementSafe⟩ :=
          elementSafe.substitutePreservingReflectiveSupport assignment
            elementAligned
        obtain ⟨outputElements, outputElementsSafe⟩ :=
          elementsSafe.substitutePreservingReflectiveSupport assignment
            elementsAligned
        let outputTyped := ElementsHaveType.cons outputElement outputElements
        exact ⟨outputTyped, .cons outputElementSafe outputElementsSafe⟩
end


end WellSorted

end Mettapedia.GSLT.LanguageDef
