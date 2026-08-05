import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyedTyping

/-!
# Reflective-support stability of rho canonicalization

Rho's canonicalizer is already known to preserve every declaration-derived
open sorted fiber.  This module proves the additional support law needed by
iterable syntax transformations: canonicalization does not move an opaque
free parameter out of an ordinary binder on which it depends, and quotation
seals the surrounding binder support.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-! ## Support-safe rho constructor wrappers -/

/-- A support-safe process under a quote remains support-safe at every outer
ambient context because the authored quote constructor resets support. -/
private theorem quote_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt support [] binderImage) :
    (rho_quote_hasSort typed).ReflectiveSupportSafeAt support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "NQuote"
      category := "Name"
      params := [.simple "p" TypeExpr.proc]
      syntaxPattern :=
        [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] }
  have membership : rule ∈ rhoCalc.terms := by
    simp [rule, rhoCalc]
  have notBare : ¬ UsesBareCollection rule := by
    simp [rule, UsesBareCollection, TypeExpr.proc, TypeExpr.baseType]
  have representation :
      MatchesParameterRepresentation (.simple "p" TypeExpr.proc) process :=
    trivial
  have parameterType :
      parameterType? (.simple "p" TypeExpr.proc) = some TypeExpr.proc :=
    rfl
  let argumentsTyped :
      ArgumentsHaveTypes rhoCalc free bound [process] rule.params :=
    .cons representation parameterType typed .nil
  let outputTyped :
      HasSort rhoCalc free bound (.apply "NQuote" [process]) "Name" :=
    HasType.constructor membership notBare argumentsTyped
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .constructorQuote
    (rule := rule) (membership := membership) (notBare := notBare)
    (argumentsTyped := argumentsTyped)
    (by
      simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
        rhoReflectivePresentation, rule])
    (.cons (representation := representation) (parameterType := parameterType)
      safe (.nil bound []))

/-- Rho's unit process has no free-variable support obligations. -/
private theorem zero_supportSafe
    (free : FreeTypeContext) (bound available : List TypeExpr)
    (support : ContextSupport.Support) (binderImage : TypeExpr → TypeExpr) :
    (rho_zero_hasSort free bound).ReflectiveSupportSafeAt support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "PZero"
      category := "Proc"
      params := []
      syntaxPattern := [.terminal "0"] }
  have membership : rule ∈ rhoCalc.terms := by
    simp [rule, rhoCalc]
  have notBare : ¬ UsesBareCollection rule := by
    simp [rule, UsesBareCollection]
  let argumentsTyped : ArgumentsHaveTypes rhoCalc free bound [] rule.params :=
    .nil
  let outputTyped :
      HasSort rhoCalc free bound (.apply "PZero" []) "Proc" :=
    HasType.constructor membership notBare argumentsTyped
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .constructorOrdinary
    (rule := rule) (membership := membership) (notBare := notBare)
    (argumentsTyped := argumentsTyped)
    (by
      simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
        rhoReflectivePresentation, rule])
    (.nil bound available)

/-- A support-safe parallel element spine remains support-safe after applying
rho's authored parallel constructor. -/
private theorem parallel_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    (rho_parallel_hasSort typed).ReflectiveSupportSafeAt support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "PPar"
      category := "Proc"
      params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
      syntaxPattern :=
        [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"] }
  have membership : rule ∈ rhoCalc.terms := by
    simp [rule, rhoCalc]
  have parameterShape : rule.params =
      [.simple "ps" (.collection .hashBag TypeExpr.proc)] := by
    rfl
  let outputTyped : HasSort rhoCalc free bound
      (.collection .hashBag processes none) "Proc" :=
    HasType.collectionConstructor membership parameterShape typed
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .collectionConstructor
    (rule := rule) (membership := membership)
    (parameterShape := parameterShape) safe

/-! ## Moving names across the quote boundary -/

/-- A well-sorted rho name that is support-safe inside a quotation remains
support-safe when quote/drop cancellation exposes it at the surrounding
support.  This is not a generic weakening principle: it uses the fact that
rho's only object-forming name constructor is quotation. -/
private theorem name_supportSafeAt_of_nil
    {free : FreeTypeContext} {bound : List TypeExpr}
    {name : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound name "Name")
    (safe : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern name = true)
    (targetAvailable : List TypeExpr) :
    typed.ReflectiveSupportSafeAt support targetAvailable binderImage := by
  change HasType rhoCalc free bound name TypeExpr.name at typed
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (sourceAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support sourceAvailable currentImage) =>
      type = TypeExpr.name → sourceAvailable = [] →
      isObjectPattern pattern = true →
      ∀ targetAvailable,
        typed.ReflectiveSupportSafeAt support targetAvailable currentImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by
      intro bound index type lookup sourceAvailable currentImage typeEquality
        sourceEquality object targetAvailable
      cases typeEquality
      exact .bvar lookup targetAvailable)
    (by
      intro bound freeName type lookup sourceAvailable currentImage shape
        typeEquality
        sourceEquality object targetAvailable
      cases typeEquality
      subst sourceAvailable
      obtain ⟨inner, supportShape⟩ := shape
      have supportNil : support freeName = [] :=
        (List.append_eq_nil_iff.mp supportShape.symm).2
      exact .fvar lookup targetAvailable
        ⟨targetAvailable, by simp [supportNil]⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH typeEquality
        sourceEquality object targetAvailable
      exact .constructorQuote (membership := membership)
        (notBare := notBare) (argumentsTyped := argumentsTyped)
        (available := targetAvailable) quoted argumentsSafe)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        typeEquality
        sourceEquality object targetAvailable
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at ordinary
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality)
    (by
      intro bound binder body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH typeEquality sourceEquality object
        targetAvailable
      simp [TypeExpr.name, TypeExpr.baseType] at typeEquality)
    (by
      intro bound arity binders body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH typeEquality sourceEquality object
        targetAvailable
      simp [TypeExpr.name, TypeExpr.baseType] at typeEquality)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        sourceAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        typeEquality sourceEquality object targetAvailable
      simp [isObjectPattern] at object)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH typeEquality sourceEquality
        object targetAvailable
      cases typeEquality)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped sourceAvailable currentImage
        elementsSafe elementsIH typeEquality sourceEquality object targetAvailable
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at typeEquality
      · simp at parameterShape
      · simp at parameterShape)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe rfl rfl object targetAvailable

/-- Inversion of support safety for rho's unary drop constructor. -/
theorem drop_argument_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {name : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound (.apply "PDrop" [name]) "Proc")
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ nameTyped : HasSort rhoCalc free bound name "Name",
      nameTyped.ReflectiveSupportSafeAt support available binderImage := by
  change HasType rhoCalc free bound (.apply "PDrop" [name]) TypeExpr.proc
    at typed
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (sourceAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support sourceAvailable currentImage) =>
      pattern = .apply "PDrop" [name] → type = TypeExpr.proc →
      ∃ nameTyped : HasType rhoCalc free bound name TypeExpr.name,
        nameTyped.ReflectiveSupportSafeAt support sourceAvailable currentImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by intros; contradiction)
    (by intros; contradiction)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        patternEquality typeEquality
      injection patternEquality with labelEquality argumentsEquality
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at labelEquality
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        patternEquality typeEquality
      injection patternEquality with labelEquality argumentsEquality
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at labelEquality
      · cases argumentsEquality
        cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected
            representation parameterType argumentTyped tailTyped =>
            cases tailTyped
            have expectedEquality : expected = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using
                parameterType.symm
            subst expected
            let emptyTyped : ArgumentsHaveTypes rhoCalc free bound [] [] :=
              .nil
            let exactSpine := ArgumentsHaveTypes.cons representation
              parameterType argumentTyped emptyTyped
            have exactSafe : exactSpine.ReflectiveSupportSafeAt
                support sourceAvailable currentImage :=
              ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
                (target := exactSpine) argumentsSafe
            exact ⟨argumentTyped,
              ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
                (representation := representation)
                (parameterType := parameterType)
                (argumentTyped := argumentTyped)
                (argumentsTyped := emptyTyped) exactSafe⟩
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe rfl rfl

/-- Quote/drop cancellation preserves both sorting and reflective support.
The non-cancellation branch stays below a fresh quote boundary; the
cancellation branch uses the rho-specific name theorem above. -/
private theorem normalizeQuote_supportSafe
    {free : FreeTypeContext} {bound : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern process = true)
    (targetAvailable : List TypeExpr) :
    ∃ normalizedTyped : HasSort rhoCalc free bound
        (normalizeQuote process) "Name",
      normalizedTyped.ReflectiveSupportSafeAt support targetAvailable
        binderImage := by
  by_cases isDrop : ∃ name, process = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := isDrop
    obtain ⟨nameTyped, nameSafe⟩ := drop_argument_supportSafe typed safe
    have nameObject : isObjectPattern name = true := by
      simpa [isObjectPattern, isObjectPatternList] using object
    have exposedSafe :=
      name_supportSafeAt_of_nil nameTyped nameSafe nameObject targetAvailable
    simpa [normalizeQuote] using ⟨nameTyped, exposedSafe⟩
  · have notDrop : ∀ name, process ≠ .apply "PDrop" [name] := by
      intro name equality
      exact isDrop ⟨name, equality⟩
    rw [normalizeQuote_eq_quote_of_not_drop notDrop]
    exact ⟨rho_quote_hasSort typed,
      quote_supportSafe (available := targetAvailable) typed safe⟩

/-! ## Support-safe parallel normalization -/

/-- Inversion of support safety for rho's authored parallel constructor. -/
private theorem parallel_elements_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {elements : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound
      (.collection .hashBag elements none) "Proc")
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ elementsTyped : ElementsHaveType rhoCalc free bound
        elements TypeExpr.proc,
      elementsTyped.ReflectiveSupportSafeAt support available binderImage := by
  change HasType rhoCalc free bound (.collection .hashBag elements none)
    TypeExpr.proc at typed
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (sourceAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support sourceAvailable currentImage) =>
      pattern = .collection .hashBag elements none →
      type = TypeExpr.proc →
      ∃ elementsTyped : ElementsHaveType rhoCalc free bound
          elements TypeExpr.proc,
        elementsTyped.ReflectiveSupportSafeAt support sourceAvailable
          currentImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by intros; contradiction)
    (by
      intro bound collectionType sourceElements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH patternEquality
        typeEquality
      injection patternEquality with collectionEquality elementsEquality
        restEquality
      cases collectionEquality
      cases elementsEquality
      cases restEquality
      cases typeEquality)
    (by
      intro bound rule parameterName collectionType sourceElements rest
        elementType membership parameterShape elementsTyped sourceAvailable
        currentImage elementsSafe elementsIH patternEquality typeEquality
      injection patternEquality with collectionEquality elementsEquality
        restEquality
      cases collectionEquality
      cases elementsEquality
      cases restEquality
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType]
          at parameterShape
        rcases parameterShape with ⟨rfl, rfl, rfl⟩
        exact ⟨elementsTyped, elementsSafe⟩
      · simp at parameterShape
      · simp at parameterShape)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe rfl rfl

/-- Every component exposed by rho's parallel splice retains its process
sorting and reflective-support witness. -/
private theorem bagSplice_member_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {process member : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort rhoCalc free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt support available binderImage)
    (membership : member ∈ bagSplice process) :
    ∃ memberTyped : HasSort rhoCalc free bound member "Proc",
      memberTyped.ReflectiveSupportSafeAt support available binderImage := by
  cases process with
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest
      · simp [bagSplice] at membership
        subst member
        exact ⟨typed, safe⟩
      · simp [bagSplice] at membership
        subst member
        exact ⟨typed, safe⟩
      · obtain ⟨elementsTyped, elementsSafe⟩ :=
          parallel_elements_supportSafe typed safe
        exact ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
          elementsSafe member membership
      · simp [bagSplice] at membership
        subst member
        exact ⟨typed, safe⟩
      · simp [bagSplice] at membership
        subst member
        exact ⟨typed, safe⟩
      · simp [bagSplice] at membership
        subst member
        exact ⟨typed, safe⟩
  | _ =>
      simp [bagSplice] at membership
      subst member
      exact ⟨typed, safe⟩

/-- Flattening, removing the unit, and sorting parallel components preserves
their pointwise typing and support discipline. -/
private theorem normalizeBagElements_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ normalizedTyped : ElementsHaveType rhoCalc free bound
        (normalizeBagElements processes) TypeExpr.proc,
      normalizedTyped.ReflectiveSupportSafeAt support available binderImage := by
  apply ElementsHaveType.ReflectiveSupportSafeAt.of_forall_mem
  intro member membership
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeBagElements_mem_source membership
  obtain ⟨sourceTyped, sourceSafe⟩ :=
    ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
      safe source sourceMembership
  exact bagSplice_member_supportSafe sourceTyped sourceSafe memberMembership

/-- Flattening, removing the unit, and sorting parallel components by an
explicit key preserves their pointwise typing and support discipline. -/
private theorem normalizeParallelElementsBy_supportSafe
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ normalizedTyped : ElementsHaveType rhoCalc free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
          key rhoReflectivePresentation processes) TypeExpr.proc,
      normalizedTyped.ReflectiveSupportSafeAt support available binderImage := by
  apply ElementsHaveType.ReflectiveSupportSafeAt.of_forall_mem
  intro member membership
  have structuralMembership : member ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
        rhoReflectivePresentation processes :=
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy_perm
      key rhoReflectivePresentation processes).mem_iff.mp membership
  have filteredMembership : member ∈
      ((processes.flatMap
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
          rhoReflectivePresentation)).filter fun pattern =>
            pattern ≠ .apply rhoReflectivePresentation.parallelUnitConstructor
              []) :=
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm _).mem_iff.mp (by
      simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements]
        using structuralMembership)
  have flatMembership := List.mem_of_mem_filter filteredMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, memberMember⟩ := flatMembership
  have memberMember' : member ∈ bagSplice source := by
    cases source with
    | collection collectionType elements rest =>
        cases collectionType <;> cases rest <;>
          simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
            rhoReflectivePresentation, bagSplice] using memberMember
    | _ =>
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
          rhoReflectivePresentation, bagSplice] using memberMember
  obtain ⟨sourceTyped, sourceSafe⟩ :=
    ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
      safe source sourceMember
  exact bagSplice_member_supportSafe sourceTyped sourceSafe memberMember'

/-- Removing representation-only empty and singleton parallel wrappers
preserves process sorting and reflective support. -/
private theorem collapseBag_supportSafe
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ collapsedTyped : HasSort rhoCalc free bound
        (collapseBag processes) "Proc",
      collapsedTyped.ReflectiveSupportSafeAt support available binderImage := by
  cases processes with
  | nil =>
      exact ⟨rho_zero_hasSort free bound,
        zero_supportSafe free bound available support binderImage⟩
  | cons process processes =>
      cases processes with
      | nil =>
          obtain ⟨processTyped, processSafe⟩ :=
            ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
              safe process (by simp)
          simpa [collapseBag] using ⟨processTyped, processSafe⟩
      | cons second remainder =>
          exact ⟨rho_parallel_hasSort typed,
            parallel_supportSafe typed safe⟩

/-- The generic declaration-derived quote finisher specializes exactly to
rho's independently defined quote/drop normalizer. -/
private theorem finishRhoQuote_eq (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        rhoReflectivePresentation "NQuote" [pattern] =
      normalizeQuote pattern := by
  cases pattern with
  | apply constructor arguments =>
      cases arguments with
      | nil => simp [
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          rhoReflectivePresentation, normalizeQuote]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases isDrop : constructor = "PDrop"
              · subst constructor
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  rhoReflectivePresentation, normalizeQuote]
              · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  rhoReflectivePresentation, normalizeQuote, isDrop]
          | cons second remainder =>
              simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                rhoReflectivePresentation, normalizeQuote]
  | _ =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
        rhoReflectivePresentation, normalizeQuote]

/-- The generic declaration-derived parallel collapse specializes exactly to
rho's independently defined bag collapse. -/
private theorem collapseRhoParallel_eq (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
        rhoReflectivePresentation patterns =
      collapseBag patterns := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      cases patterns with
      | nil => rfl
      | cons second remainder => rfl

/-! ## The declaration-derived rho fragment -/

/-- Types whose object-forming representation is preserved by rho's
canonicalizer.  Raw collection types are excluded because a bare rho
parallel bag is represented at the authored `Proc` sort, not at a collection
sort.  Arrow types inherit the condition from their codomain. -/
def CanonicalizableRhoType : TypeExpr → Prop
  | .collection _ _ => False
  | .arrow _ codomain => CanonicalizableRhoType codomain
  | _ => True

/-- Every argument type induced by one parameter spine belongs to the rho
fragment on which canonicalization preserves typing. -/
def ParametersCanonicalizable (parameters : List TermParam) : Prop :=
  ∀ parameter ∈ parameters, ∀ expected,
    parameterType? parameter = some expected →
      CanonicalizableRhoType expected

/-- Every non-collection rho constructor has only canonicalizable argument
types.  The bare parallel rule is excluded by its representation witness. -/
theorem rhoRule_parametersCanonicalizable {rule : GrammarRule}
    (membership : rule ∈ rhoCalc.terms)
    (notBare : ¬ UsesBareCollection rule) :
    ParametersCanonicalizable rule.params := by
  simp [rhoCalc] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [ParametersCanonicalizable]
  · simp [ParametersCanonicalizable, parameterType?]
    trivial
  · simp [ParametersCanonicalizable, parameterType?]
    trivial
  · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc,
      TypeExpr.baseType] at notBare
  · simp [ParametersCanonicalizable, parameterType?]
    constructor <;> trivial
  · simp [ParametersCanonicalizable, parameterType?, TypeExpr.funType]
    constructor <;> trivial

/-- Rho canonicalization preserves the authored binder representation of a
constructor argument. -/
theorem matchesParameterRepresentation_canonicalize
    (parameter : TermParam) (pattern : Pattern) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter (canonicalize pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, canonicalize]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, canonicalize]
      case multiLambda arity binders body => cases binders <;> simp

/-- Key-parametric rho canonicalization preserves the authored binder
representation of a constructor argument at every quote-visible depth. -/
theorem matchesParameterRepresentation_canonicalizeByAt
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (availableDepth : Nat) (parameter : TermParam) (pattern : Pattern) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          key rhoReflectivePresentation availableDepth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt]
      case multiLambda arity binders body => cases binders <;> simp

/-- Two-depth keyed rho canonicalization preserves the authored binder
representation of a constructor argument. -/
theorem matchesParameterRepresentation_canonicalizeByDepths
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) (parameter : TermParam)
    (pattern : Pattern) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
          key rhoReflectivePresentation availableDepth scopeDepth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths]
      case multiLambda arity binders body => cases binders <;> simp

/-- Eliminate the normalized singleton argument spine of rho's quote
constructor and apply the quote/drop support theorem. -/
private theorem normalizeQuote_spine_supportSafe
    {free : FreeTypeContext} {bound : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ArgumentsHaveTypes rhoCalc free bound [process]
      [.simple "p" TypeExpr.proc])
    (safe : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern process = true)
    (targetAvailable : List TypeExpr) :
    ∃ normalizedTyped : HasSort rhoCalc free bound
        (normalizeQuote process) "Name",
      normalizedTyped.ReflectiveSupportSafeAt support targetAvailable
        binderImage := by
  cases typed with
  | @cons _ argument arguments parameter parameters expected representation
      parameterType argumentTyped tailTyped =>
      cases tailTyped
      have expectedEquality : expected = TypeExpr.proc := by
        simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using
          parameterType.symm
      subst expected
      let emptyTyped : ArgumentsHaveTypes rhoCalc free bound [] [] := .nil
      let exactSpine := ArgumentsHaveTypes.cons representation parameterType
        argumentTyped emptyTyped
      have exactSafe : exactSpine.ReflectiveSupportSafeAt support []
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
          (target := exactSpine) safe
      have argumentSafe : argumentTyped.ReflectiveSupportSafeAt support []
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
          (representation := representation)
          (parameterType := parameterType)
          (argumentTyped := argumentTyped)
          (argumentsTyped := emptyTyped) exactSafe
      exact normalizeQuote_supportSafe argumentTyped argumentSafe object
        targetAvailable

/-! ## Support preservation of keyed rho canonicalization -/

/-- On the declaration-derived rho fragment, two-depth keyed
canonicalization preserves both typing and reflective support.  The mutual
recursor keeps constructor arguments and parallel elements synchronized with
their authored typing spines while quotation changes only the quote-visible
depth. -/
theorem canonicalizeByDepths_supportSafe
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (scopeDepth : Nat)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType rhoCalc free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType rhoCalc free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
          key rhoReflectivePresentation available.length scopeDepth pattern)
          type,
      normalizedTyped.ReflectiveSupportSafeAt support available binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType rhoCalc free bound pattern type)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      CanonicalizableRhoType type → isObjectPattern pattern = true →
      ∀ scopeDepth,
      ∃ normalizedTyped : HasType rhoCalc free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
            key rhoReflectivePresentation available.length scopeDepth pattern)
            type,
        normalizedTyped.ReflectiveSupportSafeAt support available currentImage)
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes rhoCalc free bound arguments parameters)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      ParametersCanonicalizable parameters →
      isObjectPatternList arguments = true → ∀ scopeDepth,
      ∃ normalizedTyped : ArgumentsHaveTypes rhoCalc free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
            key rhoReflectivePresentation available.length scopeDepth arguments)
          parameters,
        normalizedTyped.ReflectiveSupportSafeAt support available currentImage)
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType rhoCalc free bound elements elementType)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      CanonicalizableRhoType elementType →
      isObjectPatternList elements = true → ∀ scopeDepth,
      ∃ normalizedTyped : ElementsHaveType rhoCalc free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
            key rhoReflectivePresentation available.length scopeDepth elements)
          elementType,
        normalizedTyped.ReflectiveSupportSafeAt support available currentImage)
    (by
      intro bound index type lookup sourceAvailable currentImage canonicalizable
        object scopeDepth
      exact ⟨HasType.bvar lookup,
        HasType.ReflectiveSupportSafeAt.bvar lookup sourceAvailable⟩)
    (by
      intro bound freeName type lookup sourceAvailable currentImage shape
        canonicalizable object scopeDepth
      exact ⟨HasType.fvar lookup,
        HasType.ReflectiveSupportSafeAt.fvar lookup sourceAvailable shape⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        canonicalizable object scopeDepth
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted
      · cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected
            representation parameterType argumentTyped tailTyped =>
            cases tailTyped
            have expectedEquality : expected = TypeExpr.proc := by
              simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using
                parameterType.symm
            subst expected
            have parametersCanonicalizable :
                ParametersCanonicalizable
                  [TermParam.simple "p" TypeExpr.proc] := by
              simp [ParametersCanonicalizable, parameterType?]
              trivial
            have argumentsObject :
                isObjectPatternList [argument] = true := by
              simpa [isObjectPattern, isObjectPatternList] using object
            obtain ⟨normalizedArgumentsTyped, normalizedArgumentsSafe⟩ :=
              argumentsIH parametersCanonicalizable argumentsObject scopeDepth
            have exactTyped : ArgumentsHaveTypes rhoCalc free bound
                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                  key rhoReflectivePresentation 0 scopeDepth argument]
                [TermParam.simple "p" TypeExpr.proc] := by
              simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths]
                using normalizedArgumentsTyped
            have exactSafe : exactTyped.ReflectiveSupportSafeAt support []
                currentImage :=
              ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
                (target := exactTyped) normalizedArgumentsSafe
            have canonicalObject :
                isObjectPattern
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                    key rhoReflectivePresentation 0 scopeDepth argument) = true :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_isObjectPattern
                key rhoReflectivePresentation 0 scopeDepth argument
                  (by simpa [isObjectPatternList] using argumentsObject)
            have keyedQuoteEq :
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                    key rhoReflectivePresentation sourceAvailable.length scopeDepth
                    (.apply "NQuote" [argument]) =
                  normalizeQuote
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                      key rhoReflectivePresentation 0 scopeDepth argument) := by
              simp only [
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths]
              rw [show ("NQuote" == rhoReflectivePresentation.quoteConstructor) =
                true by rfl]
              simp only [if_true]
              exact finishRhoQuote_eq _
            rw [keyedQuoteEq]
            simpa [TypeExpr.name, TypeExpr.baseType] using
              (normalizeQuote_spine_supportSafe exactTyped exactSafe
                canonicalObject sourceAvailable)
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted
      · simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoted)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        canonicalizable object scopeDepth
      have parametersCanonicalizable :=
        rhoRule_parametersCanonicalizable membership notBare
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using object
      obtain ⟨normalizedArgumentsTyped, normalizedArgumentsSafe⟩ :=
        argumentsIH parametersCanonicalizable argumentsObject scopeDepth
      let normalizedTyped :=
        HasType.constructor membership notBare normalizedArgumentsTyped
      let normalizedSafe : normalizedTyped.ReflectiveSupportSafeAt
          support sourceAvailable currentImage :=
        HasType.ReflectiveSupportSafeAt.constructorOrdinary
          (membership := membership) (notBare := notBare)
          (argumentsTyped := normalizedArgumentsTyped) ordinary
          normalizedArgumentsSafe
      have notQuote : rule.label ≠ "NQuote" := by
        intro equality
        have quoteStatus := ordinary
        rw [equality] at quoteStatus
        simp [ReflectiveContextSupport.isQuoteConstructor, rhoCalc,
          rhoReflectivePresentation] at quoteStatus
      simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
        rhoReflectivePresentation, notQuote] using
          ⟨normalizedTyped, normalizedSafe⟩)
    (by
      intro bound binder body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH canonicalizable object scopeDepth
      have codomainCanonicalizable : CanonicalizableRhoType codomain := by
        simpa [CanonicalizableRhoType] using canonicalizable
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      obtain ⟨normalizedBodyTyped, normalizedBodySafe⟩ :=
        bodyIH codomainCanonicalizable bodyObject (scopeDepth + 1)
      exact ⟨HasType.lambda normalizedBodyTyped,
        HasType.ReflectiveSupportSafeAt.lambda normalizedBodySafe⟩)
    (by
      intro bound arity binders body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH canonicalizable object scopeDepth
      have codomainCanonicalizable : CanonicalizableRhoType codomain := by
        simpa [CanonicalizableRhoType] using canonicalizable
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using object
      have alignedResult :
          ∃ normalizedBodyTyped : HasType rhoCalc free
              (List.replicate arity domain ++ bound)
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                key rhoReflectivePresentation
                (sourceAvailable.length + arity) (scopeDepth + arity) body)
                codomain,
            normalizedBodyTyped.ReflectiveSupportSafeAt support
              (List.replicate arity (currentImage domain) ++ sourceAvailable)
              currentImage := by
        simpa [List.length_append, Nat.add_comm] using
          (bodyIH codomainCanonicalizable bodyObject (scopeDepth + arity))
      obtain ⟨normalizedBodyTyped, normalizedBodySafe⟩ := alignedResult
      simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths]
        using
        ⟨HasType.multiLambda normalizedBodyTyped,
          HasType.ReflectiveSupportSafeAt.multiLambda normalizedBodySafe⟩)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        sourceAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        canonicalizable object scopeDepth
      simp [isObjectPattern] at object)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH canonicalizable
        object scopeDepth
      simp [CanonicalizableRhoType] at canonicalizable)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped sourceAvailable currentImage
        elementsSafe elementsIH canonicalizable object scopeDepth
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType]
          at parameterShape
        rcases parameterShape with ⟨rfl, rfl, rfl⟩
        cases rest with
        | none =>
            have elementsObject : isObjectPatternList elements = true := by
              simpa [isObjectPattern] using object
            obtain ⟨canonicalElementsTyped, canonicalElementsSafe⟩ :=
              elementsIH (by trivial) elementsObject scopeDepth
            obtain ⟨normalizedElementsTyped, normalizedElementsSafe⟩ :=
              normalizeParallelElementsBy_supportSafe
                (key sourceAvailable.length scopeDepth) canonicalElementsTyped
                canonicalElementsSafe
            have keyedParallelEq :
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                    key rhoReflectivePresentation sourceAvailable.length scopeDepth
                    (.collection .hashBag elements none) =
                  collapseBag
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
                      (key sourceAvailable.length scopeDepth)
                      rhoReflectivePresentation
                      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
                        key rhoReflectivePresentation sourceAvailable.length
                        scopeDepth elements)) := by
              simp only [
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths]
              rw [show (.hashBag == rhoReflectivePresentation.parallelCollection) =
                true by rfl]
              simp only [if_true]
              exact collapseRhoParallel_eq _
            rw [keyedParallelEq]
            simpa [TypeExpr.proc, TypeExpr.baseType] using
              (collapseBag_supportSafe normalizedElementsTyped
                normalizedElementsSafe)
        | some restName => simp [isObjectPattern] at object
      · simp at parameterShape
      · simp at parameterShape)
    (by
      intro bound sourceAvailable currentImage parametersCanonicalizable object
        scopeDepth
      exact ⟨ArgumentsHaveTypes.nil,
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.nil bound sourceAvailable⟩)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        sourceAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH parametersCanonicalizable object scopeDepth
      have argumentCanonicalizable : CanonicalizableRhoType expected :=
        parametersCanonicalizable parameter (by simp) expected parameterType
      have tailCanonicalizable : ParametersCanonicalizable parameters := by
        intro tailParameter membership tailExpected tailType
        exact parametersCanonicalizable tailParameter (by simp [membership])
          tailExpected tailType
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using object
      obtain ⟨normalizedArgumentTyped, normalizedArgumentSafe⟩ :=
        argumentIH argumentCanonicalizable objectParts.1 scopeDepth
      obtain ⟨normalizedArgumentsTyped, normalizedArgumentsSafe⟩ :=
        argumentsIH tailCanonicalizable objectParts.2 scopeDepth
      have normalizedRepresentation :
          MatchesParameterRepresentation parameter
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
              key rhoReflectivePresentation sourceAvailable.length scopeDepth
              argument) :=
        matchesParameterRepresentation_canonicalizeByDepths key
          sourceAvailable.length scopeDepth parameter argument representation
      change ∃ normalizedTyped : ArgumentsHaveTypes rhoCalc free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
              key rhoReflectivePresentation sourceAvailable.length scopeDepth
              argument ::
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
              key rhoReflectivePresentation sourceAvailable.length scopeDepth
              arguments)
          (parameter :: parameters),
        normalizedTyped.ReflectiveSupportSafeAt support sourceAvailable
          currentImage
      let normalizedSpine := ArgumentsHaveTypes.cons
        normalizedRepresentation parameterType normalizedArgumentTyped
        normalizedArgumentsTyped
      let normalizedSpineSafe : normalizedSpine.ReflectiveSupportSafeAt
          support sourceAvailable currentImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
          (representation := normalizedRepresentation)
          (parameterType := parameterType)
          (argumentTyped := normalizedArgumentTyped)
          (argumentsTyped := normalizedArgumentsTyped)
          normalizedArgumentSafe normalizedArgumentsSafe
      exact ⟨normalizedSpine, normalizedSpineSafe⟩)
    (by
      intro bound elementType sourceAvailable currentImage canonicalizable object
        scopeDepth
      exact ⟨ElementsHaveType.nil bound elementType,
        ElementsHaveType.ReflectiveSupportSafeAt.nil bound elementType
          sourceAvailable⟩)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        sourceAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH canonicalizable object scopeDepth
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using object
      obtain ⟨normalizedElementTyped, normalizedElementSafe⟩ :=
        elementIH canonicalizable objectParts.1 scopeDepth
      obtain ⟨normalizedElementsTyped, normalizedElementsSafe⟩ :=
        elementsIH canonicalizable objectParts.2 scopeDepth
      exact ⟨ElementsHaveType.cons normalizedElementTyped
          normalizedElementsTyped,
        ElementsHaveType.ReflectiveSupportSafeAt.cons
          normalizedElementSafe normalizedElementsSafe⟩)
    safe canonicalizable object scopeDepth

/-- The original quote-visible keyed interface is the exact specialization
whose key ignores structural depth. -/
theorem canonicalizeByAt_supportSafe
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType rhoCalc free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType rhoCalc free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          key rhoReflectivePresentation available.length pattern) type,
      normalizedTyped.ReflectiveSupportSafeAt support available binderImage := by
  simpa only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_ignoreScope]
    using
      (canonicalizeByDepths_supportSafe
        (key := fun availableDepth _ pattern => key availableDepth pattern)
        (scopeDepth := 0) typed safe canonicalizable object)

/-- The established structural rho canonicalizer is the collision-free
`patternCode` instance of keyed support preservation. -/
theorem canonicalize_supportSafe
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType rhoCalc free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType rhoCalc free bound
        (canonicalize pattern) type,
      normalizedTyped.ReflectiveSupportSafeAt support available binderImage := by
  simpa only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt_const,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeBy_patternCode,
    CanonicalMatch.derivedCanonicalize_eq] using
    (canonicalizeByAt_supportSafe
      (key := fun _ pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      typed safe canonicalizable object)

/-- Rho's open canonicalizer preserves reflective support in every authored
sort.  The target typing proof is transported only across proof
irrelevance; its pattern, contexts, and result sort are unchanged. -/
theorem rhoCanonicalizeOpenTerm_preservesReflectiveSupport
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort rhoCalc}
    (term : OpenTerm rhoIGSLT free bound sort)
    (support : ContextSupport.Support)
    (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (safe : term.2.1.ReflectiveSupportSafeAt support available binderImage) :
    (rhoCanonicalizeOpenTerm term).2.1.ReflectiveSupportSafeAt
      support available binderImage := by
  rcases term.2 with ⟨typed, canonical, object, scopeSafe⟩
  rcases rhoLangSort_eq_proc_or_name sort with rfl | rfl
  · obtain ⟨normalizedTyped, normalizedSafe⟩ :=
      canonicalize_supportSafe typed safe (by trivial) object
    exact HasType.ReflectiveSupportSafeAt.castTyping
      (source := normalizedTyped)
      (target := (rhoCanonicalizeOpenTerm term).2.1) normalizedSafe
  · obtain ⟨normalizedTyped, normalizedSafe⟩ :=
      canonicalize_supportSafe typed safe (by trivial) object
    exact HasType.ReflectiveSupportSafeAt.castTyping
      (source := normalizedTyped)
      (target := (rhoCanonicalizeOpenTerm term).2.1) normalizedSafe

/-- The exact `rhoCalc` root carries a support-stable computable open
section.  This is the rho witness needed by iterable syntax constructions;
it introduces neither a second carrier nor a second equality relation. -/
def rhoContextualOpenSection : ComputableContextualOpenSection rhoIGSLT where
  toComputableOpenSection := rhoOpenSection
  preservesFreeVariableSupport := by
    intro free bound sort term name membership
    change name ∈ (rhoCanonicalizeOpenTerm term).1.freeFvarNames at membership
    rw [rhoCanonicalizeOpenTerm_pattern] at membership
    rw [← CanonicalMatch.derivedCanonicalize_eq term.1] at membership
    exact (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
      rhoReflectivePresentation name term.1).mp membership
  normalizeRecontextualizeFree := by
    intro sourceFree targetFree bound sort term preserves
    change
      (rhoCanonicalizeOpenTerm
        (term.recontextualizeFree preserves)).1 =
      (rhoCanonicalizeOpenTerm term).1
    simp only [rhoCanonicalizeOpenTerm_pattern,
      WellSorted.OpenTerm.recontextualizeFree_pattern]
  preservesReflectiveSupport :=
    rhoCanonicalizeOpenTerm_preservesReflectiveSupport

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport
