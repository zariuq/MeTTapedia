import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
import Mettapedia.GSLT.LanguageDef.EquationSubstitution

/-!
# Canonical typing and support from rho declaration inventories

The existing two-depth keyed canonicalizer acts on any authored language
satisfying the concrete row inventory. Quotation resets the available binder
support; its cancellation restores a Name only by the admitted Name grammar.
The theorem constructs normalized typing and support derivations together.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Canonical CanonicalSupport LanguageDefCanonicalSection LanguageDefGSLT

variable {language : LanguageDef}

theorem quote_hasSort (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasSort language free bound process "Proc") :
    HasSort language free bound (.apply "NQuote" [process]) "Name" := by
  apply HasType.constructor (rule := rhoCalc.terms[2])
  · exact inventory.shared ⟨2, by decide⟩
  · simp [rhoCalc, UsesBareCollection, TypeExpr.proc, TypeExpr.baseType]
  · exact .cons trivial rfl typed .nil

theorem zero_hasSort (inventory : CanonicalInventory language)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    HasSort language free bound (.apply "PZero" []) "Proc" := by
  apply HasType.constructor (rule := rhoCalc.terms[0])
  · exact inventory.shared ⟨0, by decide⟩
  · simp [rhoCalc, UsesBareCollection]
  · exact .nil

theorem parallel_hasSort (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr} {processes : List Pattern}
    (typed : ElementsHaveType language free bound processes TypeExpr.proc) :
    HasSort language free bound (.collection .hashBag processes none) "Proc" := by
  exact HasType.collectionConstructor (inventory.shared ⟨3, by decide⟩) rfl typed

/-- A support-safe process under a quote remains support-safe at every outer
ambient context because the authored quote constructor resets support. -/
theorem quote_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support [] binderImage) :
    (quote_hasSort inventory typed).ReflectiveSupportSafeAt rhoReflectionProfile support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "NQuote"
      category := "Name"
      params := [.simple "p" TypeExpr.proc]
      syntaxPattern :=
        [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] }
  have membership : rule ∈ language.terms := by
    simpa [rule, rhoCalc] using inventory.shared ⟨2, by decide⟩
  have notBare : ¬ UsesBareCollection rule := by
    simp [rule, UsesBareCollection, TypeExpr.proc, TypeExpr.baseType]
  have representation :
      MatchesParameterRepresentation (.simple "p" TypeExpr.proc) process :=
    trivial
  have parameterType :
      parameterType? (.simple "p" TypeExpr.proc) = some TypeExpr.proc :=
    rfl
  let argumentsTyped :
      ArgumentsHaveTypes language free bound [process] rule.params :=
    .cons representation parameterType typed .nil
  let outputTyped :
      HasSort language free bound (.apply "NQuote" [process]) "Name" :=
    HasType.constructor membership notBare argumentsTyped
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .constructorQuote
    (rule := rule) (membership := membership) (notBare := notBare)
    (argumentsTyped := argumentsTyped)
    (by
      simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile, rhoReflectivePresentation, rule])
    (.cons (representation := representation) (parameterType := parameterType)
      safe (.nil bound []))

/-- Rho's unit process has no free-variable support obligations. -/
theorem zero_supportSafe (inventory : CanonicalInventory language)
    (free : FreeTypeContext) (bound available : List TypeExpr)
    (support : ContextSupport.Support) (binderImage : TypeExpr → TypeExpr) :
    (zero_hasSort inventory free bound).ReflectiveSupportSafeAt rhoReflectionProfile support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "PZero"
      category := "Proc"
      params := []
      syntaxPattern := [.terminal "0"] }
  have membership : rule ∈ language.terms := by
    simpa [rule, rhoCalc] using inventory.shared ⟨0, by decide⟩
  have notBare : ¬ UsesBareCollection rule := by
    simp [rule, UsesBareCollection]
  let argumentsTyped : ArgumentsHaveTypes language free bound [] rule.params :=
    .nil
  let outputTyped :
      HasSort language free bound (.apply "PZero" []) "Proc" :=
    HasType.constructor membership notBare argumentsTyped
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .constructorOrdinary
    (rule := rule) (membership := membership) (notBare := notBare)
    (argumentsTyped := argumentsTyped)
    (by
      simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile, rhoReflectivePresentation, rule])
    (.nil bound available)

/-- A support-safe parallel element spine remains support-safe after applying
rho's authored parallel constructor. -/
theorem parallel_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType language free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage) :
    (parallel_hasSort inventory typed).ReflectiveSupportSafeAt rhoReflectionProfile support available
      binderImage := by
  let rule : GrammarRule :=
    { label := "PPar"
      category := "Proc"
      params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
      syntaxPattern :=
        [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"]
      algebra? := some { flatten := true, unit := some "PZero" } }
  have membership : rule ∈ language.terms := by
    simpa [rule, rhoCalc] using inventory.shared ⟨3, by decide⟩
  have parameterShape : rule.params =
      [.simple "ps" (.collection .hashBag TypeExpr.proc)] := by
    rfl
  let outputTyped : HasSort language free bound
      (.collection .hashBag processes none) "Proc" :=
    HasType.collectionConstructor membership parameterShape typed
  apply HasType.ReflectiveSupportSafeAt.castTyping (source := outputTyped)
  exact .collectionConstructor
    (rule := rule) (membership := membership)
    (parameterShape := parameterShape) safe


/-- The inventory discharges the existing generic Name sealing condition. -/
theorem nameResultsSealed (inventory : CanonicalInventory language) :
    ReflectiveNameResultSealed (profile := rhoReflectionProfile) language := by
  intro declaration selected rule member category
  have same : declaration = rhoReflectivePresentation := by
    simpa [rhoReflectionProfile] using selected
  subst declaration
  have exactRule := inventory.name_row member category
  subst rule
  simp [rhoCalc, UsesBareCollection, TypeExpr.proc, TypeExpr.baseType,
    rhoReflectivePresentation]

/-- Cancellation exposes a Name only through the existing declared-Name
support theorem. The concrete inventory proves its sealing premise. -/
theorem name_supportSafeAt_of_nil (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {name : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound name "Name")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support [] binderImage)
    (object : isObjectPattern name = true)
    (targetAvailable : List TypeExpr) :
    typed.ReflectiveSupportSafeAt rhoReflectionProfile support targetAvailable binderImage :=
  safe.nameResult_of_nil inventory.nameResultsSealed.resultsQuoted rhoReflectivePresentation
    (by simp [rhoReflectionProfile]) typed rfl object targetAvailable

/-- Inversion of support safety for rho's unary drop constructor. -/
theorem drop_argument_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {name : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound (.apply "PDrop" [name]) "Proc")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage) :
    ∃ nameTyped : HasSort language free bound name "Name",
      nameTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  change HasType language free bound (.apply "PDrop" [name]) TypeExpr.proc
    at typed
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType language free bound pattern type)
      (sourceAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage) =>
      pattern = .apply "PDrop" [name] → type = TypeExpr.proc →
      ∃ nameTyped : HasType language free bound name TypeExpr.name,
        nameTyped.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by intros; contradiction)
    (by intros; contradiction)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        patternEquality typeEquality
      injection patternEquality with labelEquality argumentsEquality
      have exactRule := inventory.drop_row membership labelEquality
      subst rule
      simp [rhoCalc, ReflectiveContextSupport.isQuoteConstructor,
        rhoReflectionProfile, rhoReflectivePresentation] at quoted)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        patternEquality typeEquality
      injection patternEquality with labelEquality argumentsEquality
      have exactRule := inventory.drop_row membership labelEquality
      subst rule
      cases argumentsEquality
      cases argumentsTyped with
      | @cons _ argument arguments parameter parameters expected
          representation parameterType argumentTyped tailTyped =>
          cases tailTyped
          have expectedEquality : expected = TypeExpr.name := by
            simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using
              parameterType.symm
          subst expected
          let emptyTyped : ArgumentsHaveTypes language free bound [] [] :=
            .nil
          let exactSpine := ArgumentsHaveTypes.cons representation
            parameterType argumentTyped emptyTyped
          have exactSafe : exactSpine.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage :=
            ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
              (target := exactSpine) argumentsSafe
          exact ⟨argumentTyped,
            ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
              (representation := representation)
              (parameterType := parameterType)
              (argumentTyped := argumentTyped)
              (argumentsTyped := emptyTyped) exactSafe⟩)
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
theorem normalizeQuote_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support [] binderImage)
    (object : isObjectPattern process = true)
    (targetAvailable : List TypeExpr) :
    ∃ normalizedTyped : HasSort language free bound
        (normalizeQuote process) "Name",
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support targetAvailable
        binderImage := by
  by_cases isDrop : ∃ name, process = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := isDrop
    obtain ⟨nameTyped, nameSafe⟩ := drop_argument_supportSafe inventory typed safe
    have nameObject : isObjectPattern name = true := by
      simpa [isObjectPattern, isObjectPatternList] using object
    have exposedSafe :=
      name_supportSafeAt_of_nil inventory nameTyped nameSafe nameObject targetAvailable
    simpa [normalizeQuote] using ⟨nameTyped, exposedSafe⟩
  · have notDrop : ∀ name, process ≠ .apply "PDrop" [name] := by
      intro name equality
      exact isDrop ⟨name, equality⟩
    rw [normalizeQuote_eq_quote_of_not_drop notDrop]
    exact ⟨quote_hasSort inventory typed,
      quote_supportSafe inventory (available := targetAvailable) typed safe⟩

/-! ## Support-safe parallel normalization -/

/-- Inversion of support safety for rho's authored parallel constructor. -/
theorem parallel_elements_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {elements : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound
      (.collection .hashBag elements none) "Proc")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage) :
    ∃ elementsTyped : ElementsHaveType language free bound
        elements TypeExpr.proc,
      elementsTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  change HasType language free bound (.collection .hashBag elements none)
    TypeExpr.proc at typed
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType language free bound pattern type)
      (sourceAvailable : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage) =>
      pattern = .collection .hashBag elements none →
      type = TypeExpr.proc →
      ∃ elementsTyped : ElementsHaveType language free bound
          elements TypeExpr.proc,
        elementsTyped.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable
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
      have exactRule := inventory.collection_row membership
        ⟨parameterName, .hashBag, elementType, parameterShape⟩
      subst rule
      simp [rhoCalc, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
      rcases parameterShape with ⟨rfl, rfl⟩
      exact ⟨elementsTyped, elementsSafe⟩)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe rfl rfl

/-- Every component exposed by rho's parallel splice retains its process
sorting and reflective-support witness. -/
theorem bagSplice_member_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {process member : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasSort language free bound process "Proc")
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage)
    (membership : member ∈ bagSplice process) :
    ∃ memberTyped : HasSort language free bound member "Proc",
      memberTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
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
          parallel_elements_supportSafe inventory typed safe
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

/-- Flattening, removing the unit, and sorting parallel components by an
explicit key preserves their pointwise typing and support discipline. -/
theorem normalizeParallelElementsBy_supportSafe (inventory : CanonicalInventory language)
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType language free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage) :
    ∃ normalizedTyped : ElementsHaveType language free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
          key rhoReflectivePresentation processes) TypeExpr.proc,
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
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
  exact bagSplice_member_supportSafe inventory sourceTyped sourceSafe memberMember'

/-- Removing representation-only empty and singleton parallel wrappers
preserves process sorting and reflective support. -/
theorem collapseBag_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound available : List TypeExpr}
    {processes : List Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ElementsHaveType language free bound processes TypeExpr.proc)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage) :
    ∃ collapsedTyped : HasSort language free bound
        (collapseBag processes) "Proc",
      collapsedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  cases processes with
  | nil =>
      exact ⟨zero_hasSort inventory free bound,
        zero_supportSafe inventory free bound available support binderImage⟩
  | cons process processes =>
      cases processes with
      | nil =>
          obtain ⟨processTyped, processSafe⟩ :=
            ElementsHaveType.ReflectiveSupportSafeAt.forall_mem
              safe process (by simp)
          simpa [collapseBag] using ⟨processTyped, processSafe⟩
      | cons second remainder =>
          exact ⟨parallel_hasSort inventory typed,
            parallel_supportSafe inventory typed safe⟩


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

private theorem normalizeQuote_spine_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {process : Pattern} {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (typed : ArgumentsHaveTypes language free bound [process]
      [.simple "p" TypeExpr.proc])
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support [] binderImage)
    (object : isObjectPattern process = true)
    (targetAvailable : List TypeExpr) :
    ∃ normalizedTyped : HasSort language free bound
        (normalizeQuote process) "Name",
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support targetAvailable
        binderImage := by
  cases typed with
  | @cons _ argument arguments parameter parameters expected representation
      parameterType argumentTyped tailTyped =>
      cases tailTyped
      have expectedEquality : expected = TypeExpr.proc := by
        simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using
          parameterType.symm
      subst expected
      let emptyTyped : ArgumentsHaveTypes language free bound [] [] := .nil
      let exactSpine := ArgumentsHaveTypes.cons representation parameterType
        argumentTyped emptyTyped
      have exactSafe : exactSpine.ReflectiveSupportSafeAt rhoReflectionProfile support []
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
          (target := exactSpine) safe
      have argumentSafe : argumentTyped.ReflectiveSupportSafeAt rhoReflectionProfile support []
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
          (representation := representation)
          (parameterType := parameterType)
          (argumentTyped := argumentTyped)
          (argumentsTyped := emptyTyped) exactSafe
      exact normalizeQuote_supportSafe inventory argumentTyped argumentSafe object
        targetAvailable

/-! ## Support preservation of keyed rho canonicalization -/

/-- On the declaration-derived rho fragment, two-depth keyed
canonicalization preserves both typing and reflective support.  The mutual
recursor keeps constructor arguments and parallel elements synchronized with
their authored typing spines while quotation changes only the quote-visible
depth. -/
theorem canonicalizeByDepths_supportSafe (inventory : CanonicalInventory language)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (scopeDepth : Nat)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType language free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType language free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
          key rhoReflectivePresentation available.length scopeDepth pattern)
          type,
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType language free bound pattern type)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage) =>
      CanonicalizableRhoType type → isObjectPattern pattern = true →
      ∀ scopeDepth,
      ∃ normalizedTyped : HasType language free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
            key rhoReflectivePresentation available.length scopeDepth pattern)
            type,
        normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage)
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage) =>
      ParametersCanonicalizable parameters →
      isObjectPatternList arguments = true → ∀ scopeDepth,
      ∃ normalizedTyped : ArgumentsHaveTypes language free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
            key rhoReflectivePresentation available.length scopeDepth arguments)
          parameters,
        normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage)
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType language free bound elements elementType)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage) =>
      CanonicalizableRhoType elementType →
      isObjectPatternList elements = true → ∀ scopeDepth,
      ∃ normalizedTyped : ElementsHaveType language free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
            key rhoReflectivePresentation available.length scopeDepth elements)
          elementType,
        normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available currentImage)
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
      have label : rule.label = "NQuote" := by
        exact (show "NQuote" = rule.label by
          simpa [ReflectiveContextSupport.isQuoteConstructor,
            rhoReflectionProfile, rhoReflectivePresentation] using quoted).symm
      have exactRule := inventory.quote_row membership label
      change rule =
        { label := "NQuote", category := "Name",
          params := [.simple "p" TypeExpr.proc],
          syntaxPattern := [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] }
        at exactRule
      subst rule
      cases argumentsTyped with
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
          have exactTyped : ArgumentsHaveTypes language free bound
              [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                key rhoReflectivePresentation 0 scopeDepth argument]
              [TermParam.simple "p" TypeExpr.proc] := by
            simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths]
              using normalizedArgumentsTyped
          have exactSafe : exactTyped.ReflectiveSupportSafeAt rhoReflectionProfile support []
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
            (normalizeQuote_spine_supportSafe inventory exactTyped exactSafe
              canonicalObject sourceAvailable))
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        canonicalizable object scopeDepth
      have parametersCanonicalizable :=
        inventory.parameters membership notBare
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using object
      obtain ⟨normalizedArgumentsTyped, normalizedArgumentsSafe⟩ :=
        argumentsIH parametersCanonicalizable argumentsObject scopeDepth
      let normalizedTyped :=
        HasType.constructor membership notBare normalizedArgumentsTyped
      let normalizedSafe : normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage :=
        HasType.ReflectiveSupportSafeAt.constructorOrdinary
          (membership := membership) (notBare := notBare)
          (argumentsTyped := normalizedArgumentsTyped) ordinary
          normalizedArgumentsSafe
      have notQuote : rule.label ≠ "NQuote" := by
        intro equality
        have quoteStatus := ordinary
        rw [equality] at quoteStatus
        simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile, rhoReflectivePresentation] at quoteStatus
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
          ∃ normalizedBodyTyped : HasType language free
              (List.replicate arity domain ++ bound)
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
                key rhoReflectivePresentation
                (sourceAvailable.length + arity) (scopeDepth + arity) body)
                codomain,
            normalizedBodyTyped.ReflectiveSupportSafeAt rhoReflectionProfile support
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
      have exactRule := inventory.collection_row membership
        ⟨parameterName, collectionType, elementType, parameterShape⟩
      change rule =
        { label := "PPar", category := "Proc",
          params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)],
          syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
          algebra? := some { flatten := true, unit := some "PZero" } } at exactRule
      subst rule
      simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType]
        at parameterShape
      rcases parameterShape with ⟨rfl, rfl, rfl⟩
      cases rest with
      | none =>
          have elementsObject : isObjectPatternList elements = true := by
            simpa [isObjectPattern] using object
          obtain ⟨canonicalElementsTyped, canonicalElementsSafe⟩ :=
            elementsIH (by trivial) elementsObject scopeDepth
          obtain ⟨normalizedElementsTyped, normalizedElementsSafe⟩ :=
            normalizeParallelElementsBy_supportSafe inventory
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
            (collapseBag_supportSafe inventory normalizedElementsTyped
              normalizedElementsSafe)
      | some restName => simp [isObjectPattern] at object)
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
      change ∃ normalizedTyped : ArgumentsHaveTypes language free bound
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths
              key rhoReflectivePresentation sourceAvailable.length scopeDepth
              argument ::
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths
              key rhoReflectivePresentation sourceAvailable.length scopeDepth
              arguments)
          (parameter :: parameters),
        normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable
          currentImage
      let normalizedSpine := ArgumentsHaveTypes.cons
        normalizedRepresentation parameterType normalizedArgumentTyped
        normalizedArgumentsTyped
      let normalizedSpineSafe : normalizedSpine.ReflectiveSupportSafeAt rhoReflectionProfile support sourceAvailable currentImage :=
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
theorem canonicalizeByAt_supportSafe (inventory : CanonicalInventory language)
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType language free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType language free bound
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          key rhoReflectivePresentation available.length pattern) type,
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  simpa only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_ignoreScope]
    using
      (canonicalizeByDepths_supportSafe inventory
        (key := fun availableDepth _ pattern => key availableDepth pattern)
        (scopeDepth := 0) typed safe canonicalizable object)

/-- The established structural rho canonicalizer is the collision-free
`patternCode` instance of keyed support preservation. -/
theorem canonicalize_supportSafe (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasType language free bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasType language free bound
        (canonicalize pattern) type,
      normalizedTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage := by
  simpa only [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt_const,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeBy_patternCode,
    CanonicalMatch.derivedCanonicalize_eq] using
    (canonicalizeByAt_supportSafe inventory
      (key := fun _ pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      typed safe canonicalizable object)

/-- Ordinary typing is obtained by the existing empty-support certificate;
no reflective sealing condition is silently imposed on the source pattern. -/
theorem canonicalize_hasType (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    HasType language free bound (canonicalize pattern) type := by
  obtain ⟨normalized, _⟩ := inventory.canonicalize_supportSafe typed
    (typed.reflectiveSupportSafeAt_empty []) canonicalizable object
  exact normalized

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
