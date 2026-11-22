import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalSection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

/-!
# Rho's canonical section on the one-root semantic carrier

The generic iGSLT induced by `rhoCalc` uses the same computable
canonicalizer as the established sorted rho GSLT.  The carrier equivalence
changes only proof witnesses, so this file transports the canonical section
without introducing a second syntax, equation theory, or representative
choice.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

/-! ## Open rho canonicalization -/

/-- Inversion of the declaration-derived typing judgment for rho's unary
drop constructor. -/
private theorem rhoDrop_argument_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasSort rhoCalc free bound
      (.apply "PDrop" [name]) "Proc") :
    HasSort rhoCalc free bound name "Name" := by
  change HasType rhoCalc free bound (.apply "PDrop" [name])
    TypeExpr.proc at typed
  generalize typeEquality : TypeExpr.proc = resultType at typed
  generalize patternEquality :
    (Pattern.apply "PDrop" [name]) = pattern at typed
  cases typed with
  | bvar lookup => cases patternEquality
  | fvar lookup => cases patternEquality
  | @constructor _ rule arguments membership notBare argumentsTyped =>
      injection patternEquality with labelEquality argumentsEquality
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at labelEquality
      · cases argumentsEquality
        cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected
            representation parameterType argumentTyped argumentsTyped =>
            cases argumentsTyped
            have expectedEquality : expected = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using
                parameterType.symm
            subst expected
            exact argumentTyped
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality
      · simp at labelEquality
  | lambda bodyTyped => cases patternEquality
  | multiLambda bodyTyped => cases patternEquality
  | subst bodyTyped replacementTyped => cases patternEquality
  | collection elementsTyped => cases patternEquality
  | collectionConstructor membership parameterShape elementsTyped =>
      cases patternEquality

/-- Orienting quote/drop cancellation preserves the declaration-derived name
sort in arbitrary open typing contexts. -/
theorem normalizeQuote_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasSort rhoCalc free bound process "Proc") :
    HasSort rhoCalc free bound (normalizeQuote process) "Name" := by
  cases process with
  | apply constructor arguments =>
      cases arguments with
      | nil => simpa [normalizeQuote] using rho_quote_hasSort typed
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases isDrop : constructor = "PDrop"
              · subst constructor
                exact rhoDrop_argument_hasSort typed
              · simpa [normalizeQuote, isDrop] using rho_quote_hasSort typed
          | cons second remainder =>
              simpa [normalizeQuote] using rho_quote_hasSort typed
  | bvar index => simpa [normalizeQuote] using rho_quote_hasSort typed
  | fvar name => simpa [normalizeQuote] using rho_quote_hasSort typed
  | lambda binder body => simpa [normalizeQuote] using rho_quote_hasSort typed
  | multiLambda arity binders body =>
      simpa [normalizeQuote] using rho_quote_hasSort typed
  | subst body replacement =>
      simpa [normalizeQuote] using rho_quote_hasSort typed
  | collection collectionType elements rest =>
      simpa [normalizeQuote] using rho_quote_hasSort typed

/-- Inversion of the bare parallel representation at rho's process sort. -/
theorem rhoParallel_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : HasSort rhoCalc free bound
      (.collection .hashBag elements none) "Proc") :
    ElementsHaveType rhoCalc free bound elements TypeExpr.proc := by
  change HasType rhoCalc free bound (.collection .hashBag elements none)
    TypeExpr.proc at typed
  generalize typeEquality : TypeExpr.proc = resultType at typed
  generalize patternEquality :
    (Pattern.collection .hashBag elements none) = pattern at typed
  cases typed with
  | bvar lookup => cases patternEquality
  | fvar lookup => cases patternEquality
  | constructor membership notBare argumentsTyped => cases patternEquality
  | lambda bodyTyped => cases patternEquality
  | multiLambda bodyTyped => cases patternEquality
  | subst bodyTyped replacementTyped => cases patternEquality
  | @collection _ collectionType sourceElements rest elementType
      sourceElementsTyped =>
      simp [TypeExpr.proc, TypeExpr.baseType] at typeEquality
  | @collectionConstructor _ rule parameterName collectionType sourceElements
      rest elementType membership parameterShape sourceElementsTyped =>
      injection patternEquality with collectionEquality elementsEquality restEquality
      cases collectionEquality
      cases elementsEquality
      cases restEquality
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
        rcases parameterShape with ⟨rfl, rfl, rfl⟩
        exact sourceElementsTyped
      · simp at parameterShape
      · simp at parameterShape

/-- Pointwise characterization of declaration-derived collection-element
typing. -/
theorem elementsHaveType_iff_forall_mem
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr} :
    ElementsHaveType rhoCalc free bound elements elementType ↔
      ∀ element ∈ elements,
        HasType rhoCalc free bound element elementType := by
  constructor
  · intro typed element membership
    induction elements generalizing element with
    | nil => simp at membership
    | cons head tail inductionHypothesis =>
        cases typed
        rename_i headTyped tailTyped
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · exact headTyped
        · exact inductionHypothesis tailTyped element membership
  · intro pointwise
    induction elements with
    | nil => exact .nil _ _
    | cons element elements inductionHypothesis =>
        exact .cons (pointwise element (by simp))
          (inductionHypothesis fun member membership =>
            pointwise member (by simp [membership]))

/-- Splicing one sorted process into a surrounding parallel presentation
retains pointwise process sorting. -/
theorem bagSplice_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasSort rhoCalc free bound process "Proc") :
    ElementsHaveType rhoCalc free bound (bagSplice process) TypeExpr.proc := by
  cases process with
  | bvar index => exact .cons typed (.nil _ _)
  | fvar name => exact .cons typed (.nil _ _)
  | apply constructor arguments => exact .cons typed (.nil _ _)
  | lambda binder body => exact .cons typed (.nil _ _)
  | multiLambda arity binders body => exact .cons typed (.nil _ _)
  | subst body replacement => exact .cons typed (.nil _ _)
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest
      · exact .cons typed (.nil _ _)
      · exact .cons typed (.nil _ _)
      · exact rhoParallel_elementsHaveType typed
      · exact .cons typed (.nil _ _)
      · exact .cons typed (.nil _ _)
      · exact .cons typed (.nil _ _)

/-- Flattening nested parallel components preserves pointwise process
sorting. -/
theorem flatMap_bagSplice_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    ElementsHaveType rhoCalc free bound
      (processes.flatMap bagSplice) TypeExpr.proc := by
  rw [elementsHaveType_iff_forall_mem] at typed ⊢
  intro process membership
  rw [List.mem_flatMap] at membership
  obtain ⟨source, sourceMember, processMember⟩ := membership
  exact (elementsHaveType_iff_forall_mem.mp
    (bagSplice_elementsHaveType (typed source sourceMember)))
      process processMember

/-- Filtering a sorted parallel component list preserves its element sort. -/
theorem filter_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern} (keep : Pattern → Bool)
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    ElementsHaveType rhoCalc free bound (processes.filter keep) TypeExpr.proc := by
  rw [elementsHaveType_iff_forall_mem] at typed ⊢
  intro process membership
  exact typed process (List.mem_of_mem_filter membership)

/-- Sorting parallel components by the collision-free structural order
preserves pointwise process sorting. -/
private theorem sortPatterns_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    ElementsHaveType rhoCalc free bound (sortPatterns processes) TypeExpr.proc := by
  rw [elementsHaveType_iff_forall_mem] at typed ⊢
  intro process membership
  exact typed process (sortPatterns_mem_iff.mp membership)

/-- Parallel normalization preserves the declaration-derived element sort. -/
theorem normalizeBagElements_elementsHaveType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    ElementsHaveType rhoCalc free bound
      (normalizeBagElements processes) TypeExpr.proc := by
  apply sortPatterns_elementsHaveType
  apply filter_elementsHaveType
  exact flatMap_bagSplice_elementsHaveType typed

/-- Collapsing the representation-only empty or singleton parallel wrapper
preserves rho's process sort. -/
theorem collapseBag_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    HasSort rhoCalc free bound (collapseBag processes) "Proc" := by
  cases processes with
  | nil => exact rho_zero_hasSort free bound
  | cons process processes =>
      cases processes with
      | nil =>
          cases typed with
          | cons processTyped tailTyped => exact processTyped
      | cons second remainder => exact rho_parallel_hasSort typed

private theorem isObjectPatternList_iff_forall_mem
    {patterns : List Pattern} :
    isObjectPatternList patterns = true ↔
      ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons pattern patterns inductionHypothesis =>
      simp [isObjectPatternList, inductionHypothesis, or_imp, forall_and]

private theorem canonicalBinderMetadataList_iff_forall_mem
    {patterns : List Pattern} :
    Pattern.hasCanonicalBinderMetadataList patterns = true ↔
      ∀ pattern ∈ patterns,
        pattern.hasCanonicalBinderMetadata = true := by
  induction patterns with
  | nil => simp [Pattern.hasCanonicalBinderMetadataList]
  | cons pattern patterns inductionHypothesis =>
      simp [Pattern.hasCanonicalBinderMetadataList, inductionHypothesis,
        or_imp, forall_and]

private theorem bagSplice_isObjectPatternList
    {process : Pattern} (object : isObjectPattern process = true) :
    isObjectPatternList (bagSplice process) = true := by
  cases process with
  | bvar index => simpa [bagSplice, isObjectPatternList] using object
  | fvar name => simpa [bagSplice, isObjectPatternList] using object
  | apply constructor arguments =>
      simpa [bagSplice, isObjectPatternList] using object
  | lambda binder body => simpa [bagSplice, isObjectPatternList] using object
  | multiLambda arity binders body =>
      simpa [bagSplice, isObjectPatternList] using object
  | subst body replacement => simp [isObjectPattern] at object
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest <;>
        simp [bagSplice, isObjectPattern, isObjectPatternList] at object ⊢
      all_goals assumption

private theorem bagSplice_hasCanonicalBinderMetadataList
    {process : Pattern}
    (canonical : process.hasCanonicalBinderMetadata = true) :
    Pattern.hasCanonicalBinderMetadataList (bagSplice process) = true := by
  cases process with
  | bvar index =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | fvar name =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | apply constructor arguments =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | lambda binder body =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | multiLambda arity binders body =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | subst body replacement =>
      simpa [bagSplice, Pattern.hasCanonicalBinderMetadataList] using canonical
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest <;>
        simpa [bagSplice, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical

private theorem normalizeBagElements_isObjectPatternList
    {processes : List Pattern}
    (object : isObjectPatternList processes = true) :
    isObjectPatternList (normalizeBagElements processes) = true := by
  rw [isObjectPatternList_iff_forall_mem] at object ⊢
  intro process membership
  obtain ⟨source, sourceMember, processMember⟩ :=
    normalizeBagElements_mem_source membership
  exact (isObjectPatternList_iff_forall_mem.mp
    (bagSplice_isObjectPatternList (object source sourceMember)))
      process processMember

private theorem normalizeBagElements_hasCanonicalBinderMetadataList
    {processes : List Pattern}
    (canonical :
      Pattern.hasCanonicalBinderMetadataList processes = true) :
    Pattern.hasCanonicalBinderMetadataList
      (normalizeBagElements processes) = true := by
  rw [canonicalBinderMetadataList_iff_forall_mem] at canonical ⊢
  intro process membership
  obtain ⟨source, sourceMember, processMember⟩ :=
    normalizeBagElements_mem_source membership
  exact (canonicalBinderMetadataList_iff_forall_mem.mp
    (bagSplice_hasCanonicalBinderMetadataList
      (canonical source sourceMember))) process processMember

private theorem collapseBag_isObjectPattern
    {processes : List Pattern}
    (object : isObjectPatternList processes = true) :
    isObjectPattern (collapseBag processes) = true := by
  cases processes with
  | nil => rfl
  | cons process processes =>
      cases processes with
      | nil => simpa [collapseBag, isObjectPatternList] using object
      | cons second remainder =>
          simpa [collapseBag, isObjectPattern] using object

private theorem collapseBag_hasCanonicalBinderMetadata
    {processes : List Pattern}
    (canonical :
      Pattern.hasCanonicalBinderMetadataList processes = true) :
    (collapseBag processes).hasCanonicalBinderMetadata = true := by
  cases processes with
  | nil => rfl
  | cons process processes =>
      cases processes with
      | nil =>
          simpa [collapseBag, Pattern.hasCanonicalBinderMetadataList] using
            canonical
      | cons second remainder =>
          simpa [collapseBag, Pattern.hasCanonicalBinderMetadata] using canonical

private theorem normalizeQuote_isObjectPattern
    {process : Pattern} (object : isObjectPattern process = true) :
    isObjectPattern (normalizeQuote process) = true := by
  cases process with
  | bvar index =>
      simp [normalizeQuote, isObjectPattern, isObjectPatternList]
  | fvar name =>
      simp [normalizeQuote, isObjectPattern, isObjectPatternList]
  | apply constructor arguments =>
      cases arguments with
      | nil =>
          simp [normalizeQuote, isObjectPattern, isObjectPatternList]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases isDrop : constructor = "PDrop"
              · subst constructor
                simpa [normalizeQuote, isObjectPattern,
                  isObjectPatternList] using object
              · simpa [normalizeQuote, isDrop, isObjectPattern,
                  isObjectPatternList] using object
          | cons second remainder =>
              simpa [normalizeQuote, isObjectPattern,
                isObjectPatternList] using object
  | lambda binder body =>
      simpa [normalizeQuote, isObjectPattern, isObjectPatternList] using object
  | multiLambda arity binders body =>
      simpa [normalizeQuote, isObjectPattern, isObjectPatternList] using object
  | subst body replacement => simp [isObjectPattern] at object
  | collection collectionType elements rest =>
      simpa [normalizeQuote, isObjectPattern, isObjectPatternList] using object

private theorem normalizeQuote_hasCanonicalBinderMetadata
    {process : Pattern}
    (canonical : process.hasCanonicalBinderMetadata = true) :
    (normalizeQuote process).hasCanonicalBinderMetadata = true := by
  cases process with
  | bvar index =>
      simp [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | fvar name =>
      simp [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | apply constructor arguments =>
      cases arguments with
      | nil =>
          simp [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases isDrop : constructor = "PDrop"
              · subst constructor
                simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
                  Pattern.hasCanonicalBinderMetadataList] using canonical
              · simpa [normalizeQuote, isDrop,
                  Pattern.hasCanonicalBinderMetadata,
                  Pattern.hasCanonicalBinderMetadataList] using canonical
          | cons second remainder =>
              simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
                Pattern.hasCanonicalBinderMetadataList] using canonical
  | lambda binder body =>
      simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList] using canonical
  | multiLambda arity binders body =>
      simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList] using canonical
  | subst body replacement =>
      simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList] using canonical
  | collection collectionType elements rest =>
      simpa [normalizeQuote, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList] using canonical

mutual
  theorem canonicalize_isObjectPattern
      {pattern : Pattern} (object : isObjectPattern pattern = true) :
      isObjectPattern (canonicalize pattern) = true := by
    induction pattern using Pattern.inductionOn with
    | hbvar index => rfl
    | hfvar name => rfl
    | happly constructor arguments inductionHypothesis =>
        have argumentsObject :
            isObjectPatternList (canonicalizeList arguments) = true := by
          rw [isObjectPatternList_iff_forall_mem]
          intro canonicalArgument canonicalMember
          rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
          obtain ⟨argument, argumentMember, rfl⟩ := canonicalMember
          exact inductionHypothesis argument argumentMember
            ((isObjectPatternList_iff_forall_mem.mp object)
              argument argumentMember)
        by_cases isQuote :
            constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          change isObjectPattern (normalizeQuote (canonicalize argument)) = true
          exact normalizeQuote_isObjectPattern
            (inductionHypothesis argument (by simp)
              ((isObjectPatternList_iff_forall_mem.mp object)
                argument (by simp)))
        · rw [canonicalize_apply_general constructor arguments isQuote]
          simpa [isObjectPattern] using argumentsObject
    | hlambda binder body inductionHypothesis =>
        simpa [canonicalize, isObjectPattern] using
          inductionHypothesis object
    | hmultiLambda arity binders body inductionHypothesis =>
        simpa [canonicalize, isObjectPattern] using
          inductionHypothesis object
    | hsubst body replacement bodyInduction replacementInduction =>
        simp [isObjectPattern] at object
    | hcollection collectionType elements rest inductionHypothesis =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        have elementsObject :
            isObjectPatternList (canonicalizeList elements) = true := by
          rw [isObjectPatternList_iff_forall_mem]
          intro canonicalElement canonicalMember
          rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
          obtain ⟨element, elementMember, rfl⟩ := canonicalMember
          exact inductionHypothesis element elementMember
            ((isObjectPatternList_iff_forall_mem.mp object.2)
              element elementMember)
        by_cases isParallel : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := isParallel
          change isObjectPattern
            (collapseBag (normalizeBagElements
              (canonicalizeList elements))) = true
          exact collapseBag_isObjectPattern
            (normalizeBagElements_isObjectPatternList elementsObject)
        · rw [canonicalize_collection_general collectionType elements rest
            isParallel]
          simpa [isObjectPattern] using
            And.intro object.1 elementsObject

  private theorem canonicalize_hasCanonicalBinderMetadata
      {pattern : Pattern}
      (canonical : pattern.hasCanonicalBinderMetadata = true) :
      (canonicalize pattern).hasCanonicalBinderMetadata = true := by
    induction pattern using Pattern.inductionOn with
    | hbvar index => rfl
    | hfvar name => rfl
    | happly constructor arguments inductionHypothesis =>
        have argumentsCanonical :
            Pattern.hasCanonicalBinderMetadataList
              (canonicalizeList arguments) = true := by
          rw [canonicalBinderMetadataList_iff_forall_mem]
          intro canonicalArgument canonicalMember
          rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
          obtain ⟨argument, argumentMember, rfl⟩ := canonicalMember
          exact inductionHypothesis argument argumentMember
            ((canonicalBinderMetadataList_iff_forall_mem.mp canonical)
              argument argumentMember)
        by_cases isQuote :
            constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          change (normalizeQuote (canonicalize argument)).hasCanonicalBinderMetadata =
            true
          exact normalizeQuote_hasCanonicalBinderMetadata
            (inductionHypothesis argument (by simp)
              ((canonicalBinderMetadataList_iff_forall_mem.mp canonical)
                argument (by simp)))
        · rw [canonicalize_apply_general constructor arguments isQuote]
          simpa [Pattern.hasCanonicalBinderMetadata] using argumentsCanonical
    | hlambda binder body inductionHypothesis =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simpa [canonicalize, Pattern.hasCanonicalBinderMetadata] using
          And.intro canonical.1 (inductionHypothesis canonical.2)
    | hmultiLambda arity binders body inductionHypothesis =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simpa [canonicalize, Pattern.hasCanonicalBinderMetadata] using
          And.intro canonical.1 (inductionHypothesis canonical.2)
    | hsubst body replacement bodyInduction replacementInduction =>
        simp only [Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true] at canonical
        simpa only [canonicalize, Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true] using
            And.intro (bodyInduction canonical.1)
              (replacementInduction canonical.2)
    | hcollection collectionType elements rest inductionHypothesis =>
        have elementsCanonical :
            Pattern.hasCanonicalBinderMetadataList
              (canonicalizeList elements) = true := by
          rw [canonicalBinderMetadataList_iff_forall_mem]
          intro canonicalElement canonicalMember
          rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
          obtain ⟨element, elementMember, rfl⟩ := canonicalMember
          exact inductionHypothesis element elementMember
            ((canonicalBinderMetadataList_iff_forall_mem.mp canonical)
              element elementMember)
        by_cases isParallel : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := isParallel
          change (collapseBag (normalizeBagElements
            (canonicalizeList elements))).hasCanonicalBinderMetadata = true
          exact collapseBag_hasCanonicalBinderMetadata
            (normalizeBagElements_hasCanonicalBinderMetadataList
              elementsCanonical)
        · rw [canonicalize_collection_general collectionType elements rest
            isParallel]
          simpa [Pattern.hasCanonicalBinderMetadata] using elementsCanonical
end

mutual
  /-- Rho canonicalization preserves the declaration-derived name sort in
  arbitrary open type contexts. -/
  theorem canonicalize_name_hasSort
      {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
      (typed : HasSort rhoCalc free bound name "Name")
      (object : isObjectPattern name = true) :
      HasSort rhoCalc free bound (canonicalize name) "Name" := by
    change HasType rhoCalc free bound name TypeExpr.name at typed
    change HasType rhoCalc free bound (canonicalize name) TypeExpr.name
    generalize resultTypeEquality : TypeExpr.name = resultType at typed
    cases typed with
    | @bvar bound index type lookup =>
        cases resultTypeEquality
        exact .bvar lookup
    | @fvar bound name type lookup =>
        cases resultTypeEquality
        exact .fvar lookup
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · cases argumentsTyped with
          | @cons _ argument arguments parameter parameters expected
              representation parameterType argumentTyped argumentsTyped =>
              cases argumentsTyped
              have expectedEquality : expected = TypeExpr.proc := by
                simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using
                  parameterType.symm
              subst expected
              simp [isObjectPattern, isObjectPatternList] at object
              change HasType rhoCalc free bound
                (normalizeQuote (canonicalize argument)) TypeExpr.name
              exact normalizeQuote_hasSort
                (canonicalize_proc_hasSort argumentTyped object)
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp at parameterShape
        · simp at parameterShape

  /-- Rho canonicalization preserves the declaration-derived process sort in
  arbitrary open type contexts. -/
  theorem canonicalize_proc_hasSort
      {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
      (typed : HasSort rhoCalc free bound process "Proc")
      (object : isObjectPattern process = true) :
      HasSort rhoCalc free bound (canonicalize process) "Proc" := by
    change HasType rhoCalc free bound process TypeExpr.proc at typed
    change HasType rhoCalc free bound (canonicalize process) TypeExpr.proc
    generalize resultTypeEquality : TypeExpr.proc = resultType at typed
    cases typed with
    | @bvar bound index type lookup =>
        cases resultTypeEquality
        exact .bvar lookup
    | @fvar bound name type lookup =>
        cases resultTypeEquality
        exact .fvar lookup
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · cases argumentsTyped
          simpa [canonicalize, canonicalizeList] using
            rho_zero_hasSort free bound
        · cases argumentsTyped with
          | @cons _ argument arguments parameter parameters expected
              representation parameterType argumentTyped argumentsTyped =>
              cases argumentsTyped
              have expectedEquality : expected = TypeExpr.name := by
                simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using
                  parameterType.symm
              subst expected
              simp [isObjectPattern, isObjectPatternList] at object
              simpa [canonicalize, canonicalizeList] using
                rho_drop_hasSort
                  (canonicalize_name_hasSort argumentTyped object)
        · simp [TypeExpr.proc, TypeExpr.baseType] at resultTypeEquality
        · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc,
            TypeExpr.baseType] at notBare
        · cases argumentsTyped with
          | @cons _ channel arguments parameter parameters channelType
              channelRepresentation channelParameterType channelTyped
              argumentsTyped =>
              cases argumentsTyped with
              | @cons _ payload arguments parameter parameters payloadType
                  payloadRepresentation payloadParameterType payloadTyped
                  argumentsTyped =>
                  cases argumentsTyped
                  have channelTypeEquality : channelType = TypeExpr.name := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.baseType]
                      using channelParameterType.symm
                  have payloadTypeEquality : payloadType = TypeExpr.proc := by
                    simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType]
                      using payloadParameterType.symm
                  subst channelType
                  subst payloadType
                  simp [isObjectPattern, isObjectPatternList] at object
                  simpa [canonicalize, canonicalizeList] using
                    rho_output_hasSort
                      (canonicalize_name_hasSort channelTyped object.1)
                      (canonicalize_proc_hasSort payloadTyped object.2)
        · cases argumentsTyped with
          | @cons _ channel arguments parameter parameters channelType
              channelRepresentation channelParameterType channelTyped
              argumentsTyped =>
              cases argumentsTyped with
              | @cons _ abstraction arguments parameter parameters bodyType
                  bodyRepresentation bodyParameterType abstractionTyped
                  argumentsTyped =>
                  cases argumentsTyped
                  have channelTypeEquality : channelType = TypeExpr.name := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.baseType]
                      using channelParameterType.symm
                  have bodyTypeEquality : bodyType =
                      TypeExpr.arrow TypeExpr.name TypeExpr.proc := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.proc,
                      TypeExpr.funType, TypeExpr.baseType] using
                        bodyParameterType.symm
                  subst channelType
                  subst bodyType
                  cases abstraction with
                  | lambda binder body =>
                      cases binder with
                      | none =>
                          cases abstractionTyped with
                          | lambda bodyTyped =>
                              simp [isObjectPattern, isObjectPatternList] at object
                              simpa [canonicalize, canonicalizeList] using
                                rho_input_hasSort
                                  (canonicalize_name_hasSort channelTyped
                                    object.1)
                                  (canonicalize_proc_hasSort bodyTyped object.2)
                      | some binderName =>
                          simp [MatchesParameterRepresentation] at bodyRepresentation
                  | bvar index =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | fvar name =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | apply name arguments =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | multiLambda arity binders body =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | subst body replacement =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | collection collectionType elements rest =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
          rcases parameterShape with ⟨rfl, rfl, rfl⟩
          cases rest with
          | none =>
              simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
                at object
              change HasType rhoCalc free bound
                (collapseBag
                  (normalizeBagElements (canonicalizeList elements)))
                TypeExpr.proc
              exact collapseBag_hasSort
                (normalizeBagElements_elementsHaveType
                  (canonicalize_procElementsHaveType elementsTyped object))
          | some restName => simp [isObjectPattern] at object
        · simp at parameterShape
        · simp at parameterShape

  /-- Pointwise form of process-sort preservation for rho's parallel
  collection representation. -/
  theorem canonicalize_procElementsHaveType
      {free : FreeTypeContext} {bound : List TypeExpr}
      {processes : List Pattern}
      (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
      (object : isObjectPatternList processes = true) :
      ElementsHaveType rhoCalc free bound
        (canonicalizeList processes) TypeExpr.proc := by
    cases typed with
    | nil => exact .nil _ _
    | cons processTyped processesTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        exact .cons (canonicalize_proc_hasSort processTyped object.1)
          (canonicalize_procElementsHaveType processesTyped object.2)
end

/-- The exact `rhoCalc` root authors only the process and name sorts. -/
theorem rhoLangSort_eq_proc_or_name (sort : LangSort rhoCalc) :
    sort = rhoProc ∨ sort = rhoName := by
  have membership := sort.2
  change sort.1 ∈ ["Proc", "Name"] at membership
  simp at membership
  rcases membership with processName | nameName
  · left
    apply Subtype.ext
    exact processName
  · right
    apply Subtype.ext
    exact nameName

/-- Rho canonicalization preserves every reflective quotation boundary
declared by the sole authored language root. -/
theorem canonicalize_reflectiveScopeSafeAt
    {depth : Nat} {pattern : Pattern}
    (safe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoReflectionProfile depth pattern) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoReflectionProfile depth (canonicalize pattern) := by
  intro presentation membership
  have presentationEquality :
      presentation =
        rhoReflectivePresentation.toReflectivePresentationDecl := by
    simpa [rhoReflectionProfile] using membership
  subst presentation
  exact CanonicalTyping.canonicalize_binderSafeAt pattern depth
    (safe rhoReflectivePresentation.toReflectivePresentationDecl (by
      simp [rhoReflectionProfile]))

/-- Rho's canonicalizer acts within every open object-language fiber derived
from the exact `rhoCalc` presentation. -/
def rhoCanonicalizeOpenTerm {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort rhoCalc}
    (term : OpenTerm rhoIGSLT free bound sort) :
    OpenTerm rhoIGSLT free bound sort := by
  refine ⟨canonicalize term.1, ?_⟩
  rcases term.2 with ⟨typed, canonical, object, safe⟩
  rcases rhoLangSort_eq_proc_or_name sort with rfl | rfl
  · let normalizedTyped := canonicalize_proc_hasSort typed object
    exact ⟨normalizedTyped, canonicalize_hasCanonicalBinderMetadata canonical,
      canonicalize_isObjectPattern object, normalizedTyped.isWellScopedAt⟩
  · let normalizedTyped := canonicalize_name_hasSort typed object
    exact ⟨normalizedTyped, canonicalize_hasCanonicalBinderMetadata canonical,
      canonicalize_isObjectPattern object, normalizedTyped.isWellScopedAt⟩

@[simp]
theorem rhoCanonicalizeOpenTerm_pattern {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort rhoCalc}
    (term : OpenTerm rhoIGSLT free bound sort) :
    (rhoCanonicalizeOpenTerm term).1 = canonicalize term.1 :=
  rfl

/-- The one-root rho presentation has a computable canonical section on all
open authored-sort fibers, not merely on the closed process carrier. -/
def rhoOpenSection : ComputableReflectiveOpenSection rhoIGSLT
    rhoCalcValidatedReflective.admittedReflection where
  normalize := rhoCanonicalizeOpenTerm
  equivalent := by
    intro free bound sort term
    have membership :
        List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
          rhoReflectionProfile.presentations := by
      change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
        [rhoReflectivePresentation.toReflectivePresentationDecl]
      exact .head _
    apply Relation.EqvGen.rel
    apply ReflectiveEquationContextStep.reflectiveInContext .hole
      membership
    change
      ReflectiveCanonical.canonicalize rhoReflectivePresentation
          (Canonical.canonicalize term.1) =
        ReflectiveCanonical.canonicalize rhoReflectivePresentation term.1
    simpa only [derivedCanonicalize_eq] using
      Canonical.canonicalize_idempotent term.1
  complete := by
    intro free bound sort left right equivalent
    induction equivalent with
    | rel left right generator =>
        apply Subtype.ext
        exact rhoEquationContextStep_canonicalize_eq generator
    | refl term => rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH
  preservesReflectiveScope := by
    intro free bound sort term safe
    exact canonicalize_reflectiveScopeSafeAt safe

/-- Restrict the same rho canonicalizer to the exact admitted reflective
fibre.  The raw normalizer is still `rhoCanonicalizeOpenTerm`; this
construction only retains the quote-safety evidence in the carrier. -/
def rhoCanonicalizeReflectiveOpenTerm {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort rhoCalc}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile rhoCalc free
      bound sort) :
    ReflectiveWellSorted.OpenTerm rhoReflectionProfile rhoCalc free bound
      sort :=
  ⟨(rhoCanonicalizeOpenTerm term.toCore).1,
    (rhoCanonicalizeOpenTerm term.toCore).2,
    canonicalize_reflectiveScopeSafeAt term.2.2⟩

@[simp]
theorem rhoCanonicalizeReflectiveOpenTerm_pattern
    {free : FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCalc}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile rhoCalc free
      bound sort) :
    (rhoCanonicalizeReflectiveOpenTerm term).1 = canonicalize term.1 :=
  rfl

/-- The rho canonical section on exactly the quote-safe fibre selected by
the admitted reflection extension. -/
def rhoFiberOpenSection : ComputableReflectiveFiberSection rhoIGSLT
    rhoCalcValidatedReflective.admittedReflection where
  normalize := rhoCanonicalizeReflectiveOpenTerm
  equivalent := by
    intro free bound sort term
    have membership :
        List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
          rhoReflectionProfile.presentations := by
      change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
        [rhoReflectivePresentation.toReflectivePresentationDecl]
      exact .head _
    apply Relation.EqvGen.rel
    apply ReflectiveEquationContextStep.reflectiveInContext .hole membership
    change
      ReflectiveCanonical.canonicalize rhoReflectivePresentation
          (Canonical.canonicalize term.1) =
        ReflectiveCanonical.canonicalize rhoReflectivePresentation term.1
    simpa only [derivedCanonicalize_eq] using
      Canonical.canonicalize_idempotent term.1
  complete := by
    intro free bound sort left right equivalent
    induction equivalent with
    | rel left right generator =>
        apply Subtype.ext
        exact rhoEquationContextStep_canonicalize_eq generator
    | refl term => rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH

/-- Rho normalization transported through the exact generic/established
closed-carrier equivalence. -/
def rhoNormalize (term : rhoIGSLT.toGSLT.Term) : rhoIGSLT.toGSLT.Term :=
  openTermEmptyToClosed (rhoOpenSection.normalize (closedTermToOpen term))

@[simp]
theorem rhoNormalize_pattern (term : rhoIGSLT.toGSLT.Term) :
    (rhoNormalize term).1 = Canonical.canonicalize term.1 :=
  rfl

/-- The paper-facing closed canonical section is the restriction of rho's
reflection-indexed open section.  Its relation is explicitly the one selected
by the admitted rho reflection fibre, not the five-field core relation. -/
def rhoCanonicalSection : ComputableReflectiveCanonicalSection rhoIGSLT
    rhoCalcValidatedReflective.admittedReflection :=
  rhoOpenSection.toCanonicalSection

/-- Generic rho canonical equality is computed by the established rho
canonicalizer on raw patterns. -/
theorem rho_equivalent_iff_canonicalize_eq
    (left right : rhoIGSLT.toGSLT.Term) :
    (reflectiveClosedEquationSetoid rhoIGSLT
      rhoCalcValidatedReflective.admittedReflection).r left right ↔
      Canonical.canonicalize left.1 = Canonical.canonicalize right.1 := by
  constructor
  · intro equivalent
    exact congrArg Subtype.val (rhoCanonicalSection.complete equivalent)
  · intro representatives
    apply Relation.EqvGen.rel
    apply ReflectiveEquationContextStep.reflectiveInContext .hole
    · change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
        [rhoReflectivePresentation.toReflectivePresentationDecl]
      exact .head _
    · simpa only [derivedCanonicalize_eq] using representatives

/-- The quotient representative computes the same raw canonical pattern as
normalizing an explicit generic rho term. -/
@[simp]
theorem rhoRepresentative_mk_pattern (term : rhoIGSLT.toGSLT.Term) :
    (rhoCanonicalSection.normalize term).1 =
      Canonical.canonicalize term.1 :=
  rfl

/-- A closed process containing one static quote/drop cancellation beneath
an executable-free outer Drop. -/
def closedQuoteDropShell : RhoClosedTerm rhoProc :=
  ⟨.apply "PDrop"
      [.apply "NQuote"
        [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]]],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.drop (.quote (.drop (.quote .unit))), by decide⟩⟩

/-- Positive control: canonicalization removes the static quote/drop shell
without granting free Drop an executable step. -/
theorem rhoCanonicalSection_quote_drop :
    let process : rhoIGSLT.toGSLT.Term :=
      ReflectiveWellSorted.ClosedTerm.toCore
        (presentedRhoProcessEquiv.symm closedQuoteDropShell)
    (rhoCanonicalSection.normalize process).1 =
      .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]] := by
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
