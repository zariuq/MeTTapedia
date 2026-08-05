import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Typing preservation for keyed reflective canonicalization

An executable representative may order parallel processes by any linear key.
This file proves that the choice of key is irrelevant to the derived
name/process sorting judgment: splicing, unit removal, permutation, and
collapse all remain inside the authored process fiber.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A derived process-list judgment is pointwise over list membership. -/
theorem procListWellSorted_iff_forall_mem
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern} :
    ProcListWellSorted presentation free bound processes ↔
      ∀ process ∈ processes, ProcWellSorted presentation free bound process := by
  constructor
  · intro typed process membership
    induction processes generalizing process with
    | nil => simp at membership
    | cons head tail inductionHypothesis =>
        cases typed with
        | cons headTyped tailTyped =>
            rcases List.mem_cons.mp membership with rfl | membership
            · exact headTyped
            · exact inductionHypothesis tailTyped process membership
  · intro pointwise
    induction processes with
    | nil => exact .nil
    | cons process processes inductionHypothesis =>
        exact .cons (pointwise process (by simp))
          (inductionHypothesis fun member membership =>
            pointwise member (by simp [membership]))

/-- Reflective parallel splicing preserves the homogeneous process-list
fiber. -/
theorem parallelSplice_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process) :
    ProcListWellSorted presentation free bound
      (parallelSplice presentation.toReflectivePresentationDecl process) := by
  cases typed with
  | bvar lookup => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.bvar lookup)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | fvar lookup => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.fvar lookup)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | unit => simpa [parallelSplice] using
      (ProcListWellSorted.cons
        (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor []))
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | drop nameTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.drop nameTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | output channelTyped payloadTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons
        (ProcWellSorted.output channelTyped payloadTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | input channelTyped bodyTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.input channelTyped bodyTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | parallel processesTyped => simpa [parallelSplice] using processesTyped

/-- Key sorting, flattening, and unit removal preserve process-list typing. -/
theorem normalizeParallelElementsBy_procListWellSorted
    {Key : Type} [LinearOrder Key]
    (key : Pattern → Key)
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcListWellSorted presentation free bound
      (normalizeParallelElementsBy key
        presentation.toReflectivePresentationDecl processes) := by
  rw [procListWellSorted_iff_forall_mem] at typed ⊢
  intro process membership
  have sourceMembership : process ∈
      ((processes.flatMap
        (parallelSplice presentation.toReflectivePresentationDecl)).filter
          fun pattern =>
            pattern ≠ .apply presentation.parallelUnitConstructor []) :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).mem_iff.mp
      membership
  have flatMembership := List.mem_of_mem_filter sourceMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, processMember⟩ := flatMembership
  exact (procListWellSorted_iff_forall_mem.mp
    (parallelSplice_procListWellSorted (typed source sourceMember)))
      process processMember

/-- Removing representation-only empty and singleton wrappers preserves the
derived process judgment. -/
theorem collapseParallel_procWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcWellSorted presentation free bound
      (collapseParallel presentation.toReflectivePresentationDecl processes) := by
  cases processes with
  | nil => exact .unit
  | cons process processes =>
      cases processes with
      | nil =>
          exact (procListWellSorted_iff_forall_mem.mp typed) process (by simp)
      | cons second remainder => exact .parallel typed

/-- The post-order quote/drop contraction maps a sorted process to a sorted
name. -/
theorem finishQuote_nameWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process) :
    NameWellSorted presentation free bound
      (finishNormalizeReflectiveApply
        presentation.toReflectivePresentationDecl
        presentation.quoteConstructor [process]) := by
  cases typed with
  | bvar lookup => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote (ProcWellSorted.bvar lookup))
  | fvar lookup => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote (ProcWellSorted.fvar lookup))
  | unit => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote
        (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor [])))
  | drop nameTyped => simpa [finishNormalizeReflectiveApply] using nameTyped
  | output channelTyped payloadTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.output channelTyped payloadTyped))
  | input channelTyped bodyTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.input channelTyped bodyTyped))
  | parallel processesTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.parallel processesTyped))

mutual
  /-- Depth-aware keyed canonicalization preserves the derived name fiber. -/
  theorem canonicalizeByAt_nameWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {name : Pattern}
      (typed : NameWellSorted presentation free bound name) :
      NameWellSorted presentation free bound
        (canonicalizeByAt key presentation.toReflectivePresentationDecl
          availableDepth name) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped =>
        simp only [canonicalizeByAt, beq_self_eq_true, if_true,
          canonicalizeListByAt]
        exact finishQuote_nameWellSorted
          (canonicalizeByAt_procWellSorted key presentation quote_ne_drop
            0 processTyped)

  /-- Depth-aware keyed canonicalization preserves the derived process
  fiber. -/
  theorem canonicalizeByAt_procWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {process : Pattern}
      (typed : ProcWellSorted presentation free bound process) :
      ProcWellSorted presentation free bound
        (canonicalizeByAt key presentation.toReflectivePresentationDecl
          availableDepth process) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | unit =>
        simp [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply]
        exact (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor []))
    | drop nameTyped =>
        have drop_ne_quote : presentation.dropConstructor ≠
            presentation.quoteConstructor := Ne.symm quote_ne_drop
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, drop_ne_quote] using
          (ProcWellSorted.drop
            (canonicalizeByAt_nameWellSorted key presentation
              quote_ne_drop availableDepth nameTyped))
    | output channelTyped payloadTyped =>
        let childDepth :=
          if presentation.outputConstructor == presentation.quoteConstructor
          then 0 else availableDepth
        have channelNormalized := canonicalizeByAt_nameWellSorted key
          presentation quote_ne_drop childDepth channelTyped
        have payloadNormalized := canonicalizeByAt_procWellSorted key
          presentation quote_ne_drop childDepth payloadTyped
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, childDepth] using
          (ProcWellSorted.output channelNormalized payloadNormalized)
    | input channelTyped bodyTyped =>
        let childDepth :=
          if presentation.inputConstructor == presentation.quoteConstructor
          then 0 else availableDepth
        have channelNormalized := canonicalizeByAt_nameWellSorted key
          presentation quote_ne_drop childDepth channelTyped
        have bodyNormalized := canonicalizeByAt_procWellSorted key
          presentation quote_ne_drop (childDepth + 1) bodyTyped
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, childDepth] using
          (ProcWellSorted.input channelNormalized bodyNormalized)
    | parallel processesTyped =>
        simp only [canonicalizeByAt, beq_self_eq_true, if_true]
        apply collapseParallel_procWellSorted
        apply normalizeParallelElementsBy_procListWellSorted
        exact canonicalizeListByAt_procListWellSorted key presentation
          quote_ne_drop availableDepth processesTyped

  /-- Pointwise process-list companion to keyed canonicalization. -/
  theorem canonicalizeListByAt_procListWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted presentation free bound processes) :
      ProcListWellSorted presentation free bound
        (canonicalizeListByAt key presentation.toReflectivePresentationDecl
          availableDepth processes) := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        exact .cons
          (canonicalizeByAt_procWellSorted key presentation
            quote_ne_drop availableDepth processTyped)
          (canonicalizeListByAt_procListWellSorted key presentation
            quote_ne_drop availableDepth processesTyped)
end

/-! ## Object-language preservation -/

private theorem isObjectPatternList_iff_forall_mem_keyed
    {patterns : List Pattern} :
    isObjectPatternList patterns = true ↔
      ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons pattern patterns inductionHypothesis =>
      simp [isObjectPatternList, inductionHypothesis, or_imp, forall_and]

private theorem parallelSplice_isObjectPatternList
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (object : isObjectPattern pattern = true) :
    isObjectPatternList (parallelSplice declaration pattern) = true := by
  cases pattern with
  | bvar index => simpa [parallelSplice, isObjectPatternList] using object
  | fvar name => simpa [parallelSplice, isObjectPatternList] using object
  | apply constructor arguments =>
      simpa [parallelSplice, isObjectPatternList] using object
  | lambda binder body =>
      simpa [parallelSplice, isObjectPatternList] using object
  | multiLambda arity binders body =>
      simpa [parallelSplice, isObjectPatternList] using object
  | subst body replacement => simp [isObjectPattern] at object
  | collection collectionType elements rest =>
      cases rest with
      | some restName => simp [isObjectPattern] at object
      | none =>
          by_cases isParallel : collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [parallelSplice, isObjectPattern] using object
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [parallelSplice, notParallelBool, isObjectPattern,
              isObjectPatternList] using object

private theorem normalizeParallelElementsBy_isObjectPatternList
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (object : isObjectPatternList patterns = true) :
    isObjectPatternList
        (normalizeParallelElementsBy key declaration patterns) = true := by
  rw [isObjectPatternList_iff_forall_mem_keyed] at object ⊢
  intro member membership
  have filteredMembership : member ∈
      ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []) :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).mem_iff.mp
      membership
  have flatMembership := List.mem_of_mem_filter filteredMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, memberMember⟩ := flatMembership
  exact (isObjectPatternList_iff_forall_mem_keyed.mp
    (parallelSplice_isObjectPatternList declaration
      (object source sourceMember))) member memberMember

private theorem collapseParallel_isObjectPattern
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (object : isObjectPatternList patterns = true) :
    isObjectPattern (collapseParallel declaration patterns) = true := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      cases patterns with
      | nil => simpa [collapseParallel, isObjectPatternList] using object
      | cons second remainder =>
          simpa [collapseParallel, isObjectPattern] using object

private theorem finishNormalizeReflectiveApply_isObjectPattern
    (declaration : ReflectivePresentationDecl) (constructor : String)
    {arguments : List Pattern}
    (object : isObjectPatternList arguments = true) :
    isObjectPattern
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      true := by
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil => simp [finishNormalizeReflectiveApply, isObjectPattern,
        isObjectPatternList]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder =>
            simpa [finishNormalizeReflectiveApply, isObjectPattern,
              isObjectPatternList] using object
        | nil =>
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply, isObjectPattern,
                      isObjectPatternList] at object ⊢
                | cons name tail =>
                    cases tail with
                    | cons second remainder =>
                        simpa [finishNormalizeReflectiveApply, isObjectPattern,
                          isObjectPatternList] using object
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simpa [finishNormalizeReflectiveApply,
                            isObjectPattern, isObjectPatternList] using object
                        · simpa [finishNormalizeReflectiveApply, isDrop,
                            isObjectPattern, isObjectPatternList] using object
            | _ =>
                simp [finishNormalizeReflectiveApply, isObjectPattern,
                  isObjectPatternList] at object ⊢ <;> exact object
  · have notQuoteBool :
        (constructor == declaration.quoteConstructor) = false :=
      beq_eq_false_iff_ne.mpr isQuote
    simpa [finishNormalizeReflectiveApply, notQuoteBool, isObjectPattern]
      using object

/-- Key-parametric reflective canonicalization preserves the boundary between
object terms and schema-only substitution/open-collection forms. -/
theorem canonicalizeByAt_isObjectPattern
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    ∀ availableDepth pattern,
      isObjectPattern pattern = true →
        isObjectPattern
            (canonicalizeByAt key declaration availableDepth pattern) = true
  := by
  intro availableDepth pattern object
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have argumentsObject : isObjectPatternList
          (canonicalizeListByAt key declaration
            (if constructor == declaration.quoteConstructor then 0
              else availableDepth) arguments) = true := by
        rw [canonicalizeListByAt_eq_map,
          isObjectPatternList_iff_forall_mem_keyed]
        intro normalizedArgument normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨argument, argumentMember, rfl⟩ := normalizedMember
        exact inductionHypothesis argument argumentMember _
          ((isObjectPatternList_iff_forall_mem_keyed.mp object)
            argument argumentMember)
      exact finishNormalizeReflectiveApply_isObjectPattern declaration
        constructor argumentsObject
  | hlambda binder body inductionHypothesis =>
      simpa [canonicalizeByAt, isObjectPattern] using
        inductionHypothesis (availableDepth + 1) object
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [canonicalizeByAt, isObjectPattern] using
        inductionHypothesis (availableDepth + arity) object
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      cases rest with
      | some restName => simp [isObjectPattern] at object
      | none =>
          have elementsObject : isObjectPatternList
              (canonicalizeListByAt key declaration availableDepth elements) =
              true := by
            rw [canonicalizeListByAt_eq_map,
              isObjectPatternList_iff_forall_mem_keyed]
            intro normalizedElement normalizedMember
            rw [List.mem_map] at normalizedMember
            obtain ⟨element, elementMember, rfl⟩ := normalizedMember
            exact inductionHypothesis element elementMember _
              ((isObjectPatternList_iff_forall_mem_keyed.mp
                (by simpa [isObjectPattern] using object)) element elementMember)
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [canonicalizeByAt] using
              collapseParallel_isObjectPattern declaration
                (normalizeParallelElementsBy_isObjectPatternList
                  (key availableDepth) declaration elementsObject)
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [canonicalizeByAt, notParallelBool, isObjectPattern] using
              elementsObject

/-- Two-depth keyed canonicalization preserves the boundary between object
terms and schema-only substitution/open-collection forms.  The structural
depth is available to the key but cannot change the term constructors. -/
theorem canonicalizeByDepths_isObjectPattern
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    ∀ availableDepth scopeDepth pattern,
      isObjectPattern pattern = true →
        isObjectPattern
            (canonicalizeByDepths key declaration availableDepth scopeDepth
              pattern) = true := by
  intro availableDepth scopeDepth pattern object
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have argumentsObject : isObjectPatternList
          (canonicalizeListByDepths key declaration
            (if constructor == declaration.quoteConstructor then 0
              else availableDepth) scopeDepth arguments) = true := by
        rw [canonicalizeListByDepths_eq_map,
          isObjectPatternList_iff_forall_mem_keyed]
        intro normalizedArgument normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨argument, argumentMember, rfl⟩ := normalizedMember
        exact inductionHypothesis argument argumentMember _ _
          ((isObjectPatternList_iff_forall_mem_keyed.mp object)
            argument argumentMember)
      exact finishNormalizeReflectiveApply_isObjectPattern declaration
        constructor argumentsObject
  | hlambda binder body inductionHypothesis =>
      simpa [canonicalizeByDepths, isObjectPattern] using
        inductionHypothesis (availableDepth + 1) (scopeDepth + 1) object
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [canonicalizeByDepths, isObjectPattern] using
        inductionHypothesis (availableDepth + arity) (scopeDepth + arity) object
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      cases rest with
      | some restName => simp [isObjectPattern] at object
      | none =>
          have elementsObject : isObjectPatternList
              (canonicalizeListByDepths key declaration availableDepth
                scopeDepth elements) = true := by
            rw [canonicalizeListByDepths_eq_map,
              isObjectPatternList_iff_forall_mem_keyed]
            intro normalizedElement normalizedMember
            rw [List.mem_map] at normalizedMember
            obtain ⟨element, elementMember, rfl⟩ := normalizedMember
            exact inductionHypothesis element elementMember _ _
              ((isObjectPatternList_iff_forall_mem_keyed.mp
                (by simpa [isObjectPattern] using object)) element elementMember)
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [canonicalizeByDepths] using
              collapseParallel_isObjectPattern declaration
                (normalizeParallelElementsBy_isObjectPatternList
                  (key availableDepth scopeDepth) declaration elementsObject)
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [canonicalizeByDepths, notParallelBool, isObjectPattern] using
              elementsObject

/-! ## Canonical binder-metadata preservation -/

private theorem canonicalBinderMetadataList_iff_forall_mem_keyed
    {patterns : List Pattern} :
    Pattern.hasCanonicalBinderMetadataList patterns = true ↔
      ∀ pattern ∈ patterns,
        pattern.hasCanonicalBinderMetadata = true := by
  induction patterns with
  | nil => simp [Pattern.hasCanonicalBinderMetadataList]
  | cons pattern patterns inductionHypothesis =>
      simp [Pattern.hasCanonicalBinderMetadataList, inductionHypothesis,
        or_imp, forall_and]

private theorem parallelSplice_hasCanonicalBinderMetadataList
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (canonical : pattern.hasCanonicalBinderMetadata = true) :
    Pattern.hasCanonicalBinderMetadataList
        (parallelSplice declaration pattern) = true := by
  cases pattern with
  | bvar index =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | fvar name =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | apply constructor arguments =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | lambda binder body =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | multiLambda arity binders body =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | subst body replacement =>
      simpa [parallelSplice, Pattern.hasCanonicalBinderMetadataList] using
        canonical
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simpa [parallelSplice, Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList] using canonical
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [parallelSplice, Pattern.hasCanonicalBinderMetadata,
              Pattern.hasCanonicalBinderMetadataList] using canonical
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [parallelSplice, notParallelBool,
              Pattern.hasCanonicalBinderMetadata,
              Pattern.hasCanonicalBinderMetadataList] using canonical

private theorem normalizeParallelElementsBy_hasCanonicalBinderMetadataList
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (canonical :
      Pattern.hasCanonicalBinderMetadataList patterns = true) :
    Pattern.hasCanonicalBinderMetadataList
        (normalizeParallelElementsBy key declaration patterns) = true := by
  rw [canonicalBinderMetadataList_iff_forall_mem_keyed] at canonical ⊢
  intro member membership
  have filteredMembership : member ∈
      ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []) :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).mem_iff.mp
      membership
  have flatMembership := List.mem_of_mem_filter filteredMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, memberMember⟩ := flatMembership
  exact (canonicalBinderMetadataList_iff_forall_mem_keyed.mp
    (parallelSplice_hasCanonicalBinderMetadataList declaration
      (canonical source sourceMember))) member memberMember

private theorem collapseParallel_hasCanonicalBinderMetadata
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (canonical :
      Pattern.hasCanonicalBinderMetadataList patterns = true) :
    (collapseParallel declaration patterns).hasCanonicalBinderMetadata =
      true := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      cases patterns with
      | nil =>
          simpa [collapseParallel,
            Pattern.hasCanonicalBinderMetadataList] using canonical
      | cons second remainder =>
          simpa [collapseParallel,
            Pattern.hasCanonicalBinderMetadata] using canonical

private theorem finishNormalizeReflectiveApply_hasCanonicalBinderMetadata
    (declaration : ReflectivePresentationDecl) (constructor : String)
    {arguments : List Pattern}
    (canonical :
      Pattern.hasCanonicalBinderMetadataList arguments = true) :
    (finishNormalizeReflectiveApply declaration constructor arguments
      ).hasCanonicalBinderMetadata = true := by
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [finishNormalizeReflectiveApply,
          Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder =>
            simpa [finishNormalizeReflectiveApply,
              Pattern.hasCanonicalBinderMetadata,
              Pattern.hasCanonicalBinderMetadataList] using canonical
        | nil =>
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply,
                      Pattern.hasCanonicalBinderMetadata,
                      Pattern.hasCanonicalBinderMetadataList] at canonical ⊢
                | cons name tail =>
                    cases tail with
                    | cons second remainder =>
                        simpa [finishNormalizeReflectiveApply,
                          Pattern.hasCanonicalBinderMetadata,
                          Pattern.hasCanonicalBinderMetadataList] using
                            canonical
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simpa [finishNormalizeReflectiveApply,
                            Pattern.hasCanonicalBinderMetadata,
                            Pattern.hasCanonicalBinderMetadataList] using
                              canonical
                        · simpa [finishNormalizeReflectiveApply, isDrop,
                            Pattern.hasCanonicalBinderMetadata,
                            Pattern.hasCanonicalBinderMetadataList] using
                              canonical
            | _ =>
                simp [finishNormalizeReflectiveApply,
                  Pattern.hasCanonicalBinderMetadata,
                  Pattern.hasCanonicalBinderMetadataList] at canonical ⊢ <;>
                    exact canonical
  · have notQuoteBool :
        (constructor == declaration.quoteConstructor) = false :=
      beq_eq_false_iff_ne.mpr isQuote
    simpa [finishNormalizeReflectiveApply, notQuoteBool,
      Pattern.hasCanonicalBinderMetadata] using canonical

/-- Two-depth keyed reflective canonicalization preserves canonical locally
nameless binder metadata.  The semantic key can change only the order of
parallel occurrences; it never becomes an authority for binder names. -/
theorem canonicalizeByDepths_hasCanonicalBinderMetadata
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    ∀ availableDepth scopeDepth pattern,
      pattern.hasCanonicalBinderMetadata = true →
        (canonicalizeByDepths key declaration availableDepth scopeDepth
          pattern).hasCanonicalBinderMetadata = true := by
  intro availableDepth scopeDepth pattern canonical
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have argumentsCanonical :
          Pattern.hasCanonicalBinderMetadataList
            (canonicalizeListByDepths key declaration
              (if constructor == declaration.quoteConstructor then 0
                else availableDepth) scopeDepth arguments) = true := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalBinderMetadataList_iff_forall_mem_keyed]
        intro normalizedArgument normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨argument, argumentMember, rfl⟩ := normalizedMember
        exact inductionHypothesis argument argumentMember _ _
          ((canonicalBinderMetadataList_iff_forall_mem_keyed.mp canonical)
            argument argumentMember)
      exact finishNormalizeReflectiveApply_hasCanonicalBinderMetadata
        declaration constructor argumentsCanonical
  | hlambda binder body inductionHypothesis =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simpa [canonicalizeByDepths, Pattern.hasCanonicalBinderMetadata] using
        And.intro canonical.1
          (inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
            canonical.2)
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simpa [canonicalizeByDepths, Pattern.hasCanonicalBinderMetadata] using
        And.intro canonical.1
          (inductionHypothesis (availableDepth + arity) (scopeDepth + arity)
            canonical.2)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simpa [canonicalizeByDepths, Pattern.hasCanonicalBinderMetadata] using
        And.intro
          (bodyInduction (availableDepth + 1) (scopeDepth + 1) canonical.1)
          (replacementInduction availableDepth scopeDepth canonical.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsCanonical :
          Pattern.hasCanonicalBinderMetadataList
            (canonicalizeListByDepths key declaration availableDepth
              scopeDepth elements) = true := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalBinderMetadataList_iff_forall_mem_keyed]
        intro normalizedElement normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨element, elementMember, rfl⟩ := normalizedMember
        exact inductionHypothesis element elementMember _ _
          ((canonicalBinderMetadataList_iff_forall_mem_keyed.mp canonical)
            element elementMember)
      cases rest with
      | some restName =>
          simpa [canonicalizeByDepths,
            Pattern.hasCanonicalBinderMetadata] using elementsCanonical
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [canonicalizeByDepths] using
              collapseParallel_hasCanonicalBinderMetadata declaration
                (normalizeParallelElementsBy_hasCanonicalBinderMetadataList
                  (key availableDepth scopeDepth) declaration
                  elementsCanonical)
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [canonicalizeByDepths, notParallelBool,
              Pattern.hasCanonicalBinderMetadata] using elementsCanonical

/-- One-depth keyed canonicalization is the structural-depth-insensitive
specialization of the two-depth metadata theorem. -/
theorem canonicalizeByAt_hasCanonicalBinderMetadata
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth : Nat) (pattern : Pattern)
    (canonical : pattern.hasCanonicalBinderMetadata = true) :
    (canonicalizeByAt key declaration availableDepth pattern
      ).hasCanonicalBinderMetadata = true := by
  rw [← canonicalizeByDepths_ignoreScope key declaration availableDepth 0
    pattern]
  exact canonicalizeByDepths_hasCanonicalBinderMetadata
    (fun availableDepth _ pattern => key availableDepth pattern)
    declaration availableDepth 0 pattern canonical

/-! ## Quote-aware scope preservation -/

private theorem binderSafeListAt_mono_keyed
    (quoteConstructor : String) {small large : Nat}
    {patterns : List Pattern}
    (safe : binderSafeListAt quoteConstructor small patterns = true)
    (scope : small ≤ large) :
    binderSafeListAt quoteConstructor large patterns = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro pattern membership
  exact binderSafeAt_mono quoteConstructor (safe pattern membership) scope

private theorem parallelSplice_binderSafeListAt
    (declaration : ReflectivePresentationDecl)
    (quoteConstructor : String) (depth : Nat) {pattern : Pattern}
    (safe : binderSafeAt quoteConstructor depth pattern = true) :
    binderSafeListAt quoteConstructor depth
        (parallelSplice declaration pattern) = true := by
  cases pattern with
  | bvar index =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | fvar name =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | apply constructor arguments =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | lambda binder body =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | multiLambda arity binders body =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | subst body replacement =>
      simpa [parallelSplice, binderSafeListAt] using safe
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simpa [parallelSplice, binderSafeAt, binderSafeListAt] using safe
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [parallelSplice, binderSafeAt] using safe
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [parallelSplice, notParallelBool, binderSafeAt,
              binderSafeListAt] using safe

private theorem normalizeParallelElementsBy_binderSafeListAt
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quoteConstructor : String) (depth : Nat) {patterns : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth patterns = true) :
    binderSafeListAt quoteConstructor depth
        (normalizeParallelElementsBy key declaration patterns) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro member membership
  have filteredMembership : member ∈
      ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []) :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).mem_iff.mp
      membership
  have flatMembership := List.mem_of_mem_filter filteredMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, memberMember⟩ := flatMembership
  exact (binderSafeListAt_eq_true_iff _ _ _).mp
    (parallelSplice_binderSafeListAt declaration quoteConstructor depth
      (safe source sourceMember)) member memberMember

private theorem collapseParallel_binderSafeAt
    (declaration : ReflectivePresentationDecl)
    (quoteConstructor : String) (depth : Nat) {patterns : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth patterns = true) :
    binderSafeAt quoteConstructor depth
        (collapseParallel declaration patterns) = true := by
  cases patterns with
  | nil => simp [collapseParallel, binderSafeAt, binderSafeListAt]
  | cons pattern patterns =>
      cases patterns with
      | nil => simpa [collapseParallel, binderSafeListAt] using safe
      | cons second remainder =>
          simpa [collapseParallel, binderSafeAt] using safe

private theorem finishNormalizeReflectiveApply_binderSafeAt
    (declaration : ReflectivePresentationDecl)
    (observedQuote constructor : String) (depth : Nat)
    {arguments : List Pattern}
    (safe : binderSafeAt observedQuote depth
      (.apply constructor arguments) = true) :
    binderSafeAt observedQuote depth
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      true := by
  have safeAtDepth :
      binderSafeListAt observedQuote depth arguments = true := by
    cases arguments with
    | nil => simp [binderSafeListAt]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder => simpa [binderSafeAt] using safe
        | nil =>
            by_cases isObserved : constructor = observedQuote
            · subst constructor
              have argumentSafe :
                  binderSafeAt observedQuote 0 argument = true := by
                simpa [binderSafeAt] using safe
              simp only [binderSafeListAt, Bool.and_true]
              exact binderSafeAt_mono observedQuote argumentSafe
                (Nat.zero_le depth)
            · simpa [binderSafeAt, isObserved, binderSafeListAt] using safe
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [finishNormalizeReflectiveApply, binderSafeAt,
          binderSafeListAt]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder =>
            simpa [finishNormalizeReflectiveApply, binderSafeAt] using
              safeAtDepth
        | nil =>
            have argumentSafe : binderSafeAt observedQuote
                (if declaration.quoteConstructor == observedQuote then 0
                  else depth) argument = true := by
              by_cases outerObserved :
                  declaration.quoteConstructor = observedQuote
              · have outerDecision :
                    (declaration.quoteConstructor == observedQuote) = true :=
                  beq_iff_eq.mpr outerObserved
                simpa [binderSafeAt, outerDecision] using safe
              · have outerDecision :
                    (declaration.quoteConstructor == observedQuote) = false :=
                  beq_eq_false_iff_ne.mpr outerObserved
                simpa [binderSafeAt, outerDecision, binderSafeListAt] using
                  safe
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simpa [finishNormalizeReflectiveApply] using safe
                | cons name tail =>
                    cases tail with
                    | cons second remainder =>
                        simpa [finishNormalizeReflectiveApply] using safe
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          have nestedSafe : binderSafeAt observedQuote
                              (if declaration.quoteConstructor == observedQuote
                                then 0 else depth)
                              (.apply declaration.dropConstructor [name]) =
                              true := argumentSafe
                          have nameSafeAtDepth :
                              binderSafeAt observedQuote depth name = true := by
                            by_cases outerObserved :
                                declaration.quoteConstructor = observedQuote
                            · have outerDecision :
                                  (declaration.quoteConstructor ==
                                    observedQuote) = true :=
                                beq_iff_eq.mpr outerObserved
                              simp only [outerDecision, if_true] at nestedSafe
                              by_cases dropObserved :
                                  declaration.dropConstructor = observedQuote
                              · have dropDecision :
                                    (declaration.dropConstructor ==
                                      observedQuote) = true :=
                                  beq_iff_eq.mpr dropObserved
                                simp only [binderSafeAt, dropDecision, if_true]
                                  at nestedSafe
                                exact binderSafeAt_mono observedQuote nestedSafe
                                  (Nat.zero_le depth)
                              · have dropDecision :
                                    (declaration.dropConstructor ==
                                      observedQuote) = false :=
                                  beq_eq_false_iff_ne.mpr dropObserved
                                simp only [binderSafeAt, dropDecision,
                                  binderSafeListAt, Bool.and_true] at nestedSafe
                                exact binderSafeAt_mono observedQuote nestedSafe
                                  (Nat.zero_le depth)
                            · have outerDecision :
                                  (declaration.quoteConstructor ==
                                    observedQuote) = false :=
                                beq_eq_false_iff_ne.mpr outerObserved
                              simp only [outerDecision] at nestedSafe
                              by_cases dropObserved :
                                  declaration.dropConstructor = observedQuote
                              · have dropDecision :
                                    (declaration.dropConstructor ==
                                      observedQuote) = true :=
                                  beq_iff_eq.mpr dropObserved
                                simp only [binderSafeAt, dropDecision, if_true]
                                  at nestedSafe
                                exact binderSafeAt_mono observedQuote nestedSafe
                                  (Nat.zero_le depth)
                              · have dropDecision :
                                    (declaration.dropConstructor ==
                                      observedQuote) = false :=
                                  beq_eq_false_iff_ne.mpr dropObserved
                                simpa [binderSafeAt, dropDecision,
                                  binderSafeListAt] using nestedSafe
                          simpa [finishNormalizeReflectiveApply] using
                            nameSafeAtDepth
                        · simpa [finishNormalizeReflectiveApply, isDrop] using
                            safe
            | _ =>
                simpa [finishNormalizeReflectiveApply] using safe
  · have notQuoteBool :
        (constructor == declaration.quoteConstructor) = false :=
      beq_eq_false_iff_ne.mpr isQuote
    simpa [finishNormalizeReflectiveApply, notQuoteBool] using safe

/-- Two-depth keyed canonicalization preserves quote-aware local scope for
every observed quotation constructor.  The selected presentation controls
normalization, while `observedQuote` controls only the invariant being
transported. -/
theorem canonicalizeByDepths_binderSafeAt
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (observedQuote : String) :
    ∀ availableDepth scopeDepth safetyDepth pattern,
      binderSafeAt observedQuote safetyDepth pattern = true →
        binderSafeAt observedQuote safetyDepth
          (canonicalizeByDepths key declaration availableDepth scopeDepth
            pattern) = true := by
  intro availableDepth scopeDepth safetyDepth pattern safe
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth safetyDepth with
  | hbvar index => simpa [canonicalizeByDepths] using safe
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      let childSafetyDepth := match arguments with
        | [_] => if constructor == observedQuote then 0 else safetyDepth
        | _ => safetyDepth
      have argumentsSafe : binderSafeListAt observedQuote childSafetyDepth
          arguments = true := by
        cases arguments with
        | nil => simp [binderSafeListAt]
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases isObserved : constructor = observedQuote
                · have observedDecision :
                      (constructor == observedQuote) = true :=
                    beq_iff_eq.mpr isObserved
                  simpa [childSafetyDepth, binderSafeAt, observedDecision,
                    binderSafeListAt] using safe
                · have observedDecision :
                      (constructor == observedQuote) = false :=
                    beq_eq_false_iff_ne.mpr isObserved
                  simpa [childSafetyDepth, binderSafeAt, observedDecision,
                    binderSafeListAt] using safe
            | cons second remainder =>
                simpa [childSafetyDepth, binderSafeAt] using safe
      have normalizedArgumentsSafe :
          binderSafeListAt observedQuote childSafetyDepth
            (canonicalizeListByDepths key declaration
              (if constructor == declaration.quoteConstructor then 0
                else availableDepth) scopeDepth arguments) = true := by
        rw [canonicalizeListByDepths_eq_map,
          binderSafeListAt_eq_true_iff]
        intro normalizedArgument normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨argument, argumentMember, rfl⟩ := normalizedMember
        exact inductionHypothesis argument argumentMember _ _ _
          ((binderSafeListAt_eq_true_iff _ _ _).mp argumentsSafe argument
            argumentMember)
      have normalizedApplySafe : binderSafeAt observedQuote safetyDepth
          (.apply constructor
            (canonicalizeListByDepths key declaration
              (if constructor == declaration.quoteConstructor then 0
                else availableDepth) scopeDepth arguments)) = true := by
        cases arguments with
        | nil => simp [canonicalizeListByDepths, binderSafeAt,
            binderSafeListAt]
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases isObserved : constructor = observedQuote
                · have observedDecision :
                      (constructor == observedQuote) = true :=
                    beq_iff_eq.mpr isObserved
                  simpa [childSafetyDepth, binderSafeAt, observedDecision,
                    canonicalizeListByDepths, binderSafeListAt] using
                      normalizedArgumentsSafe
                · have observedDecision :
                      (constructor == observedQuote) = false :=
                    beq_eq_false_iff_ne.mpr isObserved
                  simpa [childSafetyDepth, binderSafeAt, observedDecision,
                    canonicalizeListByDepths, binderSafeListAt] using
                      normalizedArgumentsSafe
            | cons second remainder =>
                simpa [childSafetyDepth, binderSafeAt,
                  canonicalizeListByDepths] using
                  normalizedArgumentsSafe
      exact finishNormalizeReflectiveApply_binderSafeAt declaration
        observedQuote constructor safetyDepth normalizedApplySafe
  | hlambda binder body inductionHypothesis =>
      have bodySafe :
          binderSafeAt observedQuote (safetyDepth + 1) body = true := by
        simpa [binderSafeAt] using safe
      simpa [canonicalizeByDepths, binderSafeAt] using
        inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
          (safetyDepth + 1) bodySafe
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodySafe :
          binderSafeAt observedQuote (safetyDepth + arity) body = true := by
        simpa [binderSafeAt] using safe
      simpa [canonicalizeByDepths, binderSafeAt] using
        inductionHypothesis (availableDepth + arity) (scopeDepth + arity)
          (safetyDepth + arity) bodySafe
  | hsubst body replacement bodyInduction replacementInduction =>
      have componentsSafe :
          binderSafeAt observedQuote (safetyDepth + 1) body = true ∧
            binderSafeAt observedQuote safetyDepth replacement = true := by
        simpa [binderSafeAt, Bool.and_eq_true] using safe
      simpa [canonicalizeByDepths, binderSafeAt, Bool.and_eq_true] using
        And.intro
          (bodyInduction (availableDepth + 1) (scopeDepth + 1)
            (safetyDepth + 1) componentsSafe.1)
          (replacementInduction availableDepth scopeDepth safetyDepth
            componentsSafe.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsSafe :
          binderSafeListAt observedQuote safetyDepth elements = true := by
        simpa [binderSafeAt] using safe
      have normalizedElementsSafe :
          binderSafeListAt observedQuote safetyDepth
            (canonicalizeListByDepths key declaration availableDepth
              scopeDepth elements) = true := by
        rw [canonicalizeListByDepths_eq_map,
          binderSafeListAt_eq_true_iff]
        intro normalizedElement normalizedMember
        rw [List.mem_map] at normalizedMember
        obtain ⟨element, elementMember, rfl⟩ := normalizedMember
        exact inductionHypothesis element elementMember _ _ _
          ((binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe element
            elementMember)
      cases rest with
      | some restName =>
          simpa [canonicalizeByDepths, binderSafeAt] using
            normalizedElementsSafe
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [canonicalizeByDepths] using
              collapseParallel_binderSafeAt declaration observedQuote
                safetyDepth
                (normalizeParallelElementsBy_binderSafeListAt
                  (key availableDepth scopeDepth) declaration observedQuote
                  safetyDepth normalizedElementsSafe)
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [canonicalizeByDepths, notParallelBool, binderSafeAt] using
              normalizedElementsSafe

/-- One-depth keyed canonicalization preserves every quote-aware scope
invariant as the scope-insensitive specialization above. -/
theorem canonicalizeByAt_binderSafeAt
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (observedQuote : String)
    (availableDepth safetyDepth : Nat) (pattern : Pattern)
    (safe : binderSafeAt observedQuote safetyDepth pattern = true) :
    binderSafeAt observedQuote safetyDepth
        (canonicalizeByAt key declaration availableDepth pattern) = true := by
  rw [← canonicalizeByDepths_ignoreScope key declaration availableDepth 0
    pattern]
  exact canonicalizeByDepths_binderSafeAt
    (fun availableDepth _ pattern => key availableDepth pattern)
    declaration observedQuote availableDepth 0 safetyDepth pattern safe

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
