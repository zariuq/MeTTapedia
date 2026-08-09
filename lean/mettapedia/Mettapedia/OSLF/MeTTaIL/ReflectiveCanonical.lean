import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# Canonical matching compiled from reflective presentation data

`ReflectivePresentationDecl` already names the quote/drop equation, parallel
collection, and parallel unit of a reflective calculus.  This module compiles
that authored data into a canonical representative and uses it only for
repeated metavariable checks in the declaration's selected rewrite rule.

Languages and rules without a unique matching declaration continue to call
the original structural matcher directly.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Reflection

/-- Splice a normalized occurrence of the declared parallel collection into
its parent parallel collection. -/
def parallelSplice (declaration : ReflectivePresentationDecl) : Pattern → List Pattern
  | pattern@(.collection collectionType elements none) =>
      if collectionType == declaration.parallelCollection then elements else [pattern]
  | pattern => [pattern]

/-- Normalize an already-recursively-normalized parallel element list. -/
def normalizeParallelElements
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) : List Pattern :=
  PatternCode.sortPatterns
    ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor [])

/-- Rebuild the declared parallel composition without representation-only
empty and singleton wrappers. -/
def collapseParallel (declaration : ReflectivePresentationDecl) : List Pattern → Pattern
  | [] => .apply declaration.parallelUnitConstructor []
  | [pattern] => pattern
  | patterns => .collection declaration.parallelCollection patterns none

mutual
  /-- Canonical representative compiled solely from a reflective declaration.

  It recursively orients the declaration's quote/drop equation and presents
  its parallel collection as a flattened, unit-free, structurally sorted bag.
  No executable drop step is introduced. -/
  def canonicalize
      (declaration : ReflectivePresentationDecl) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeList declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (canonicalize declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (canonicalize declaration body)
    | .subst body replacement =>
        .subst (canonicalize declaration body) (canonicalize declaration replacement)
    | .collection collectionType elements none =>
        let normalizedElements := canonicalizeList declaration elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElements declaration normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType (canonicalizeList declaration elements) rest

  def canonicalizeList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalize declaration pattern :: canonicalizeList declaration patterns
end

/-! ## Generic normal-form invariant -/

mutual
  /-- Intrinsic normal forms for the declaration-compiled canonicalizer.

  The predicate is phrased uniformly, rather than by hard-coded rho
  constructors: a quote may not contain an immediately reducible drop, and a
  surviving parallel node is sorted, flat, unit-free, and non-degenerate. -/
  def IsCanonical (declaration : ReflectivePresentationDecl) : Pattern → Prop
    | .bvar _ | .fvar _ => True
    | .apply constructor arguments =>
        IsCanonicalList declaration arguments ∧
          ∀ name, constructor = declaration.quoteConstructor →
            arguments ≠ [.apply declaration.dropConstructor [name]]
    | .lambda _ body | .multiLambda _ _ body =>
        IsCanonical declaration body
    | .subst body replacement =>
        IsCanonical declaration body ∧ IsCanonical declaration replacement
    | .collection collectionType elements rest =>
        IsCanonicalList declaration elements ∧
          (collectionType = declaration.parallelCollection ∧ rest = none →
            2 ≤ elements.length ∧
            PatternCode.sortPatterns elements = elements ∧
            (∀ element ∈ elements,
              element ≠ .apply declaration.parallelUnitConstructor [] ∧
              ∀ nested,
                element ≠ .collection declaration.parallelCollection nested none))

  /-- Pointwise normality for lists of patterns. -/
  def IsCanonicalList (declaration : ReflectivePresentationDecl) :
      List Pattern → Prop
    | [] => True
    | pattern :: patterns =>
        IsCanonical declaration pattern ∧
          IsCanonicalList declaration patterns
end

theorem isCanonicalList_mem (declaration : ReflectivePresentationDecl) :
    ∀ {patterns : List Pattern}, IsCanonicalList declaration patterns →
      ∀ {pattern}, pattern ∈ patterns → IsCanonical declaration pattern
  | [], _, _, membership => by simp at membership
  | head :: tail, canonical, pattern, membership => by
      rcases List.mem_cons.mp membership with rfl | tailMembership
      · exact canonical.1
      · exact isCanonicalList_mem declaration canonical.2 tailMembership

theorem isCanonicalList_of_forall (declaration : ReflectivePresentationDecl) :
    ∀ {patterns : List Pattern},
      (∀ pattern ∈ patterns, IsCanonical declaration pattern) →
        IsCanonicalList declaration patterns
  | [], _ => trivial
  | head :: tail, allCanonical =>
      ⟨allCanonical head (by simp),
        isCanonicalList_of_forall declaration (fun pattern membership =>
          allCanonical pattern (by simp [membership]))⟩

theorem canonicalizeList_length (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    (canonicalizeList declaration patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

theorem sortPatterns_perm (patterns : List Pattern) :
    List.Perm (PatternCode.sortPatterns patterns) patterns := by
  exact List.mergeSort_perm patterns _

theorem sortPatterns_mem_iff {pattern : Pattern} {patterns : List Pattern} :
    pattern ∈ PatternCode.sortPatterns patterns ↔ pattern ∈ patterns :=
  (sortPatterns_perm patterns).mem_iff

theorem sortPatterns_idempotent (patterns : List Pattern) :
    PatternCode.sortPatterns (PatternCode.sortPatterns patterns) =
      PatternCode.sortPatterns patterns := by
  exact PatternCode.sortPatterns_eq_of_perm (sortPatterns_perm patterns)

theorem normalizeParallelElements_sorted
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    PatternCode.sortPatterns (normalizeParallelElements declaration patterns) =
      normalizeParallelElements declaration patterns :=
  sortPatterns_idempotent _

/-- Classification of one member produced by reflective parallel splicing. -/
theorem mem_parallelSplice {declaration : ReflectivePresentationDecl}
    {source member : Pattern} (membership : member ∈ parallelSplice declaration source) :
    (∃ elements,
      source = .collection declaration.parallelCollection elements none ∧
        member ∈ elements) ∨
      (member = source ∧
        ∀ elements,
          source ≠ .collection declaration.parallelCollection elements none) := by
  unfold parallelSplice at membership
  split at membership
  case h_1 collectionType elements =>
    split at membership <;> simp_all
  case h_2 notCollection =>
    exact Or.inr ⟨by simpa using membership, by
      intro elements equality
      exact notCollection _ _ equality⟩

theorem normalizeParallelElements_mem_source
    {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern} {member : Pattern}
    (membership : member ∈ normalizeParallelElements declaration patterns) :
    ∃ source ∈ patterns, member ∈ parallelSplice declaration source := by
  have filteredMembership :
      member ∈
        ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
          pattern ≠ .apply declaration.parallelUnitConstructor []) :=
    sortPatterns_mem_iff.mp membership
  have flatMembership :
      member ∈ patterns.flatMap (parallelSplice declaration) :=
    (List.mem_filter.mp filteredMembership).1
  simpa [List.mem_flatMap] using flatMembership

theorem normalizeParallelElements_no_unit
    {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern} {member : Pattern}
    (membership : member ∈ normalizeParallelElements declaration patterns) :
    member ≠ .apply declaration.parallelUnitConstructor [] := by
  have filteredMembership :
      member ∈
        ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
          pattern ≠ .apply declaration.parallelUnitConstructor []) :=
    sortPatterns_mem_iff.mp membership
  exact of_decide_eq_true (List.mem_filter.mp filteredMembership).2

theorem normalizeParallelElements_member_isCanonical
    {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList declaration patterns)
    {member : Pattern}
    (membership : member ∈ normalizeParallelElements declaration patterns) :
    IsCanonical declaration member := by
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeParallelElements_mem_source membership
  have sourceCanonical :=
    isCanonicalList_mem declaration patternsCanonical sourceMembership
  rcases mem_parallelSplice memberMembership with
    ⟨elements, sourceEquality, memberInElements⟩ | ⟨rfl, _⟩
  · subst sourceEquality
    exact isCanonicalList_mem declaration sourceCanonical.1 memberInElements
  · exact sourceCanonical

theorem normalizeParallelElements_no_nested
    {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList declaration patterns)
    {member : Pattern}
    (membership : member ∈ normalizeParallelElements declaration patterns) :
    ∀ nested,
      member ≠ .collection declaration.parallelCollection nested none := by
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeParallelElements_mem_source membership
  have sourceCanonical :=
    isCanonicalList_mem declaration patternsCanonical sourceMembership
  rcases mem_parallelSplice memberMembership with
    ⟨elements, sourceEquality, memberInElements⟩ |
      ⟨rfl, sourceNotParallel⟩
  · subst sourceEquality
    exact (sourceCanonical.2 ⟨rfl, rfl⟩).2.2 member memberInElements |>.2
  · exact sourceNotParallel

theorem normalizeParallelElements_isCanonicalList
    {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList declaration patterns) :
    IsCanonicalList declaration
      (normalizeParallelElements declaration patterns) :=
  isCanonicalList_of_forall declaration (fun _ membership =>
    normalizeParallelElements_member_isCanonical patternsCanonical membership)

mutual
  /-- The declaration-compiled canonicalizer always produces an intrinsic
  normal form. -/
  theorem canonicalize_isCanonical (declaration : ReflectivePresentationDecl) :
      ∀ pattern, IsCanonical declaration (canonicalize declaration pattern)
    | .bvar _ => trivial
    | .fvar _ => trivial
    | .apply constructor arguments => by
        have argumentsCanonical :=
          canonicalizeList_isCanonical declaration arguments
        unfold canonicalize
        unfold finishNormalizeReflectiveApply
        by_cases isQuote : constructor = declaration.quoteConstructor
        · subst constructor
          simp only [beq_self_eq_true, if_true]
          generalize normalizedEquality :
              canonicalizeList declaration arguments = normalizedArguments
            at argumentsCanonical ⊢
          cases normalizedArguments with
          | nil =>
              simp [IsCanonical, IsCanonicalList]
          | cons argument remaining =>
              cases remaining with
              | nil =>
                  cases argument with
                  | apply nestedConstructor nestedArguments =>
                      cases nestedArguments with
                      | nil =>
                          simp [IsCanonical, IsCanonicalList]
                      | cons name tail =>
                          cases tail with
                          | nil =>
                              by_cases isDrop :
                                  nestedConstructor = declaration.dropConstructor
                              · subst nestedConstructor
                                simpa [IsCanonical, IsCanonicalList] using
                                  argumentsCanonical.1.1.1
                              · simpa [isDrop, IsCanonical, IsCanonicalList]
                                  using argumentsCanonical.1
                          | cons second tail =>
                              simpa [IsCanonical, IsCanonicalList] using
                                argumentsCanonical.1
                  | bvar index =>
                      simp [IsCanonical, IsCanonicalList]
                  | fvar name =>
                      simp [IsCanonical, IsCanonicalList]
                  | lambda binder body =>
                      simpa [IsCanonical, IsCanonicalList] using
                        argumentsCanonical.1
                  | multiLambda arity binders body =>
                      simpa [IsCanonical, IsCanonicalList] using
                        argumentsCanonical.1
                  | subst body replacement =>
                      simpa [IsCanonical, IsCanonicalList] using
                        argumentsCanonical.1
                  | collection collectionType elements rest =>
                      simpa [IsCanonical, IsCanonicalList] using
                        argumentsCanonical.1
              | cons second tail =>
                  simpa [IsCanonical, IsCanonicalList] using
                    argumentsCanonical
        · have notMappedQuote : ¬constructor = declaration.quoteConstructor :=
            isQuote
          simp [isQuote, IsCanonical, argumentsCanonical]
    | .lambda binder body => canonicalize_isCanonical declaration body
    | .multiLambda arity binders body =>
        canonicalize_isCanonical declaration body
    | .subst body replacement =>
        ⟨canonicalize_isCanonical declaration body,
          canonicalize_isCanonical declaration replacement⟩
    | .collection collectionType elements rest => by
        have elementsCanonical :=
          canonicalizeList_isCanonical declaration elements
        cases rest with
        | some restName =>
            simp [canonicalize, IsCanonical, elementsCanonical]
        | none =>
            by_cases isParallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              let normalized := normalizeParallelElements declaration
                (canonicalizeList declaration elements)
              have normalizedCanonical :
                  IsCanonicalList declaration normalized :=
                normalizeParallelElements_isCanonicalList elementsCanonical
              have normalizedSorted :
                  PatternCode.sortPatterns normalized = normalized :=
                normalizeParallelElements_sorted declaration _
              have normalizedProperties : ∀ element ∈ normalized,
                  element ≠ .apply declaration.parallelUnitConstructor [] ∧
                  ∀ nested,
                    element ≠
                      .collection declaration.parallelCollection nested none := by
                intro element membership
                exact ⟨normalizeParallelElements_no_unit membership,
                  normalizeParallelElements_no_nested elementsCanonical
                    membership⟩
              simp only [canonicalize, beq_self_eq_true, if_true]
              change IsCanonical declaration (collapseParallel declaration normalized)
              cases normalizedEquality : normalized with
              | nil =>
                  simp [collapseParallel, IsCanonical, IsCanonicalList]
              | cons first remaining =>
                  cases remaining with
                  | nil =>
                      rw [show collapseParallel declaration [first] = first by rfl]
                      exact isCanonicalList_mem declaration
                        (by simpa [normalizedEquality] using normalizedCanonical)
                        (by simp)
                  | cons second tail =>
                      refine ⟨by simpa [normalizedEquality] using
                        normalizedCanonical, ?_⟩
                      intro _
                      exact ⟨by simp,
                        by simpa [normalizedEquality] using normalizedSorted,
                        by simpa [normalizedEquality] using normalizedProperties⟩
            · simp [canonicalize, IsCanonical, isParallel, elementsCanonical]

  /-- Canonicalization is pointwise normal on lists. -/
  theorem canonicalizeList_isCanonical
      (declaration : ReflectivePresentationDecl) :
      ∀ patterns,
        IsCanonicalList declaration (canonicalizeList declaration patterns)
    | [] => trivial
    | pattern :: patterns =>
        ⟨canonicalize_isCanonical declaration pattern,
          canonicalizeList_isCanonical declaration patterns⟩
end

/-- A non-parallel pattern contributes exactly itself to parallel splicing. -/
theorem parallelSplice_eq_singleton_of_not_parallel
    (declaration : ReflectivePresentationDecl) (pattern : Pattern)
    (notParallel : ∀ elements,
      pattern ≠ .collection declaration.parallelCollection elements none) :
    parallelSplice declaration pattern = [pattern] := by
  cases pattern <;> try rfl
  case collection collectionType elements rest =>
    cases rest with
    | some restName => rfl
    | none =>
        by_cases sameCollection :
            collectionType = declaration.parallelCollection
        · subst collectionType
          exact False.elim (notParallel elements rfl)
        · simp [parallelSplice, sameCollection]

/-- Splicing is inert on a list whose elements contain no unguarded nested
parallel node. -/
theorem flatMap_parallelSplice_eq_self
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (noNested : ∀ pattern ∈ patterns, ∀ nested,
      pattern ≠ .collection declaration.parallelCollection nested none) :
    patterns.flatMap (parallelSplice declaration) = patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      have headSplice : parallelSplice declaration pattern = [pattern] :=
        parallelSplice_eq_singleton_of_not_parallel declaration pattern
          (noNested pattern (by simp))
      have tailNoNested : ∀ child ∈ patterns, ∀ nested,
          child ≠ .collection declaration.parallelCollection nested none := by
        intro child membership
        exact noNested child (by simp [membership])
      simp [List.flatMap_cons, headSplice,
        inductionHypothesis tailNoNested]

theorem collapseParallel_eq_collection_of_length_ge_two
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (lengthAtLeastTwo : 2 ≤ patterns.length) :
    collapseParallel declaration patterns =
      .collection declaration.parallelCollection patterns none := by
  match patterns with
  | [] => simp at lengthAtLeastTwo
  | [_] => simp at lengthAtLeastTwo
  | _ :: _ :: _ => rfl

mutual
  /-- Intrinsic declaration-normal forms are fixed points of the compiled
  canonicalizer. -/
  theorem canonicalize_eq_of_isCanonical
      (declaration : ReflectivePresentationDecl) :
      ∀ {pattern}, IsCanonical declaration pattern →
        canonicalize declaration pattern = pattern
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .apply constructor arguments, canonical => by
        have argumentsFixed :
            canonicalizeList declaration arguments = arguments :=
          canonicalizeList_eq_of_isCanonical declaration canonical.1
        unfold canonicalize
        rw [argumentsFixed]
        unfold finishNormalizeReflectiveApply
        by_cases isQuote : constructor = declaration.quoteConstructor
        · subst constructor
          simp only [beq_self_eq_true, if_true]
          cases arguments with
          | nil => rfl
          | cons argument remaining =>
              cases remaining with
              | nil =>
                  cases argument with
                  | apply nestedConstructor nestedArguments =>
                      cases nestedArguments with
                      | nil => rfl
                      | cons name tail =>
                          cases tail with
                          | nil =>
                              by_cases isDrop :
                                  nestedConstructor = declaration.dropConstructor
                              · exact False.elim
                                  (canonical.2 name rfl (by simp [isDrop]))
                              · simp [isDrop]
                          | cons second tail => rfl
                  | bvar index => rfl
                  | fvar name => rfl
                  | lambda binder body => rfl
                  | multiLambda arity binders body => rfl
                  | subst body replacement => rfl
                  | collection collectionType elements rest => rfl
              | cons second tail => simp
        · simp [isQuote]
    | .lambda binder body, canonical => by
        simp only [canonicalize]
        rw [canonicalize_eq_of_isCanonical declaration
          (pattern := body) canonical]
    | .multiLambda arity binders body, canonical => by
        simp only [canonicalize]
        rw [canonicalize_eq_of_isCanonical declaration
          (pattern := body) canonical]
    | .subst body replacement, canonical => by
        simp only [canonicalize]
        rw [canonicalize_eq_of_isCanonical declaration canonical.1,
          canonicalize_eq_of_isCanonical declaration canonical.2]
    | .collection collectionType elements rest, canonical => by
        have elementsFixed :
            canonicalizeList declaration elements = elements :=
          canonicalizeList_eq_of_isCanonical declaration canonical.1
        cases rest with
        | some restName =>
            simp [canonicalize, elementsFixed]
        | none =>
            by_cases isParallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              have properties := canonical.2 ⟨rfl, rfl⟩
              have spliceFixed :
                  elements.flatMap (parallelSplice declaration) = elements :=
                flatMap_parallelSplice_eq_self declaration
                  (fun element membership =>
                    (properties.2.2 element membership).2)
              have filterFixed :
                  elements.filter (fun element =>
                    element ≠ .apply declaration.parallelUnitConstructor []) =
                    elements :=
                List.filter_eq_self.mpr (fun element membership => by
                  simpa using (properties.2.2 element membership).1)
              simp only [canonicalize, beq_self_eq_true, if_true, elementsFixed]
              unfold normalizeParallelElements
              rw [spliceFixed, filterFixed, properties.2.1]
              exact collapseParallel_eq_collection_of_length_ge_two
                declaration properties.1
            · simp [canonicalize, elementsFixed, isParallel]

  /-- Lists of intrinsic normal forms are fixed pointwise. -/
  theorem canonicalizeList_eq_of_isCanonical
      (declaration : ReflectivePresentationDecl) :
      ∀ {patterns}, IsCanonicalList declaration patterns →
        canonicalizeList declaration patterns = patterns
    | [], _ => rfl
    | pattern :: patterns, canonical => by
        simp only [canonicalizeList]
        rw [canonicalize_eq_of_isCanonical declaration canonical.1,
          canonicalizeList_eq_of_isCanonical declaration canonical.2]
end

/-- Declaration-compiled canonicalization is constructively idempotent. -/
theorem canonicalize_idempotent (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    canonicalize declaration (canonicalize declaration pattern) =
      canonicalize declaration pattern :=
  canonicalize_eq_of_isCanonical declaration
    (canonicalize_isCanonical declaration pattern)

/-- Listwise idempotence of declaration-compiled canonicalization. -/
theorem canonicalizeList_idempotent
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    canonicalizeList declaration (canonicalizeList declaration patterns) =
      canonicalizeList declaration patterns :=
  canonicalizeList_eq_of_isCanonical declaration
    (canonicalizeList_isCanonical declaration patterns)

/-! ## Algebra of declaration-selected parallel contents -/

/-- The unsorted multiset presentation obtained by flattening the selected
parallel collection once and deleting its selected unit. -/
def parallelContents (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) : List Pattern :=
  (patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []

theorem normalizeParallelElements_eq_sort_parallelContents
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    normalizeParallelElements declaration patterns =
      PatternCode.sortPatterns (parallelContents declaration patterns) :=
  rfl

theorem parallelContents_append (declaration : ReflectivePresentationDecl)
    (left right : List Pattern) :
    parallelContents declaration (left ++ right) =
      parallelContents declaration left ++ parallelContents declaration right := by
  simp [parallelContents, List.flatMap_append, List.filter_append]

theorem parallelContents_perm (declaration : ReflectivePresentationDecl)
    {left right : List Pattern} (permutation : List.Perm left right) :
    List.Perm (parallelContents declaration left)
      (parallelContents declaration right) := by
  exact (permutation.flatMap_right (parallelSplice declaration)).filter
    (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])

theorem normalizeParallelElements_eq_of_perm
    (declaration : ReflectivePresentationDecl) {left right : List Pattern}
    (permutation : List.Perm left right) :
    normalizeParallelElements declaration left =
      normalizeParallelElements declaration right := by
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents]
  exact PatternCode.sortPatterns_eq_of_perm
    (parallelContents_perm declaration permutation)

theorem canonicalizeList_eq_map (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    canonicalizeList declaration patterns =
      patterns.map (canonicalize declaration) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

/-! ## Free-variable support of reflective representatives -/

/-- Flattening one selected parallel occurrence does not change the free
variables carried by that occurrence. -/
theorem mem_flatMap_freeFvarNames_parallelSplice_iff
    (declaration : ReflectivePresentationDecl) (name : String)
    (pattern : Pattern) :
    name ∈ (parallelSplice declaration pattern).flatMap Pattern.freeFvarNames ↔
      name ∈ pattern.freeFvarNames := by
  cases pattern with
  | bvar index => simp [parallelSplice, Pattern.freeFvarNames]
  | fvar variableName => simp [parallelSplice, Pattern.freeFvarNames]
  | apply constructor arguments =>
      simp [parallelSplice, Pattern.freeFvarNames]
  | lambda binder body => simp [parallelSplice, Pattern.freeFvarNames]
  | multiLambda arity binders body =>
      simp [parallelSplice, Pattern.freeFvarNames]
  | subst body replacement =>
      simp [parallelSplice, Pattern.freeFvarNames]
  | collection collectionType elements rest =>
      cases rest with
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp [parallelSplice, Pattern.freeFvarNames]
          · simp [parallelSplice, Pattern.freeFvarNames, selected]
      | some restName =>
          simp [parallelSplice, Pattern.freeFvarNames]

/-- Splicing every selected parallel occurrence preserves the aggregate
free-variable support of the list. -/
theorem mem_flatMap_freeFvarNames_flatMap_parallelSplice_iff
    (declaration : ReflectivePresentationDecl) (name : String) :
    ∀ patterns : List Pattern,
      name ∈ (patterns.flatMap (parallelSplice declaration)).flatMap
          Pattern.freeFvarNames ↔
        name ∈ patterns.flatMap Pattern.freeFvarNames
  | [] => by simp
  | pattern :: patterns => by
      simp only [List.flatMap_cons, List.flatMap_append, List.mem_append]
      rw [mem_flatMap_freeFvarNames_parallelSplice_iff,
        mem_flatMap_freeFvarNames_flatMap_parallelSplice_iff]

/-- Deleting the selected parallel unit cannot delete a free variable,
because that nullary constructor carries none. -/
theorem mem_flatMap_freeFvarNames_filter_parallelUnit_iff
    (declaration : ReflectivePresentationDecl) (name : String) :
    ∀ patterns : List Pattern,
      name ∈ (patterns.filter fun pattern =>
          pattern ≠ .apply declaration.parallelUnitConstructor []).flatMap
            Pattern.freeFvarNames ↔
        name ∈ patterns.flatMap Pattern.freeFvarNames
  | [] => by simp
  | pattern :: patterns => by
      have inductionHypothesis :=
        mem_flatMap_freeFvarNames_filter_parallelUnit_iff
          declaration name patterns
      by_cases unit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        simpa [Pattern.freeFvarNames] using inductionHypothesis
      · simpa [unit] using
          (Iff.or Iff.rfl inductionHypothesis)

/-- The unsorted flattened parallel presentation has exactly the aggregate
free-variable support of its input list. -/
theorem mem_flatMap_freeFvarNames_parallelContents_iff
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    name ∈ (parallelContents declaration patterns).flatMap
        Pattern.freeFvarNames ↔
      name ∈ patterns.flatMap Pattern.freeFvarNames := by
  unfold parallelContents
  rw [mem_flatMap_freeFvarNames_filter_parallelUnit_iff,
    mem_flatMap_freeFvarNames_flatMap_parallelSplice_iff]

/-- Sorting, flattening, and unit removal preserve aggregate free-variable
support. -/
theorem mem_flatMap_freeFvarNames_normalizeParallelElements_iff
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    name ∈ (normalizeParallelElements declaration patterns).flatMap
        Pattern.freeFvarNames ↔
      name ∈ patterns.flatMap Pattern.freeFvarNames := by
  rw [normalizeParallelElements_eq_sort_parallelContents]
  have permutation :=
    (sortPatterns_perm (parallelContents declaration patterns)).flatMap_right
      Pattern.freeFvarNames
  exact permutation.mem_iff.trans
    (mem_flatMap_freeFvarNames_parallelContents_iff declaration name patterns)

/-- Empty, singleton, and genuine parallel representations all carry the
aggregate free-variable support of their component list. -/
theorem mem_freeFvarNames_collapseParallel_iff
    (declaration : ReflectivePresentationDecl) (name : String)
    (patterns : List Pattern) :
    name ∈ (collapseParallel declaration patterns).freeFvarNames ↔
      name ∈ patterns.flatMap Pattern.freeFvarNames := by
  cases patterns with
  | nil => simp [collapseParallel, Pattern.freeFvarNames]
  | cons first remaining =>
      cases remaining with
      | nil => simp [collapseParallel]
      | cons second tail => simp [collapseParallel, Pattern.freeFvarNames]

/-- Orienting the selected quote/drop equation does not change the
free-variable support of the normalized application arguments. -/
theorem mem_freeFvarNames_finishNormalizeReflectiveApply_iff
    (declaration : ReflectivePresentationDecl) (name constructor : String)
    (arguments : List Pattern) :
    name ∈ (finishNormalizeReflectiveApply declaration constructor arguments).freeFvarNames ↔
      name ∈ arguments.flatMap Pattern.freeFvarNames := by
  unfold finishNormalizeReflectiveApply
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    simp only [beq_self_eq_true, if_true]
    split <;> simp_all [Pattern.freeFvarNames]
    split <;> simp_all [Pattern.freeFvarNames]
  · simp [quoted, Pattern.freeFvarNames]

/-- The declaration-compiled representative has exactly the same
free-variable support as its input.  The statement is about membership, not
list order or multiplicity: parallel canonicalization deliberately sorts and
flattens its components. -/
theorem mem_freeFvarNames_canonicalize_iff
    (declaration : ReflectivePresentationDecl) (name : String)
    (pattern : Pattern) :
    name ∈ (canonicalize declaration pattern).freeFvarNames ↔
      name ∈ pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [canonicalize, Pattern.freeFvarNames]
  | hfvar variableName => simp [canonicalize, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      have listSupport :
          name ∈ (canonicalizeList declaration arguments).flatMap
              Pattern.freeFvarNames ↔
            name ∈ arguments.flatMap Pattern.freeFvarNames := by
        rw [canonicalizeList_eq_map]
        simp only [List.mem_flatMap, List.mem_map]
        constructor
        · rintro ⟨normalized, ⟨argument, membership, rfl⟩, support⟩
          exact ⟨argument, membership,
            (inductionHypothesis argument membership).mp support⟩
        · rintro ⟨argument, membership, support⟩
          exact ⟨canonicalize declaration argument,
            ⟨argument, membership, rfl⟩,
            (inductionHypothesis argument membership).mpr support⟩
      simp only [canonicalize]
      rw [mem_freeFvarNames_finishNormalizeReflectiveApply_iff]
      simpa [Pattern.freeFvarNames] using listSupport
  | hlambda binderName body inductionHypothesis =>
      simpa [canonicalize, Pattern.freeFvarNames] using inductionHypothesis
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simpa [canonicalize, Pattern.freeFvarNames] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [canonicalize, Pattern.freeFvarNames,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listSupport :
          name ∈ (canonicalizeList declaration elements).flatMap
              Pattern.freeFvarNames ↔
            name ∈ elements.flatMap Pattern.freeFvarNames := by
        rw [canonicalizeList_eq_map]
        simp only [List.mem_flatMap, List.mem_map]
        constructor
        · rintro ⟨normalized, ⟨element, membership, rfl⟩, support⟩
          exact ⟨element, membership,
            (inductionHypothesis element membership).mp support⟩
        · rintro ⟨element, membership, support⟩
          exact ⟨canonicalize declaration element,
            ⟨element, membership, rfl⟩,
            (inductionHypothesis element membership).mpr support⟩
      cases rest with
      | some restName =>
          simp [canonicalize, Pattern.freeFvarNames, listSupport]
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [canonicalize, beq_self_eq_true, if_true]
            rw [mem_freeFvarNames_collapseParallel_iff,
              mem_flatMap_freeFvarNames_normalizeParallelElements_iff]
            simpa [Pattern.freeFvarNames] using listSupport
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false := by
              simp [selected]
            simp [canonicalize, Pattern.freeFvarNames, selectedFalse,
              listSupport]

theorem canonicalizeList_perm (declaration : ReflectivePresentationDecl)
    {left right : List Pattern} (permutation : List.Perm left right) :
    List.Perm (canonicalizeList declaration left)
      (canonicalizeList declaration right) := by
  rw [canonicalizeList_eq_map, canonicalizeList_eq_map]
  exact permutation.map (canonicalize declaration)

theorem canonicalizeList_append (declaration : ReflectivePresentationDecl)
    (left right : List Pattern) :
    canonicalizeList declaration (left ++ right) =
      canonicalizeList declaration left ++ canonicalizeList declaration right := by
  induction left with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

theorem collapse_normalize_singleton_of_isCanonical
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (canonical : IsCanonical declaration pattern) :
    collapseParallel declaration
        (normalizeParallelElements declaration [pattern]) = pattern := by
  by_cases isParallel : ∃ elements,
      pattern = .collection declaration.parallelCollection elements none
  · obtain ⟨elements, rfl⟩ := isParallel
    have properties := canonical.2 ⟨rfl, rfl⟩
    have filterFixed :
        elements.filter
            (fun element =>
              element ≠ .apply declaration.parallelUnitConstructor []) =
          elements :=
      List.filter_eq_self.mpr (fun element membership => by
        simpa using (properties.2.2 element membership).1)
    rw [normalizeParallelElements_eq_sort_parallelContents]
    simp only [parallelContents, List.flatMap_cons, List.flatMap_nil,
      parallelSplice, beq_self_eq_true, if_true, List.append_nil,
      filterFixed, properties.2.1]
    exact collapseParallel_eq_collection_of_length_ge_two
      declaration properties.1
  · have splice : parallelSplice declaration pattern = [pattern] :=
      parallelSplice_eq_singleton_of_not_parallel declaration pattern (by
        intro elements equality
        exact isParallel ⟨elements, equality⟩)
    by_cases isUnit :
        pattern = .apply declaration.parallelUnitConstructor []
    · subst isUnit
      simp [normalizeParallelElements, parallelSplice, collapseParallel,
        PatternCode.sortPatterns]
    · rw [normalizeParallelElements_eq_sort_parallelContents]
      simp [parallelContents, splice, isUnit, PatternCode.sortPatterns,
        collapseParallel]

theorem canonicalize_parallel_singleton
    (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    canonicalize declaration
        (.collection declaration.parallelCollection [pattern] none) =
      canonicalize declaration pattern := by
  simp only [canonicalize, beq_self_eq_true, if_true]
  change collapseParallel declaration
      (normalizeParallelElements declaration [canonicalize declaration pattern]) =
    canonicalize declaration pattern
  exact collapse_normalize_singleton_of_isCanonical declaration
    (canonicalize_isCanonical declaration pattern)

/-- Replacing a parallel wrapper by its representation-level empty,
singleton, or genuine collection form does not change its canonical class. -/
theorem canonicalize_parallel_collapse
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    canonicalize declaration
        (.collection declaration.parallelCollection patterns none) =
      canonicalize declaration (collapseParallel declaration patterns) := by
  cases patterns with
  | nil =>
      calc
        canonicalize declaration
            (.collection declaration.parallelCollection [] none) =
          .apply declaration.parallelUnitConstructor [] := by
            simp only [canonicalize, beq_self_eq_true, if_true,
              canonicalizeList, normalizeParallelElements,
              List.flatMap_nil, List.filter_nil, PatternCode.sortPatterns,
              List.mergeSort_nil, collapseParallel]
        _ = canonicalize declaration
            (.apply declaration.parallelUnitConstructor []) := by
          simp only [canonicalize, canonicalizeList]
          unfold finishNormalizeReflectiveApply
          by_cases sameConstructor :
              declaration.parallelUnitConstructor =
                declaration.quoteConstructor
          · simp [sameConstructor]
          · simp [sameConstructor]
  | cons first remaining =>
      cases remaining with
      | nil =>
          exact canonicalize_parallel_singleton declaration first
      | cons second tail => rfl

theorem parallelContents_unit_cons
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    parallelContents declaration
        (.apply declaration.parallelUnitConstructor [] :: patterns) =
      parallelContents declaration patterns := by
  simp [parallelContents, parallelSplice]

theorem normalizeParallelElements_unit_cons
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    normalizeParallelElements declaration
        (.apply declaration.parallelUnitConstructor [] :: patterns) =
      normalizeParallelElements declaration patterns := by
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents,
    parallelContents_unit_cons]

@[simp]
theorem canonicalize_parallel_unit
    (declaration : ReflectivePresentationDecl) :
    canonicalize declaration
        (.apply declaration.parallelUnitConstructor []) =
      .apply declaration.parallelUnitConstructor [] := by
  simp only [canonicalize, canonicalizeList]
  unfold finishNormalizeReflectiveApply
  by_cases sameConstructor :
      declaration.parallelUnitConstructor = declaration.quoteConstructor
  · simp [sameConstructor]
  · simp [sameConstructor]

/-- Removing a raw parallel unit before recursive canonicalization does not
change the eventual parallel contents. -/
theorem parallelContents_canonicalizeList_filter_unit
    (declaration : ReflectivePresentationDecl) : ∀ patterns : List Pattern,
    parallelContents declaration
        (canonicalizeList declaration
          (patterns.filter fun pattern =>
            pattern ≠ .apply declaration.parallelUnitConstructor [])) =
      parallelContents declaration
        (canonicalizeList declaration patterns)
  | [] => rfl
  | pattern :: patterns => by
      by_cases isUnit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        simpa [canonicalizeList, parallelContents, parallelSplice,
          List.filter_append] using
            (parallelContents_canonicalizeList_filter_unit
              declaration patterns)
      · have inductionHypothesis :=
          parallelContents_canonicalizeList_filter_unit declaration patterns
        have prefixed := congrArg
          (fun tail =>
            parallelContents declaration [canonicalize declaration pattern] ++
              tail)
          inductionHypothesis
        simpa [isUnit, canonicalizeList, parallelContents,
          List.filter_append] using prefixed

theorem parallelContents_collapse_normalized
    (declaration : ReflectivePresentationDecl) {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList declaration patterns) :
    parallelContents declaration
        [collapseParallel declaration
          (normalizeParallelElements declaration patterns)] =
      normalizeParallelElements declaration patterns := by
  have normalizedNoUnit : ∀ element ∈
      normalizeParallelElements declaration patterns,
      element ≠ .apply declaration.parallelUnitConstructor [] := by
    intro element membership
    exact normalizeParallelElements_no_unit membership
  have normalizedNoParallel : ∀ element ∈
      normalizeParallelElements declaration patterns, ∀ nested,
      element ≠
        .collection declaration.parallelCollection nested none := by
    intro element membership
    exact normalizeParallelElements_no_nested patternsCanonical membership
  match normalizedEquality :
      normalizeParallelElements declaration patterns with
  | [] =>
      simp [parallelContents, collapseParallel, parallelSplice]
  | [element] =>
      have notUnit :
          element ≠ .apply declaration.parallelUnitConstructor [] :=
        normalizedNoUnit element (by rw [normalizedEquality]; simp)
      have notParallel : ∀ nested,
          element ≠
            .collection declaration.parallelCollection nested none :=
        normalizedNoParallel element (by rw [normalizedEquality]; simp)
      have splice : parallelSplice declaration element = [element] :=
        parallelSplice_eq_singleton_of_not_parallel declaration element
          notParallel
      simp [parallelContents, collapseParallel, splice, notUnit]
  | first :: second :: tail =>
      have filterFixed :
          (first :: second :: tail).filter
              (fun element =>
                element ≠ .apply declaration.parallelUnitConstructor []) =
            first :: second :: tail :=
        List.filter_eq_self.mpr (fun element membership => by
          simpa using normalizedNoUnit element (by
            rw [normalizedEquality]
            exact membership))
      rw [show collapseParallel declaration (first :: second :: tail) =
        .collection declaration.parallelCollection
          (first :: second :: tail) none from rfl]
      unfold parallelContents
      simp only [List.flatMap_cons, List.flatMap_nil, parallelSplice,
        beq_self_eq_true, if_true, List.append_nil]
      exact filterFixed

theorem normalizeParallelElements_collapse_cons
    (declaration : ReflectivePresentationDecl)
    (patterns rest : List Pattern)
    (patternsCanonical : IsCanonicalList declaration patterns) :
    normalizeParallelElements declaration
        (collapseParallel declaration
            (normalizeParallelElements declaration patterns) :: rest) =
      normalizeParallelElements declaration (patterns ++ rest) := by
  change PatternCode.sortPatterns
      (parallelContents declaration
        (collapseParallel declaration
            (normalizeParallelElements declaration patterns) :: rest)) =
    PatternCode.sortPatterns
      (parallelContents declaration (patterns ++ rest))
  apply PatternCode.sortPatterns_eq_of_perm
  rw [show parallelContents declaration
        (collapseParallel declaration
            (normalizeParallelElements declaration patterns) :: rest) =
      parallelContents declaration
          [collapseParallel declaration
            (normalizeParallelElements declaration patterns)] ++
        parallelContents declaration rest by
      simpa using parallelContents_append declaration
        [collapseParallel declaration
          (normalizeParallelElements declaration patterns)] rest,
    parallelContents_collapse_normalized declaration patternsCanonical,
    parallelContents_append]
  exact (sortPatterns_perm (parallelContents declaration patterns))
    |>.append_right (parallelContents declaration rest)

/-- One recursively canonicalized element contributes the same parallel
multiset as recursively canonicalizing its raw flattened contribution. -/
theorem parallelContents_canonicalize_singleton_perm
    (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    List.Perm
      (parallelContents declaration [canonicalize declaration pattern])
      (parallelContents declaration
        (canonicalizeList declaration
          (parallelContents declaration [pattern]))) := by
  by_cases isParallel : ∃ elements,
      pattern = .collection declaration.parallelCollection elements none
  · obtain ⟨elements, rfl⟩ := isParallel
    have canonicalElements :
        IsCanonicalList declaration (canonicalizeList declaration elements) :=
      canonicalizeList_isCanonical declaration elements
    simp only [canonicalize, beq_self_eq_true, if_true]
    rw [parallelContents_collapse_normalized declaration canonicalElements]
    rw [normalizeParallelElements_eq_sort_parallelContents]
    apply (sortPatterns_perm
      (parallelContents declaration
        (canonicalizeList declaration elements))).trans
    have filtered :=
      parallelContents_canonicalizeList_filter_unit declaration elements
    simpa [parallelContents, parallelSplice, canonicalizeList] using
      List.Perm.of_eq filtered.symm
  · have splice : parallelSplice declaration pattern = [pattern] :=
      parallelSplice_eq_singleton_of_not_parallel declaration pattern (by
        intro elements equality
        exact isParallel ⟨elements, equality⟩)
    by_cases isUnit :
        pattern = .apply declaration.parallelUnitConstructor []
    · subst pattern
      simp [parallelContents, parallelSplice, canonicalizeList]
    · simp [parallelContents, splice, isUnit, canonicalizeList]

/-- Canonicalizing a list before or after exposing its raw parallel
contents yields the same eventual multiset of canonical parallel atoms. -/
theorem parallelContents_canonicalizeList_perm
    (declaration : ReflectivePresentationDecl) : ∀ patterns : List Pattern,
    List.Perm
      (parallelContents declaration
        (canonicalizeList declaration patterns))
      (parallelContents declaration
        (canonicalizeList declaration
          (parallelContents declaration patterns)))
  | [] => by simp [parallelContents, canonicalizeList]
  | pattern :: patterns => by
      rw [show pattern :: patterns = [pattern] ++ patterns by rfl,
        parallelContents_append,
        canonicalizeList_append,
        parallelContents_append,
        canonicalizeList_append,
        parallelContents_append]
      exact List.Perm.append
        (parallelContents_canonicalize_singleton_perm declaration pattern)
        (parallelContents_canonicalizeList_perm declaration patterns)

/-- Pre-normalizing the raw parallel list is absorbed by full recursive
canonicalization.  This is the algebraic form used by structural embeddings:
the source and target may sort atoms differently, while both still present
the same multiset. -/
theorem canonicalize_parallel_normalize_input
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    canonicalize declaration
        (.collection declaration.parallelCollection patterns none) =
      canonicalize declaration
        (.collection declaration.parallelCollection
          (normalizeParallelElements declaration patterns) none) := by
  simp only [canonicalize, beq_self_eq_true, if_true]
  congr 1
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents]
  apply PatternCode.sortPatterns_eq_of_perm
  exact (parallelContents_canonicalizeList_perm declaration patterns).trans
    (parallelContents_perm declaration
      (canonicalizeList_perm declaration
        (sortPatterns_perm
          (parallelContents declaration patterns)).symm))

theorem canonicalize_parallel_permutation
    (declaration : ReflectivePresentationDecl) {left right : List Pattern}
    (permutation : List.Perm left right) :
    canonicalize declaration
        (.collection declaration.parallelCollection left none) =
      canonicalize declaration
        (.collection declaration.parallelCollection right none) := by
  simp only [canonicalize, beq_self_eq_true, if_true]
  rw [normalizeParallelElements_eq_of_perm declaration
    (canonicalizeList_perm declaration permutation)]

theorem canonicalize_parallel_flatten
    (declaration : ReflectivePresentationDecl)
    (leading nestedPatterns : List Pattern) :
    canonicalize declaration
        (.collection declaration.parallelCollection
          (leading ++
            [.collection declaration.parallelCollection nestedPatterns none])
          none) =
      canonicalize declaration
        (.collection declaration.parallelCollection
          (leading ++ nestedPatterns) none) := by
  let leading' := canonicalizeList declaration leading
  let nested' := canonicalizeList declaration nestedPatterns
  have nestedCanonical : IsCanonicalList declaration nested' :=
    canonicalizeList_isCanonical declaration nestedPatterns
  simp only [canonicalize, beq_self_eq_true, if_true]
  change collapseParallel declaration
      (normalizeParallelElements declaration
        (canonicalizeList declaration
          (leading ++
            [.collection declaration.parallelCollection nestedPatterns none]))) =
    collapseParallel declaration
      (normalizeParallelElements declaration
        (canonicalizeList declaration (leading ++ nestedPatterns)))
  rw [canonicalizeList_append, canonicalizeList_append]
  simp only [canonicalizeList, canonicalize, beq_self_eq_true, if_true]
  change collapseParallel declaration
      (normalizeParallelElements declaration
        (leading' ++
          [collapseParallel declaration
            (normalizeParallelElements declaration nested')])) =
    collapseParallel declaration
      (normalizeParallelElements declaration (leading' ++ nested'))
  congr 1
  calc
    normalizeParallelElements declaration
        (leading' ++
          [collapseParallel declaration
            (normalizeParallelElements declaration nested')]) =
      normalizeParallelElements declaration
        (collapseParallel declaration
            (normalizeParallelElements declaration nested') :: leading') :=
        normalizeParallelElements_eq_of_perm declaration
          (List.perm_append_comm
            (l₁ := leading')
            (l₂ := [collapseParallel declaration
              (normalizeParallelElements declaration nested')]))
    _ = normalizeParallelElements declaration (nested' ++ leading') :=
      normalizeParallelElements_collapse_cons declaration nested' leading'
        nestedCanonical
    _ = normalizeParallelElements declaration (leading' ++ nested') :=
      normalizeParallelElements_eq_of_perm declaration
        (List.perm_append_comm (l₁ := nested') (l₂ := leading'))

/-- A validated reflective presentation cannot identify quote and drop: their
unique declarations have opposite source and target sorts, while validation
requires those sorts to be distinct. -/
theorem quoteConstructor_ne_dropConstructor_of_validate
    (language : LanguageDef) (declaration : ReflectivePresentationDecl)
    (valid : language.validateReflectivePresentation declaration = []) :
    declaration.quoteConstructor ≠ declaration.dropConstructor := by
  rcases LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      language declaration valid with ⟨witness⟩
  intro sameConstructor
  have sameTerm : witness.quote = witness.drop := by
    have singletonEquality : [witness.quote] = [witness.drop] := by
      rw [← witness.quoteUnique, ← witness.dropUnique, sameConstructor]
    simpa using singletonEquality
  apply witness.sortsDistinct
  calc
    declaration.processSort = witness.drop.category :=
      witness.dropCategory.symm
    _ = witness.quote.category := congrArg GrammarRule.category sameTerm.symm
    _ = declaration.nameSort := witness.quoteCategory

/-- Boolean equality of representatives compiled from one declaration. -/
def canonicalEquivalent
    (declaration : ReflectivePresentationDecl) (left right : Pattern) : Bool :=
  decide (canonicalize declaration left = canonicalize declaration right)

theorem canonicalEquivalent_eq_true_iff
    {declaration : ReflectivePresentationDecl} {left right : Pattern} :
    canonicalEquivalent declaration left right = true ↔
      canonicalize declaration left = canonicalize declaration right := by
  simp [canonicalEquivalent]

/-- Rule-aware matching compiled from the authored `LanguageDef`.

Only repeated metavariable consistency changes for the selected reflective
rule.  Constructor matching, binder handling, and collection search remain
the generic matcher. -/
def matchPatternForRuleUsing
    (profile : ReflectionProfile) (rule : RewriteRule)
    (term : Pattern) : List Bindings :=
  match matchingPresentationForRule? profile rule with
  | some declaration =>
      matchPatternWith (canonicalEquivalent declaration) rule.left term
  | none => matchPattern rule.left term

/-- Match an authored rule in the five-field, reflection-free core. -/
def matchPatternForRule
    (_language : LanguageDef) (rule : RewriteRule)
    (term : Pattern) : List Bindings :=
  matchPatternForRuleUsing .empty rule term

/-- Rule-aware matching is unchanged when two languages share both reflective
data tables. -/
theorem matchPatternForRuleUsing_eq_of_reflectiveData_eq
    {profile₁ profile₂ : ReflectionProfile}
    (samePresentations : profile₁.presentations = profile₂.presentations)
    (sameRules : profile₁.rules = profile₂.rules)
    (rule : RewriteRule) (term : Pattern) :
    matchPatternForRuleUsing profile₁ rule term =
      matchPatternForRuleUsing profile₂ rule term := by
  simp only [matchPatternForRuleUsing]
  rw [matchingPresentationForRule?_eq_of_reflectiveData_eq
    samePresentations sameRules rule]

/-- Missing or ambiguous reflective data is definitionally backward
compatible with structural matching. -/
theorem matchPatternForRule_eq_syntactic_of_no_presentation
    {profile : ReflectionProfile} {rule : RewriteRule}
    (missing : matchingPresentationForRule? profile rule = none)
    (term : Pattern) :
    matchPatternForRuleUsing profile rule term = matchPattern rule.left term := by
  simp [matchPatternForRuleUsing, missing]

@[simp] theorem matchPatternForRule_eq_syntactic_of_no_presentations
    {profile : ReflectionProfile} (empty : profile.presentations = [])
    (rule : RewriteRule) (term : Pattern) :
    matchPatternForRuleUsing profile rule term = matchPattern rule.left term := by
  apply matchPatternForRule_eq_syntactic_of_no_presentation
  exact matchingPresentationForRule?_eq_none_of_no_presentations empty rule

@[simp] theorem matchPatternForRule_eq_syntactic_of_no_reflectiveRules
    {profile : ReflectionProfile} (empty : profile.rules = [])
    (rule : RewriteRule) (term : Pattern) :
    matchPatternForRuleUsing profile rule term = matchPattern rule.left term := by
  apply matchPatternForRule_eq_syntactic_of_no_presentation
  exact matchingPresentationForRule?_eq_none_of_no_rules empty rule

@[simp] theorem matchPatternForRule_eq_syntactic
    (language : LanguageDef) (rule : RewriteRule) (term : Pattern) :
    matchPatternForRule language rule term = matchPattern rule.left term := by
  simp [matchPatternForRule, matchPatternForRuleUsing,
    ReflectionProfile.empty, matchingPresentationForRule?,
    reflectiveRuleForRule?]

/-! ## Executable boundary examples -/

private def canonicalChannel : Pattern :=
  .apply "NQuote" [.apply "PZero" []]

private def unitExpandedChannel : Pattern :=
  .apply "NQuote"
    [.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none]

private def distinctChannel : Pattern :=
  .apply "NQuote"
    [.apply "POutput" [canonicalChannel, .apply "PZero" []]]

private def commCandidate (outputChannel : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "PInput" [unitExpandedChannel, .lambda none (.bvar 0)],
      .apply "POutput" [outputChannel, .apply "PZero" []]]
    none

private def rhoProfile : ReflectionProfile :=
  { presentations :=
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    rules := [rhoReflectiveRule] }

-- The declaration-derived matcher admits two presentations of one channel.
#guard !(matchPatternForRuleUsing rhoProfile rhoCommRewrite
  (commCandidate canonicalChannel)).isEmpty

-- It still rejects a genuinely distinct channel.
#guard (matchPatternForRuleUsing rhoProfile rhoCommRewrite
  (commCandidate distinctChannel)).isEmpty

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
