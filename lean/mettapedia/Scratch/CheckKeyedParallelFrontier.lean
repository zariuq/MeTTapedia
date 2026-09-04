import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnostic

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

#check parallelContents_canonicalizeList_perm
#check canonicalize_parallelContents_keyed_plain_perm
#check List.Forall₂.get
#check List.Forall₂.length_eq
#check List.Perm.mem_iff

theorem check_parallelContents_collapseParallel_eq
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (noUnit : ∀ element ∈ patterns,
      element ≠ .apply declaration.parallelUnitConstructor [])
    (noParallel : ∀ element ∈ patterns, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none) :
    parallelContents declaration [collapseParallel declaration patterns] =
      patterns := by
  cases patterns with
  | nil => simp [parallelContents, collapseParallel, parallelSplice]
  | cons first remaining =>
      cases remaining with
      | nil =>
          have firstNotUnit := noUnit first (by simp)
          have firstNotParallel := noParallel first (by simp)
          have splice : parallelSplice declaration first = [first] :=
            parallelSplice_eq_singleton_of_not_parallel declaration first
              firstNotParallel
          simp [collapseParallel, parallelContents, splice, firstNotUnit]
      | cons second tail =>
          have filterFixed :
              (first :: second :: tail).filter
                  (fun element =>
                    element ≠ .apply declaration.parallelUnitConstructor []) =
                first :: second :: tail :=
            List.filter_eq_self.mpr (fun element membership =>
              by simpa using noUnit element membership)
          simp only [collapseParallel, parallelContents, List.flatMap_cons,
            List.flatMap_nil, parallelSplice, beq_self_eq_true, if_true,
            List.append_nil]
          exact filterFixed

theorem check_orderAgnosticList_noUnit
    {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right)
    (rightNoUnit : ∀ element ∈ right,
      element ≠ .apply declaration.parallelUnitConstructor []) :
    ∀ element ∈ left,
      element ≠ .apply declaration.parallelUnitConstructor [] := by
  let rec go {left right : List Pattern}
      (related : ParallelOrderAgnosticList declaration left right)
      (rightNoUnit : ∀ element ∈ right,
        element ≠ .apply declaration.parallelUnitConstructor []) :
      ∀ element ∈ left,
        element ≠ .apply declaration.parallelUnitConstructor [] :=
    match related with
    | .nil => by simp
    | .cons head tail => by
        intro element membership
        rcases List.mem_cons.mp membership with rfl | inTail
        · intro leftUnit
          have rightUnit := head.unit_iff.mp leftUnit
          exact rightNoUnit _ (by simp) rightUnit
        · exact go tail (fun candidate candidateMembership =>
            rightNoUnit candidate (by simp [candidateMembership])) element
              inTail
  exact go related rightNoUnit

theorem check_orderAgnosticList_noParallel
    {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right)
    (rightNoParallel : ∀ element ∈ right, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none) :
    ∀ element ∈ left, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none := by
  let rec go {left right : List Pattern}
      (related : ParallelOrderAgnosticList declaration left right)
      (rightNoParallel : ∀ element ∈ right, ∀ nested,
        element ≠ .collection declaration.parallelCollection nested none) :
      ∀ element ∈ left, ∀ nested,
        element ≠ .collection declaration.parallelCollection nested none :=
    match related with
    | .nil => by simp
    | .cons head tail => by
        intro element membership nested
        rcases List.mem_cons.mp membership with rfl | inTail
        · intro leftParallel
          rcases head.bareParallel_cases with parallel | rigid
          · obtain ⟨leftElements, middleElements, rightElements, leftEq,
                rightEq, pointwise, permutation⟩ := parallel
            exact rightNoParallel _ (by simp) rightElements rightEq
          · exact rigid.1 nested leftParallel
        · exact go tail (fun candidate candidateMembership candidateNested =>
            rightNoParallel candidate (by simp [candidateMembership])
              candidateNested) element inTail nested
  exact go related rightNoParallel

theorem check_orderAgnosticPermutation_noUnit
    {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnostic.ParallelOrderAgnosticPermutation
      declaration left right)
    (rightNoUnit : ∀ element ∈ right,
      element ≠ .apply declaration.parallelUnitConstructor []) :
    ∀ element ∈ left,
      element ≠ .apply declaration.parallelUnitConstructor [] := by
  obtain ⟨middle, aligned, reordered⟩ := related
  apply check_orderAgnosticList_noUnit aligned
  intro element membership
  exact rightNoUnit element (reordered.mem_iff.mp membership)

theorem check_orderAgnosticPermutation_noParallel
    {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnostic.ParallelOrderAgnosticPermutation
      declaration left right)
    (rightNoParallel : ∀ element ∈ right, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none) :
    ∀ element ∈ left, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none := by
  obtain ⟨middle, aligned, reordered⟩ := related
  apply check_orderAgnosticList_noParallel aligned
  intro element membership
  exact rightNoParallel element (reordered.mem_iff.mp membership)

theorem check_keyedParallelFrontier_noUnit
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (patterns : List Pattern) :
    ∀ element ∈ parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth patterns),
      element ≠ .apply declaration.parallelUnitConstructor [] := by
  have elementsRelated : ParallelOrderAgnosticList declaration
      (canonicalizeListByAt key declaration availableDepth patterns)
      (canonicalizeList declaration patterns) := by
    rw [canonicalizeListByAt_eq_map, canonicalizeList_eq_map]
    exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
      (fun pattern membership =>
        canonicalizeByAt_parallelOrderAgnostic key declaration
          availableDepth pattern)
  have spliced :=
    ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.flatMapParallelSplice
      elementsRelated
  have filtered :=
    ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.filterNotUnit
      spliced
  change ∀ element ∈
      ((canonicalizeListByAt key declaration availableDepth patterns).flatMap
        (parallelSplice declaration)).filter
          (fun pattern =>
            pattern ≠ .apply declaration.parallelUnitConstructor []),
    element ≠ .apply declaration.parallelUnitConstructor []
  apply check_orderAgnosticPermutation_noUnit filtered
  intro element membership
  exact of_decide_eq_true (List.mem_filter.mp membership).2

theorem check_keyedParallelFrontier_noParallel
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (patterns : List Pattern) :
    ∀ element ∈ parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth patterns),
      ∀ nested,
        element ≠ .collection declaration.parallelCollection nested none := by
  have elementsRelated : ParallelOrderAgnosticList declaration
      (canonicalizeListByAt key declaration availableDepth patterns)
      (canonicalizeList declaration patterns) := by
    rw [canonicalizeListByAt_eq_map, canonicalizeList_eq_map]
    exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
      (fun pattern membership =>
        canonicalizeByAt_parallelOrderAgnostic key declaration
          availableDepth pattern)
  have spliced :=
    ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.flatMapParallelSplice
      elementsRelated
  have filtered :=
    ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.filterNotUnit
      spliced
  change ∀ element ∈
      ((canonicalizeListByAt key declaration availableDepth patterns).flatMap
        (parallelSplice declaration)).filter
          (fun pattern =>
            pattern ≠ .apply declaration.parallelUnitConstructor []),
    ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none
  apply check_orderAgnosticPermutation_noParallel filtered
  intro element membership nested
  have canonicalElements : IsCanonicalList declaration
      (canonicalizeList declaration patterns) :=
    canonicalizeList_isCanonical declaration patterns
  have inNormalized : element ∈ normalizeParallelElements declaration
      (canonicalizeList declaration patterns) :=
    (sortPatterns_perm
      (parallelContents declaration
        (canonicalizeList declaration patterns))).mem_iff.mpr membership
  exact normalizeParallelElements_no_nested canonicalElements inNormalized
    nested

@[simp] theorem check_canonicalizeByAt_parallelUnit
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
    canonicalizeByAt key declaration availableDepth
        (.apply declaration.parallelUnitConstructor []) =
      .apply declaration.parallelUnitConstructor [] := by
  simp [canonicalizeByAt, canonicalizeListByAt,
    ReflectiveSubstitution.finishNormalizeReflectiveApply]

theorem check_parallelContents_canonicalizeListByAt_filter_unit
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
    ∀ patterns : List Pattern,
    parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth
          (patterns.filter fun pattern =>
            pattern ≠ .apply declaration.parallelUnitConstructor [])) =
      parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth patterns)
  | [] => rfl
  | pattern :: patterns => by
      by_cases isUnit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        simpa [canonicalizeListByAt, parallelContents, parallelSplice,
          List.filter_append] using
            (check_parallelContents_canonicalizeListByAt_filter_unit key
              declaration availableDepth patterns)
      · have inductionHypothesis :=
          check_parallelContents_canonicalizeListByAt_filter_unit key
            declaration availableDepth patterns
        have prefixed := congrArg
          (fun tail =>
            parallelContents declaration
                [canonicalizeByAt key declaration availableDepth pattern] ++
              tail)
          inductionHypothesis
        simpa [isUnit, canonicalizeListByAt, parallelContents,
          List.filter_append] using prefixed

theorem check_parallelContents_canonicalizeByAt_singleton_perm
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth : Nat) (pattern : Pattern) :
    List.Perm
      (parallelContents declaration
        [canonicalizeByAt key declaration availableDepth pattern])
      (parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth
          (parallelContents declaration [pattern]))) := by
  by_cases isParallel : ∃ elements,
      pattern = .collection declaration.parallelCollection elements none
  · obtain ⟨elements, rfl⟩ := isParallel
    let canonicalElements :=
      canonicalizeListByAt key declaration availableDepth elements
    let normalized := normalizeParallelElementsBy
      (key availableDepth) declaration canonicalElements
    have normalizedNoUnit : ∀ element ∈ normalized,
        element ≠ .apply declaration.parallelUnitConstructor [] := by
      intro element membership
      have sourceMembership :=
        (PatternCode.sortPatternsBy_perm (key availableDepth)
          (parallelContents declaration canonicalElements)).mem_iff.mp
          membership
      exact check_keyedParallelFrontier_noUnit key declaration
        availableDepth elements element sourceMembership
    have normalizedNoParallel : ∀ element ∈ normalized, ∀ nested,
        element ≠ .collection declaration.parallelCollection nested none := by
      intro element membership nested
      have sourceMembership :=
        (PatternCode.sortPatternsBy_perm (key availableDepth)
          (parallelContents declaration canonicalElements)).mem_iff.mp
          membership
      exact check_keyedParallelFrontier_noParallel key declaration
        availableDepth elements element sourceMembership nested
    have exposed : parallelContents declaration
        [collapseParallel declaration normalized] = normalized :=
      check_parallelContents_collapseParallel_eq declaration normalized
        normalizedNoUnit normalizedNoParallel
    have normalizedPerm : List.Perm normalized
        (parallelContents declaration canonicalElements) :=
      PatternCode.sortPatternsBy_perm (key availableDepth)
        (parallelContents declaration canonicalElements)
    rw [show canonicalizeByAt key declaration availableDepth
          (.collection declaration.parallelCollection elements none) =
        collapseParallel declaration normalized by
      simp [canonicalizeByAt, canonicalElements, normalized]]
    rw [exposed]
    have filtered :=
      check_parallelContents_canonicalizeListByAt_filter_unit key declaration
        availableDepth elements
    simpa [parallelContents, parallelSplice, canonicalElements] using
      normalizedPerm.trans (List.Perm.of_eq filtered.symm)
  · have splice : parallelSplice declaration pattern = [pattern] :=
      parallelSplice_eq_singleton_of_not_parallel declaration pattern (by
        intro elements equality
        exact isParallel ⟨elements, equality⟩)
    by_cases isUnit : pattern =
        .apply declaration.parallelUnitConstructor []
    · subst pattern
      simp [parallelContents, parallelSplice, canonicalizeListByAt]
    · simp [parallelContents, splice, isUnit, canonicalizeListByAt]

theorem check_parallelContents_canonicalizeListByAt_perm
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
    ∀ patterns : List Pattern,
    List.Perm
      (parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth patterns))
      (parallelContents declaration
        (canonicalizeListByAt key declaration availableDepth
          (parallelContents declaration patterns)))
  | [] => by simp [parallelContents, canonicalizeListByAt]
  | pattern :: patterns => by
      rw [show pattern :: patterns = [pattern] ++ patterns by rfl,
        parallelContents_append,
        canonicalizeListByAt_eq_map, List.map_append,
        parallelContents_append,
        canonicalizeListByAt_eq_map, List.map_append,
        parallelContents_append]
      apply List.Perm.append
      · simpa [canonicalizeListByAt_eq_map] using
          (check_parallelContents_canonicalizeByAt_singleton_perm key
            declaration availableDepth pattern)
      · simpa [canonicalizeListByAt_eq_map] using
          (check_parallelContents_canonicalizeListByAt_perm key declaration
            availableDepth patterns)

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
