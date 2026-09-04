import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem check_canonicalize_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠ declaration.dropConstructor)
    (constructor : String) (arguments : List Pattern) :
    canonicalize declaration
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      canonicalize declaration (.apply constructor arguments) := by
  have drop_ne_quote :
      declaration.dropConstructor ≠ declaration.quoteConstructor :=
    Ne.symm quote_ne_drop
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil => simp [finishNormalizeReflectiveApply, canonicalize]
    | cons argument arguments =>
        cases arguments with
        | nil =>
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil => simp [finishNormalizeReflectiveApply, canonicalize,
                    canonicalizeList]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [finishNormalizeReflectiveApply, canonicalize,
                            canonicalizeList, drop_ne_quote]
                        · simp [finishNormalizeReflectiveApply, canonicalize,
                            canonicalizeList, isDrop]
                    | cons second tail =>
                        simp [finishNormalizeReflectiveApply, canonicalize,
                          canonicalizeList]
            | bvar index =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
            | fvar name =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
            | lambda binder body =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
            | multiLambda arity binders body =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
            | subst body replacement =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
            | collection collectionType elements rest =>
                simp [finishNormalizeReflectiveApply, canonicalize,
                  canonicalizeList]
        | cons second tail =>
            simp [finishNormalizeReflectiveApply, canonicalize,
              canonicalizeList]
  · simp [finishNormalizeReflectiveApply, canonicalize, isQuote]

theorem check_normalizeParallelElementsBy_perm
    {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    List.Perm (normalizeParallelElementsBy key declaration patterns)
      (normalizeParallelElements declaration patterns) := by
  unfold normalizeParallelElementsBy normalizeParallelElements
  exact (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).trans
    (sortPatterns_perm _).symm

mutual
  theorem check_canonicalize_canonicalizeByAt
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (quote_ne_drop : declaration.quoteConstructor ≠
        declaration.dropConstructor) :
      ∀ availableDepth pattern,
        canonicalize declaration
            (canonicalizeByAt key declaration availableDepth pattern) =
          canonicalize declaration pattern
    | _, .bvar _ => rfl
    | _, .fvar _ => rfl
    | availableDepth, .apply constructor arguments => by
        simp only [canonicalizeByAt]
        rw [check_canonicalize_finishNormalizeReflectiveApply declaration
          quote_ne_drop]
        simp only [canonicalize]
        apply congrArg
        exact check_canonicalizeList_canonicalizeListByAt key declaration
          quote_ne_drop _ arguments
    | availableDepth, .lambda binder body => by
        simp only [canonicalizeByAt, canonicalize, Pattern.lambda.injEq,
          true_and]
        exact check_canonicalize_canonicalizeByAt key declaration quote_ne_drop
          (availableDepth + 1) body
    | availableDepth, .multiLambda arity binders body => by
        simp only [canonicalizeByAt, canonicalize,
          Pattern.multiLambda.injEq, true_and]
        exact check_canonicalize_canonicalizeByAt key declaration quote_ne_drop
          (availableDepth + arity) body
    | availableDepth, .subst body replacement => by
        simp only [canonicalizeByAt, canonicalize, Pattern.subst.injEq]
        exact ⟨
          check_canonicalize_canonicalizeByAt key declaration quote_ne_drop
            (availableDepth + 1) body,
          check_canonicalize_canonicalizeByAt key declaration quote_ne_drop
            availableDepth replacement⟩
    | availableDepth, .collection collectionType elements none => by
        simp only [canonicalizeByAt]
        by_cases isParallel : collectionType = declaration.parallelCollection
        · subst collectionType
          simp only [beq_self_eq_true, if_true]
          rw [← canonicalize_parallel_collapse declaration
            (normalizeParallelElementsBy (key availableDepth) declaration
              (canonicalizeListByAt key declaration availableDepth elements))]
          rw [canonicalize_parallel_permutation declaration
            (check_normalizeParallelElementsBy_perm (key availableDepth)
              declaration
              (canonicalizeListByAt key declaration availableDepth elements))]
          rw [← canonicalize_parallel_normalize_input declaration
            (canonicalizeListByAt key declaration availableDepth elements)]
          simp only [canonicalize, beq_self_eq_true, if_true]
          rw [check_canonicalizeList_canonicalizeListByAt key declaration
            quote_ne_drop availableDepth elements]
        · have notParallelBool :
              (collectionType == declaration.parallelCollection) = false := by
            exact beq_eq_false_iff_ne.mpr isParallel
          simp [canonicalize, notParallelBool,
            check_canonicalizeList_canonicalizeListByAt key declaration
              quote_ne_drop availableDepth elements]
    | availableDepth, .collection collectionType elements (some rest) => by
        simp only [canonicalizeByAt, canonicalize, Pattern.collection.injEq,
          true_and]
        exact ⟨
          check_canonicalizeList_canonicalizeListByAt key declaration
            quote_ne_drop availableDepth elements,
          trivial⟩

  theorem check_canonicalizeList_canonicalizeListByAt
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (quote_ne_drop : declaration.quoteConstructor ≠
        declaration.dropConstructor) :
      ∀ availableDepth patterns,
        canonicalizeList declaration
            (canonicalizeListByAt key declaration availableDepth patterns) =
          canonicalizeList declaration patterns
    | _, [] => rfl
    | availableDepth, pattern :: patterns => by
        simp only [canonicalizeListByAt, canonicalizeList]
        rw [check_canonicalize_canonicalizeByAt key declaration quote_ne_drop
          availableDepth pattern]
        rw [check_canonicalizeList_canonicalizeListByAt key declaration
          quote_ne_drop availableDepth patterns]
end

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
