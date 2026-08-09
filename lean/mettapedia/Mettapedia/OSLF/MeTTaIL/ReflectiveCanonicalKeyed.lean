import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Key-parametric reflective canonicalization

Reflective parallel composition is a bag semantically, but an executable
canonical representative still needs an order.  The original canonicalizer
uses the collision-free structural code of the compact `Pattern`.  This module
separates that ordering policy from the authored reflective laws.

The parameter is a key into any linear order.  Cost elaborations can therefore
order opaque boundary atoms by their normalized semantic values while retaining
the original structural canonicalizer as the exact default instance.
-/

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Deterministically sort compact patterns by an explicit semantic key. -/
def sortPatternsBy {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (patterns : List Pattern) : List Pattern :=
  patterns.mergeSort (fun left right => decide (key left ≤ key right))

@[simp]
theorem sortPatternsBy_patternCode (patterns : List Pattern) :
    sortPatternsBy patternCode patterns = sortPatterns patterns :=
  rfl

/-- Key sorting changes only order and retains every occurrence. -/
theorem sortPatternsBy_perm {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (patterns : List Pattern) :
    List.Perm (sortPatternsBy key patterns) patterns := by
  exact List.mergeSort_perm patterns _

/-- Stable key sorting is idempotent even when distinct patterns have equal
keys.  Antisymmetry on patterns is neither available nor desirable here:
equal-key occurrences retain their input order. -/
theorem sortPatternsBy_idempotent {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (patterns : List Pattern) :
    sortPatternsBy key (sortPatternsBy key patterns) =
      sortPatternsBy key patterns := by
  let relation : Pattern → Pattern → Bool :=
    fun left right => decide (key left ≤ key right)
  have transitive : ∀ left middle right,
      relation left middle → relation middle right → relation left right := by
    intro left middle right leftMiddle middleRight
    simpa [relation] using le_trans
      (of_decide_eq_true leftMiddle) (of_decide_eq_true middleRight)
  have total : ∀ left right, relation left right || relation right left := by
    intro left right
    rcases le_total (key left) (key right) with ordered | ordered
    · simp [relation, ordered]
    · simp [relation, ordered]
  apply List.mergeSort_of_pairwise
  exact List.pairwise_mergeSort transitive total patterns

/-- A two-element list already ordered by the supplied semantic key is a
fixed point of keyed sorting. -/
theorem sortPatternsBy_pair_eq_of_le {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (left right : Pattern)
    (ordered : key left ≤ key right) :
    sortPatternsBy key [left, right] = [left, right] := by
  simp [sortPatternsBy, List.mergeSort, ordered]

/-- For a fixed unary constructor, the canonical structural code is strictly
monotone in the code of its free-variable argument. -/
theorem patternCode_apply_single_fvar_lt_of_stringCode_lt
    (constructor : String) {left right : String}
    (strict : stringCode left < stringCode right) :
    patternCode (.apply constructor [.fvar left]) <
      patternCode (.apply constructor [.fvar right]) := by
  have freeVariableStep : patternCode (.fvar left) <
      patternCode (.fvar right) := by
    simpa [patternCode] using Nat.pair_lt_pair_right 1 strict
  have argumentStep : patternListCode [.fvar left] <
      patternListCode [.fvar right] := by
    simpa [patternListCode] using
      Nat.succ_lt_succ (Nat.pair_lt_pair_left 0 freeVariableStep)
  simpa [patternCode] using Nat.pair_lt_pair_right 2
    (Nat.pair_lt_pair_right (stringCode constructor) argumentStep)

end Mettapedia.OSLF.MeTTaIL.PatternCode

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Flatten and remove the selected unit exactly as the ordinary reflective
canonicalizer does, but order the surviving occurrences by `key`. -/
def normalizeParallelElementsBy {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) : List Pattern :=
  PatternCode.sortPatternsBy key
    ((patterns.flatMap (parallelSplice declaration)).filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor [])

@[simp]
theorem normalizeParallelElementsBy_patternCode
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    normalizeParallelElementsBy PatternCode.patternCode declaration patterns =
    normalizeParallelElements declaration patterns :=
  rfl

mutual
  /-- Key-parametric reflective canonicalization that also exposes the
  quote-visible binder depth at which an ordering key is interpreted.  An
  authored quote resets that depth exactly as reflective supported
  substitution does. -/
  def canonicalizeByAt {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
      Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        let childDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeListByAt key declaration childDepth arguments)
    | .lambda binderName body =>
        .lambda binderName
          (canonicalizeByAt key declaration (availableDepth + 1) body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (canonicalizeByAt key declaration (availableDepth + arity) body)
    | .subst body replacement =>
        .subst
          (canonicalizeByAt key declaration (availableDepth + 1) body)
          (canonicalizeByAt key declaration availableDepth replacement)
    | .collection collectionType elements none =>
        let normalizedElements :=
          canonicalizeListByAt key declaration availableDepth elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElementsBy (key availableDepth) declaration
              normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType
          (canonicalizeListByAt key declaration availableDepth elements) rest

  /-- Pointwise companion to `canonicalizeByAt`. -/
  def canonicalizeListByAt {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalizeByAt key declaration availableDepth pattern ::
          canonicalizeListByAt key declaration availableDepth patterns
end

/-- The list companion is exactly pointwise keyed canonicalization. -/
theorem canonicalizeListByAt_eq_map {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (patterns : List Pattern) :
    canonicalizeListByAt key declaration availableDepth patterns =
      patterns.map (canonicalizeByAt key declaration availableDepth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeListByAt, inductionHypothesis]

@[simp]
theorem canonicalizeListByAt_length {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (patterns : List Pattern) :
    (canonicalizeListByAt key declaration availableDepth patterns).length =
      patterns.length := by
  rw [canonicalizeListByAt_eq_map, List.length_map]

mutual
  /-- Key-parametric canonicalization with separate quote-visible and
  structural binder depths.  Quotation resets only `availableDepth`; binder
  traversal advances both depths. -/
  def canonicalizeByDepths {Key : Type} [LinearOrder Key]
      (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeListByDepths key declaration childAvailableDepth
            scopeDepth arguments)
    | .lambda binderName body =>
        .lambda binderName
          (canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (canonicalizeByDepths key declaration (availableDepth + arity)
            (scopeDepth + arity) body)
    | .subst body replacement =>
        .subst
          (canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body)
          (canonicalizeByDepths key declaration availableDepth scopeDepth
            replacement)
    | .collection collectionType elements none =>
        let normalizedElements :=
          canonicalizeListByDepths key declaration availableDepth scopeDepth
            elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElementsBy (key availableDepth scopeDepth)
              declaration normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType
          (canonicalizeListByDepths key declaration availableDepth scopeDepth
            elements) rest

  /-- Pointwise companion to two-depth canonicalization. -/
  def canonicalizeListByDepths {Key : Type} [LinearOrder Key]
      (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalizeByDepths key declaration availableDepth scopeDepth pattern ::
          canonicalizeListByDepths key declaration availableDepth scopeDepth
            patterns
end

/-- Two-depth keyed canonicalization cancels the reflective declaration's
quote/drop shell exactly.  The ordering key is irrelevant at this redex;
quotation resets only the available depth before the enclosed name is
canonicalized. -/
@[simp]
theorem canonicalizeByDepths_quote_drop
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (availableDepth scopeDepth : Nat) (name : Pattern) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]]) =
      canonicalizeByDepths key declaration 0 scopeDepth name := by
  simp [canonicalizeByDepths, canonicalizeListByDepths,
    finishNormalizeReflectiveApply, Ne.symm quote_ne_drop]

/-- The two-depth list companion is pointwise canonicalization. -/
theorem canonicalizeListByDepths_eq_map {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (patterns : List Pattern) :
    canonicalizeListByDepths key declaration availableDepth scopeDepth patterns =
      patterns.map
        (canonicalizeByDepths key declaration availableDepth scopeDepth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeListByDepths, inductionHypothesis]

mutual
  /-- Ignoring structural depth recovers the original one-depth keyed
  canonicalizer exactly. -/
  theorem canonicalizeByDepths_ignoreScope
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) :
      ∀ availableDepth scopeDepth pattern,
        canonicalizeByDepths (fun availableDepth _ pattern =>
            key availableDepth pattern) declaration availableDepth scopeDepth
            pattern =
          canonicalizeByAt key declaration availableDepth pattern
    | _, _, .bvar _ => rfl
    | _, _, .fvar _ => rfl
    | availableDepth, scopeDepth, .apply constructor arguments => by
        simp only [canonicalizeByDepths, canonicalizeByAt]
        exact congrArg
          (finishNormalizeReflectiveApply declaration constructor)
          (canonicalizeListByDepths_ignoreScope key declaration
            (if constructor == declaration.quoteConstructor then 0
              else availableDepth) scopeDepth arguments)
    | availableDepth, scopeDepth, .lambda binderName body => by
        simp only [canonicalizeByDepths, canonicalizeByAt,
          Pattern.lambda.injEq, true_and]
        exact canonicalizeByDepths_ignoreScope key declaration
          (availableDepth + 1) (scopeDepth + 1) body
    | availableDepth, scopeDepth,
        .multiLambda arity binderNames body => by
        simp only [canonicalizeByDepths, canonicalizeByAt,
          Pattern.multiLambda.injEq, true_and]
        exact canonicalizeByDepths_ignoreScope key declaration
          (availableDepth + arity) (scopeDepth + arity) body
    | availableDepth, scopeDepth, .subst body replacement => by
        simp only [canonicalizeByDepths, canonicalizeByAt,
          Pattern.subst.injEq]
        exact ⟨
          canonicalizeByDepths_ignoreScope key declaration
            (availableDepth + 1) (scopeDepth + 1) body,
          canonicalizeByDepths_ignoreScope key declaration availableDepth
            scopeDepth replacement⟩
    | availableDepth, scopeDepth,
        .collection collectionType elements none => by
        simp only [canonicalizeByDepths, canonicalizeByAt,
          canonicalizeListByDepths_ignoreScope key declaration availableDepth
            scopeDepth elements]
    | availableDepth, scopeDepth,
        .collection collectionType elements (some rest) => by
        simp only [canonicalizeByDepths, canonicalizeByAt,
          Pattern.collection.injEq, true_and]
        exact ⟨canonicalizeListByDepths_ignoreScope key declaration
          availableDepth scopeDepth elements, trivial⟩

  theorem canonicalizeListByDepths_ignoreScope
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) :
      ∀ availableDepth scopeDepth patterns,
        canonicalizeListByDepths (fun availableDepth _ pattern =>
            key availableDepth pattern) declaration availableDepth scopeDepth
            patterns =
          canonicalizeListByAt key declaration availableDepth patterns
    | _, _, [] => rfl
    | availableDepth, scopeDepth, pattern :: patterns => by
        simp only [canonicalizeListByDepths, canonicalizeListByAt,
          canonicalizeByDepths_ignoreScope key declaration availableDepth
            scopeDepth pattern,
          canonicalizeListByDepths_ignoreScope key declaration availableDepth
            scopeDepth patterns]
end

/-- The one-depth keyed canonicalizer cancels the declared Quote/Drop shell.
The child is canonicalized at quote-visible depth zero; the ambient depth is
irrelevant to the contraction itself. -/
@[simp]
theorem canonicalizeByAt_quote_drop
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (availableDepth : Nat) (name : Pattern) :
    canonicalizeByAt key declaration availableDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]]) =
      canonicalizeByAt key declaration 0 name := by
  simpa only [
      canonicalizeByDepths_ignoreScope key declaration availableDepth 0,
      canonicalizeByDepths_ignoreScope key declaration 0 0] using
    (canonicalizeByDepths_quote_drop
      (fun availableDepth _ pattern => key availableDepth pattern)
      declaration quote_ne_drop availableDepth 0 name)

/-- Finishing a reflective application before recursively canonicalizing it
does not change its eventual canonical representative. -/
theorem canonicalize_finishNormalizeReflectiveApply
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

/-- Key normalization and structural normalization retain the same parallel
occurrences; they differ only in the chosen order. -/
theorem normalizeParallelElementsBy_perm
    {Key : Type} [LinearOrder Key]
    (key : Pattern → Key) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    List.Perm (normalizeParallelElementsBy key declaration patterns)
      (normalizeParallelElements declaration patterns) := by
  unfold normalizeParallelElementsBy normalizeParallelElements
  exact (PatternCode.sortPatternsBy_perm key _).trans
    (sortPatterns_perm _).symm

mutual
  /-- Re-canonicalizing a depth-aware keyed representative with the authored
  structural canonicalizer yields the ordinary representative. -/
  theorem canonicalize_canonicalizeByAt
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
        rw [canonicalize_finishNormalizeReflectiveApply declaration
          quote_ne_drop]
        simp only [canonicalize]
        apply congrArg
        exact canonicalizeList_canonicalizeListByAt key declaration
          quote_ne_drop _ arguments
    | availableDepth, .lambda binder body => by
        simp only [canonicalizeByAt, canonicalize, Pattern.lambda.injEq,
          true_and]
        exact canonicalize_canonicalizeByAt key declaration quote_ne_drop
          (availableDepth + 1) body
    | availableDepth, .multiLambda arity binders body => by
        simp only [canonicalizeByAt, canonicalize,
          Pattern.multiLambda.injEq, true_and]
        exact canonicalize_canonicalizeByAt key declaration quote_ne_drop
          (availableDepth + arity) body
    | availableDepth, .subst body replacement => by
        simp only [canonicalizeByAt, canonicalize, Pattern.subst.injEq]
        exact ⟨
          canonicalize_canonicalizeByAt key declaration quote_ne_drop
            (availableDepth + 1) body,
          canonicalize_canonicalizeByAt key declaration quote_ne_drop
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
            (normalizeParallelElementsBy_perm (key availableDepth)
              declaration
              (canonicalizeListByAt key declaration availableDepth elements))]
          rw [← canonicalize_parallel_normalize_input declaration
            (canonicalizeListByAt key declaration availableDepth elements)]
          simp only [canonicalize, beq_self_eq_true, if_true]
          rw [canonicalizeList_canonicalizeListByAt key declaration
            quote_ne_drop availableDepth elements]
        · have notParallelBool :
              (collectionType == declaration.parallelCollection) = false := by
            exact beq_eq_false_iff_ne.mpr isParallel
          simp [canonicalize, notParallelBool,
            canonicalizeList_canonicalizeListByAt key declaration
              quote_ne_drop availableDepth elements]
    | availableDepth, .collection collectionType elements (some rest) => by
        simp only [canonicalizeByAt, canonicalize, Pattern.collection.injEq,
          true_and]
        exact ⟨
          canonicalizeList_canonicalizeListByAt key declaration
            quote_ne_drop availableDepth elements,
          trivial⟩

  /-- Pointwise absorption companion for lists. -/
  theorem canonicalizeList_canonicalizeListByAt
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
        rw [canonicalize_canonicalizeByAt key declaration quote_ne_drop
          availableDepth pattern]
        rw [canonicalizeList_canonicalizeListByAt key declaration
          quote_ne_drop availableDepth patterns]
end

mutual
  /-- Re-canonicalizing a two-depth keyed representative with the authored
  structural canonicalizer yields the ordinary representative. Structural
  depth may affect the ordering key, but only the resulting permutation. -/
  theorem canonicalize_canonicalizeByDepths
      {Key : Type} [LinearOrder Key]
      (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (quote_ne_drop : declaration.quoteConstructor ≠
        declaration.dropConstructor) :
      ∀ availableDepth scopeDepth pattern,
        canonicalize declaration
            (canonicalizeByDepths key declaration availableDepth scopeDepth
              pattern) =
          canonicalize declaration pattern
    | _, _, .bvar _ => rfl
    | _, _, .fvar _ => rfl
    | availableDepth, scopeDepth, .apply constructor arguments => by
        simp only [canonicalizeByDepths]
        rw [canonicalize_finishNormalizeReflectiveApply declaration
          quote_ne_drop]
        simp only [canonicalize]
        apply congrArg
        exact canonicalizeList_canonicalizeListByDepths key declaration
          quote_ne_drop _ scopeDepth arguments
    | availableDepth, scopeDepth, .lambda binder body => by
        simp only [canonicalizeByDepths, canonicalize, Pattern.lambda.injEq,
          true_and]
        exact canonicalize_canonicalizeByDepths key declaration quote_ne_drop
          (availableDepth + 1) (scopeDepth + 1) body
    | availableDepth, scopeDepth,
        .multiLambda arity binders body => by
        simp only [canonicalizeByDepths, canonicalize,
          Pattern.multiLambda.injEq, true_and]
        exact canonicalize_canonicalizeByDepths key declaration quote_ne_drop
          (availableDepth + arity) (scopeDepth + arity) body
    | availableDepth, scopeDepth, .subst body replacement => by
        simp only [canonicalizeByDepths, canonicalize, Pattern.subst.injEq]
        exact ⟨
          canonicalize_canonicalizeByDepths key declaration quote_ne_drop
            (availableDepth + 1) (scopeDepth + 1) body,
          canonicalize_canonicalizeByDepths key declaration quote_ne_drop
            availableDepth scopeDepth replacement⟩
    | availableDepth, scopeDepth,
        .collection collectionType elements none => by
        simp only [canonicalizeByDepths]
        by_cases isParallel :
            collectionType = declaration.parallelCollection
        · subst collectionType
          simp only [beq_self_eq_true, if_true]
          rw [← canonicalize_parallel_collapse declaration
            (normalizeParallelElementsBy (key availableDepth scopeDepth)
              declaration
              (canonicalizeListByDepths key declaration availableDepth
                scopeDepth elements))]
          rw [canonicalize_parallel_permutation declaration
            (normalizeParallelElementsBy_perm (key availableDepth scopeDepth)
              declaration
              (canonicalizeListByDepths key declaration availableDepth
                scopeDepth elements))]
          rw [← canonicalize_parallel_normalize_input declaration
            (canonicalizeListByDepths key declaration availableDepth scopeDepth
              elements)]
          simp only [canonicalize, beq_self_eq_true, if_true]
          rw [canonicalizeList_canonicalizeListByDepths key declaration
            quote_ne_drop availableDepth scopeDepth elements]
        · have notParallelBool :
              (collectionType == declaration.parallelCollection) = false := by
            exact beq_eq_false_iff_ne.mpr isParallel
          simp [canonicalize, notParallelBool,
            canonicalizeList_canonicalizeListByDepths key declaration
              quote_ne_drop availableDepth scopeDepth elements]
    | availableDepth, scopeDepth,
        .collection collectionType elements (some rest) => by
        simp only [canonicalizeByDepths, canonicalize,
          Pattern.collection.injEq, true_and]
        exact ⟨
          canonicalizeList_canonicalizeListByDepths key declaration
            quote_ne_drop availableDepth scopeDepth elements,
          trivial⟩

  /-- Pointwise absorption companion for two-depth keyed lists. -/
  theorem canonicalizeList_canonicalizeListByDepths
      {Key : Type} [LinearOrder Key]
      (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (quote_ne_drop : declaration.quoteConstructor ≠
        declaration.dropConstructor) :
      ∀ availableDepth scopeDepth patterns,
        canonicalizeList declaration
            (canonicalizeListByDepths key declaration availableDepth scopeDepth
              patterns) =
          canonicalizeList declaration patterns
    | _, _, [] => rfl
    | availableDepth, scopeDepth, pattern :: patterns => by
        simp only [canonicalizeListByDepths, canonicalizeList]
        rw [canonicalize_canonicalizeByDepths key declaration quote_ne_drop
          availableDepth scopeDepth pattern]
        rw [canonicalizeList_canonicalizeListByDepths key declaration
          quote_ne_drop availableDepth scopeDepth patterns]
end

mutual
  /-- Reflective canonicalization with an explicit ordering key for each
  selected parallel collection.  All authored quote/drop, flattening, and unit
  laws are unchanged. -/
  def canonicalizeBy {Key : Type} [LinearOrder Key]
      (key : Pattern → Key) (declaration : ReflectivePresentationDecl) :
      Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        finishNormalizeReflectiveApply declaration constructor
          (canonicalizeListBy key declaration arguments)
    | .lambda binderName body =>
        .lambda binderName (canonicalizeBy key declaration body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (canonicalizeBy key declaration body)
    | .subst body replacement =>
        .subst (canonicalizeBy key declaration body)
          (canonicalizeBy key declaration replacement)
    | .collection collectionType elements none =>
        let normalizedElements := canonicalizeListBy key declaration elements
        if collectionType == declaration.parallelCollection then
          collapseParallel declaration
            (normalizeParallelElementsBy key declaration normalizedElements)
        else
          .collection collectionType normalizedElements none
    | .collection collectionType elements rest =>
        .collection collectionType
          (canonicalizeListBy key declaration elements) rest

  /-- Pointwise companion to `canonicalizeBy`. -/
  def canonicalizeListBy {Key : Type} [LinearOrder Key]
      (key : Pattern → Key) (declaration : ReflectivePresentationDecl) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        canonicalizeBy key declaration pattern ::
          canonicalizeListBy key declaration patterns
end

mutual
  /-- A depth-independent key recovers the original key-parametric
  canonicalizer at every ambient depth. -/
  theorem canonicalizeByAt_const {Key : Type} [LinearOrder Key]
      (key : Pattern → Key) (declaration : ReflectivePresentationDecl) :
      ∀ availableDepth pattern,
        canonicalizeByAt (fun _ pattern => key pattern) declaration
            availableDepth pattern =
          canonicalizeBy key declaration pattern
    | _, .bvar _ => rfl
    | _, .fvar _ => rfl
    | availableDepth, .apply constructor arguments => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeListByAt_const key declaration _ arguments]
    | availableDepth, .lambda binderName body => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeByAt_const key declaration (availableDepth + 1) body]
    | availableDepth, .multiLambda arity binderNames body => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeByAt_const key declaration (availableDepth + arity) body]
    | availableDepth, .subst body replacement => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeByAt_const key declaration (availableDepth + 1) body,
          canonicalizeByAt_const key declaration availableDepth replacement]
    | availableDepth, .collection collectionType elements none => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeListByAt_const key declaration availableDepth elements]
    | availableDepth, .collection collectionType elements (some rest) => by
        simp only [canonicalizeByAt, canonicalizeBy,
          canonicalizeListByAt_const key declaration availableDepth elements]

  theorem canonicalizeListByAt_const {Key : Type} [LinearOrder Key]
      (key : Pattern → Key) (declaration : ReflectivePresentationDecl) :
      ∀ availableDepth patterns,
        canonicalizeListByAt (fun _ pattern => key pattern) declaration
            availableDepth patterns =
          canonicalizeListBy key declaration patterns
    | _, [] => rfl
    | availableDepth, pattern :: patterns => by
        simp only [canonicalizeListByAt, canonicalizeListBy,
          canonicalizeByAt_const key declaration availableDepth pattern,
          canonicalizeListByAt_const key declaration availableDepth patterns]
end

mutual
  /-- The existing structural canonicalizer is exactly the `patternCode`
  instance of the key-parametric construction. -/
  theorem canonicalizeBy_patternCode
      (declaration : ReflectivePresentationDecl) :
      ∀ pattern,
        canonicalizeBy PatternCode.patternCode declaration pattern =
          canonicalize declaration pattern
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .apply constructor arguments => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeListBy_patternCode declaration arguments]
    | .lambda binderName body => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeBy_patternCode declaration body]
    | .multiLambda arity binderNames body => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeBy_patternCode declaration body]
    | .subst body replacement => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeBy_patternCode declaration body,
          canonicalizeBy_patternCode declaration replacement]
    | .collection collectionType elements none => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeListBy_patternCode declaration elements,
          normalizeParallelElementsBy_patternCode]
    | .collection collectionType elements (some rest) => by
        simp only [canonicalizeBy, canonicalize,
          canonicalizeListBy_patternCode declaration elements]

  theorem canonicalizeListBy_patternCode
      (declaration : ReflectivePresentationDecl) :
      ∀ patterns,
        canonicalizeListBy PatternCode.patternCode declaration patterns =
          canonicalizeList declaration patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [canonicalizeListBy, canonicalizeList,
          canonicalizeBy_patternCode declaration pattern,
          canonicalizeListBy_patternCode declaration patterns]
end

/-! ## Executable policy canaries -/

private def keyedFixtureDeclaration : ReflectivePresentationDecl where
  name := "keyed-fixture"
  processSort := "Proc"
  nameSort := "Name"
  quoteConstructor := "quote"
  dropConstructor := "drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "zero"
  quoteDropEquation := "quote-drop"

private def keyedFixturePattern : Pattern :=
  .collection .hashBag [.fvar "a", .fvar "b"] none

private def swapABKey : Pattern → Nat
  | .fvar "a" => 1
  | .fvar "b" => 0
  | pattern => PatternCode.patternCode pattern + 2

private def keepABKey : Pattern → Nat
  | .fvar "a" => 0
  | .fvar "b" => 1
  | pattern => PatternCode.patternCode pattern + 2

/-- Positive canary: the supplied key, rather than compact source spelling,
controls the selected parallel representative. -/
theorem canonicalizeBy_swapABKey_canary :
    canonicalizeBy swapABKey keyedFixtureDeclaration keyedFixturePattern =
      .collection .hashBag [.fvar "b", .fvar "a"] none := by
  simp [keyedFixturePattern, canonicalizeBy, canonicalizeListBy,
    normalizeParallelElementsBy, PatternCode.sortPatternsBy, parallelSplice,
    collapseParallel, keyedFixtureDeclaration, swapABKey, List.mergeSort]

theorem canonicalizeBy_keepABKey_canary :
    canonicalizeBy keepABKey keyedFixtureDeclaration keyedFixturePattern =
      .collection .hashBag [.fvar "a", .fvar "b"] none := by
  simp [keyedFixturePattern, canonicalizeBy, canonicalizeListBy,
    normalizeParallelElementsBy, PatternCode.sortPatternsBy, parallelSplice,
    collapseParallel, keyedFixtureDeclaration, keepABKey, List.mergeSort]

/-- Negative canary: changing the key can observably change the exact compact
representative even though the authored bag laws are unchanged. -/
theorem canonicalizeBy_key_observable_canary :
    canonicalizeBy swapABKey keyedFixtureDeclaration keyedFixturePattern ≠
      canonicalizeBy keepABKey keyedFixtureDeclaration keyedFixturePattern := by
  rw [canonicalizeBy_swapABKey_canary, canonicalizeBy_keepABKey_canary]
  decide

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
