import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyedSingleton
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalInversion
import Mathlib.Data.List.Perm.Basic

/-!
# Keyed and plain canonical forms agree up to bare-parallel order

The keyed canonicalizer sorts bare parallel contents by a semantic key; the
plain canonicalizer sorts them by structural code.  The two outputs are
therefore not equal — the banked tie falsifier is exact — but they differ
*only* in the order of bare parallel contents, hereditarily.  This module
defines that relation and proves the coherence theorem.

The consequence is load-bearing for the universal apex recursion: every
question of the form "does the keyed pipeline make the same structural
decision as the plain pipeline" — does a quote absorb its argument, is an
element the parallel unit, what is the root constructor — is answered once
by this relation's shape preservation, instead of case-by-case inside the
recursion.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  /-- Hereditary equality up to the order of bare parallel contents.  Every
  rigid constructor is congruent; a bare parallel collection may permute its
  pointwise-related contents. -/
  inductive ParallelOrderAgnostic (declaration : ReflectivePresentationDecl) :
      Pattern → Pattern → Prop where
    | bvar (index : Nat) :
        ParallelOrderAgnostic declaration (.bvar index) (.bvar index)
    | fvar (name : String) :
        ParallelOrderAgnostic declaration (.fvar name) (.fvar name)
    | apply (constructor : String) {leftArguments rightArguments : List Pattern}
        (arguments : ParallelOrderAgnosticList declaration leftArguments
          rightArguments) :
        ParallelOrderAgnostic declaration (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : ParallelOrderAgnostic declaration leftBody rightBody) :
        ParallelOrderAgnostic declaration (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : ParallelOrderAgnostic declaration leftBody rightBody) :
        ParallelOrderAgnostic declaration
          (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : ParallelOrderAgnostic declaration leftBody rightBody)
        (replacement : ParallelOrderAgnostic declaration leftReplacement
          rightReplacement) :
        ParallelOrderAgnostic declaration (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection (collectionType : CollType) (rest : Option String)
        {leftElements rightElements : List Pattern}
        (elements : ParallelOrderAgnosticList declaration leftElements
          rightElements) :
        ParallelOrderAgnostic declaration
          (.collection collectionType leftElements rest)
          (.collection collectionType rightElements rest)
    | parallel {leftElements middleElements rightElements : List Pattern}
        (pointwise : ParallelOrderAgnosticList declaration leftElements
          middleElements)
        (permutation : middleElements.Perm rightElements) :
        ParallelOrderAgnostic declaration
          (.collection declaration.parallelCollection leftElements none)
          (.collection declaration.parallelCollection rightElements none)

  /-- Pointwise companion. -/
  inductive ParallelOrderAgnosticList
      (declaration : ReflectivePresentationDecl) :
      List Pattern → List Pattern → Prop where
    | nil : ParallelOrderAgnosticList declaration [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : ParallelOrderAgnostic declaration leftHead rightHead)
        (tail : ParallelOrderAgnosticList declaration leftTail rightTail) :
        ParallelOrderAgnosticList declaration (leftHead :: leftTail)
          (rightHead :: rightTail)
end

namespace ParallelOrderAgnostic

mutual
  /-- Reflexivity. -/
  theorem refl (declaration : ReflectivePresentationDecl) :
      ∀ pattern, ParallelOrderAgnostic declaration pattern pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        .apply constructor (ParallelOrderAgnosticList.refl declaration
          arguments)
    | .lambda binder body => .lambda binder (refl declaration body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (refl declaration body)
    | .subst body replacement =>
        .subst (refl declaration body) (refl declaration replacement)
    | .collection collectionType elements rest =>
        .collection collectionType rest
          (ParallelOrderAgnosticList.refl declaration elements)

  /-- Listwise reflexivity. -/
  theorem ParallelOrderAgnosticList.refl
      (declaration : ReflectivePresentationDecl) :
      ∀ patterns, ParallelOrderAgnosticList declaration patterns patterns
    | [] => .nil
    | pattern :: patterns =>
        .cons (refl declaration pattern)
          (ParallelOrderAgnosticList.refl declaration patterns)
end

mutual
  /-- Plain reflective canonicalization quotients exactly the order variation
  admitted by `ParallelOrderAgnostic`.  In the parallel constructor the
  pointwise correspondence first identifies the recursively canonicalized
  entries; the retained permutation is then erased by structural-code
  sorting. -/
  theorem canonicalize_eq {declaration : ReflectivePresentationDecl}
      {left right : Pattern}
      (related : ParallelOrderAgnostic declaration left right) :
      canonicalize declaration left = canonicalize declaration right := by
    cases related with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        unfold canonicalize
        rw [canonicalizeList_eq arguments]
    | lambda binder body =>
        simp only [canonicalize]
        rw [canonicalize_eq body]
    | multiLambda arity binders body =>
        simp only [canonicalize]
        rw [canonicalize_eq body]
    | subst body replacement =>
        simp only [canonicalize]
        rw [canonicalize_eq body, canonicalize_eq replacement]
    | collection collectionType rest elements =>
        cases rest <;> simp only [canonicalize] <;>
          rw [canonicalizeList_eq elements]
    | @parallel leftElements middleElements rightElements pointwise reordered =>
        have leftMiddle : canonicalizeList declaration leftElements =
            canonicalizeList declaration middleElements :=
          canonicalizeList_eq pointwise
        have middleRight : List.Perm
            (canonicalizeList declaration middleElements)
            (canonicalizeList declaration rightElements) := by
          rw [canonicalizeList_eq_map, canonicalizeList_eq_map]
          exact reordered.map (canonicalize declaration)
        have leftRight : List.Perm
            (canonicalizeList declaration leftElements)
            (canonicalizeList declaration rightElements) :=
          (List.Perm.of_eq leftMiddle).trans middleRight
        simp only [canonicalize, beq_self_eq_true, if_true]
        rw [normalizeParallelElements_eq_of_perm declaration leftRight]

  /-- Listwise companion of `ParallelOrderAgnostic.canonicalize_eq`. -/
  theorem canonicalizeList_eq
      {declaration : ReflectivePresentationDecl} {left right : List Pattern}
      (related : ParallelOrderAgnosticList declaration left right) :
      canonicalizeList declaration left = canonicalizeList declaration right := by
    cases related with
    | nil => rfl
    | cons head tail =>
        simp only [canonicalizeList]
        rw [canonicalize_eq head, canonicalizeList_eq tail]
end

/-- A pointwise order-agnostic correspondence followed by a permutation.

This is the natural list currency for the parallel pipeline: splicing and
unit filtering preserve the pointwise relation, while either sorting policy
may change only the final order. -/
def ParallelOrderAgnosticPermutation
    (declaration : ReflectivePresentationDecl)
    (left right : List Pattern) : Prop :=
  ∃ middle, ParallelOrderAgnosticList declaration left middle ∧
    middle.Perm right

namespace ParallelOrderAgnosticList

/-- The project-specific pointwise relation is propositionally the standard
`List.Forall₂` relation used by the permutation API. -/
def toForall₂ {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right) :
    List.Forall₂ (ParallelOrderAgnostic declaration) left right :=
  match related with
  | .nil => .nil
  | .cons head tail => .cons head (toForall₂ tail)

/-- Convert the standard pointwise relation back to the project-specific
inductive carrier. -/
def ofForall₂ {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : List.Forall₂ (ParallelOrderAgnostic declaration) left right) :
    ParallelOrderAgnosticList declaration left right := by
  induction related with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- Pointwise correspondence is preserved by concatenation. -/
def append {declaration : ReflectivePresentationDecl}
    {left₁ right₁ left₂ right₂ : List Pattern}
    (first : ParallelOrderAgnosticList declaration left₁ right₁)
    (second : ParallelOrderAgnosticList declaration left₂ right₂) :
    ParallelOrderAgnosticList declaration (left₁ ++ left₂)
      (right₁ ++ right₂) :=
  match first with
  | .nil => second
  | .cons head tail => .cons head (append tail second)

/-- Filtering out the reflective parallel unit preserves pointwise
order-agnostic correspondence. -/
def filterNotUnit {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right) :
    ParallelOrderAgnosticList declaration
      (left.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor [])
      (right.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []) := by
  cases related with
  | nil => exact .nil
  | @cons leftHead rightHead leftTail rightTail head tail =>
      have unitIff :
          leftHead = .apply declaration.parallelUnitConstructor [] ↔
            rightHead = .apply declaration.parallelUnitConstructor [] := by
        constructor
        · intro leftUnit
          subst leftUnit
          cases head with
          | apply constructor arguments => cases arguments; rfl
        · intro rightUnit
          subst rightUnit
          cases head with
          | apply constructor arguments => cases arguments; rfl
      let inductionHypothesis := filterNotUnit tail
      by_cases leftUnit :
          leftHead = .apply declaration.parallelUnitConstructor []
      · have rightUnit := unitIff.mp leftUnit
        simpa [leftUnit, rightUnit] using inductionHypothesis
      · have rightUnit :
            rightHead ≠ .apply declaration.parallelUnitConstructor [] := by
          intro equality
          exact leftUnit (unitIff.mpr equality)
        simpa [leftUnit, rightUnit] using
          ParallelOrderAgnosticList.cons head inductionHypothesis

/-- Build pointwise correspondence between two maps of the same list. -/
theorem mapPair {declaration : ReflectivePresentationDecl}
    {patterns : List Pattern} {left right : Pattern → Pattern}
    (related : ∀ pattern ∈ patterns,
      ParallelOrderAgnostic declaration (left pattern) (right pattern)) :
    ParallelOrderAgnosticList declaration (patterns.map left)
      (patterns.map right) := by
  induction patterns with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (related head (by simp))
        (inductionHypothesis fun pattern membership =>
          related pattern (by simp [membership]))

end ParallelOrderAgnosticList

namespace ParallelOrderAgnosticPermutation

/-- A pointwise correspondence is a correspondence up to permutation. -/
theorem ofAligned {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right) :
    ParallelOrderAgnosticPermutation declaration left right :=
  ⟨right, related, .refl right⟩

/-- Correspondences up to permutation compose under concatenation. -/
theorem append {declaration : ReflectivePresentationDecl}
    {left₁ right₁ left₂ right₂ : List Pattern}
    (first : ParallelOrderAgnosticPermutation declaration left₁ right₁)
    (second : ParallelOrderAgnosticPermutation declaration left₂ right₂) :
    ParallelOrderAgnosticPermutation declaration (left₁ ++ left₂)
      (right₁ ++ right₂) := by
  obtain ⟨firstMiddle, firstAligned, firstReordered⟩ := first
  obtain ⟨secondMiddle, secondAligned, secondReordered⟩ := second
  exact ⟨firstMiddle ++ secondMiddle,
    ParallelOrderAgnosticList.append firstAligned secondAligned,
    firstReordered.append secondReordered⟩

/-- Splicing one related pair exposes corresponding parallel contents up to
permutation. -/
theorem parallelSplice {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (related : ParallelOrderAgnostic declaration left right) :
    ParallelOrderAgnosticPermutation declaration
      (ReflectiveCanonical.parallelSplice declaration left)
      (ReflectiveCanonical.parallelSplice declaration right) := by
  cases related with
  | bvar index => exact ofAligned (.cons (.bvar index) .nil)
  | fvar name => exact ofAligned (.cons (.fvar name) .nil)
  | apply constructor arguments =>
      exact ofAligned (.cons (.apply constructor arguments) .nil)
  | lambda binder body =>
      exact ofAligned (.cons (.lambda binder body) .nil)
  | multiLambda arity binders body =>
      exact ofAligned (.cons (.multiLambda arity binders body) .nil)
  | subst body replacement =>
      exact ofAligned (.cons (.subst body replacement) .nil)
  | @collection collectionType rest leftElements rightElements elements =>
      by_cases bare : collectionType = declaration.parallelCollection ∧
        rest = none
      · obtain ⟨typeEq, restEq⟩ := bare
        subst typeEq
        subst restEq
        simpa [ReflectiveCanonical.parallelSplice] using ofAligned elements
      · have leftRigid : ∀ contents,
            Pattern.collection collectionType leftElements rest ≠
              .collection declaration.parallelCollection contents none := by
          intro contents equality
          exact bare (by cases equality; exact ⟨rfl, rfl⟩)
        have rightRigid : ∀ contents,
            Pattern.collection collectionType rightElements rest ≠
              .collection declaration.parallelCollection contents none := by
          intro contents equality
          exact bare (by cases equality; exact ⟨rfl, rfl⟩)
        rw [parallelSplice_eq_singleton_of_not_parallel declaration _ leftRigid,
          parallelSplice_eq_singleton_of_not_parallel declaration _ rightRigid]
        exact ofAligned (.cons (.collection collectionType rest elements) .nil)
  | @parallel leftElements middleElements rightElements pointwise reordered =>
      simpa [ParallelOrderAgnosticPermutation,
        ReflectiveCanonical.parallelSplice] using
        (⟨middleElements, pointwise, reordered⟩ :
          ∃ middle, ParallelOrderAgnosticList declaration leftElements middle ∧
            middle.Perm rightElements)

/-- Pointwise-related lists have spliced frontiers related up to
permutation. -/
theorem flatMapParallelSplice {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticList declaration left right) :
    ParallelOrderAgnosticPermutation declaration
      (left.flatMap (ReflectiveCanonical.parallelSplice declaration))
      (right.flatMap (ReflectiveCanonical.parallelSplice declaration)) :=
  match related with
  | .nil => ofAligned .nil
  | .cons head tail => by
      simpa only [List.flatMap_cons] using
        append (parallelSplice head) (flatMapParallelSplice tail)

/-- Unit filtering preserves a correspondence up to permutation. -/
theorem filterNotUnit {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticPermutation declaration left right) :
    ParallelOrderAgnosticPermutation declaration
      (left.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor [])
      (right.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []) := by
  obtain ⟨middle, aligned, reordered⟩ := related
  exact ⟨middle.filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor [],
    ParallelOrderAgnosticList.filterNotUnit aligned,
    reordered.filter fun pattern =>
      pattern ≠ .apply declaration.parallelUnitConstructor []⟩

/-- Arbitrary deterministic sorting policies preserve an existing
order-agnostic correspondence up to permutation. -/
theorem sort
    {declaration : ReflectivePresentationDecl}
    {Key : Type} [LinearOrder Key]
    (leftKey : Pattern → Key) (rightKey : Pattern → Nat)
    {left right : List Pattern}
    (related : ParallelOrderAgnosticPermutation declaration left right) :
    ParallelOrderAgnosticPermutation declaration
      (PatternCode.sortPatternsBy leftKey left)
      (PatternCode.sortPatternsBy rightKey right) := by
  obtain ⟨middle, aligned, reordered⟩ := related
  obtain ⟨sortedMiddle, sortedAligned, sortedToMiddle⟩ :=
    List.perm_comp_forall₂ (PatternCode.sortPatternsBy_perm leftKey left)
      (ParallelOrderAgnostic.ParallelOrderAgnosticList.toForall₂ aligned)
  exact ⟨sortedMiddle,
    ParallelOrderAgnostic.ParallelOrderAgnosticList.ofForall₂ sortedAligned,
    sortedToMiddle.trans (reordered.trans
      (PatternCode.sortPatternsBy_perm rightKey right).symm)⟩

/-- Collapsing corresponding normalized parallel frontiers preserves the
order-agnostic relation.  The empty, singleton, and proper-bag cases agree
because pointwise alignment and permutation preserve length. -/
theorem collapse {declaration : ReflectivePresentationDecl}
    {left right : List Pattern}
    (related : ParallelOrderAgnosticPermutation declaration left right) :
    ParallelOrderAgnostic declaration
      (ReflectiveCanonical.collapseParallel declaration left)
      (ReflectiveCanonical.collapseParallel declaration right) := by
  obtain ⟨middle, aligned, reordered⟩ := related
  have lengthEq : left.length = right.length :=
    (ParallelOrderAgnostic.ParallelOrderAgnosticList.toForall₂ aligned
      ).length_eq.trans reordered.length_eq
  cases left with
  | nil =>
      have rightNil : right = [] :=
        List.length_eq_zero_iff.mp (by simpa using lengthEq.symm)
      subst right
      exact .apply declaration.parallelUnitConstructor .nil
  | cons leftHead leftTail =>
      cases leftTail with
      | nil =>
          obtain ⟨rightHead, rightEq⟩ :=
            List.length_eq_one_iff.mp (by simpa using lengthEq.symm)
          subst rightEq
          cases aligned with
          | cons head tail =>
              cases tail
              have headEq : _ = rightHead :=
                (List.cons.inj (List.perm_singleton.mp reordered)).1
              subst rightHead
              simpa [ReflectiveCanonical.collapseParallel] using head
      | cons leftSecond leftRest =>
          cases right with
          | nil => simp at lengthEq
          | cons rightHead rightTail =>
              cases rightTail with
              | nil => simp at lengthEq
              | cons rightSecond rightRest =>
                  simpa [ReflectiveCanonical.collapseParallel] using
                    (ParallelOrderAgnostic.parallel aligned reordered)

end ParallelOrderAgnosticPermutation

/-- Related patterns agree on being the parallel unit. -/
theorem unit_iff {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (related : ParallelOrderAgnostic declaration left right) :
    left = .apply declaration.parallelUnitConstructor [] ↔
      right = .apply declaration.parallelUnitConstructor [] := by
  constructor
  · intro leftUnit
    subst leftUnit
    cases related with
    | apply constructor arguments =>
        cases arguments
        rfl
  · intro rightUnit
    subst rightUnit
    cases related with
    | apply constructor arguments =>
        cases arguments
        rfl

/-- Related patterns agree on being a bare parallel collection, and their
contents relate pointwise up to permutation. -/
theorem bareParallel_cases {declaration : ReflectivePresentationDecl}
    {left right : Pattern}
    (related : ParallelOrderAgnostic declaration left right) :
    (∃ leftElements middleElements rightElements,
      left = .collection declaration.parallelCollection leftElements none ∧
      right = .collection declaration.parallelCollection rightElements none ∧
      ParallelOrderAgnosticList declaration leftElements middleElements ∧
      middleElements.Perm rightElements) ∨
    ((∀ elements, left ≠
        .collection declaration.parallelCollection elements none) ∧
      (∀ elements, right ≠
        .collection declaration.parallelCollection elements none)) := by
  cases related with
  | bvar index =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | fvar name =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | apply constructor arguments =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | lambda binder body =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | multiLambda arity binders body =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | subst body replacement =>
      refine Or.inr ⟨?_, ?_⟩ <;> intro elements h <;> cases h
  | @collection collectionType rest leftElements rightElements elements =>
      by_cases bare : collectionType = declaration.parallelCollection ∧
        rest = none
      · obtain ⟨typeEq, restEq⟩ := bare
        subst typeEq
        subst restEq
        exact Or.inl ⟨leftElements, rightElements, rightElements,
          rfl, rfl, elements, List.Perm.refl _⟩
      · refine Or.inr ⟨fun other h => bare ?_, fun other h => bare ?_⟩
        · cases h; exact ⟨rfl, rfl⟩
        · cases h; exact ⟨rfl, rfl⟩
  | @parallel leftElements middleElements rightElements pointwise
      permutation =>
      exact Or.inl ⟨leftElements, middleElements, rightElements, rfl, rfl,
        pointwise, permutation⟩

end ParallelOrderAgnostic

open ParallelOrderAgnostic in
/-- Quote/Drop finishing preserves order-agnostic equality: related argument
spines make the same absorption decision, because the fire shape — a
singleton drop-headed application with a singleton payload — is preserved
and reflected by the relation.  This is the keyed/plain quote-fire coherence
at one constructor layer. -/
theorem finishNormalizeReflectiveApply_parallelOrderAgnostic
    (declaration : ReflectivePresentationDecl) (constructor : String)
    {leftArguments rightArguments : List Pattern}
    (related : ParallelOrderAgnosticList declaration leftArguments
      rightArguments) :
    ParallelOrderAgnostic declaration
      (finishNormalizeReflectiveApply declaration constructor leftArguments)
      (finishNormalizeReflectiveApply declaration constructor
        rightArguments) := by
  by_cases quoteHead :
      (constructor == declaration.quoteConstructor) = true
  · cases related with
    | nil =>
        simp only [finishNormalizeReflectiveApply, quoteHead, if_true]
        exact .apply constructor .nil
    | cons headRelated tailRelated =>
        cases tailRelated with
        | cons secondRelated restRelated =>
            simp only [finishNormalizeReflectiveApply, quoteHead, if_true]
            exact .apply constructor
              (.cons headRelated (.cons secondRelated restRelated))
        | nil =>
            cases headRelated with
            | bvar index =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor (.cons (.bvar index) .nil)
            | fvar name =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor (.cons (.fvar name) .nil)
            | lambda binder body =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor (.cons (.lambda binder body) .nil)
            | multiLambda arity binders body =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor
                  (.cons (.multiLambda arity binders body) .nil)
            | subst body replacement =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor (.cons (.subst body replacement) .nil)
            | collection collectionType rest elements =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor
                  (.cons (.collection collectionType rest elements) .nil)
            | parallel pointwise permutation =>
                simp only [finishNormalizeReflectiveApply, quoteHead,
                  if_true]
                exact .apply constructor
                  (.cons (.parallel pointwise permutation) .nil)
            | @apply innerHead innerLeft innerRight innerRelated =>
                cases innerRelated with
                | nil =>
                    simp only [finishNormalizeReflectiveApply, quoteHead,
                      if_true]
                    exact .apply constructor
                      (.cons (.apply innerHead .nil) .nil)
                | cons payloadRelated payloadTail =>
                    cases payloadTail with
                    | cons secondPayload restPayload =>
                        simp only [finishNormalizeReflectiveApply, quoteHead,
                          if_true]
                        exact .apply constructor
                          (.cons (.apply innerHead
                            (.cons payloadRelated
                              (.cons secondPayload restPayload))) .nil)
                    | nil =>
                        by_cases dropHead :
                            (innerHead == declaration.dropConstructor) = true
                        · simp only [finishNormalizeReflectiveApply,
                            quoteHead, if_true, dropHead]
                          exact payloadRelated
                        · simp only [finishNormalizeReflectiveApply,
                            quoteHead, if_true, dropHead, if_false,
                            Bool.false_eq_true]
                          exact .apply constructor
                            (.cons (.apply innerHead
                              (.cons payloadRelated .nil)) .nil)
  · have quoteHeadFalse :
        (constructor == declaration.quoteConstructor) = false :=
      Bool.not_eq_true _ ▸ (by simpa using quoteHead)
    simp only [finishNormalizeReflectiveApply, quoteHeadFalse,
      Bool.false_eq_true, if_false]
    exact .apply constructor related

/-- Keyed and plain reflective canonicalization differ only by hereditary
bare-parallel order.  This is the whole-pipeline coherence theorem: quote
firing, unit deletion, nested-parallel splicing, and collapse shape agree;
only the final sorting policy may permute surviving parallel contents. -/
theorem canonicalizeByAt_parallelOrderAgnostic
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (pattern : Pattern) :
    ParallelOrderAgnostic declaration
      (canonicalizeByAt key declaration availableDepth pattern)
      (canonicalize declaration pattern) := by
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index => exact .bvar index
  | hfvar name => exact .fvar name
  | happly constructor arguments inductionHypothesis =>
      let childDepth :=
        if constructor == declaration.quoteConstructor then 0
        else availableDepth
      have argumentsRelated : ParallelOrderAgnosticList declaration
          (canonicalizeListByAt key declaration childDepth arguments)
          (canonicalizeList declaration arguments) := by
        rw [canonicalizeListByAt_eq_map, canonicalizeList_eq_map]
        exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
          (fun argument membership =>
            inductionHypothesis argument membership childDepth)
      simpa [canonicalizeByAt, canonicalize, childDepth] using
        finishNormalizeReflectiveApply_parallelOrderAgnostic declaration
          constructor argumentsRelated
  | hlambda binder body inductionHypothesis =>
      exact .lambda binder (inductionHypothesis (availableDepth + 1))
  | hmultiLambda arity binders body inductionHypothesis =>
      exact .multiLambda arity binders
        (inductionHypothesis (availableDepth + arity))
  | hsubst body replacement bodyInduction replacementInduction =>
      exact .subst (bodyInduction (availableDepth + 1))
        (replacementInduction availableDepth)
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsRelated : ParallelOrderAgnosticList declaration
          (canonicalizeListByAt key declaration availableDepth elements)
          (canonicalizeList declaration elements) := by
        rw [canonicalizeListByAt_eq_map, canonicalizeList_eq_map]
        exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
          (fun element membership =>
            inductionHypothesis element membership availableDepth)
      cases rest with
      | some restName =>
          exact .collection collectionType (some restName) elementsRelated
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection
          · subst collectionType
            let spliced :=
              ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.flatMapParallelSplice
                elementsRelated
            let filtered :=
              ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.filterNotUnit
                spliced
            have sorted :
                ParallelOrderAgnostic.ParallelOrderAgnosticPermutation
                  declaration
                  (normalizeParallelElementsBy (key availableDepth)
                    declaration
                    (canonicalizeListByAt key declaration availableDepth
                      elements))
                  (normalizeParallelElements declaration
                    (canonicalizeList declaration elements)) := by
              simpa [normalizeParallelElementsBy,
                normalizeParallelElements] using
                ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.sort
                  (key availableDepth) PatternCode.patternCode filtered
            simpa [canonicalizeByAt, canonicalize] using
              ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.collapse
                sorted
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr selected
            simpa [canonicalizeByAt, canonicalize, selectedFalse] using
              (ParallelOrderAgnostic.collection collectionType none
                elementsRelated)

/-- Re-canonicalizing a keyed representative erases its semantic-key order
choice, without requiring the quote and drop constructor names to be
distinct.  The older direct proof carries that language-side separation as a
premise; order-agnostic coherence shows it is unnecessary for this quotient
law itself. -/
theorem canonicalize_canonicalizeByAt_unconditional
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (pattern : Pattern) :
    canonicalize declaration
        (canonicalizeByAt key declaration availableDepth pattern) =
      canonicalize declaration pattern :=
  (ParallelOrderAgnostic.canonicalize_eq
      (canonicalizeByAt_parallelOrderAgnostic key declaration availableDepth
        pattern)).trans
    (canonicalize_idempotent declaration pattern)

/-- Ordinary canonical equality is preserved when both representatives are
compiled with arbitrary keyed orders and independently selected visible
depths.  This is the exact syntax-level input required by the subsequent
typed common-restoration construction. -/
theorem canonicalize_keyed_eq_of_canonicalize_eq
    {LeftKey RightKey : Type} [LinearOrder LeftKey] [LinearOrder RightKey]
    (leftKey : Nat → Pattern → LeftKey)
    (rightKey : Nat → Pattern → RightKey)
    (declaration : ReflectivePresentationDecl)
    {left right : Pattern} (leftDepth rightDepth : Nat)
    (equal : canonicalize declaration left = canonicalize declaration right) :
    canonicalize declaration
        (canonicalizeByAt leftKey declaration leftDepth left) =
      canonicalize declaration
        (canonicalizeByAt rightKey declaration rightDepth right) := by
  rw [canonicalize_canonicalizeByAt_unconditional,
    canonicalize_canonicalizeByAt_unconditional]
  exact equal

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
