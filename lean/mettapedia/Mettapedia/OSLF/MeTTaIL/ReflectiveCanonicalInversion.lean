import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Per-case inversion for the reflective canonicalizer

Equality of canonical representatives does not invert through one global
constructor-injectivity principle: the quote application may collapse a
Quote/Drop pair to its payload, and the selected parallel collection is
flattened, unit-filtered, and sorted.  This module records the honest
inversion boundary case by case:

- rigid applications (any constructor other than the declared quote) and
  the ordinary structural constructors invert pointwise;
- the Quote/Drop pair is absorbed, so application heads are *not* injective
  under canonicalization — recorded as a compiled corollary;
- equal canonical parallel collections invert to equality of their
  normalized (spliced, unit-free, sorted) canonical contents, hence to a
  permutation of their flattened canonical contents.  This permutation is
  exactly the premise consumed by the common-restoration terminals; no raw
  keyed-equality claim is made or needed here.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Mapping equal images pointwise: two lists with equal images under one
function are pointwise image-equal. -/
theorem forall₂_of_map_eq {α β : Type} (function : α → β) :
    ∀ {left right : List α},
      left.map function = right.map function →
        List.Forall₂ (fun l r => function l = function r) left right
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, images => by simp at images
  | _ :: _, [], images => by simp at images
  | l :: ls, r :: rs, images => by
      simp only [List.map_cons, List.cons.injEq] at images
      exact List.Forall₂.cons images.1 (forall₂_of_map_eq function images.2)

/-! ## Computation equations -/

@[simp]
theorem finishNormalizeReflectiveApply_of_ne_quote
    (declaration : ReflectivePresentationDecl) {constructor : String}
    (ne : constructor ≠ declaration.quoteConstructor)
    (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration constructor arguments =
      .apply constructor arguments := by
  simp [finishNormalizeReflectiveApply, ne]

@[simp]
theorem finishNormalizeReflectiveApply_quote_drop
    (declaration : ReflectivePresentationDecl) (inner : Pattern) :
    finishNormalizeReflectiveApply declaration declaration.quoteConstructor
        [.apply declaration.dropConstructor [inner]] =
      inner := by
  simp [finishNormalizeReflectiveApply]

theorem canonicalize_apply_eq_finish
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List Pattern) :
    canonicalize declaration (.apply constructor arguments) =
      finishNormalizeReflectiveApply declaration constructor
        (arguments.map (canonicalize declaration)) := by
  simp [canonicalize, canonicalizeList_eq_map]

theorem canonicalize_apply_of_ne_quote
    (declaration : ReflectivePresentationDecl) {constructor : String}
    (ne : constructor ≠ declaration.quoteConstructor)
    (arguments : List Pattern) :
    canonicalize declaration (.apply constructor arguments) =
      .apply constructor (arguments.map (canonicalize declaration)) := by
  rw [canonicalize_apply_eq_finish,
    finishNormalizeReflectiveApply_of_ne_quote declaration ne]

theorem canonicalize_parallel
    (declaration : ReflectivePresentationDecl) (elements : List Pattern) :
    canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      collapseParallel declaration
        (normalizeParallelElements declaration
          (elements.map (canonicalize declaration))) := by
  simp [canonicalize, canonicalizeList_eq_map]

theorem canonicalize_collection_of_ne_parallel
    (declaration : ReflectivePresentationDecl) {collectionType : CollType}
    (ne : collectionType ≠ declaration.parallelCollection)
    (elements : List Pattern) :
    canonicalize declaration (.collection collectionType elements none) =
      .collection collectionType
        (elements.map (canonicalize declaration)) none := by
  simp [canonicalize, canonicalizeList_eq_map, ne]

theorem canonicalize_collection_rest
    (declaration : ReflectivePresentationDecl) (collectionType : CollType)
    (elements : List Pattern) (rest : String) :
    canonicalize declaration
        (.collection collectionType elements (some rest)) =
      .collection collectionType
        (elements.map (canonicalize declaration)) (some rest) := by
  simp [canonicalize, canonicalizeList_eq_map]

/-! ## Quote/Drop absorption and head non-injectivity -/

/-- The declared Quote/Drop pair is absorbed at every payload, provided the
two reflective constructors are distinct.  This is the generic plain-form
absorption underlying every generated Quote/Drop equation. -/
theorem canonicalize_quote_drop
    (declaration : ReflectivePresentationDecl)
    (ne : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (inner : Pattern) :
    canonicalize declaration
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [inner]]) =
      canonicalize declaration inner := by
  rw [canonicalize_apply_eq_finish]
  simp only [List.map_cons, List.map_nil]
  rw [canonicalize_apply_of_ne_quote declaration ne]
  simp

/-- Canonicalization is not injective on outer heads: a Quote/Drop shell and
its bare payload share one canonical representative while their outer
constructors differ.  Any inversion principle must therefore classify the
collapse cases separately. -/
theorem canonicalize_not_head_injective
    (declaration : ReflectivePresentationDecl)
    (ne : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    ∃ left right : Pattern,
      canonicalize declaration left = canonicalize declaration right ∧
        (∃ constructor arguments, left = .apply constructor arguments) ∧
        (∃ name, right = .fvar name) := by
  refine ⟨.apply declaration.quoteConstructor
      [.apply declaration.dropConstructor [.fvar "n"]], .fvar "n",
    ?_, ⟨_, _, rfl⟩, ⟨_, rfl⟩⟩
  exact canonicalize_quote_drop declaration ne (.fvar "n")

/-! ## Pointwise inversion at rigid and structural heads -/

/-- Rigid applications (constructor differs from the declared quote) invert
pointwise: equal canonical representatives force pairwise canonical
equality of the argument lists. -/
theorem canonicalize_apply_rigid_inj
    (declaration : ReflectivePresentationDecl) {constructor : String}
    (ne : constructor ≠ declaration.quoteConstructor)
    {leftArguments rightArguments : List Pattern}
    (equal : canonicalize declaration (.apply constructor leftArguments) =
      canonicalize declaration (.apply constructor rightArguments)) :
    List.Forall₂
      (fun l r => canonicalize declaration l = canonicalize declaration r)
      leftArguments rightArguments := by
  rw [canonicalize_apply_of_ne_quote declaration ne,
    canonicalize_apply_of_ne_quote declaration ne] at equal
  exact forall₂_of_map_eq (canonicalize declaration)
    (Pattern.apply.inj equal).2

theorem canonicalize_lambda_inj
    (declaration : ReflectivePresentationDecl)
    {leftBinder rightBinder : Option String} {leftBody rightBody : Pattern}
    (equal : canonicalize declaration (.lambda leftBinder leftBody) =
      canonicalize declaration (.lambda rightBinder rightBody)) :
    leftBinder = rightBinder ∧
      canonicalize declaration leftBody =
        canonicalize declaration rightBody := by
  simp only [canonicalize] at equal
  exact ⟨(Pattern.lambda.inj equal).1, (Pattern.lambda.inj equal).2⟩

theorem canonicalize_multiLambda_inj
    (declaration : ReflectivePresentationDecl)
    {leftArity rightArity : Nat} {leftBinders rightBinders : List String}
    {leftBody rightBody : Pattern}
    (equal : canonicalize declaration
        (.multiLambda leftArity leftBinders leftBody) =
      canonicalize declaration
        (.multiLambda rightArity rightBinders rightBody)) :
    leftArity = rightArity ∧ leftBinders = rightBinders ∧
      canonicalize declaration leftBody =
        canonicalize declaration rightBody := by
  simp only [canonicalize] at equal
  exact ⟨(Pattern.multiLambda.inj equal).1,
    (Pattern.multiLambda.inj equal).2.1,
    (Pattern.multiLambda.inj equal).2.2⟩

theorem canonicalize_subst_inj
    (declaration : ReflectivePresentationDecl)
    {leftBody rightBody leftReplacement rightReplacement : Pattern}
    (equal : canonicalize declaration (.subst leftBody leftReplacement) =
      canonicalize declaration (.subst rightBody rightReplacement)) :
    canonicalize declaration leftBody = canonicalize declaration rightBody ∧
      canonicalize declaration leftReplacement =
        canonicalize declaration rightReplacement := by
  simp only [canonicalize] at equal
  exact ⟨(Pattern.subst.inj equal).1, (Pattern.subst.inj equal).2⟩

theorem canonicalize_collection_inj_of_ne_parallel
    (declaration : ReflectivePresentationDecl) {collectionType : CollType}
    (ne : collectionType ≠ declaration.parallelCollection)
    {leftElements rightElements : List Pattern}
    (equal : canonicalize declaration
        (.collection collectionType leftElements none) =
      canonicalize declaration
        (.collection collectionType rightElements none)) :
    List.Forall₂
      (fun l r => canonicalize declaration l = canonicalize declaration r)
      leftElements rightElements := by
  rw [canonicalize_collection_of_ne_parallel declaration ne,
    canonicalize_collection_of_ne_parallel declaration ne] at equal
  exact forall₂_of_map_eq (canonicalize declaration)
    (Pattern.collection.inj equal).2.1

theorem canonicalize_collection_rest_inj
    (declaration : ReflectivePresentationDecl) {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : String}
    (equal : canonicalize declaration
        (.collection collectionType leftElements (some rest)) =
      canonicalize declaration
        (.collection collectionType rightElements (some rest))) :
    List.Forall₂
      (fun l r => canonicalize declaration l = canonicalize declaration r)
      leftElements rightElements := by
  rw [canonicalize_collection_rest, canonicalize_collection_rest] at equal
  exact forall₂_of_map_eq (canonicalize declaration)
    (Pattern.collection.inj equal).2.1

/-! ## Parallel inversion through the normalized contents -/

/-- Rebuilding is injective on normalized parallel element lists: unit-free,
nested-free lists that rebuild to the same pattern are equal.  The empty,
singleton, and proper-collection images are separated exactly by the
unit-freeness and nested-freeness of normalized contents. -/
theorem collapseParallel_inj_of_normalized
    (declaration : ReflectivePresentationDecl)
    {left right : List Pattern}
    (leftNoUnit : ∀ member ∈ left,
      member ≠ .apply declaration.parallelUnitConstructor [])
    (rightNoUnit : ∀ member ∈ right,
      member ≠ .apply declaration.parallelUnitConstructor [])
    (leftNoNested : ∀ member ∈ left, ∀ nested,
      member ≠ .collection declaration.parallelCollection nested none)
    (rightNoNested : ∀ member ∈ right, ∀ nested,
      member ≠ .collection declaration.parallelCollection nested none)
    (equal : collapseParallel declaration left =
      collapseParallel declaration right) :
    left = right := by
  match left, right with
  | [], [] => rfl
  | [], [rightHead] =>
      simp only [collapseParallel] at equal
      exact absurd equal.symm (rightNoUnit rightHead (by simp))
  | [leftHead], [] =>
      simp only [collapseParallel] at equal
      exact absurd equal (leftNoUnit leftHead (by simp))
  | [], rightFirst :: rightSecond :: rightRest =>
      rw [collapseParallel_eq_collection_of_length_ge_two declaration
        (patterns := rightFirst :: rightSecond :: rightRest)
        (by simp)] at equal
      simp only [collapseParallel] at equal
      exact Pattern.noConfusion equal
  | leftFirst :: leftSecond :: leftRest, [] =>
      rw [collapseParallel_eq_collection_of_length_ge_two declaration
        (patterns := leftFirst :: leftSecond :: leftRest)
        (by simp)] at equal
      simp only [collapseParallel] at equal
      exact Pattern.noConfusion equal
  | [leftHead], [rightHead] =>
      simp only [collapseParallel] at equal
      rw [equal]
  | [leftHead], rightFirst :: rightSecond :: rightRest =>
      rw [collapseParallel_eq_collection_of_length_ge_two declaration
        (patterns := rightFirst :: rightSecond :: rightRest)
        (by simp)] at equal
      simp only [collapseParallel] at equal
      exact absurd equal
        (leftNoNested leftHead (by simp)
          (rightFirst :: rightSecond :: rightRest))
  | leftFirst :: leftSecond :: leftRest, [rightHead] =>
      rw [collapseParallel_eq_collection_of_length_ge_two declaration
        (patterns := leftFirst :: leftSecond :: leftRest)
        (by simp)] at equal
      simp only [collapseParallel] at equal
      exact absurd equal.symm
        (rightNoNested rightHead (by simp)
          (leftFirst :: leftSecond :: leftRest))
  | leftFirst :: leftSecond :: leftRest,
      rightFirst :: rightSecond :: rightRest =>
      rw [collapseParallel_eq_collection_of_length_ge_two declaration
          (patterns := leftFirst :: leftSecond :: leftRest) (by simp),
        collapseParallel_eq_collection_of_length_ge_two declaration
          (patterns := rightFirst :: rightSecond :: rightRest)
          (by simp)] at equal
      exact (Pattern.collection.inj equal).2.1

/-- Equal canonical parallel collections have equal normalized canonical
contents.  This is the exact inversion available at the parallel head; no
claim is made below the sorted unit-free presentation. -/
theorem canonicalize_parallel_inj
    (declaration : ReflectivePresentationDecl)
    {leftElements rightElements : List Pattern}
    (equal : canonicalize declaration
        (.collection declaration.parallelCollection leftElements none) =
      canonicalize declaration
        (.collection declaration.parallelCollection rightElements none)) :
    normalizeParallelElements declaration
        (leftElements.map (canonicalize declaration)) =
      normalizeParallelElements declaration
        (rightElements.map (canonicalize declaration)) := by
  rw [canonicalize_parallel, canonicalize_parallel] at equal
  have leftCanonical : IsCanonicalList declaration
      (leftElements.map (canonicalize declaration)) := by
    apply isCanonicalList_of_forall
    intro member membership
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp membership
    exact canonicalize_isCanonical declaration source
  have rightCanonical : IsCanonicalList declaration
      (rightElements.map (canonicalize declaration)) := by
    apply isCanonicalList_of_forall
    intro member membership
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp membership
    exact canonicalize_isCanonical declaration source
  exact collapseParallel_inj_of_normalized declaration
    (fun member membership => normalizeParallelElements_no_unit membership)
    (fun member membership => normalizeParallelElements_no_unit membership)
    (fun member membership =>
      normalizeParallelElements_no_nested leftCanonical membership)
    (fun member membership =>
      normalizeParallelElements_no_nested rightCanonical membership)
    equal

/-- Equal canonical parallel collections have permuted flattened canonical
contents.  This permutation is the premise consumed by the
common-restoration parallel terminals; raw keyed equality is deliberately
not derived here. -/
theorem canonicalize_parallel_inj_contents_perm
    (declaration : ReflectivePresentationDecl)
    {leftElements rightElements : List Pattern}
    (equal : canonicalize declaration
        (.collection declaration.parallelCollection leftElements none) =
      canonicalize declaration
        (.collection declaration.parallelCollection rightElements none)) :
    List.Perm
      (parallelContents declaration
        (leftElements.map (canonicalize declaration)))
      (parallelContents declaration
        (rightElements.map (canonicalize declaration))) := by
  have normalized := canonicalize_parallel_inj declaration equal
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents] at normalized
  have leftSorted := (sortPatterns_perm (parallelContents declaration
    (leftElements.map (canonicalize declaration)))).symm
  have rightSorted := sortPatterns_perm (parallelContents declaration
    (rightElements.map (canonicalize declaration)))
  rw [normalized] at leftSorted
  exact leftSorted.trans rightSorted

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
