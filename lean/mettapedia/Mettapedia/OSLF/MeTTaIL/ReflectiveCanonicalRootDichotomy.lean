import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalInversion

/-!
# Root dichotomy for reflective canonical equality

The reflective canonicalizer changes a root constructor in exactly two
situations: a quote-constructor application may absorb its drop-constructor
argument, and a bare parallel collection may splice, sort, and collapse its
contents.  Every other root survives canonicalization with its constructor,
head, binder data, and spine length intact.

Consequently, two patterns with equal canonicalizations either expose a
collapsing root on one side, or they share their root constructor with
childwise equal canonicalizations.  This theorem is deliberately only about
reflective syntax.  A client language must separately prove how its typing
and elaboration classify a collapsing root; no Cost-region role is assumed
here.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A root at which canonicalization may change the outer constructor: a
quote application (Quote/Drop absorption) or a bare parallel collection
(splice, sort, unit and singleton collapse). -/
def CollapsingRoot (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) : Prop :=
  (∃ arguments, pattern = .apply declaration.quoteConstructor arguments) ∨
    (∃ elements, pattern =
      .collection declaration.parallelCollection elements none)

/-- Structural root agreement delivered by canonical equality away from
collapsing roots: the same root constructor with childwise equal
canonicalizations.  Parallel collections never appear here without an open
rest, and quote applications never appear at all. -/
inductive CanonicalRootAligned (declaration : ReflectivePresentationDecl) :
    Pattern → Pattern → Prop where
  | bvar (index : Nat) :
      CanonicalRootAligned declaration (.bvar index) (.bvar index)
  | fvar (name : String) :
      CanonicalRootAligned declaration (.fvar name) (.fvar name)
  | apply {constructor : String}
      (ne : constructor ≠ declaration.quoteConstructor)
      {leftArguments rightArguments : List Pattern}
      (children : List.Forall₂
        (fun l r => canonicalize declaration l = canonicalize declaration r)
        leftArguments rightArguments) :
      CanonicalRootAligned declaration (.apply constructor leftArguments)
        (.apply constructor rightArguments)
  | lambda (binder : Option String) {leftBody rightBody : Pattern}
      (body : canonicalize declaration leftBody =
        canonicalize declaration rightBody) :
      CanonicalRootAligned declaration (.lambda binder leftBody)
        (.lambda binder rightBody)
  | multiLambda (arity : Nat) (binders : List String)
      {leftBody rightBody : Pattern}
      (body : canonicalize declaration leftBody =
        canonicalize declaration rightBody) :
      CanonicalRootAligned declaration
        (.multiLambda arity binders leftBody)
        (.multiLambda arity binders rightBody)
  | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
      (body : canonicalize declaration leftBody =
        canonicalize declaration rightBody)
      (replacement : canonicalize declaration leftReplacement =
        canonicalize declaration rightReplacement) :
      CanonicalRootAligned declaration
        (.subst leftBody leftReplacement)
        (.subst rightBody rightReplacement)
  | collection {collectionType : CollType}
      (ne : collectionType ≠ declaration.parallelCollection)
      {leftElements rightElements : List Pattern}
      (children : List.Forall₂
        (fun l r => canonicalize declaration l = canonicalize declaration r)
        leftElements rightElements) :
      CanonicalRootAligned declaration
        (.collection collectionType leftElements none)
        (.collection collectionType rightElements none)
  | collectionRest (collectionType : CollType) (rest : String)
      {leftElements rightElements : List Pattern}
      (children : List.Forall₂
        (fun l r => canonicalize declaration l = canonicalize declaration r)
        leftElements rightElements) :
      CanonicalRootAligned declaration
        (.collection collectionType leftElements (some rest))
        (.collection collectionType rightElements (some rest))

/-- Structural canonical-root alignment is symmetric.  Child evidence is
reversed pointwise; no canonicalizer injectivity beyond the data already
stored in the alignment is used. -/
theorem CanonicalRootAligned.symm
    {declaration : ReflectivePresentationDecl} {left right : Pattern}
    (aligned : CanonicalRootAligned declaration left right) :
    CanonicalRootAligned declaration right left := by
  have reverseChildren : ∀ {leftChildren rightChildren : List Pattern},
      List.Forall₂
          (fun leftChild rightChild =>
            canonicalize declaration leftChild =
              canonicalize declaration rightChild)
          leftChildren rightChildren →
        List.Forall₂
          (fun rightChild leftChild =>
            canonicalize declaration rightChild =
              canonicalize declaration leftChild)
          rightChildren leftChildren := by
    intro leftChildren rightChildren children
    induction children with
    | nil => exact .nil
    | cons head tail inductionHypothesis =>
        exact .cons head.symm inductionHypothesis
  cases aligned with
  | bvar index => exact .bvar index
  | fvar name => exact .fvar name
  | apply ne children => exact .apply ne (reverseChildren children)
  | lambda binder body => exact .lambda binder body.symm
  | multiLambda arity binders body =>
      exact .multiLambda arity binders body.symm
  | subst body replacement => exact .subst body.symm replacement.symm
  | collection ne children =>
      exact .collection ne (reverseChildren children)
  | collectionRest collectionType rest children =>
      exact .collectionRest collectionType rest (reverseChildren children)

private theorem canonicalize_bvar
    (declaration : ReflectivePresentationDecl) (index : Nat) :
    canonicalize declaration (.bvar index) = .bvar index := by
  simp [canonicalize]

private theorem canonicalize_fvar
    (declaration : ReflectivePresentationDecl) (name : String) :
    canonicalize declaration (.fvar name) = .fvar name := by
  simp [canonicalize]

private theorem canonicalize_lambda
    (declaration : ReflectivePresentationDecl) (binder : Option String)
    (body : Pattern) :
    canonicalize declaration (.lambda binder body) =
      .lambda binder (canonicalize declaration body) := by
  simp [canonicalize]

private theorem canonicalize_multiLambda
    (declaration : ReflectivePresentationDecl) (arity : Nat)
    (binders : List String) (body : Pattern) :
    canonicalize declaration (.multiLambda arity binders body) =
      .multiLambda arity binders (canonicalize declaration body) := by
  simp [canonicalize]

private theorem canonicalize_subst
    (declaration : ReflectivePresentationDecl) (body replacement : Pattern) :
    canonicalize declaration (.subst body replacement) =
      .subst (canonicalize declaration body)
        (canonicalize declaration replacement) := by
  simp [canonicalize]

/-- Root dichotomy: equal canonicalizations expose a collapsing root on one
side, or the two roots agree structurally with childwise equal
canonicalizations.  Each side is classified independently; no matching-root
assumption enters. -/
theorem canonicalize_eq_root_cases
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (equal : canonicalize declaration left = canonicalize declaration right) :
    CollapsingRoot declaration left ∨ CollapsingRoot declaration right ∨
      CanonicalRootAligned declaration left right := by
  by_cases leftCollapsing : CollapsingRoot declaration left
  · exact Or.inl leftCollapsing
  by_cases rightCollapsing : CollapsingRoot declaration right
  · exact Or.inr (Or.inl rightCollapsing)
  refine Or.inr (Or.inr ?_)
  have leftApplyNe : ∀ {constructor : String} {arguments : List Pattern},
      left = .apply constructor arguments →
      constructor ≠ declaration.quoteConstructor := by
    intro constructor arguments shape headEq
    exact leftCollapsing (Or.inl ⟨arguments, by rw [shape, headEq]⟩)
  have rightApplyNe : ∀ {constructor : String} {arguments : List Pattern},
      right = .apply constructor arguments →
      constructor ≠ declaration.quoteConstructor := by
    intro constructor arguments shape headEq
    exact rightCollapsing (Or.inl ⟨arguments, by rw [shape, headEq]⟩)
  have leftCollectionNe : ∀ {collectionType : CollType}
      {elements : List Pattern},
      left = .collection collectionType elements none →
      collectionType ≠ declaration.parallelCollection := by
    intro collectionType elements shape typeEq
    exact leftCollapsing (Or.inr ⟨elements, by rw [shape, typeEq]⟩)
  have rightCollectionNe : ∀ {collectionType : CollType}
      {elements : List Pattern},
      right = .collection collectionType elements none →
      collectionType ≠ declaration.parallelCollection := by
    intro collectionType elements shape typeEq
    exact rightCollapsing (Or.inr ⟨elements, by rw [shape, typeEq]⟩)
  have leftCanonical : ∀ {pattern : Pattern}, left = pattern →
      canonicalize declaration pattern = canonicalize declaration right :=
    fun shape => shape ▸ equal
  clear equal
  cases left with
  | bvar leftIndex =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_bvar, canonicalize_bvar] at this
          cases this
          exact .bvar _
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_bvar, canonicalize_fvar] at this
          cases this
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_bvar,
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          cases this
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_bvar, canonicalize_lambda] at this
          cases this
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_bvar, canonicalize_multiLambda] at this
          cases this
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_bvar, canonicalize_subst] at this
          cases this
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_bvar,
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_bvar, canonicalize_collection_rest] at this
              cases this
  | fvar leftName =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_fvar, canonicalize_bvar] at this
          cases this
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_fvar, canonicalize_fvar] at this
          cases this
          exact .fvar _
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_fvar,
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          cases this
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_fvar, canonicalize_lambda] at this
          cases this
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_fvar, canonicalize_multiLambda] at this
          cases this
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_fvar, canonicalize_subst] at this
          cases this
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_fvar,
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_fvar, canonicalize_collection_rest] at this
              cases this
  | apply leftConstructor leftArguments =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_bvar] at this
          cases this
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_fvar] at this
          cases this
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          obtain ⟨headEq, argumentsEq⟩ := Pattern.apply.inj this
          cases headEq
          exact .apply (leftApplyNe rfl)
            (forall₂_of_map_eq (canonicalize declaration) argumentsEq)
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_lambda] at this
          cases this
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_multiLambda] at this
          cases this
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_apply_of_ne_quote declaration (leftApplyNe rfl),
            canonicalize_subst] at this
          cases this
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_apply_of_ne_quote declaration
                  (leftApplyNe rfl),
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_apply_of_ne_quote declaration
                  (leftApplyNe rfl),
                canonicalize_collection_rest] at this
              cases this
  | lambda leftBinder leftBody =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_lambda, canonicalize_bvar] at this
          cases this
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_lambda, canonicalize_fvar] at this
          cases this
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_lambda,
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          cases this
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_lambda, canonicalize_lambda] at this
          obtain ⟨binderEq, bodyEq⟩ := Pattern.lambda.inj this
          cases binderEq
          exact .lambda _ bodyEq
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_lambda, canonicalize_multiLambda] at this
          cases this
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_lambda, canonicalize_subst] at this
          cases this
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_lambda,
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_lambda, canonicalize_collection_rest] at this
              cases this
  | multiLambda leftArity leftBinders leftBody =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda, canonicalize_bvar] at this
          cases this
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda, canonicalize_fvar] at this
          cases this
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda,
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          cases this
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda, canonicalize_lambda] at this
          cases this
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda, canonicalize_multiLambda] at this
          obtain ⟨arityEq, bindersEq, bodyEq⟩ :=
            Pattern.multiLambda.inj this
          cases arityEq
          cases bindersEq
          exact .multiLambda _ _ bodyEq
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_multiLambda, canonicalize_subst] at this
          cases this
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_multiLambda,
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_multiLambda,
                canonicalize_collection_rest] at this
              cases this
  | subst leftBody leftReplacement =>
      cases right with
      | bvar rightIndex =>
          have := leftCanonical rfl
          rw [canonicalize_subst, canonicalize_bvar] at this
          cases this
      | fvar rightName =>
          have := leftCanonical rfl
          rw [canonicalize_subst, canonicalize_fvar] at this
          cases this
      | apply rightConstructor rightArguments =>
          have := leftCanonical rfl
          rw [canonicalize_subst,
            canonicalize_apply_of_ne_quote declaration
              (rightApplyNe rfl)] at this
          cases this
      | lambda rightBinder rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_subst, canonicalize_lambda] at this
          cases this
      | multiLambda rightArity rightBinders rightBody =>
          have := leftCanonical rfl
          rw [canonicalize_subst, canonicalize_multiLambda] at this
          cases this
      | subst rightBody rightReplacement =>
          have := leftCanonical rfl
          rw [canonicalize_subst, canonicalize_subst] at this
          obtain ⟨bodyEq, replacementEq⟩ := Pattern.subst.inj this
          exact .subst bodyEq replacementEq
      | collection rightType rightElements rightRest =>
          cases rightRest with
          | none =>
              have := leftCanonical rfl
              rw [canonicalize_subst,
                canonicalize_collection_of_ne_parallel declaration
                  (rightCollectionNe rfl)] at this
              cases this
          | some rest =>
              have := leftCanonical rfl
              rw [canonicalize_subst, canonicalize_collection_rest] at this
              cases this
  | collection leftType leftElements leftRest =>
      cases leftRest with
      | none =>
          cases right with
          | bvar rightIndex =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_bvar] at this
              cases this
          | fvar rightName =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_fvar] at this
              cases this
          | apply rightConstructor rightArguments =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_apply_of_ne_quote declaration
                  (rightApplyNe rfl)] at this
              cases this
          | lambda rightBinder rightBody =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_lambda] at this
              cases this
          | multiLambda rightArity rightBinders rightBody =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_multiLambda] at this
              cases this
          | subst rightBody rightReplacement =>
              have := leftCanonical rfl
              rw [canonicalize_collection_of_ne_parallel declaration
                  (leftCollectionNe rfl),
                canonicalize_subst] at this
              cases this
          | collection rightType rightElements rightRest =>
              cases rightRest with
              | none =>
                  have := leftCanonical rfl
                  rw [canonicalize_collection_of_ne_parallel declaration
                      (leftCollectionNe rfl),
                    canonicalize_collection_of_ne_parallel declaration
                      (rightCollectionNe rfl)] at this
                  obtain ⟨typeEq, elementsEq, -⟩ :=
                    Pattern.collection.inj this
                  cases typeEq
                  exact .collection (leftCollectionNe rfl)
                    (forall₂_of_map_eq (canonicalize declaration) elementsEq)
              | some rest =>
                  have := leftCanonical rfl
                  rw [canonicalize_collection_of_ne_parallel declaration
                      (leftCollectionNe rfl),
                    canonicalize_collection_rest] at this
                  obtain ⟨-, -, restEq⟩ := Pattern.collection.inj this
                  cases restEq
      | some leftRestName =>
          cases right with
          | bvar rightIndex =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest, canonicalize_bvar] at this
              cases this
          | fvar rightName =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest, canonicalize_fvar] at this
              cases this
          | apply rightConstructor rightArguments =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest,
                canonicalize_apply_of_ne_quote declaration
                  (rightApplyNe rfl)] at this
              cases this
          | lambda rightBinder rightBody =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest, canonicalize_lambda] at this
              cases this
          | multiLambda rightArity rightBinders rightBody =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest,
                canonicalize_multiLambda] at this
              cases this
          | subst rightBody rightReplacement =>
              have := leftCanonical rfl
              rw [canonicalize_collection_rest, canonicalize_subst] at this
              cases this
          | collection rightType rightElements rightRest =>
              cases rightRest with
              | none =>
                  have := leftCanonical rfl
                  rw [canonicalize_collection_rest,
                    canonicalize_collection_of_ne_parallel declaration
                      (rightCollectionNe rfl)] at this
                  obtain ⟨-, -, restEq⟩ := Pattern.collection.inj this
                  cases restEq
              | some rightRestName =>
                  have := leftCanonical rfl
                  rw [canonicalize_collection_rest,
                    canonicalize_collection_rest] at this
                  obtain ⟨typeEq, elementsEq, restEq⟩ :=
                    Pattern.collection.inj this
                  cases typeEq
                  cases restEq
                  exact .collectionRest _ _
                    (forall₂_of_map_eq (canonicalize declaration) elementsEq)

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
