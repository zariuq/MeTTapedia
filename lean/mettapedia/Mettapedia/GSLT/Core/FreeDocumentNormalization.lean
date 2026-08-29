import Mettapedia.GSLT.Core.FreeDocumentComposition

set_option linter.dupNamespace false

/-!
# Normalizing nested free-document products

The general product of two compositional GSLTs treats each complete component
term as one block.  When both components are already free finite documents,
that creates a document of tagged documents.  The flat product instead tags
the original generators and takes the free-document construction once.

This module relates those constructions without identifying them.  `flatten`
forgets block boundaries, preserves equations and one-step reduction, and has
the canonical `singletonize` section.  It is deliberately not injective:
different blockings of the same generator sequence normalize to the same flat
term.  The elaboration theorem proves that this is exactly the information the
generic product does not observe.
-/

namespace Mettapedia.GSLT.GSLT

universe u v p q

namespace FreeDocumentProduct

/-! ## Syntax normalization -/

/-- Normalize one tagged component document to tagged generators. -/
def flattenBlock {Left : Type u} {Right : Type v} :
    List Left ⊕ List Right → List (Left ⊕ Right)
  | .inl left => left.map Sum.inl
  | .inr right => right.map Sum.inr

/-- Normalize a document of tagged component documents to one flat tagged
generator document. -/
def flatten {Left : Type u} {Right : Type v} :
    List (List Left ⊕ List Right) → List (Left ⊕ Right) :=
  List.flatMap flattenBlock

/-- Regard each tagged generator as a singleton component document. -/
def singletonize {Left : Type u} {Right : Type v} :
    List (Left ⊕ Right) → List (List Left ⊕ List Right) :=
  List.map fun term =>
    match term with
    | .inl left => .inl [left]
    | .inr right => .inr [right]

@[simp] theorem flatten_nil {Left : Type u} {Right : Type v} :
    flatten ([] : List (List Left ⊕ List Right)) = [] :=
  rfl

@[simp] theorem flatten_cons {Left : Type u} {Right : Type v}
    (head : List Left ⊕ List Right)
    (tail : List (List Left ⊕ List Right)) :
    flatten (head :: tail) = flattenBlock head ++ flatten tail :=
  rfl

@[simp] theorem flatten_append {Left : Type u} {Right : Type v}
    (first second : List (List Left ⊕ List Right)) :
    flatten (first ++ second) = flatten first ++ flatten second := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

@[simp] theorem flatten_singletonize {Left : Type u} {Right : Type v}
    (source : List (Left ⊕ Right)) :
    flatten (singletonize source) = source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head <;>
        change _ :: flatten (singletonize tail) = _ :: tail <;>
        rw [inductionHypothesis]

/-! ## Operational preservation -/

private theorem mapLeftEquiv {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List left.Term}
    (equivalent : DocumentEquiv left source target) :
    DocumentEquiv (disjointSum left right)
      (source.map Sum.inl) (target.map Sum.inl) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (.left head) inductionHypothesis

private theorem mapRightEquiv {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List right.Term}
    (equivalent : DocumentEquiv right source target) :
    DocumentEquiv (disjointSum left right)
      (source.map Sum.inr) (target.map Sum.inr) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (.right head) inductionHypothesis

private theorem mapLeftRawStep {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List left.Term}
    (step : RawDocumentStep left source target) :
    RawDocumentStep (disjointSum left right)
      (source.map Sum.inl) (target.map Sum.inl) := by
  induction step with
  | head rewrite => exact .head (.left rewrite)
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

private theorem mapRightRawStep {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List right.Term}
    (step : RawDocumentStep right source target) :
    RawDocumentStep (disjointSum left right)
      (source.map Sum.inr) (target.map Sum.inr) := by
  induction step with
  | head rewrite => exact .head (.right rewrite)
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

private theorem mapLeftStep {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List left.Term}
    (step : DocumentStep left source target) :
    DocumentStep (disjointSum left right)
      (source.map Sum.inl) (target.map Sum.inl) := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  exact ⟨middleSource.map Sum.inl, middleTarget.map Sum.inl,
    mapLeftEquiv sourceMiddle, mapLeftRawStep rewrite,
    mapLeftEquiv middleTargetTarget⟩

private theorem mapRightStep {left : GSLT.{u}} {right : GSLT.{v}}
    {source target : List right.Term}
    (step : DocumentStep right source target) :
    DocumentStep (disjointSum left right)
      (source.map Sum.inr) (target.map Sum.inr) := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  exact ⟨middleSource.map Sum.inr, middleTarget.map Sum.inr,
    mapRightEquiv sourceMiddle, mapRightRawStep rewrite,
    mapRightEquiv middleTargetTarget⟩

private theorem flattenBlock_equiv {left : GSLT.{u}} {right : GSLT.{v}}
    {source target :
      (freeDocument left).Term ⊕ (freeDocument right).Term}
    (equivalent :
      (disjointSum (freeDocument left) (freeDocument right)).Equiv
        source target) :
    DocumentEquiv (disjointSum left right)
      (flattenBlock source) (flattenBlock target) := by
  cases equivalent with
  | left equivalent => exact mapLeftEquiv equivalent
  | right equivalent => exact mapRightEquiv equivalent

private theorem flattenBlock_step {left : GSLT.{u}} {right : GSLT.{v}}
    {source target :
      (freeDocument left).Term ⊕ (freeDocument right).Term}
    (step : (disjointSum (freeDocument left) (freeDocument right)).Step
      source target) :
    DocumentStep (disjointSum left right)
      (flattenBlock source) (flattenBlock target) := by
  cases step with
  | left step => exact mapLeftStep step
  | right step => exact mapRightStep step

/-- Flattening preserves every authored equation of the nested product. -/
theorem flatten_equiv {left : GSLT.{u}} {right : GSLT.{v}}
    {source target :
      (freeDocument
        (disjointSum (freeDocument left) (freeDocument right))).Term}
    (equivalent :
      (freeDocument
        (disjointSum (freeDocument left) (freeDocument right))).Equiv
          source target) :
    (freeDocument (disjointSum left right)).Equiv
      (flatten source) (flatten target) := by
  induction equivalent with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact (flattenBlock_equiv head).append inductionHypothesis

private theorem flatten_rawStep {left : GSLT.{u}} {right : GSLT.{v}}
    {source target :
      (freeDocument
        (disjointSum (freeDocument left) (freeDocument right))).Term}
    (step : RawDocumentStep
      (disjointSum (freeDocument left) (freeDocument right)) source target) :
    DocumentStep (disjointSum left right)
      (flatten source) (flatten target) := by
  induction step with
  | head rewrite =>
      exact (flattenBlock_step rewrite).append_right (flatten _)
  | tail step inductionHypothesis =>
      rename_i block innerSource innerTarget
      exact inductionHypothesis.append_left (flattenBlock block)

/-- Flattening preserves every one-step reduction.  An inner component step
remains one equation-closed step of the flat free document. -/
theorem flatten_step {left : GSLT.{u}} {right : GSLT.{v}}
    {source target :
      (freeDocument
        (disjointSum (freeDocument left) (freeDocument right))).Term}
    (step :
      (freeDocument
        (disjointSum (freeDocument left) (freeDocument right))).Step
          source target) :
    (freeDocument (disjointSum left right)).Step
      (flatten source) (flatten target) := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  rcases flatten_rawStep rewrite with
    ⟨rewriteSource, rewriteTarget, middleRewriteSource,
      mappedRewrite, rewriteTargetMiddle⟩
  exact ⟨rewriteSource, rewriteTarget,
    (flatten_equiv sourceMiddle).trans middleRewriteSource,
    mappedRewrite,
    rewriteTargetMiddle.trans (flatten_equiv middleTargetTarget)⟩

/-! ## Elaboration factorization -/

/-- The generic nested product and the flat generator product have identical
payload semantics after normalization. -/
theorem elaborate_genericProduct_eq_flatProduct
    {Left : Type p} {Right : Type q}
    (left : FreeDocumentElaboration Left)
    (right : FreeDocumentElaboration Right) :
    ∀ source : List
      (List left.generators.Term ⊕ List right.generators.Term),
      ((left.toCompositionalElaboration.product
          right.toCompositionalElaboration).elaboration.elaborate source) =
        (left.product right).elaboration.elaborate (flatten source) := by
  intro source
  induction source with
  | nil =>
      calc
        (left.toCompositionalElaboration.product
            right.toCompositionalElaboration).elaboration.elaborate [] =
            some (left.emptyPayload, right.emptyPayload) :=
          (left.toCompositionalElaboration.product
            right.toCompositionalElaboration).elaborate_empty
        _ = (left.product right).elaboration.elaborate (flatten []) := by
          symm
          exact (left.product right).elaborate_empty
  | cons head tail inductionHypothesis =>
      have headAgreement :
          ((left.toCompositionalElaboration.product
              right.toCompositionalElaboration).elaboration.elaborate
                [head]) =
            (left.product right).elaboration.elaborate
              (flattenBlock head) := by
        cases head with
        | inl leftSource =>
            exact (left.toCompositionalElaboration.product_elaborates_left_only
              right.toCompositionalElaboration leftSource).trans
                (left.product_elaborates_left_only right leftSource).symm
        | inr rightSource =>
            exact (left.toCompositionalElaboration.product_elaborates_right_only
              right.toCompositionalElaboration rightSource).trans
                (left.product_elaborates_right_only right rightSource).symm
      calc
        (left.toCompositionalElaboration.product
            right.toCompositionalElaboration).elaboration.elaborate
              (head :: tail) =
            (left.toCompositionalElaboration.product
              right.toCompositionalElaboration).elaboration.elaborate
                ((left.toCompositionalElaboration.product
                  right.toCompositionalElaboration).authoring.append
                    [head] tail) := by
              rfl
        _ =
            ((left.toCompositionalElaboration.product
                right.toCompositionalElaboration).elaboration.elaborate
                  [head]).bind fun headValue =>
              ((left.toCompositionalElaboration.product
                right.toCompositionalElaboration).elaboration.elaborate
                    tail).bind fun tailValue =>
                (left.toCompositionalElaboration.product
                  right.toCompositionalElaboration).merge
                  headValue tailValue := by
            exact (left.toCompositionalElaboration.product
              right.toCompositionalElaboration).elaborate_append
                [head] tail
        _ = ((left.product right).elaboration.elaborate
              (flattenBlock head)).bind fun headValue =>
              ((left.product right).elaboration.elaborate
                (flatten tail)).bind fun tailValue =>
                (left.toCompositionalElaboration.product
                  right.toCompositionalElaboration).merge
                  headValue tailValue := by
            rw [headAgreement, inductionHypothesis]
        _ = ((left.product right).elaboration.elaborate
              (flattenBlock head)).bind fun headValue =>
              ((left.product right).elaboration.elaborate
                (flatten tail)).bind fun tailValue =>
                (left.product right).merge headValue tailValue := by
            rfl
        _ = (left.product right).elaboration.elaborate
              (flatten (head :: tail)) := by
            symm
            exact (left.product right).elaborate_append
              (flattenBlock head) (flatten tail)

/-! ## Executable controls -/

namespace Canary

/-- Positive: normalization retains tagged generator order. -/
example :
    flatten
      ([Sum.inl ([2, 5] : List Nat), Sum.inr ([true] : List Bool),
        Sum.inl ([7] : List Nat)] :
        List (List Nat ⊕ List Bool)) =
      [Sum.inl 2, Sum.inl 5, Sum.inr true, Sum.inl 7] :=
  rfl

/-- Negative: block boundaries are not observable in the flat normal form. -/
theorem flatten_not_injective :
    ¬ Function.Injective
      (flatten : List (List Nat ⊕ List Bool) → List (Nat ⊕ Bool)) := by
  intro injective
  have impossible := injective
    (show
      flatten ([Sum.inl ([1, 2] : List Nat)] :
        List (List Nat ⊕ List Bool)) =
      flatten ([Sum.inl ([1] : List Nat), Sum.inl ([2] : List Nat)] :
        List (List Nat ⊕ List Bool)) from rfl)
  cases impossible

end Canary

end FreeDocumentProduct

end Mettapedia.GSLT.GSLT
