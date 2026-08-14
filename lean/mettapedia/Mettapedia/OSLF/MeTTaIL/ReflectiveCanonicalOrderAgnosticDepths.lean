import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnostic

/-!
# Two-depth keyed canonicalization is order-agnostic

The two-depth keyed canonicalizer used by hereditary normalization has the
same structural decisions as ordinary reflective canonicalization.  The two
outputs may differ only by the order of surviving bare-parallel elements.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Two-depth keyed and ordinary reflective canonicalization differ only by
hereditary bare-parallel order. -/
theorem canonicalizeByDepths_parallelOrderAgnostic
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (pattern : Pattern) :
    ParallelOrderAgnostic declaration
      (canonicalizeByDepths key declaration availableDepth scopeDepth pattern)
      (canonicalize declaration pattern) := by
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth with
  | hbvar index => exact .bvar index
  | hfvar name => exact .fvar name
  | happly constructor arguments inductionHypothesis =>
      let childAvailableDepth :=
        if constructor == declaration.quoteConstructor then 0
        else availableDepth
      have argumentsRelated : ParallelOrderAgnosticList declaration
          (canonicalizeListByDepths key declaration childAvailableDepth
            scopeDepth arguments)
          (canonicalizeList declaration arguments) := by
        rw [canonicalizeListByDepths_eq_map, canonicalizeList_eq_map]
        exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
          (fun argument membership =>
            inductionHypothesis argument membership childAvailableDepth
              scopeDepth)
      simpa [canonicalizeByDepths, canonicalize, childAvailableDepth] using
        finishNormalizeReflectiveApply_parallelOrderAgnostic declaration
          constructor argumentsRelated
  | hlambda binder body inductionHypothesis =>
      exact .lambda binder
        (inductionHypothesis (availableDepth + 1) (scopeDepth + 1))
  | hmultiLambda arity binders body inductionHypothesis =>
      exact .multiLambda arity binders
        (inductionHypothesis (availableDepth + arity) (scopeDepth + arity))
  | hsubst body replacement bodyInduction replacementInduction =>
      exact .subst
        (bodyInduction (availableDepth + 1) (scopeDepth + 1))
        (replacementInduction availableDepth scopeDepth)
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsRelated : ParallelOrderAgnosticList declaration
          (canonicalizeListByDepths key declaration availableDepth scopeDepth
            elements)
          (canonicalizeList declaration elements) := by
        rw [canonicalizeListByDepths_eq_map, canonicalizeList_eq_map]
        exact ParallelOrderAgnostic.ParallelOrderAgnosticList.mapPair
          (fun element membership =>
            inductionHypothesis element membership availableDepth scopeDepth)
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
                  (normalizeParallelElementsBy
                    (key availableDepth scopeDepth) declaration
                    (canonicalizeListByDepths key declaration availableDepth
                      scopeDepth elements))
                  (normalizeParallelElements declaration
                    (canonicalizeList declaration elements)) := by
              simpa [normalizeParallelElementsBy,
                normalizeParallelElements] using
                ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.sort
                  (key availableDepth scopeDepth) PatternCode.patternCode
                    filtered
            simpa [canonicalizeByDepths, canonicalize] using
              ParallelOrderAgnostic.ParallelOrderAgnosticPermutation.collapse
                sorted
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr selected
            simpa [canonicalizeByDepths, canonicalize, selectedFalse] using
              (ParallelOrderAgnostic.collection collectionType none
                elementsRelated)

/-- An order-agnostic relative of a free variable is that exact free
variable. -/
theorem ParallelOrderAgnostic.eq_fvar_of_right_eq
    {declaration : ReflectivePresentationDecl} {left right : Pattern}
    (related : ParallelOrderAgnostic declaration left right) {name : String}
    (rightEq : right = .fvar name) : left = .fvar name := by
  cases related <;> cases rightEq
  rfl

/-- If ordinary canonicalization collapses to a free variable, every
two-depth keyed canonicalization collapses to the same variable exactly. -/
theorem canonicalizeByDepths_eq_fvar_of_canonicalize_eq
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) {pattern : Pattern} {name : String}
    (collapse : canonicalize declaration pattern = .fvar name) :
    canonicalizeByDepths key declaration availableDepth scopeDepth pattern =
      .fvar name :=
  (canonicalizeByDepths_parallelOrderAgnostic key declaration availableDepth
    scopeDepth pattern).eq_fvar_of_right_eq collapse

/-- An order-agnostic relative of a bound variable is that exact bound
variable. -/
theorem ParallelOrderAgnostic.eq_bvar_of_right_eq
    {declaration : ReflectivePresentationDecl} {left right : Pattern}
    (related : ParallelOrderAgnostic declaration left right) {index : Nat}
    (rightEq : right = .bvar index) : left = .bvar index := by
  cases related <;> cases rightEq
  rfl

/-- If ordinary canonicalization collapses to a bound variable, every
two-depth keyed canonicalization collapses to the same variable exactly. -/
theorem canonicalizeByDepths_eq_bvar_of_canonicalize_eq
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) {pattern : Pattern} {index : Nat}
    (collapse : canonicalize declaration pattern = .bvar index) :
    canonicalizeByDepths key declaration availableDepth scopeDepth pattern =
      .bvar index :=
  (canonicalizeByDepths_parallelOrderAgnostic key declaration availableDepth
    scopeDepth pattern).eq_bvar_of_right_eq collapse

-- Positive canary: keyed canonicalization fixes every bound-variable leaf.
example {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth index : Nat) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
      (.bvar index) = .bvar index := rfl

-- Negative canary: the bridge preserves the index rather than choosing an
-- arbitrary bound-variable representative.
example {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth leftIndex rightIndex : Nat)
    (different : leftIndex ≠ rightIndex) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
      (.bvar leftIndex) ≠ .bvar rightIndex := by
  simpa [canonicalizeByDepths] using different

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
