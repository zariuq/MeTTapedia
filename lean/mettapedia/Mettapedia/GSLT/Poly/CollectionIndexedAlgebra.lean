import Mettapedia.GSLT.Poly.RhoCalcControl
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-!
# Parallel algebra of closed ρ processes

Permutation, flattening, the singleton law, and deletion of `PZero` are
equations on hash bags. They transport under application and under a
lambda, so they transport under an input binder. `QuoteDrop` and renaming
of a free name are not among these equations. The algebra is sound for the
multiset reading. The converse fails on a quotation that `QuoteDrop` would
contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionIndexedAlgebra

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.Poly.RhoCalcControl
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-- Permutation, flattening, singleton, and `PZero`, closed under application,
lambda, and collection. -/
inductive AlgebraCong : Pattern → Pattern → Prop where
  | refl (pattern : Pattern) : AlgebraCong pattern pattern
  | symm {left right : Pattern} : AlgebraCong left right → AlgebraCong right left
  | trans {left mid right : Pattern} :
      AlgebraCong left mid → AlgebraCong mid right → AlgebraCong left right
  | perm {elements swapped : List Pattern} :
      List.Perm elements swapped →
        AlgebraCong (.collection .hashBag elements none)
          (.collection .hashBag swapped none)
  | flatten {before nested after : List Pattern} :
      AlgebraCong
        (.collection .hashBag
          (before ++ .collection .hashBag nested none :: after) none)
        (.collection .hashBag (before ++ nested ++ after) none)
  | singleton {pattern : Pattern} :
      AlgebraCong (.collection .hashBag [pattern] none) pattern
  | dropZero {before after : List Pattern} :
      AlgebraCong
        (.collection .hashBag (before ++ .apply "PZero" [] :: after) none)
        (.collection .hashBag (before ++ after) none)
  | applyAt {label : String} {before : List Pattern} {left right : Pattern}
      {after : List Pattern} :
      AlgebraCong left right →
        AlgebraCong (.apply label (before ++ left :: after))
          (.apply label (before ++ right :: after))
  | lambdaAt {binder : Option String} {left right : Pattern} :
      AlgebraCong left right →
        AlgebraCong (.lambda binder left) (.lambda binder right)
  | collectionAt {kind : CollType} {before : List Pattern} {left right : Pattern}
      {after : List Pattern} {rest : Option String} :
      AlgebraCong left right →
        AlgebraCong (.collection kind (before ++ left :: after) rest)
          (.collection kind (before ++ right :: after) rest)

theorem canonicalize_hashBag (elements : List Pattern) :
    canonicalize (.collection .hashBag elements none) =
      collapseBag (normalizeBagElements (canonicalizeList elements)) :=
  rfl

theorem canonicalize_lambda_eq (binder : Option String) (body : Pattern) :
    canonicalize (.lambda binder body) = .lambda binder (canonicalize body) :=
  rfl

theorem canonicalize_quote (argument : Pattern) :
    canonicalize (.apply "NQuote" [argument]) =
      normalizeQuote (canonicalize argument) :=
  rfl

theorem canonicalize_zero :
    canonicalize (.apply "PZero" []) = .apply "PZero" [] :=
  rfl

theorem canonicalize_bag_perm {elements swapped : List Pattern}
    (permutation : List.Perm elements swapped) :
    canonicalize (.collection .hashBag elements none) =
      canonicalize (.collection .hashBag swapped none) := by
  rw [canonicalize_hashBag, canonicalize_hashBag]
  exact congrArg collapseBag
    (normalizeBagElements_eq_of_perm (canonicalizeList_perm permutation))

theorem canonicalize_flatten {before nested after : List Pattern} :
    canonicalize
        (.collection .hashBag
          (before ++ .collection .hashBag nested none :: after) none) =
      canonicalize (.collection .hashBag (before ++ nested ++ after) none) := by
  have toEnd :
      List.Perm (before ++ .collection .hashBag nested none :: after)
        ((before ++ after) ++ [.collection .hashBag nested none]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have flatShift :
      List.Perm (before ++ nested ++ after) ((before ++ after) ++ nested) := by
    simpa [List.append_assoc] using
      List.Perm.append_left before (List.perm_append_comm (l₁ := nested) (l₂ := after))
  calc
    canonicalize
          (.collection .hashBag
            (before ++ .collection .hashBag nested none :: after) none) =
        canonicalize
          (.collection .hashBag
            ((before ++ after) ++ [.collection .hashBag nested none]) none) :=
      canonicalize_bag_perm toEnd
    _ = canonicalize
          (.collection .hashBag ((before ++ after) ++ nested) none) :=
      canonicalize_parallel_flatten (before ++ after) nested
    _ = canonicalize (.collection .hashBag (before ++ nested ++ after) none) :=
      (canonicalize_bag_perm flatShift).symm

theorem bagContents_erase_zero (before after : List Pattern) :
    bagContents (before ++ .apply "PZero" [] :: after) = bagContents (before ++ after) := by
  simp [bagContents, List.flatMap_append, List.filter_append, bagSplice]

theorem canonicalizeList_cons_append (before : List Pattern) (head : Pattern)
    (after : List Pattern) :
    canonicalizeList (before ++ head :: after) =
      canonicalizeList before ++ canonicalize head :: canonicalizeList after := by
  induction before with
  | nil => rfl
  | cons pattern before inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis, List.cons_append]

theorem canonicalize_drop_zero {before after : List Pattern} :
    canonicalize
        (.collection .hashBag (before ++ .apply "PZero" [] :: after) none) =
      canonicalize (.collection .hashBag (before ++ after) none) := by
  rw [canonicalize_hashBag, canonicalize_hashBag, canonicalizeList_cons_append, canonicalize_zero,
    canonicalizeList_append]
  apply congrArg collapseBag
  rw [normalizeBagElements_eq_sort_bagContents, normalizeBagElements_eq_sort_bagContents]
  exact congrArg sortPatterns (bagContents_erase_zero _ _)

theorem canonicalizeList_congr {before after : List Pattern} {left right : Pattern}
    (equal : canonicalize left = canonicalize right) :
    canonicalizeList (before ++ left :: after) =
      canonicalizeList (before ++ right :: after) := by
  simp [canonicalizeList_cons_append, equal]

theorem canonicalize_apply_congr {label : String} {arguments swapped : List Pattern}
    (equal : canonicalizeList arguments = canonicalizeList swapped) :
    canonicalize (.apply label arguments) = canonicalize (.apply label swapped) := by
  by_cases name : label = "NQuote"
  · subst name
    cases arguments with
    | nil =>
        cases swapped with
        | nil => rfl
        | cons _ _ => simp [canonicalizeList] at equal
    | cons head tail =>
        cases tail with
        | nil =>
            cases swapped with
            | nil => simp [canonicalizeList] at equal
            | cons other rest =>
                cases rest with
                | nil =>
                    simp [canonicalizeList] at equal
                    rw [canonicalize_quote, canonicalize_quote, equal]
                | cons _ _ => simp [canonicalizeList] at equal
        | cons second more =>
            cases swapped with
            | nil => simp [canonicalizeList] at equal
            | cons other rest =>
                cases rest with
                | nil => simp [canonicalizeList] at equal
                | cons third tail =>
                    have leftReduced :
                        canonicalize (.apply "NQuote" (head :: second :: more)) =
                          .apply "NQuote"
                            (canonicalizeList (head :: second :: more)) :=
                      rfl
                    have rightReduced :
                        canonicalize (.apply "NQuote" (other :: third :: tail)) =
                          .apply "NQuote"
                            (canonicalizeList (other :: third :: tail)) :=
                      rfl
                    rw [leftReduced, rightReduced]
                    exact congrArg (fun arguments => Pattern.apply "NQuote" arguments) equal
  · simp [canonicalize, name, equal]

/-- The parallel algebra does not change the canonical multiset representative. -/
theorem algebra_canonicalize {left right : Pattern} (related : AlgebraCong left right) :
    canonicalize left = canonicalize right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | perm permutation => exact canonicalize_bag_perm permutation
  | flatten => exact canonicalize_flatten
  | singleton => exact canonicalize_parallel_singleton _
  | dropZero => exact canonicalize_drop_zero
  | applyAt step inductionHypothesis =>
      exact canonicalize_apply_congr (canonicalizeList_congr inductionHypothesis)
  | lambdaAt _ inductionHypothesis =>
      rw [canonicalize_lambda_eq, canonicalize_lambda_eq, inductionHypothesis]
  | collectionAt step inductionHypothesis =>
      -- A hash bag uses the bag normalizer. Every other collection is structural.
      rename_i kind before leftPattern rightPattern after rest
      cases kind with
      | hashBag =>
          cases rest with
          | none =>
              rw [canonicalize_hashBag, canonicalize_hashBag]
              exact congrArg collapseBag
                (congrArg normalizeBagElements (canonicalizeList_congr inductionHypothesis))
          | some name =>
              simp [canonicalize, canonicalizeList_congr inductionHypothesis]
      | vec =>
          simp [canonicalize, canonicalizeList_congr inductionHypothesis]
      | hashSet =>
          simp [canonicalize, canonicalizeList_congr inductionHypothesis]

/-- Closed processes related by the parallel algebra have the same bag of primes. -/
theorem algebra_fromProcess {left right : RhoProcess}
    (related : AlgebraCong left.1 right.1) :
    fromProcess left = fromProcess right :=
  (fromProcess_eq_iff left right).mpr (algebra_canonicalize related)

/-! ## What the algebra does not identify -/

mutual
  def dropCount : Pattern → Nat
    | .apply label arguments =>
        (if label = "PDrop" then 1 else 0) + dropCountList arguments
    | .lambda _ body => dropCount body
    | .multiLambda _ _ body => dropCount body
    | .subst body replacement => dropCount body + dropCount replacement
    | .collection _ elements _ => dropCountList elements
    | .bvar _ => 0
    | .fvar _ => 0

  def dropCountList : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => dropCount pattern + dropCountList patterns
end

theorem dropCountList_append (left right : List Pattern) :
    dropCountList (left ++ right) = dropCountList left + dropCountList right := by
  induction left with
  | nil => simp [dropCountList]
  | cons _ _ inductionHypothesis =>
      simp [dropCountList, inductionHypothesis, Nat.add_assoc]

theorem dropCountList_eq_sum (patterns : List Pattern) :
    dropCountList patterns = (patterns.map dropCount).sum := by
  induction patterns with
  | nil => simp [dropCountList]
  | cons _ _ inductionHypothesis =>
      simp [dropCountList, inductionHypothesis]

theorem dropCountList_perm {left right : List Pattern} (permutation : List.Perm left right) :
    dropCountList left = dropCountList right := by
  rw [dropCountList_eq_sum, dropCountList_eq_sum]
  exact List.Perm.sum_nat (permutation.map dropCount)

theorem dropCountList_replace {before after : List Pattern} {left right : Pattern}
    (equal : dropCount left = dropCount right) :
    dropCountList (before ++ left :: after) = dropCountList (before ++ right :: after) := by
  simp [dropCountList_append, dropCountList, equal]

theorem algebra_dropCount {left right : Pattern} (related : AlgebraCong left right) :
    dropCount left = dropCount right := by
  induction related with
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ inductionHypothesis inductionHypothesis' =>
      exact inductionHypothesis.trans inductionHypothesis'
  | perm permutation =>
      simpa [dropCount] using dropCountList_perm permutation
  | flatten =>
      simp [dropCount, dropCountList_append, dropCountList]
  | singleton =>
      simp [dropCount, dropCountList]
  | dropZero =>
      simp [dropCount, dropCountList_append, dropCountList]
  | applyAt _ inductionHypothesis =>
      simp [dropCount, dropCountList_replace inductionHypothesis]
  | lambdaAt _ inductionHypothesis =>
      simp [dropCount, inductionHypothesis]
  | collectionAt _ inductionHypothesis =>
      simp [dropCount, dropCountList_replace inductionHypothesis]

/-- `POutput` of a quoted drop, which `QuoteDrop` would contract. -/
def quotedOutput : Pattern :=
  .apply "POutput" [.apply "NQuote" [procDrop], procZero]

theorem quotedOutput_dropCount : dropCount quotedOutput = 1 := by
  simp [quotedOutput, procDrop, procZero, dropCount, dropCountList]

theorem procOutput_dropCount : dropCount procOutput = 0 := by
  simp [procOutput, procZero, dropCount, dropCountList]

theorem quoted_not_algebra : ¬ AlgebraCong quotedOutput procOutput := by
  intro related
  have counts := algebra_dropCount related
  simp [quotedOutput_dropCount, procOutput_dropCount] at counts

theorem quotedOutput_process :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] quotedOutput :=
  .output (.quote procDrop_process) .unit

theorem quotedOutput_safe : binderSafeAt "NQuote" 0 quotedOutput = true := by
  decide

theorem quotedOutput_closed : RhoClosedTermWellSorted rhoProc quotedOutput :=
  (rhoClosedTermWellSorted_process_iff quotedOutput).mpr
    ⟨quotedOutput_process, quotedOutput_safe⟩

def quotedProcess : RhoProcess := ⟨quotedOutput, quotedOutput_closed⟩

def plainProcess : RhoProcess := ⟨procOutput, procOutput_closed⟩

theorem quoted_canonicalize :
    canonicalize quotedOutput = canonicalize procOutput := by
  simp [quotedOutput, procOutput, procDrop, procZero, canonicalize, canonicalizeList,
    normalizeQuote]

/-- `QuoteDrop` makes these two processes one bag. The parallel algebra does not. -/
theorem quoted_fromProcess : fromProcess quotedProcess = fromProcess plainProcess :=
  (fromProcess_eq_iff quotedProcess plainProcess).mpr quoted_canonicalize

/-- A nested bag flattens in the algebra. -/
theorem nested_flattens : AlgebraCong nestedPar orderedPar := by
  simpa [nestedPar, orderedPar, List.nil_append, List.append_nil, List.cons_append] using
    (AlgebraCong.flatten (before := []) (nested := [procDrop, procOutput]) (after := []))

/-- Deleting the unit leaves the other element. -/
theorem zero_deletes : AlgebraCong withZero onlyDrop := by
  simpa [withZero, onlyDrop, procZero, List.nil_append, List.append_nil] using
    (AlgebraCong.dropZero (before := [procDrop]) (after := []))

/-- The singleton law applies under an input binder. -/
theorem input_singleton :
    AlgebraCong
      (.apply "PInput"
        [.apply "NQuote" [procZero], .lambda none (.collection .hashBag [procDrop] none)])
      (.apply "PInput" [.apply "NQuote" [procZero], .lambda none procDrop]) :=
  AlgebraCong.applyAt (before := [.apply "NQuote" [procZero]])
    (AlgebraCong.lambdaAt AlgebraCong.singleton)

end Mettapedia.GSLT.Poly.CollectionIndexedAlgebra
