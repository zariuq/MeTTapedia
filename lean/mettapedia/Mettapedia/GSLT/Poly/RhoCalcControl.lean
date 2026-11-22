import Mathlib.Logic.Relation
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

/-!
# Permutation of parallel ρ processes

Closed processes of `rhoCalc` typed at `Proc` may be read as hash bags.
Permuting the elements of one bag does not change the multiset reading in
`CanonicalBag`. Flattening a nested bag and deleting `PZero` do change that
reading, and neither step is a permutation of bag elements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.RhoCalcControl

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-- The grammar rule at a fixed position in `rhoCalc`. -/
def ruleAt (index : Nat) (bound : index < rhoCalc.terms.length) : GrammarRule :=
  rhoCalc.terms.get ⟨index, bound⟩

theorem ruleAt_mem (index : Nat) (bound : index < rhoCalc.terms.length) :
    ruleAt index bound ∈ rhoCalc.terms :=
  List.get_mem _ _

theorem zero_bound : 0 < rhoCalc.terms.length := by simp [rhoCalc]
theorem drop_bound : 1 < rhoCalc.terms.length := by simp [rhoCalc]
theorem quote_bound : 2 < rhoCalc.terms.length := by simp [rhoCalc]
theorem par_bound : 3 < rhoCalc.terms.length := by simp [rhoCalc]
theorem output_bound : 4 < rhoCalc.terms.length := by simp [rhoCalc]

def zeroRule : GrammarRule := ruleAt 0 zero_bound
def dropRule : GrammarRule := ruleAt 1 drop_bound
def quoteRule : GrammarRule := ruleAt 2 quote_bound
def parRule : GrammarRule := ruleAt 3 par_bound
def outputRule : GrammarRule := ruleAt 4 output_bound

theorem zeroRule_label : zeroRule.label = "PZero" := by simp [zeroRule, ruleAt, rhoCalc]
theorem zeroRule_category : zeroRule.category = "Proc" := by simp [zeroRule, ruleAt, rhoCalc]
theorem zeroRule_params : zeroRule.params = [] := by simp [zeroRule, ruleAt, rhoCalc]

theorem dropRule_label : dropRule.label = "PDrop" := by simp [dropRule, ruleAt, rhoCalc]
theorem dropRule_category : dropRule.category = "Proc" := by simp [dropRule, ruleAt, rhoCalc]
theorem dropRule_params : dropRule.params = [.simple "n" TypeExpr.name] := by
  simp [dropRule, ruleAt, rhoCalc]

theorem quoteRule_label : quoteRule.label = "NQuote" := by simp [quoteRule, ruleAt, rhoCalc]
theorem quoteRule_category : quoteRule.category = "Name" := by simp [quoteRule, ruleAt, rhoCalc]
theorem quoteRule_params : quoteRule.params = [.simple "p" TypeExpr.proc] := by
  simp [quoteRule, ruleAt, rhoCalc]

theorem parRule_category : parRule.category = "Proc" := by simp [parRule, ruleAt, rhoCalc]
theorem parRule_params :
    parRule.params = [.simple "ps" (.collection .hashBag (.base "Proc"))] := by
  simp [parRule, ruleAt, rhoCalc, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType]

theorem outputRule_label : outputRule.label = "POutput" := by simp [outputRule, ruleAt, rhoCalc]
theorem outputRule_category : outputRule.category = "Proc" := by
  simp [outputRule, ruleAt, rhoCalc]
theorem outputRule_params :
    outputRule.params = [.simple "n" TypeExpr.name, .simple "q" TypeExpr.proc] := by
  simp [outputRule, ruleAt, rhoCalc]

theorem not_bare_zero : ¬ UsesBareCollection zeroRule := by
  intro ⟨_, _, _, shape⟩
  cases mode : zeroRule.collectionRepresentation <;>
    simp [GrammarRule.bareParams, mode, zeroRule_params] at shape

theorem not_bare_drop : ¬ UsesBareCollection dropRule := by
  intro ⟨_, _, _, shape⟩
  cases mode : dropRule.collectionRepresentation <;>
    simp [GrammarRule.bareParams, mode, dropRule_params, TypeExpr.name, TypeExpr.baseType] at shape

theorem not_bare_quote : ¬ UsesBareCollection quoteRule := by
  intro ⟨_, _, _, shape⟩
  cases mode : quoteRule.collectionRepresentation <;>
    simp [GrammarRule.bareParams, mode, quoteRule_params, TypeExpr.proc, TypeExpr.baseType] at shape

theorem not_bare_output : ¬ UsesBareCollection outputRule := by
  intro ⟨_, _, _, shape⟩
  cases mode : outputRule.collectionRepresentation <;>
    simp [GrammarRule.bareParams, mode, outputRule_params, TypeExpr.name, TypeExpr.baseType] at shape

/-- The unit process `PZero`. -/
def procZero : Pattern := .apply "PZero" []

/-- `PDrop` of the quotation of `PZero`. -/
def procDrop : Pattern := .apply "PDrop" [.apply "NQuote" [procZero]]

/-- `POutput` on the quotation of `PZero`, sending `PZero`. -/
def procOutput : Pattern := .apply "POutput" [.apply "NQuote" [procZero], procZero]

/-- Parallel composition of `procDrop` and `procOutput`, in that order. -/
def orderedPar : Pattern := .collection .hashBag [procDrop, procOutput] none

/-- The same two processes with the bag order reversed. -/
def swappedPar : Pattern := .collection .hashBag [procOutput, procDrop] none

/-- A bag whose single element is itself the ordered parallel bag. -/
def nestedPar : Pattern := .collection .hashBag [orderedPar] none

/-- `procDrop` in parallel with the unit. -/
def withZero : Pattern := .collection .hashBag [procDrop, procZero] none

/-- A singleton bag of `procDrop`. -/
def onlyDrop : Pattern := .collection .hashBag [procDrop] none

theorem procZero_typed :
    HasType rhoCalc FreeTypeContext.empty [] procZero (.base "Proc") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty [] [] zeroRule.params := by
    rw [zeroRule_params]
    exact ArgumentsHaveTypes.nil (bound := [])
  have typed := HasType.constructor (rule := zeroRule) (arguments := [])
    (ruleAt_mem 0 zero_bound) not_bare_zero arguments
  simpa [procZero, zeroRule_label, zeroRule_category] using typed

theorem quoteZero_typed :
    HasType rhoCalc FreeTypeContext.empty [] (.apply "NQuote" [procZero]) (.base "Name") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty []
      [procZero] quoteRule.params := by
    rw [quoteRule_params]
    exact .cons trivial rfl procZero_typed (ArgumentsHaveTypes.nil (bound := []))
  have typed := HasType.constructor (rule := quoteRule) (ruleAt_mem 2 quote_bound)
    not_bare_quote arguments
  simpa [quoteRule_label, quoteRule_category] using typed

theorem procDrop_typed :
    HasType rhoCalc FreeTypeContext.empty [] procDrop (.base "Proc") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty []
      [.apply "NQuote" [procZero]] dropRule.params := by
    rw [dropRule_params]
    exact .cons trivial rfl quoteZero_typed (ArgumentsHaveTypes.nil (bound := []))
  have typed := HasType.constructor (rule := dropRule) (ruleAt_mem 1 drop_bound)
    not_bare_drop arguments
  simpa [procDrop, dropRule_label, dropRule_category] using typed

theorem procOutput_typed :
    HasType rhoCalc FreeTypeContext.empty [] procOutput (.base "Proc") := by
  have arguments : ArgumentsHaveTypes rhoCalc FreeTypeContext.empty []
      [.apply "NQuote" [procZero], procZero] outputRule.params := by
    rw [outputRule_params]
    exact .cons trivial rfl quoteZero_typed
      (.cons trivial rfl procZero_typed (ArgumentsHaveTypes.nil (bound := [])))
  have typed := HasType.constructor (rule := outputRule) (ruleAt_mem 4 output_bound)
    not_bare_output arguments
  simpa [procOutput, outputRule_label, outputRule_category] using typed

theorem orderedPar_typed :
    HasType rhoCalc FreeTypeContext.empty [] orderedPar (.base "Proc") := by
  have typed := HasType.collectionConstructor (rule := parRule)
    (parameterName := "ps") (collectionType := .hashBag) (elementType := .base "Proc")
    (rest := none) (ruleAt_mem 3 par_bound) parRule_params
    (.cons procDrop_typed (.cons procOutput_typed (.nil [] (.base "Proc"))))
  simpa [orderedPar, parRule_category] using typed

theorem swappedPar_typed :
    HasType rhoCalc FreeTypeContext.empty [] swappedPar (.base "Proc") := by
  have typed := HasType.collectionConstructor (rule := parRule)
    (parameterName := "ps") (collectionType := .hashBag) (elementType := .base "Proc")
    (rest := none) (ruleAt_mem 3 par_bound) parRule_params
    (.cons procOutput_typed (.cons procDrop_typed (.nil [] (.base "Proc"))))
  simpa [swappedPar, parRule_category] using typed

theorem nestedPar_typed :
    HasType rhoCalc FreeTypeContext.empty [] nestedPar (.base "Proc") := by
  have typed := HasType.collectionConstructor (rule := parRule)
    (parameterName := "ps") (collectionType := .hashBag) (elementType := .base "Proc")
    (rest := none) (ruleAt_mem 3 par_bound) parRule_params
    (.cons orderedPar_typed (.nil [] (.base "Proc")))
  simpa [nestedPar, parRule_category] using typed

theorem withZero_typed :
    HasType rhoCalc FreeTypeContext.empty [] withZero (.base "Proc") := by
  have typed := HasType.collectionConstructor (rule := parRule)
    (parameterName := "ps") (collectionType := .hashBag) (elementType := .base "Proc")
    (rest := none) (ruleAt_mem 3 par_bound) parRule_params
    (.cons procDrop_typed (.cons procZero_typed (.nil [] (.base "Proc"))))
  simpa [withZero, parRule_category] using typed

theorem onlyDrop_typed :
    HasType rhoCalc FreeTypeContext.empty [] onlyDrop (.base "Proc") := by
  have typed := HasType.collectionConstructor (rule := parRule)
    (parameterName := "ps") (collectionType := .hashBag) (elementType := .base "Proc")
    (rest := none) (ruleAt_mem 3 par_bound) parRule_params
    (.cons procDrop_typed (.nil [] (.base "Proc")))
  simpa [onlyDrop, parRule_category] using typed

theorem orderedPar_object : isObjectPattern orderedPar = true := by
  simp [orderedPar, procDrop, procOutput, procZero, isObjectPattern, isObjectPatternList]

theorem swappedPar_object : isObjectPattern swappedPar = true := by
  simp [swappedPar, procDrop, procOutput, procZero, isObjectPattern, isObjectPatternList]

/-- Closed object patterns of `rhoCalc` at `Proc`. -/
abbrev ClosedRhoProc :=
  { pattern : Pattern //
      HasType rhoCalc FreeTypeContext.empty [] pattern (.base "Proc") ∧
        isObjectPattern pattern = true }

/-- One hash bag is a permutation of another. No other equation is a step. -/
inductive RhoBagStep : Pattern → Pattern → Prop where
  | perm {elements swapped : List Pattern} :
      List.Perm elements swapped →
      RhoBagStep (.collection .hashBag elements none)
        (.collection .hashBag swapped none)

/-- Length of the outermost hash bag, when the pattern is one. -/
def outerLength : Pattern → Option Nat
  | .collection .hashBag elements none => some elements.length
  | _ => none

theorem rhoBagStep_outerLength {left right : Pattern} (step : RhoBagStep left right) :
    outerLength left = outerLength right := by
  cases step with
  | perm permutation =>
      simp [outerLength, List.Perm.length_eq permutation]

theorem eqv_outerLength {left right : Pattern}
    (related : Relation.EqvGen RhoBagStep left right) :
    outerLength left = outerLength right := by
  induction related with
  | rel _ _ step => exact rhoBagStep_outerLength step
  | refl => rfl
  | symm _ _ _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Equivalence generated by permuting the elements of a hash bag. -/
def rhoBagSetoid : Setoid ClosedRhoProc where
  r left right := Relation.EqvGen RhoBagStep left.1 right.1
  iseqv :=
    { refl := fun process => Relation.EqvGen.refl process.1
      symm := fun h => Relation.EqvGen.symm _ _ h
      trans := fun h k => Relation.EqvGen.trans _ _ _ h k }

def orderedClosed : ClosedRhoProc :=
  ⟨orderedPar, orderedPar_typed, orderedPar_object⟩

def swappedClosed : ClosedRhoProc :=
  ⟨swappedPar, swappedPar_typed, swappedPar_object⟩

theorem parallel_swap_related : rhoBagSetoid.r orderedClosed swappedClosed := by
  show Relation.EqvGen RhoBagStep orderedPar swappedPar
  exact Relation.EqvGen.rel _ _
    (.perm (List.Perm.swap procOutput procDrop []))

theorem parallel_patterns_distinct : orderedPar ≠ swappedPar := by
  intro same
  simp [orderedPar, swappedPar, procDrop, procOutput, procZero, Pattern.collection.injEq,
    Pattern.apply.injEq] at same

theorem procDrop_process :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] procDrop :=
  .drop (.quote .unit)

theorem procOutput_process :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] procOutput :=
  .output (.quote .unit) .unit

theorem procZero_process :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] procZero :=
  .unit

theorem procDrop_safe : binderSafeAt "NQuote" 0 procDrop = true := by
  decide

theorem procOutput_safe : binderSafeAt "NQuote" 0 procOutput = true := by
  decide

theorem procZero_safe : binderSafeAt "NQuote" 0 procZero = true := by
  decide

theorem orderedPar_safe : binderSafeAt "NQuote" 0 orderedPar = true := by
  decide

theorem withZero_safe : binderSafeAt "NQuote" 0 withZero = true := by
  decide

theorem onlyDrop_safe : binderSafeAt "NQuote" 0 onlyDrop = true := by
  decide

theorem procDrop_closed : RhoClosedTermWellSorted rhoProc procDrop :=
  (rhoClosedTermWellSorted_process_iff procDrop).mpr ⟨procDrop_process, procDrop_safe⟩

theorem procOutput_closed : RhoClosedTermWellSorted rhoProc procOutput :=
  (rhoClosedTermWellSorted_process_iff procOutput).mpr ⟨procOutput_process, procOutput_safe⟩

theorem procZero_closed : RhoClosedTermWellSorted rhoProc procZero :=
  (rhoClosedTermWellSorted_process_iff procZero).mpr ⟨procZero_process, procZero_safe⟩

theorem orderedPar_closed : RhoClosedTermWellSorted rhoProc orderedPar :=
  (rhoClosedTermWellSorted_process_iff orderedPar).mpr
    ⟨.parallel (.cons procDrop_process (.cons procOutput_process .nil)), orderedPar_safe⟩

theorem withZero_closed : RhoClosedTermWellSorted rhoProc withZero :=
  (rhoClosedTermWellSorted_process_iff withZero).mpr
    ⟨.parallel (.cons procDrop_process (.cons procZero_process .nil)), withZero_safe⟩

theorem onlyDrop_closed : RhoClosedTermWellSorted rhoProc onlyDrop :=
  (rhoClosedTermWellSorted_process_iff onlyDrop).mpr
    ⟨.parallel (.cons procDrop_process .nil), onlyDrop_safe⟩

theorem procZero_canonical : IsCanonical procZero := by
  simp [procZero, IsCanonical, IsCanonicalList]

theorem quoteZero_canonical : IsCanonical (.apply "NQuote" [procZero]) := by
  refine ⟨procZero_canonical, ?_⟩
  intro name equal
  simp [procZero, Pattern.apply.injEq] at equal

theorem procDrop_canonical : IsCanonical procDrop := by
  simpa [procDrop, IsCanonical, IsCanonicalList] using quoteZero_canonical

theorem procOutput_canonical : IsCanonical procOutput := by
  simp [procOutput, procZero, IsCanonical, IsCanonicalList]

theorem procDrop_not_zero : procDrop ≠ procZero := by
  intro same
  simp [procDrop, procZero, Pattern.apply.injEq] at same

theorem procOutput_not_zero : procOutput ≠ procZero := by
  intro same
  simp [procOutput, procZero, Pattern.apply.injEq] at same

theorem procDrop_not_bag (elements : List Pattern) :
    procDrop ≠ .collection .hashBag elements none := by
  intro same
  cases same

theorem procOutput_not_bag (elements : List Pattern) :
    procOutput ≠ .collection .hashBag elements none := by
  intro same
  cases same

theorem procDrop_prime : IsPrime procDrop :=
  ⟨procDrop_closed, procDrop_canonical, procDrop_not_zero, procDrop_not_bag⟩

theorem procOutput_prime : IsPrime procOutput :=
  ⟨procOutput_closed, procOutput_canonical, procOutput_not_zero, procOutput_not_bag⟩

theorem pairPrimes : ∀ pattern ∈ [procDrop, procOutput], IsPrime pattern := by
  intro pattern membership
  simp [List.mem_cons] at membership
  rcases membership with rfl | rfl
  · exact procDrop_prime
  · exact procOutput_prime

theorem swapPrimes : ∀ pattern ∈ [procOutput, procDrop], IsPrime pattern := by
  intro pattern membership
  simp [List.mem_cons] at membership
  rcases membership with rfl | rfl
  · exact procOutput_prime
  · exact procDrop_prime

def orderedProcess : RhoProcess :=
  ofList [procDrop, procOutput] fun pattern membership => (pairPrimes pattern membership).1

def swappedProcess : RhoProcess :=
  ofList [procOutput, procDrop] fun pattern membership => (swapPrimes pattern membership).1

/-- `{a, b}` and `{b, a}`, typed at `Proc`, are one `CanonicalBag` multiset. -/
theorem parallel_swap_same : fromProcess orderedProcess = fromProcess swappedProcess := by
  unfold orderedProcess swappedProcess
  apply Subtype.ext
  rw [fromProcess_ofList_primes [procDrop, procOutput] pairPrimes,
    fromProcess_ofList_primes [procOutput, procDrop] swapPrimes]
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap procOutput procDrop [])

theorem nested_elements_not_perm :
    ¬ List.Perm [orderedPar] [procDrop, procOutput] := by
  intro permutation
  have lengths := List.Perm.length_eq permutation
  simp at lengths

/-- A nested bag is not a permutation of the flat bag. -/
theorem nested_not_flat : ¬ Relation.EqvGen RhoBagStep nestedPar orderedPar := by
  intro related
  have lengths := eqv_outerLength related
  simp [nestedPar, orderedPar, outerLength] at lengths

theorem bagContents_pair :
    bagContents [procDrop, procOutput] = [procDrop, procOutput] := by
  refine bagContents_eq_self ?_ ?_
  · intro pattern membership
    simp [List.mem_cons] at membership
    rcases membership with rfl | rfl
    · exact procDrop_not_zero
    · exact procOutput_not_zero
  · intro pattern membership elements
    simp [List.mem_cons] at membership
    rcases membership with rfl | rfl
    · exact procDrop_not_bag elements
    · exact procOutput_not_bag elements

theorem canonicalize_orderedPar :
    canonicalize orderedPar =
      .collection .hashBag (sortPatterns [procDrop, procOutput]) none := by
  have canonList :
      canonicalizeList [procDrop, procOutput] = [procDrop, procOutput] := by
    simp [canonicalizeList, canonicalize_eq_of_isCanonical procDrop_canonical,
      canonicalize_eq_of_isCanonical procOutput_canonical]
  have sortedLength : 2 ≤ (sortPatterns [procDrop, procOutput]).length := by
    have permutation := List.mergeSort_perm [procDrop, procOutput]
      (fun left right => decide (patternCode left ≤ patternCode right))
    have lengths := List.Perm.length_eq permutation
    simp [sortPatterns, lengths]
  unfold orderedPar
  change collapseBag (normalizeBagElements (canonicalizeList [procDrop, procOutput])) = _
  rw [canonList, normalizeBagElements_eq_sort_bagContents, bagContents_pair]
  exact collapseBag_eq_bag_of_length_ge_two sortedLength

theorem nestedClosed : ∀ pattern ∈ [orderedPar], RhoClosedTermWellSorted rhoProc pattern := by
  intro pattern membership
  simp at membership
  subst membership
  exact orderedPar_closed

theorem flatClosed : ∀ pattern ∈ [procDrop, procOutput], RhoClosedTermWellSorted rhoProc pattern :=
  fun pattern membership => (pairPrimes pattern membership).1

/-- `CanonicalBag` flattens a nested bag. Permutation does not. -/
theorem canonical_flattens :
    fromProcess (ofList [orderedPar] nestedClosed) =
      fromProcess (ofList [procDrop, procOutput] flatClosed) := by
  apply Subtype.ext
  rw [fromProcess_ofList_inventory [orderedPar] nestedClosed,
    fromProcess_ofList_primes [procDrop, procOutput] pairPrimes]
  have contents :
      bagContents [canonicalize orderedPar] = sortPatterns [procDrop, procOutput] := by
    rw [canonicalize_orderedPar]
    have splice :
        bagSplice (.collection .hashBag (sortPatterns [procDrop, procOutput]) none) =
          sortPatterns [procDrop, procOutput] := by
      simp [bagSplice]
    have noZero : ∀ pattern ∈ sortPatterns [procDrop, procOutput],
        pattern ≠ .apply "PZero" [] := by
      intro pattern membership
      have source : pattern ∈ [procDrop, procOutput] := by
        have permutation := List.mergeSort_perm [procDrop, procOutput]
          (fun left right => decide (patternCode left ≤ patternCode right))
        have sortedMember : pattern ∈ [procDrop, procOutput].mergeSort
            (fun left right => decide (patternCode left ≤ patternCode right)) := by
          simpa [sortPatterns] using membership
        exact (List.Perm.mem_iff permutation).mp sortedMember
      simp only [List.mem_cons, List.mem_nil_iff] at source
      rcases source with rfl | source
      · exact procDrop_not_zero
      · rcases source with rfl | source
        · exact procOutput_not_zero
        · cases source
    have filtered :
        (sortPatterns [procDrop, procOutput]).filter
            (fun pattern => pattern ≠ .apply "PZero" []) =
          sortPatterns [procDrop, procOutput] :=
      List.filter_eq_self.mpr fun pattern membership =>
        decide_eq_true (noZero pattern membership)
    rw [bagContents, List.flatMap_cons, List.flatMap_nil, splice, List.append_nil, filtered]
  rw [List.map_cons, List.map_nil, contents]
  exact Multiset.coe_eq_coe.mpr (by
    simpa [sortPatterns] using
      (List.mergeSort_perm [procDrop, procOutput]
        (fun left right => decide (patternCode left ≤ patternCode right))))

theorem withZeroClosed : ∀ pattern ∈ [procDrop, procZero], RhoClosedTermWellSorted rhoProc pattern := by
  intro pattern membership
  simp [List.mem_cons] at membership
  rcases membership with rfl | rfl
  · exact procDrop_closed
  · exact procZero_closed

theorem onlyDropClosed : ∀ pattern ∈ [procDrop], RhoClosedTermWellSorted rhoProc pattern := by
  intro pattern membership
  simp at membership
  subst membership
  exact procDrop_closed

theorem unit_elements_not_perm : ¬ List.Perm [procDrop, procZero] [procDrop] := by
  intro permutation
  have lengths := List.Perm.length_eq permutation
  simp at lengths

/-- Deleting `PZero` is not a permutation of bag elements. -/
theorem unit_not_deleted : ¬ Relation.EqvGen RhoBagStep withZero onlyDrop := by
  intro related
  have lengths := eqv_outerLength related
  simp [withZero, onlyDrop, outerLength] at lengths

/-- `CanonicalBag` deletes the unit. The permutation quotient does not. -/
theorem canonical_drops_unit :
    fromProcess (ofList [procDrop, procZero] withZeroClosed) =
      fromProcess (ofList [procDrop] onlyDropClosed) := by
  apply (fromProcess_eq_iff _ _).mpr
  rw [rhoProcessEquations_iff]
  show canonicalize (.collection .hashBag [procDrop, procZero] none) =
    canonicalize (.collection .hashBag [procDrop] none)
  have dropFixed : canonicalize procDrop = procDrop :=
    canonicalize_eq_of_isCanonical procDrop_canonical
  have zeroFixed : canonicalize procZero = procZero :=
    canonicalize_eq_of_isCanonical procZero_canonical
  have listFixed : canonicalizeList [procDrop, procZero] = [procDrop, procZero] := by
    simp [canonicalizeList, dropFixed, zeroFixed]
  have singletonFixed : canonicalizeList [procDrop] = [procDrop] := by
    simp [canonicalizeList, dropFixed]
  change collapseBag (normalizeBagElements (canonicalizeList [procDrop, procZero])) =
    collapseBag (normalizeBagElements (canonicalizeList [procDrop]))
  rw [listFixed, singletonFixed, normalizeBagElements_eq_sort_bagContents,
    normalizeBagElements_eq_sort_bagContents]
  have dropKept : decide (procDrop ≠ .apply "PZero" []) = true :=
    decide_eq_true procDrop_not_zero
  have zeroDropped : decide (procZero ≠ .apply "PZero" []) = false := by
    simp [procZero]
  have spliceDrop : bagSplice procDrop = [procDrop] :=
    bagSplice_eq_singleton_of_not_bag procDrop_not_bag
  have spliceZero : bagSplice procZero = [procZero] :=
    bagSplice_eq_singleton_of_not_bag fun _ equal => by cases equal
  have withContents : bagContents [procDrop, procZero] = [procDrop] := by
    simp only [bagContents, List.flatMap_cons, List.flatMap_nil, spliceDrop, spliceZero,
      List.append_nil, List.singleton_append]
    rw [List.filter_cons, dropKept, if_pos rfl, List.filter_cons, zeroDropped,
      if_neg Bool.false_ne_true, List.filter_nil]
  have onlyContents : bagContents [procDrop] = [procDrop] := by
    simp only [bagContents, List.flatMap_cons, List.flatMap_nil, spliceDrop, List.append_nil]
    rw [List.filter_cons, dropKept, if_pos rfl, List.filter_nil]
  rw [withContents, onlyContents]

end Mettapedia.GSLT.Poly.RhoCalcControl
