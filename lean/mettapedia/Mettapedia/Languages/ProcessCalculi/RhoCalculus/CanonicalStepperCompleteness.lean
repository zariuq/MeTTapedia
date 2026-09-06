import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# The canonical stepper is complete

A runtime that keeps every process in canonical form steps only canonical
representatives.  For that to be a faithful implementation of the
step modulo equations, every step from any representative must be matched,
up to the equations, by a depth-one COMM on the canonical representative.
This module proves that statement for closed rho processes.

The proof inverts the compiled step: a step is a COMM at the top of a
parallel bag or a `ParCong` descent into one component.  In both cases the
communicating pair survives canonicalization (flattening only merges bags,
sorting only reorders them, unit absorption only removes nil), so COMM fires
on the canonical bag at the pair's new positions, and the contractum's
canonical form agrees by the substitution commutation theorem and the bag
laws.  Depth one suffices on canonical bags because their components are
never bags, so no `ParCong` descent can fire.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRuleUsing)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation

set_option autoImplicit false

/-! ## Normalized parallel lists -/

/-- The contents of a list with no unit and no nested bag are the list. -/
theorem bagContents_eq_self :
    ∀ {patterns : List Pattern},
      (∀ pattern ∈ patterns, pattern ≠ .apply "PZero" []) →
      (∀ pattern ∈ patterns, ∀ nested, pattern ≠ .collection .hashBag nested none) →
      bagContents patterns = patterns
  | [], _, _ => rfl
  | pattern :: patterns, noZero, noBag => by
      have splice : bagSplice pattern = [pattern] :=
        bagSplice_eq_singleton_of_not_bag (noBag pattern (by simp))
      have head : bagContents [pattern] = [pattern] := by
        simp [bagContents, splice, noZero pattern (by simp)]
      have tail := bagContents_eq_self (patterns := patterns)
        (fun p membership => noZero p (List.mem_cons_of_mem _ membership))
        (fun p membership => noBag p (List.mem_cons_of_mem _ membership))
      rw [← List.singleton_append, bagContents_append, head, tail]

/-- Members of the canonical parallel list of any elements are canonical,
nonunit, and not bags; the list is its own contents and is fixed by
canonicalization. -/
theorem canonicalList_facts (elements : List Pattern) :
    (∀ member ∈ normalizeBagElements (elements.map canonicalize), IsCanonical member) ∧
    (∀ member ∈ normalizeBagElements (elements.map canonicalize),
      member ≠ .apply "PZero" []) ∧
    (∀ member ∈ normalizeBagElements (elements.map canonicalize),
      ∀ nested, member ≠ .collection .hashBag nested none) := by
  have canonical := isCanonicalList_map_canonicalize' elements
  exact ⟨fun member membership => normalizeBagElements_member_isCanonical canonical membership,
    fun member membership => normalizeBagElements_no_zero membership,
    fun member membership => normalizeBagElements_no_nested_bag canonical membership⟩

theorem bagContents_normalized (elements : List Pattern) :
    bagContents (normalizeBagElements (elements.map canonicalize)) =
      normalizeBagElements (elements.map canonicalize) :=
  bagContents_eq_self (canonicalList_facts elements).2.1 (canonicalList_facts elements).2.2

theorem map_canonicalize_normalized (elements : List Pattern) :
    (normalizeBagElements (elements.map canonicalize)).map canonicalize =
      normalizeBagElements (elements.map canonicalize) := by
  conv_rhs => rw [← List.map_id (normalizeBagElements (elements.map canonicalize))]
  exact List.map_congr_left fun member membership =>
    canonicalize_eq_of_isCanonical ((canonicalList_facts elements).1 member membership)

/-- The canonical form of a parallel bag. -/
theorem canonicalize_bag (elements : List Pattern) :
    canonicalize (.collection .hashBag elements none) =
      collapseBag (normalizeBagElements (elements.map canonicalize)) := by
  simp [canonicalize, canonicalizeList_eq_map]

/-! ## COMM at arbitrary positions of a bag -/

/-- The matcher bindings for a COMM at the given positions. -/
def commBindingsAt (elements : List Pattern) (inputIndex outputIndex : Nat)
    (inputChannel body payload : Pattern) : Bindings :=
  [("q", payload),
   ("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
   ("p", body), ("n", inputChannel)]

/-- COMM fires on any bag holding an input and an output on canonically
equivalent channels, at whatever positions they occupy. -/
theorem rhoStepAt_one_comm {elements : List Pattern} {inputIndex outputIndex : Nat}
    (inputBound : inputIndex < elements.length)
    (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {inputChannel body outputChannel payload : Pattern}
    (inputEq : elements[inputIndex] = .apply "PInput" [inputChannel, .lambda none body])
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] =
      .apply "POutput" [outputChannel, payload])
    (channels : rhoCanonicalEquivalent inputChannel outputChannel = true) :
    RhoStepAt 1 (.collection .hashBag elements none)
      (applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (commBindingsAt elements inputIndex outputIndex inputChannel body payload)) := by
  refine StepAt.rule (rule := rhoCommRewrite)
    (initialBindings := commBindingsAt elements inputIndex outputIndex inputChannel body payload)
    (finalBindings := commBindingsAt elements inputIndex outputIndex inputChannel body payload)
    rhoCommRewrite_mem ?_ (PremisesAt.nil _) rfl
  change _ ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite _
  rw [matchPatternForRule_rhoComm_iff]
  apply MatchRelWith.collection
  refine MatchBagRelWith.cons
    (headBindings := [("p", body), ("n", inputChannel)])
    (tailBindings :=
      [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
       ("q", payload), ("n", outputChannel)])
    inputIndex inputBound ?_ ?_ ?_
  · rw [inputEq]
    apply MatchRelWith.apply
    · apply MatchArgsRelWith.cons MatchRelWith.fvar
      · apply MatchArgsRelWith.cons
        · exact MatchRelWith.lambda MatchRelWith.fvar
        · exact MatchArgsRelWith.nil
        · rfl
      · rfl
    · rfl
  · refine MatchBagRelWith.cons
      (headBindings := [("q", payload), ("n", outputChannel)])
      (tailBindings :=
        [("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none)])
      outputIndex outputBound ?_ ?_ ?_
    · rw [outputEq]
      apply MatchRelWith.apply
      · apply MatchArgsRelWith.cons MatchRelWith.fvar
        · apply MatchArgsRelWith.cons MatchRelWith.fvar MatchArgsRelWith.nil
          rfl
        · rfl
      · rfl
    · exact MatchBagRelWith.nilRest
    · rfl
  · simp [commBindingsAt, mergeBindingsWith, channels]

/-- The contractum of a COMM at given positions, on derived syntax. -/
theorem apply_commBindingsAt
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free bound payload)
    (elements : List Pattern) (inputIndex outputIndex : Nat) (inputChannel : Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (commBindingsAt elements inputIndex outputIndex inputChannel body payload) =
      .collection .hashBag
        (semanticCommSubst body payload ::
          (elements.eraseIdx inputIndex).eraseIdx outputIndex) none := by
  show applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
    (rhoCommMatchedBindings inputChannel body payload
      ((elements.eraseIdx inputIndex).eraseIdx outputIndex)) = _
  rw [rhoComm_apply_exact]
  exact applyBindingsForRule_rhoComm_agrees_derived bodyTyped payloadTyped inputChannel _

/-! ## Inversion of the compiled step -/

/-- A depth-one step is a top-level COMM. -/
theorem rhoStepAt_one_inv {source target : Pattern} (step : RhoStepAt 1 source target) :
    ∃ bindings, bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite source ∧
      applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite bindings = target := by
  cases step with
  | rule membership matched premises applied =>
      rw [rhoCalc_rewrites] at membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · change PremisesAt _ _ _ _ _ [] _ at premises
        cases premises
        exact ⟨_, matched, applied⟩
      · change PremisesAt _ _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first _ =>
            cases first with
            | congruence componentStep _ _ => cases componentStep

/-- Inverting the plain matcher on the `ParCong` frame exposes the selected
component and the residue. -/
theorem rhoParCong_match_shape {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈
      matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite source) :
    ∃ (elements : List Pattern) (termRest : Option String)
      (index : Nat) (indexBound : index < elements.length),
      source = .collection .hashBag elements termRest ∧
      bindings = [("rest", .collection .hashBag (elements.eraseIdx index) none),
        ("S", elements[index])] := by
  rw [matchPatternForRuleUsing_iff_matchRel_of_no_presentation
    rhoParCong_no_matchingPresentation] at matched
  cases matched
  rename_i elements termRest bagMatch
  cases bagMatch
  rename_i headBindings restBindings index indexBound headMatch restMatch merged
  cases headMatch
  cases restMatch
  simp [mergeBindings] at merged
  subst merged
  exact ⟨elements, termRest, index, indexBound, rfl, rfl⟩

/-- A step at depth `fuel + 1` is a top-level COMM or a `ParCong` descent into
one component, whose result is that component's step placed in front of the
residue. -/
theorem rhoStepAt_succ_inv {fuel : Nat} {source target : Pattern}
    (step : RhoStepAt (fuel + 1) source target) :
    (∃ bindings,
        bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite source ∧
        applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite bindings = target) ∨
    (∃ (elements : List Pattern) (termRest : Option String)
        (index : Nat) (indexBound : index < elements.length) (candidate : Pattern),
        source = .collection .hashBag elements termRest ∧
        RhoStepAt fuel elements[index] candidate ∧
        target = .collection .hashBag (candidate :: elements.eraseIdx index) none) := by
  cases step with
  | rule membership matched premises applied =>
      rw [rhoCalc_rewrites] at membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · left
        change PremisesAt _ _ _ _ _ [] _ at premises
        cases premises
        exact ⟨_, matched, applied⟩
      · right
        obtain ⟨elements, termRest, index, indexBound, sourceEq, bindingsEq⟩ :=
          rhoParCong_match_shape matched
        subst sourceEq
        subst bindingsEq
        change PremisesAt _ _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first rest =>
            cases first with
            | @congruence _ _ premiseBindings middle _ _ candidate componentStep
                premiseMatched merged =>
                cases rest
                have premiseEq : premiseBindings = [("T", candidate)] := by
                  simpa [matchPattern] using premiseMatched
                subst premiseEq
                simp [mergeBindings] at merged
                subst merged
                refine ⟨elements, termRest, index, indexBound, candidate, rfl, ?_, ?_⟩
                · simpa [applyBindings] using componentStep
                · rw [← applied]
                  change applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
                  rw [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation]
                  simp [rhoParCongRewrite, applyBindings]

/-! ## Bag bookkeeping -/

theorem bagContents_singleton_of_plain {pattern : Pattern}
    (noZero : pattern ≠ .apply "PZero" [])
    (noBag : ∀ nested, pattern ≠ .collection .hashBag nested none) :
    bagContents [pattern] = [pattern] := by
  have splice : bagSplice pattern = [pattern] := bagSplice_eq_singleton_of_not_bag noBag
  simp [bagContents, splice, noZero]

theorem bagContents_cons (pattern : Pattern) (patterns : List Pattern) :
    bagContents (pattern :: patterns) = bagContents [pattern] ++ bagContents patterns := by
  rw [← List.singleton_append, bagContents_append]

theorem bagContents_cons_plain (pattern : Pattern) (patterns : List Pattern)
    (noZero : pattern ≠ .apply "PZero" [])
    (noBag : ∀ nested, pattern ≠ .collection .hashBag nested none) :
    bagContents (pattern :: patterns) = pattern :: bagContents patterns := by
  rw [bagContents_cons, bagContents_singleton_of_plain noZero noBag, List.singleton_append]

/-- The canonical form of a bag with a distinguished head. -/
theorem canonicalize_bag_cons (head : Pattern) (tail : List Pattern) :
    canonicalize (.collection .hashBag (head :: tail) none) =
      collapseBag (sortPatterns
        (bagContents [canonicalize head] ++ bagContents (tail.map canonicalize))) := by
  rw [canonicalize_bag, normalizeBagElements_eq_sort_bagContents, List.map_cons, bagContents_cons]

/-- Two bags with the same head and tails of the same contents, up to
permutation, have the same canonical form. -/
theorem canonicalize_bag_cons_congr {head head' : Pattern} {tail tail' : List Pattern}
    (headEq : canonicalize head = canonicalize head')
    (tails : List.Perm (bagContents (tail.map canonicalize))
      (bagContents (tail'.map canonicalize))) :
    canonicalize (.collection .hashBag (head :: tail) none) =
      canonicalize (.collection .hashBag (head' :: tail') none) := by
  rw [canonicalize_bag_cons, canonicalize_bag_cons, headEq]
  exact congrArg collapseBag (sortPatterns_eq_of_perm (tails.append_left _))

/-- A normalized list is its own contents after canonicalizing its members. -/
theorem bagContents_map_canonicalize_of_normalized {patterns : List Pattern}
    (canonical : ∀ pattern ∈ patterns, IsCanonical pattern)
    (noZero : ∀ pattern ∈ patterns, pattern ≠ .apply "PZero" [])
    (noBag : ∀ pattern ∈ patterns, ∀ nested, pattern ≠ .collection .hashBag nested none) :
    bagContents (patterns.map canonicalize) = patterns := by
  have fixed : patterns.map canonicalize = patterns := by
    conv_rhs => rw [← List.map_id patterns]
    exact List.map_congr_left fun pattern membership =>
      canonicalize_eq_of_isCanonical (canonical pattern membership)
  rw [fixed]
  exact bagContents_eq_self noZero noBag

/-- Membership in a doubly erased list is membership in the list. -/
theorem mem_of_mem_eraseIdx_eraseIdx {patterns : List Pattern} {i j : Nat} {pattern : Pattern}
    (membership : pattern ∈ (patterns.eraseIdx i).eraseIdx j) : pattern ∈ patterns :=
  List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership)

/-- Inverting the collapse of a normalized list into a bag. -/
theorem collapseBag_eq_bag_inv {patterns elements : List Pattern}
    (noBag : ∀ pattern ∈ patterns, ∀ nested, pattern ≠ .collection .hashBag nested none)
    (equal : collapseBag patterns = .collection .hashBag elements none) :
    patterns = elements := by
  match patterns, equal with
  | [], equal => simp [collapseBag] at equal
  | [pattern], equal =>
      simp only [collapseBag] at equal
      exact absurd equal (noBag pattern (by simp) elements)
  | first :: second :: rest, equal =>
      simp only [collapseBag, Pattern.collection.injEq, true_and, and_true] at equal
      exact equal

/-- Locating two distinct members of a list that is a permutation of the two
members followed by a residue. -/
theorem locate_pair {patterns : List Pattern} {first second : Pattern} {residue : List Pattern}
    (perm : List.Perm patterns (first :: second :: residue)) :
    ∃ (i : Nat) (iBound : i < patterns.length) (j : Nat)
      (jBound : j < (patterns.eraseIdx i).length),
      patterns[i] = first ∧ (patterns.eraseIdx i)[j] = second ∧
        List.Perm ((patterns.eraseIdx i).eraseIdx j) residue := by
  have firstMem : first ∈ patterns := perm.symm.subset (by simp)
  obtain ⟨i, iBound, firstEq⟩ := List.mem_iff_getElem.mp firstMem
  have erased : List.Perm (patterns.eraseIdx i) (second :: residue) := by
    have split := List.getElem_cons_eraseIdx_perm iBound
    rw [firstEq] at split
    exact (split.trans perm).cons_inv
  have secondMem : second ∈ patterns.eraseIdx i := erased.symm.subset (by simp)
  obtain ⟨j, jBound, secondEq⟩ := List.mem_iff_getElem.mp secondMem
  have erasedAgain : List.Perm ((patterns.eraseIdx i).eraseIdx j) residue := by
    have split := List.getElem_cons_eraseIdx_perm jBound
    rw [secondEq] at split
    exact (split.trans erased).cons_inv
  exact ⟨i, iBound, j, jBound, firstEq, secondEq, erasedAgain⟩

/-! ## Closedness bookkeeping -/

/-- Inversion of the derived process judgment at a parallel bag. -/
theorem rho_parallel_wellSorted_inv {free : FreeSortContext} {bound : List String}
    {elements : List Pattern} {termRest : Option String}
    (typed : ProcWellSorted rhoReflectivePresentation free bound
      (.collection .hashBag elements termRest)) :
    termRest = none ∧ ProcListWellSorted rhoReflectivePresentation free bound elements := by
  generalize patternEq : (Pattern.collection .hashBag elements termRest) = pattern at typed
  cases typed <;> simp [rhoReflectivePresentation] at patternEq
  rename_i elementsTyped
  rcases patternEq with ⟨rfl, rfl⟩
  exact ⟨rfl, elementsTyped⟩

/-- Every member of a closed bag is closed. -/
theorem closed_member {free : FreeSortContext} {elements : List Pattern} {termRest : Option String}
    (typed : ProcWellSorted rhoReflectivePresentation free []
      (.collection .hashBag elements termRest))
    (safe : binderSafeAt "NQuote" 0 (.collection .hashBag elements termRest) = true)
    {member : Pattern} (membership : member ∈ elements) :
    ProcWellSorted rhoReflectivePresentation free [] member ∧
      binderSafeAt "NQuote" 0 member = true := by
  obtain ⟨_, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
  refine ⟨procListWellSorted_iff_forall_mem.mp elementsTyped member membership, ?_⟩
  have listSafe : binderSafeListAt "NQuote" 0 elements = true := by
    simpa [binderSafeAt] using safe
  exact (binderSafeListAt_eq_true_iff _ _ _).mp listSafe member membership

/-- The canonical form of a closed process is closed. -/
theorem closed_canonicalize {free : FreeSortContext} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] process)
    (safe : binderSafeAt "NQuote" 0 process = true) :
    ProcWellSorted rhoReflectivePresentation free [] (canonicalize process) ∧
      binderSafeAt "NQuote" 0 (canonicalize process) = true :=
  ⟨canonicalize_procWellSorted [] typed, canonicalize_binderSafeAt process 0 safe⟩

/-- The compiled channel comparator decides canonical equality. -/
theorem rhoCanonicalEquivalent_iff (left right : Pattern) :
    rhoCanonicalEquivalent left right = true ↔ canonicalize left = canonicalize right := by
  rw [rhoCanonicalEquivalent, Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalEquivalent_eq_true_iff,
    derivedCanonicalize_eq, derivedCanonicalize_eq]

/-- Canonical channel equivalence survives canonicalizing both channels. -/
theorem rhoCanonicalEquivalent_canonicalize {left right : Pattern}
    (equivalent : rhoCanonicalEquivalent left right = true) :
    rhoCanonicalEquivalent (canonicalize left) (canonicalize right) = true := by
  rw [rhoCanonicalEquivalent_iff] at equivalent ⊢
  rw [canonicalize_idempotent, canonicalize_idempotent]
  exact equivalent

theorem canonicalize_input (channel body : Pattern) :
    canonicalize (.apply "PInput" [channel, .lambda none body]) =
      .apply "PInput" [canonicalize channel, .lambda none (canonicalize body)] := by
  rw [canonicalize_apply_general "PInput" _ (by simp)]
  simp [canonicalizeList, canonicalize]

theorem canonicalize_output (channel payload : Pattern) :
    canonicalize (.apply "POutput" [channel, payload]) =
      .apply "POutput" [canonicalize channel, canonicalize payload] := by
  rw [canonicalize_apply_general "POutput" _ (by simp)]
  simp [canonicalizeList]

/-! ## One COMM on a canonical bag from a pair among its members -/

/-- Given a canonical parallel list holding, up to permutation, a canonical
input and output on equivalent channels plus a residue, COMM fires on the
bag at depth one and the contractum is the substitution result in front of a
list with the residue's contents. -/
theorem canonical_comm_of_pair
    {free : FreeSortContext} {elements : List Pattern}
    {inputChannel body outputChannel payload : Pattern} {residue : List Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      (rhoReflectivePresentation.nameSort :: []) body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (channels : rhoCanonicalEquivalent inputChannel outputChannel = true)
    (perm : List.Perm (normalizeBagElements (elements.map canonicalize))
      (.apply "PInput" [inputChannel, .lambda none body] ::
        .apply "POutput" [outputChannel, payload] :: residue)) :
    ∃ tail, RhoStepAt 1 (canonicalize (.collection .hashBag elements none))
        (.collection .hashBag (semanticCommSubst body payload :: tail) none) ∧
      List.Perm (bagContents (tail.map canonicalize)) residue := by
  obtain ⟨i, iBound, j, jBound, inputEq, outputEq, tailPerm⟩ := locate_pair perm
  have twoElements : 2 ≤ (normalizeBagElements (elements.map canonicalize)).length := by
    rw [perm.length_eq]
    simp
  refine ⟨(normalizeBagElements (elements.map canonicalize)).eraseIdx i |>.eraseIdx j, ?_, ?_⟩
  · rw [canonicalize_bag, collapseBag_eq_bag_of_length_ge_two twoElements]
    have step := rhoStepAt_one_comm iBound jBound inputEq outputEq channels
    rwa [apply_commBindingsAt bodyTyped payloadTyped] at step
  · have facts := canonicalList_facts elements
    have subset : ∀ pattern ∈ ((normalizeBagElements (elements.map canonicalize)).eraseIdx i
        |>.eraseIdx j), pattern ∈ normalizeBagElements (elements.map canonicalize) :=
      fun pattern membership => mem_of_mem_eraseIdx_eraseIdx membership
    rw [bagContents_map_canonicalize_of_normalized
      (fun pattern membership => facts.1 pattern (subset pattern membership))
      (fun pattern membership => facts.2.1 pattern (subset pattern membership))
      (fun pattern membership => facts.2.2 pattern (subset pattern membership))]
    exact tailPerm

/-! ## The keystone -/

/-- Every step from a closed process is matched, up to canonical form, by a
depth-one COMM on its canonical representative. -/
theorem canonicalStep_complete {free : FreeSortContext} :
    ∀ (fuel : Nat) {source target : Pattern},
      ProcWellSorted rhoReflectivePresentation free [] source →
      binderSafeAt "NQuote" 0 source = true →
      RhoStepAt fuel source target →
      ∃ target', RhoStepAt 1 (canonicalize source) target' ∧
        canonicalize target' = canonicalize target := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target _ _ step
      cases step
  | succ fuel inductionHypothesis =>
      intro source target sourceTyped sourceSafe step
      rcases rhoStepAt_succ_inv step with
        ⟨bindings, matched, applied⟩ |
        ⟨elements, termRest, index, indexBound, candidate, sourceEq, componentStep, targetEq⟩
      · -- a top-level COMM
        obtain ⟨elements, termRest, i, iBound, j, jBound, inputChannel, body, inputBinder,
          outputChannel, payload, sourceEq, inputEq, outputEq, channels, bindingsEq⟩ :=
            rhoComm_match_shape matched
        subst sourceEq
        subst bindingsEq
        obtain ⟨restEq, _⟩ := rho_parallel_wellSorted_inv sourceTyped
        subst restEq
        have inputMember : elements[i] ∈ elements := List.getElem_mem iBound
        have outputMember : (elements.eraseIdx i)[j] ∈ elements :=
          List.mem_of_mem_eraseIdx (List.getElem_mem jBound)
        obtain ⟨inputTyped, inputSafe⟩ := closed_member sourceTyped sourceSafe inputMember
        obtain ⟨outputTyped, outputSafe⟩ := closed_member sourceTyped sourceSafe outputMember
        rw [inputEq] at inputTyped inputSafe
        rw [outputEq] at outputTyped outputSafe
        obtain ⟨binderEq, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
        subst binderEq
        obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
        obtain ⟨_, bodySafe⟩ := binderSafe_of_input inputSafe
        have targetEq : target =
            .collection .hashBag (semanticCommSubst body payload ::
              (elements.eraseIdx i).eraseIdx j) none := by
          rw [← applied]
          exact apply_commBindingsAt bodyTyped payloadTyped elements i j inputChannel
        subst targetEq
        -- the pair survives canonicalization
        have elementsPerm : List.Perm elements
            (elements[i] :: (elements.eraseIdx i)[j] :: (elements.eraseIdx i).eraseIdx j) :=
          ((List.getElem_cons_eraseIdx_perm jBound).cons _ |>.trans
            (List.getElem_cons_eraseIdx_perm iBound)).symm
        rw [inputEq, outputEq] at elementsPerm
        have canonicalPerm : List.Perm (normalizeBagElements (elements.map canonicalize))
            (.apply "PInput" [canonicalize inputChannel, .lambda none (canonicalize body)] ::
              .apply "POutput" [canonicalize outputChannel, canonicalize payload] ::
                bagContents (((elements.eraseIdx i).eraseIdx j).map canonicalize)) := by
          rw [normalizeBagElements_eq_of_perm (elementsPerm.map canonicalize)]
          rw [normalizeBagElements_eq_sort_bagContents, List.map_cons, List.map_cons,
            canonicalize_input, canonicalize_output,
            bagContents_cons_plain _ _ (by simp) (by simp),
            bagContents_cons_plain _ _ (by simp) (by simp)]
          exact (sortPatterns_perm _).symm
        obtain ⟨tail, canonicalStep, tailPerm⟩ := canonical_comm_of_pair
          (canonicalize_procWellSorted _ bodyTyped) (canonicalize_procWellSorted _ payloadTyped)
          (rhoCanonicalEquivalent_canonicalize channels) canonicalPerm
        refine ⟨_, canonicalStep, ?_⟩
        exact canonicalize_bag_cons_congr
          (canonicalize_semanticCommSubst_canonicalize bodyTyped bodySafe
            (rhoProcWellSorted_hashSetFree payloadTyped))
          tailPerm
      · -- a ParCong descent into one component
        subst sourceEq
        subst targetEq
        obtain ⟨restEq, _⟩ := rho_parallel_wellSorted_inv sourceTyped
        subst restEq
        have componentMember : elements[index] ∈ elements := List.getElem_mem indexBound
        obtain ⟨componentTyped, componentSafe⟩ :=
          closed_member sourceTyped sourceSafe componentMember
        obtain ⟨candidate', canonicalComponentStep, candidateEq⟩ :=
          inductionHypothesis componentTyped componentSafe componentStep
        obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv canonicalComponentStep
        obtain ⟨inner, innerRest, i, iBound, j, jBound, inputChannel, body, inputBinder,
          outputChannel, payload, innerEq, inputEq, outputEq, channels, bindingsEq⟩ :=
            rhoComm_match_shape matched
        subst bindingsEq
        obtain ⟨canonicalTyped, canonicalSafe⟩ := closed_canonicalize componentTyped componentSafe
        rw [innerEq] at canonicalTyped canonicalSafe
        obtain ⟨innerRestEq, _⟩ := rho_parallel_wellSorted_inv canonicalTyped
        subst innerRestEq
        have inputMember : inner[i] ∈ inner := List.getElem_mem iBound
        have outputMember : (inner.eraseIdx i)[j] ∈ inner :=
          List.mem_of_mem_eraseIdx (List.getElem_mem jBound)
        obtain ⟨inputTyped, _⟩ := closed_member canonicalTyped canonicalSafe inputMember
        obtain ⟨outputTyped, _⟩ := closed_member canonicalTyped canonicalSafe outputMember
        rw [inputEq] at inputTyped
        rw [outputEq] at outputTyped
        obtain ⟨binderEq, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
        subst binderEq
        obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
        have candidate'Eq : candidate' =
            .collection .hashBag (semanticCommSubst body payload ::
              (inner.eraseIdx i).eraseIdx j) none := by
          rw [← applied]
          exact apply_commBindingsAt bodyTyped payloadTyped inner i j inputChannel
        subst candidate'Eq
        -- the inner canonical list is normalized
        have innerCanonical : IsCanonical (.collection .hashBag inner none) := by
          rw [← innerEq]
          exact canonicalize_isCanonical _
        obtain ⟨_, _, innerPlain, innerList⟩ := innerCanonical
        have innerNoZero : ∀ p ∈ inner, p ≠ .apply "PZero" [] :=
          fun p membership => (innerPlain p membership).1
        have innerNoBag : ∀ p ∈ inner, ∀ nested, p ≠ .collection .hashBag nested none :=
          fun p membership => (innerPlain p membership).2
        have innerIsCanonical : ∀ p ∈ inner, IsCanonical p :=
          fun _ membership => isCanonicalList_mem innerList membership
        have innerSub : ∀ p ∈ (inner.eraseIdx i).eraseIdx j, p ∈ inner :=
          fun p membership => mem_of_mem_eraseIdx_eraseIdx membership
        -- the outer canonical list holds the pair and the residue
        have outerPerm : List.Perm (normalizeBagElements (elements.map canonicalize))
            (.apply "PInput" [inputChannel, .lambda none body] ::
              .apply "POutput" [outputChannel, payload] ::
                ((inner.eraseIdx i).eraseIdx j ++
                  bagContents ((elements.eraseIdx index).map canonicalize))) := by
          have elementsPerm : List.Perm elements (elements[index] :: elements.eraseIdx index) :=
            (List.getElem_cons_eraseIdx_perm indexBound).symm
          rw [normalizeBagElements_eq_of_perm (elementsPerm.map canonicalize),
            normalizeBagElements_eq_sort_bagContents, List.map_cons, innerEq, bagContents_cons]
          have innerContents : bagContents [.collection .hashBag inner none] = inner := by
            simp only [bagContents, List.flatMap_cons, List.flatMap_nil, bagSplice,
              List.append_nil]
            exact List.filter_eq_self.mpr (fun p membership => by
              simpa using innerNoZero p membership)
          rw [innerContents]
          have innerPerm : List.Perm inner
              (inner[i] :: (inner.eraseIdx i)[j] :: (inner.eraseIdx i).eraseIdx j) :=
            ((List.getElem_cons_eraseIdx_perm jBound).cons _ |>.trans
              (List.getElem_cons_eraseIdx_perm iBound)).symm
          rw [inputEq, outputEq] at innerPerm
          exact (sortPatterns_perm _).symm.trans (innerPerm.append_right _)
        obtain ⟨tail, canonicalStep, tailPerm⟩ :=
          canonical_comm_of_pair bodyTyped payloadTyped channels outerPerm
        refine ⟨_, canonicalStep, ?_⟩
        rw [canonicalize_bag_cons, canonicalize_bag_cons, ← candidateEq, canonicalize_bag]
        have candidateContents : bagContents [collapseBag (normalizeBagElements
            ((semanticCommSubst body payload :: (inner.eraseIdx i).eraseIdx j).map
              canonicalize))] =
            normalizeBagElements
              ((semanticCommSubst body payload :: (inner.eraseIdx i).eraseIdx j).map
                canonicalize) :=
          bagContents_collapse_normalized (isCanonicalList_map_canonicalize' _)
        rw [candidateContents, normalizeBagElements_eq_sort_bagContents, List.map_cons,
          bagContents_cons (canonicalize (semanticCommSubst body payload))
            (List.map canonicalize ((inner.eraseIdx i).eraseIdx j)),
          bagContents_map_canonicalize_of_normalized
            (fun p membership => innerIsCanonical p (innerSub p membership))
            (fun p membership => innerNoZero p (innerSub p membership))
            (fun p membership => innerNoBag p (innerSub p membership))]
        apply congrArg collapseBag
        apply sortPatterns_eq_of_perm
        exact (tailPerm.append_left _).trans
          ((List.Perm.of_eq (List.append_assoc _ _ _).symm).trans
            ((sortPatterns_perm _).append_right _))

/-- The keystone for the least relation. -/
theorem canonicalStep_complete_of_rhoStep {free : FreeSortContext} {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (step : RhoStep source target) :
    ∃ target', RhoStepAt 1 (canonicalize source) target' ∧
      canonicalize target' = canonicalize target := by
  obtain ⟨fuel, bounded⟩ := step
  exact canonicalStep_complete fuel sourceTyped sourceSafe bounded

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
