import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
import Mettapedia.OSLF.MeTTaIL.ReflectiveCoherentSubstitution

/-!
# Steps on canonical representatives

Our rho calculus identifies terms by its declared equations
(`rhoReflectivePresentation`: quote-drop, and unit, associativity and
commutativity of parallel composition); two terms are equal when their
canonical forms are. Its step relation `RhoStep`, compiled from the authored
rules COMM and `ParCong`, reads a parallel bag as it is written: COMM selects an
input and an output among the members of one bag, and `ParCong` steps one member.

* `RhoStep` is not closed under the equations. `nestedRedex`, an output and the
  unit in an inner bag beside an input on the same channel, has no step, while
  its canonical form steps (`rhoStep_not_closed_under_canonical_equality`).
* Steps are coherent with canonical forms. Every step from any term is matched,
  up to the equations, by a step from its canonical form
  (`rhoStep_canonicalize`). No hypothesis on the term is needed: COMM compares
  channels by canonical equality, its contractum depends only on the canonical
  forms of body and payload (`canonicalize_commContractum`), and a step inside a
  member survives flattening and reordering of the enclosing bags.
* Rewriting modulo the equations is therefore complete on canonical
  representatives (`stepModulo_complete`, `stepModulo_iff_canonicalStep`). An
  engine must step canonical representatives, or equivalently step modulo the
  equations; doing so loses no step.

`CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep` proves a
stronger conclusion, a COMM at the top of the canonical form, for closed
well-sorted sources. That conclusion needs a hypothesis: a member that is a bag
with a rest variable is not flattened by canonicalization, and a step inside it
is a `ParCong` step (`top_comm_fails_with_rest`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent
  (canonicalize_parallel_eq canonicalize_substituteResolved_resolveQuotes
    canonicalize_normalizeReflective finish_long finish_not_quote)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings mergeBindings mergeBindingsWith matchPattern
  applyBindings applyRuleBindings applyBindingsScoped_zero_of_binderFree binderFree)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel)
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec (MatchRelWith MatchArgsRelWith MatchBagRelWith)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
  (matchPatternForRuleUsing_iff_matchRel_of_no_presentation)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (StepAt PremisesAt PremiseAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (RhoStepAt RhoStep rhoRuleInterpretation rhoBasePremises rhoComm_match_shape rhoComm_apply_exact
    rhoCommMatchedBindings rhoParCong_match_shape rhoParCong_no_substitutionPresentation
    rhoParCong_no_matchingPresentation)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
  (rhoCommRewrite_mem applyBindingsForRule_rhoComm matchPatternForRule_rhoComm_iff)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch (rhoCanonicalEquivalent)
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns sortPatterns_eq_of_perm)

/-! ## The shape of a step -/

/-- Every step of our calculus is a COMM between an input and an output of one
parallel bag, or a step of one member of a parallel bag. -/
theorem rhoStepAt_cases {fuel : Nat} {source target : Pattern}
    (step : RhoStepAt fuel source target) :
    (∃ (elements : List Pattern) (termRest : Option String) (inputIndex : Nat)
        (inputBound : inputIndex < elements.length) (outputIndex : Nat)
        (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
        (inputChannel body : Pattern) (binder : Option String) (outputChannel payload : Pattern),
      source = .collection .hashBag elements termRest ∧
      elements[inputIndex] = .apply "PInput" [inputChannel, .lambda binder body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutput" [outputChannel, payload] ∧
      canonicalize rhoReflectivePresentation inputChannel =
        canonicalize rhoReflectivePresentation outputChannel ∧
      target = .collection .hashBag
        (substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation payload]) body ::
          (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) ∨
    (∃ (smaller : Nat) (elements : List Pattern) (termRest : Option String) (index : Nat)
        (indexBound : index < elements.length) (candidate : Pattern),
      fuel = smaller + 1 ∧ source = .collection .hashBag elements termRest ∧
      RhoStepAt smaller elements[index] candidate ∧
      target = .collection .hashBag (candidate :: elements.eraseIdx index) none) := by
  cases step with
  | @rule smaller _ _ rule initial final ruleMember matched premises targetEq =>
  change rule ∈ [rhoCommRewrite, rhoParCongRewrite] at ruleMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with rfl | rfl
  · left
    cases premises
    obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
      inputChannel, body, binder, outputChannel, payload, sourceEq, inputEq, outputEq,
      channels, bindingsEq⟩ := rhoComm_match_shape matched
    refine ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel,
      body, binder, outputChannel, payload, sourceEq, inputEq, outputEq,
      canonicalEquivalent_eq_true_iff.mp channels, ?_⟩
    rw [← targetEq]
    subst bindingsEq
    change applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
      (rhoCommMatchedBindings inputChannel body payload _) = _
    rw [rhoComm_apply_exact, applyBindingsForRule_rhoComm]
  · right
    obtain ⟨elements, termRest, index, indexBound, selected, sourceEq, selectedEq, initialEq⟩ :=
      rhoParCong_match_shape matched
    subst initialEq
    change PremisesAt rhoRuleInterpretation rhoBasePremises rhoCalc smaller
      [("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", selected)]
      [.congruence (.fvar "S") (.fvar "T")] final at premises
    cases premises with
    | cons firstPremise remainingPremises =>
    cases remainingPremises
    cases firstPremise with
    | congruence recursiveStep targetMatch merged =>
    rename_i premiseBindings candidate
    simp [matchPattern] at targetMatch
    subst premiseBindings
    simp [mergeBindings] at merged
    subst final
    have innerStep : RhoStepAt smaller selected candidate := by
      simpa [applyBindings, Bindings.lookup] using recursiveStep
    refine ⟨smaller, elements, termRest, index, indexBound, candidate, rfl, sourceEq,
      selectedEq ▸ innerStep, ?_⟩
    rw [← targetEq]
    change applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
    simp only [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation,
      applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
        (by decide : binderFree rhoParCongRewrite.right = true)]
    simp [rhoParCongRewrite, applyBindings]

/-- Only a parallel bag steps. -/
theorem rhoStepAt_source_bag {fuel : Nat} {source target : Pattern}
    (step : RhoStepAt fuel source target) :
    ∃ elements termRest, source = .collection .hashBag elements termRest := by
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, _, _, _, _, _, _, _, _, _, sourceEq, _⟩ |
    ⟨_, elements, termRest, _, _, _, _, sourceEq, _⟩
  · exact ⟨elements, termRest, sourceEq⟩
  · exact ⟨elements, termRest, sourceEq⟩

/-! ## Constructing steps -/

/-- COMM fires between any input and any output of a parallel bag whose channels
have the same canonical form, whatever the binder hint and the rest variable. -/
theorem rhoStepAt_comm_at {elements : List Pattern} {termRest : Option String}
    {inputIndex outputIndex : Nat}
    (inputBound : inputIndex < elements.length)
    (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
    {inputChannel body outputChannel payload : Pattern} {binder : Option String}
    (inputEq : elements[inputIndex] = .apply "PInput" [inputChannel, .lambda binder body])
    (outputEq : (elements.eraseIdx inputIndex)[outputIndex] =
      .apply "POutput" [outputChannel, payload])
    (channels : canonicalize rhoReflectivePresentation inputChannel =
      canonicalize rhoReflectivePresentation outputChannel) :
    RhoStepAt 1 (.collection .hashBag elements termRest)
      (.collection .hashBag
        (substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation payload]) body ::
          (elements.eraseIdx inputIndex).eraseIdx outputIndex) none) := by
  have equivalent : rhoCanonicalEquivalent inputChannel outputChannel = true :=
    canonicalEquivalent_eq_true_iff.mpr channels
  refine .rule rhoCommRewrite_mem (initialBindings := rhoCommMatchedBindings inputChannel body
    payload ((elements.eraseIdx inputIndex).eraseIdx outputIndex)) ?_ (.nil _) ?_
  · change _ ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite _
    rw [matchPatternForRule_rhoComm_iff]
    apply MatchRelWith.collection (by decide)
    apply MatchBagRelWith.cons inputIndex inputBound
    · rw [inputEq]
      apply MatchRelWith.apply
      · apply MatchArgsRelWith.cons MatchRelWith.fvar
        · apply MatchArgsRelWith.cons
          · exact MatchRelWith.lambda MatchRelWith.fvar
          · exact MatchArgsRelWith.nil
          · rfl
        · rfl
      · rfl
    · apply MatchBagRelWith.cons outputIndex outputBound
      · rw [outputEq]
        apply MatchRelWith.apply
        · apply MatchArgsRelWith.cons MatchRelWith.fvar
          · apply MatchArgsRelWith.cons MatchRelWith.fvar MatchArgsRelWith.nil
            rfl
          · rfl
        · rfl
      · exact MatchBagRelWith.nilRest
      · rfl
    · simp [rhoCommMatchedBindings, mergeBindingsWith, equivalent]
  · change applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
      (rhoCommMatchedBindings inputChannel body payload _) = _
    rw [rhoComm_apply_exact, applyBindingsForRule_rhoComm]

/-- `ParCong` steps any member of a parallel bag, whatever its rest variable. -/
theorem rhoStepAt_par_at {fuel : Nat} {elements : List Pattern} {termRest : Option String}
    {index : Nat} (indexBound : index < elements.length) {candidate : Pattern}
    (step : RhoStepAt fuel elements[index] candidate) :
    RhoStepAt (fuel + 1) (.collection .hashBag elements termRest)
      (.collection .hashBag (candidate :: elements.eraseIdx index) none) := by
  refine .rule (rule := rhoParCongRewrite) (by simp [rhoCalc])
    (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx index) none),
      ("S", elements[index])])
    (finalBindings := [("T", candidate),
      ("rest", .collection .hashBag (elements.eraseIdx index) none), ("S", elements[index])])
    ?_ ?_ ?_
  · change _ ∈ matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite _
    rw [matchPatternForRuleUsing_iff_matchRel_of_no_presentation
      rhoParCong_no_matchingPresentation]
    apply MatchRel.collection (by decide)
    exact MatchBagRel.cons index indexBound MatchRel.fvar MatchBagRel.nilRest rfl
  · change PremisesAt rhoRuleInterpretation rhoBasePremises rhoCalc fuel _
      [.congruence (.fvar "S") (.fvar "T")] _
    refine .cons (.congruence (candidate := candidate) (premiseBindings := [("T", candidate)])
      ?_ ?_ ?_) (.nil _)
    · simpa [applyBindings, Bindings.lookup] using step
    · simp [matchPattern]
    · rfl
  · change applyBindingsForRuleUsing rhoReflectionProfile rhoParCongRewrite _ = _
    simp only [applyBindingsForRuleUsing, rhoParCong_no_substitutionPresentation,
      applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
        (by decide : binderFree rhoParCongRewrite.right = true)]
    simp [rhoParCongRewrite, applyBindings]

/-! ## The contractum sees only canonical forms -/

section Substitution

variable (declaration : ReflectivePresentationDecl)

private theorem canonicalize_collection_congr (kind : CollType) (rest : Option String)
    {left right : List Pattern}
    (same : left.map (canonicalize declaration) = right.map (canonicalize declaration)) :
    canonicalize declaration (.collection kind left rest) =
      canonicalize declaration (.collection kind right rest) := by
  cases rest <;> simp only [canonicalize, canonicalizeList_eq_map, same]

private theorem canonicalize_apply_congr (constructor : String) {left right : List Pattern}
    (same : left.map (canonicalize declaration) = right.map (canonicalize declaration)) :
    canonicalize declaration (.apply constructor left) =
      canonicalize declaration (.apply constructor right) := by
  simp only [canonicalize, canonicalizeList_eq_map, same]

/-- **Binder elimination sees only canonical forms of what it substitutes.** Two
index actions whose values have the same canonical forms, and whose received
processes at the eliminated binder have the same canonical forms, give results
with the same canonical form, for every declaration, body and depth. -/
theorem canonicalize_substituteResolved_congr {first second : Nat → Nat → Pattern}
    (values : ∀ level index, canonicalize declaration (first level index) =
      canonicalize declaration (second level index))
    (received : ∀ level,
      canonicalize declaration
          (receive declaration declaration.dropConstructor (first level level)) =
        canonicalize declaration
          (receive declaration declaration.dropConstructor (second level level)))
    (body : Pattern) : ∀ depth : Nat,
    canonicalize declaration (substituteResolved declaration first depth body) =
      canonicalize declaration (substituteResolved declaration second depth body) := by
  induction body using Pattern.inductionOn with
  | hbvar index => intro depth; exact values depth index
  | hfvar name => intro depth; rfl
  | hlambda binder body ih =>
      intro depth; simp only [substituteResolved, canonicalize, ih (depth + 1)]
  | hmultiLambda arity binders body ih =>
      intro depth; simp only [substituteResolved, canonicalize, ih (depth + arity)]
  | hsubst body value ihBody ihValue =>
      intro depth
      simp only [substituteResolved, canonicalize, ihBody (depth + 1), ihValue depth]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substituteResolved, substituteResolvedList_eq_map]
      apply canonicalize_collection_congr
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left fun pattern member => ih pattern member depth
  | happly constructor arguments ih =>
      intro depth
      match arguments, ih with
      | [], _ => rfl
      | [payload], ih =>
          have payloadSame := ih payload (by simp) depth
          by_cases quoted : constructor = declaration.quoteConstructor
          · simp only [substituteResolved, quoted, if_true]
          · by_cases dropped : constructor = declaration.dropConstructor
            · subst dropped
              simp only [substituteResolved, quoted, if_false, if_true]
              split
              · exact received depth
              · apply canonicalize_apply_congr
                simp [payloadSame]
            · simp only [substituteResolved, quoted, dropped, if_false]
              apply canonicalize_apply_congr
              simp [payloadSame]
      | first :: second :: rest, ih =>
          simp only [substituteResolved, substituteResolvedList_eq_map]
          apply canonicalize_apply_congr
          simp only [List.map_map, Function.comp_def]
          exact List.map_congr_left fun pattern member => ih pattern member depth

end Substitution

private theorem rho_distinct :
    rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor ≠
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
  decide

/-- **The COMM contractum sees only canonical forms**: substituting the quoted
payload into the body gives the canonical form obtained from the canonical body
and the canonical payload, for every body and payload. -/
theorem canonicalize_commContractum (body payload : Pattern) :
    canonicalize rhoReflectivePresentation
        (substituteReflective rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation payload]) body) =
      canonicalize rhoReflectivePresentation
        (substituteReflective rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
            (canonicalize rhoReflectivePresentation payload)])
          (canonicalize rhoReflectivePresentation body)) := by
  unfold substituteReflective
  rw [canonicalize_substituteResolved_resolveQuotes, canonicalize_substituteResolved_resolveQuotes,
    canonicalize_idempotent]
  have payloads : canonicalize rhoReflectivePresentation
        (normalizeReflective rhoReflectivePresentation payload) =
      canonicalize rhoReflectivePresentation (normalizeReflective rhoReflectivePresentation
        (canonicalize rhoReflectivePresentation payload)) := by
    rw [canonicalize_normalizeReflective rho_distinct,
      canonicalize_normalizeReflective rho_distinct, canonicalize_idempotent]
  apply canonicalize_substituteResolved_congr
  · intro level index
    by_cases hit : index = level
    · simp only [hit, if_true, canonicalize, canonicalizeList, payloads]
    · simp only [hit, if_false]
  · intro level
    simpa [receive, rhoReflectivePresentation] using payloads

/-! ## Canonical forms of parallel bags -/

private theorem canonicalize_hashBag (elements : List Pattern) :
    canonicalize rhoReflectivePresentation (.collection .hashBag elements none) =
      collapseParallel rhoReflectivePresentation
        (normalizeParallelElements rhoReflectivePresentation
          (elements.map (canonicalize rhoReflectivePresentation))) :=
  canonicalize_parallel_eq elements

private theorem canonicalize_hashBag_rest (elements : List Pattern) (rest : String) :
    canonicalize rhoReflectivePresentation (.collection .hashBag elements (some rest)) =
      .collection .hashBag (elements.map (canonicalize rhoReflectivePresentation)) (some rest) := by
  simp [canonicalize, canonicalizeList_eq_map]

private theorem canonicalList (patterns : List Pattern) :
    IsCanonicalList rhoReflectivePresentation
      (patterns.map (canonicalize rhoReflectivePresentation)) := by
  rw [← canonicalizeList_eq_map]
  exact canonicalizeList_isCanonical _ _

/-- Two bags have the same canonical form when the parallel members of their
canonicalized elements agree up to order. -/
theorem canonicalize_hashBag_eq_of_perm {left right : List Pattern}
    (same : (parallelContents rhoReflectivePresentation
        (left.map (canonicalize rhoReflectivePresentation))).Perm
      (parallelContents rhoReflectivePresentation
        (right.map (canonicalize rhoReflectivePresentation)))) :
    canonicalize rhoReflectivePresentation (.collection .hashBag left none) =
      canonicalize rhoReflectivePresentation (.collection .hashBag right none) := by
  rw [canonicalize_hashBag, canonicalize_hashBag, normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents, sortPatterns_eq_of_perm same]

private theorem contents_cons (pattern : Pattern) (patterns : List Pattern) :
    parallelContents rhoReflectivePresentation
        ((pattern :: patterns).map (canonicalize rhoReflectivePresentation)) =
      parallelContents rhoReflectivePresentation [canonicalize rhoReflectivePresentation pattern] ++
        parallelContents rhoReflectivePresentation
          (patterns.map (canonicalize rhoReflectivePresentation)) := by
  rw [List.map_cons, ← List.singleton_append, parallelContents_append]

private theorem contents_append (left right : List Pattern) :
    parallelContents rhoReflectivePresentation
        ((left ++ right).map (canonicalize rhoReflectivePresentation)) =
      parallelContents rhoReflectivePresentation
          (left.map (canonicalize rhoReflectivePresentation)) ++
        parallelContents rhoReflectivePresentation
          (right.map (canonicalize rhoReflectivePresentation)) := by
  rw [List.map_append, parallelContents_append]

private theorem contents_perm {left right : List Pattern} (permutation : left.Perm right) :
    (parallelContents rhoReflectivePresentation
        (left.map (canonicalize rhoReflectivePresentation))).Perm
      (parallelContents rhoReflectivePresentation
        (right.map (canonicalize rhoReflectivePresentation))) :=
  parallelContents_perm _ (permutation.map _)

/-- The parallel members of a canonical bag are those of its canonicalized
elements. -/
private theorem contents_canonicalize_hashBag (elements : List Pattern) :
    (parallelContents rhoReflectivePresentation
        [canonicalize rhoReflectivePresentation (.collection .hashBag elements none)]).Perm
      (parallelContents rhoReflectivePresentation
        (elements.map (canonicalize rhoReflectivePresentation))) := by
  rw [canonicalize_hashBag, parallelContents_collapse_normalized _ (canonicalList elements),
    normalizeParallelElements_eq_sort_parallelContents]
  exact sortPatterns_perm _

/-- A member of a parallel bag: neither the unit nor a bag without rest variable. -/
private def Plain (pattern : Pattern) : Prop :=
  pattern ≠ .apply "PZero" [] ∧ ∀ nested, pattern ≠ .collection .hashBag nested none

/-- Every parallel member of canonicalized terms is canonical and plain. -/
private theorem member_facts {patterns : List Pattern} {member : Pattern}
    (membership : member ∈ parallelContents rhoReflectivePresentation
      (patterns.map (canonicalize rhoReflectivePresentation))) :
    canonicalize rhoReflectivePresentation member = member ∧ Plain member := by
  have sorted : member ∈ normalizeParallelElements rhoReflectivePresentation
      (patterns.map (canonicalize rhoReflectivePresentation)) := by
    rw [normalizeParallelElements_eq_sort_parallelContents]
    exact sortPatterns_mem_iff.mpr membership
  exact ⟨canonicalize_eq_of_isCanonical _
      (normalizeParallelElements_member_isCanonical (canonicalList patterns) sorted),
    normalizeParallelElements_no_unit sorted,
    normalizeParallelElements_no_nested (canonicalList patterns) sorted⟩

/-- A list of plain members is its own parallel contents. -/
private theorem parallelContents_of_plain {patterns : List Pattern}
    (plain : ∀ member ∈ patterns, Plain member) :
    parallelContents rhoReflectivePresentation patterns = patterns := by
  unfold parallelContents
  rw [flatMap_parallelSplice_eq_self _ (fun member found => (plain member found).2)]
  exact List.filter_eq_self.mpr (fun member found => decide_eq_true (plain member found).1)

/-- The parallel contents of canonicalized terms are fixed by canonicalizing
them again. -/
private theorem contents_contents (patterns : List Pattern) :
    parallelContents rhoReflectivePresentation
        ((parallelContents rhoReflectivePresentation
          (patterns.map (canonicalize rhoReflectivePresentation))).map
          (canonicalize rhoReflectivePresentation)) =
      parallelContents rhoReflectivePresentation
        (patterns.map (canonicalize rhoReflectivePresentation)) := by
  rw [List.map_congr_left (fun member found => (member_facts found).1), List.map_id']
  exact parallelContents_of_plain (fun member found => (member_facts found).2)

private theorem map_canonicalize_twice (patterns : List Pattern) :
    (patterns.map (canonicalize rhoReflectivePresentation)).map
        (canonicalize rhoReflectivePresentation) =
      patterns.map (canonicalize rhoReflectivePresentation) := by
  rw [List.map_map]
  exact List.map_congr_left fun pattern _ => canonicalize_idempotent _ pattern

/-! ## Lifting a step into a larger bag -/

private theorem locate {listed rest : List Pattern} {member : Pattern}
    (arranged : listed.Perm (member :: rest)) :
    ∃ (index : Nat) (indexBound : index < listed.length),
      listed[index] = member ∧ (listed.eraseIdx index).Perm rest := by
  obtain ⟨index, indexBound, found⟩ :=
    List.getElem_of_mem (arranged.symm.subset List.mem_cons_self)
  refine ⟨index, indexBound, found, ?_⟩
  have whole := (List.getElem_cons_eraseIdx_perm indexBound).trans arranged
  rw [found] at whole
  exact whole.cons_inv

/-- A step of one member is a step of any bag that lists it. -/
private theorem lift_member {fuel : Nat} {member candidate : Pattern}
    (step : RhoStepAt fuel member candidate) {listed others : List Pattern}
    (arranged : listed.Perm (member :: others)) (termRest : Option String) :
    ∃ target, RhoStep (.collection .hashBag listed termRest) target ∧
      canonicalize rhoReflectivePresentation target =
        canonicalize rhoReflectivePresentation (.collection .hashBag (candidate :: others) none) := by
  obtain ⟨index, indexBound, found, rest⟩ := locate arranged
  refine ⟨_, ⟨fuel + 1, rhoStepAt_par_at indexBound (found ▸ step)⟩, ?_⟩
  exact canonicalize_parallel_permutation _ (rest.cons candidate)

/-- A step of a bag is a step of any bag that lists its elements beside others,
up to the equations. -/
private theorem lift_bag {fuel : Nat} {inner : List Pattern} {innerRest : Option String}
    {candidate : Pattern} (step : RhoStepAt fuel (.collection .hashBag inner innerRest) candidate)
    {listed others : List Pattern} (arranged : listed.Perm (inner ++ others))
    (termRest : Option String) :
    ∃ target, RhoStep (.collection .hashBag listed termRest) target ∧
      canonicalize rhoReflectivePresentation target =
        canonicalize rhoReflectivePresentation (.collection .hashBag (candidate :: others) none) := by
  rcases rhoStepAt_cases step with
    ⟨elements, _, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body, binder,
      outputChannel, payload, sourceEq, inputEq, outputEq, channels, rfl⟩ |
    ⟨smaller, elements, _, index, indexBound, selected, rfl, sourceEq, innerStep, rfl⟩
  · simp only [Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    have extracted : inner.Perm (inner[inputIndex] :: (inner.eraseIdx inputIndex)[outputIndex] ::
        (inner.eraseIdx inputIndex).eraseIdx outputIndex) :=
      ((List.getElem_cons_eraseIdx_perm outputBound).cons _ |>.trans
        (List.getElem_cons_eraseIdx_perm inputBound)).symm
    rw [inputEq, outputEq] at extracted
    obtain ⟨i, iBound, iFound, afterInput⟩ := locate (arranged.trans (extracted.append_right others))
    obtain ⟨j, jBound, jFound, residue⟩ := locate afterInput
    refine ⟨_, ⟨1, rhoStepAt_comm_at iBound jBound iFound jFound channels⟩, ?_⟩
    apply canonicalize_hashBag_eq_of_perm
    rw [contents_cons, contents_cons]
    refine List.Perm.trans ?_ ((contents_canonicalize_hashBag _).symm.append_right _)
    rw [contents_cons, List.append_assoc, ← contents_append]
    exact (contents_perm residue).append_left _
  · simp only [Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    have extracted : inner.Perm (inner[index] :: inner.eraseIdx index) :=
      (List.getElem_cons_eraseIdx_perm indexBound).symm
    obtain ⟨target, targetStep, same⟩ :=
      lift_member innerStep (arranged.trans (extracted.append_right others)) termRest
    refine ⟨target, targetStep, same.trans ?_⟩
    apply canonicalize_hashBag_eq_of_perm
    rw [contents_cons, contents_cons]
    refine List.Perm.trans ?_ ((contents_canonicalize_hashBag _).symm.append_right _)
    rw [List.append_eq, contents_append, contents_cons, List.append_assoc]

/-! ## Coherence: a step from any term is a step from its canonical form -/

private theorem canonicalize_input (channel body : Pattern) (binder : Option String) :
    canonicalize rhoReflectivePresentation (.apply "PInput" [channel, .lambda binder body]) =
      .apply "PInput" [canonicalize rhoReflectivePresentation channel,
        .lambda binder (canonicalize rhoReflectivePresentation body)] := by
  simp only [canonicalize, canonicalizeList, finish_long]

private theorem canonicalize_output (channel payload : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "POutput" [channel, payload]) =
      .apply "POutput" [canonicalize rhoReflectivePresentation channel,
        canonicalize rhoReflectivePresentation payload] := by
  simp only [canonicalize, canonicalizeList, finish_long]

/-- **Coherence.** Every step of our calculus, from any term, is matched by a
step from the term's canonical form, landing on the same canonical form. -/
theorem rhoStepAt_canonicalize : ∀ {fuel : Nat} {source target : Pattern},
    RhoStepAt fuel source target →
    ∃ target', RhoStep (canonicalize rhoReflectivePresentation source) target' ∧
      canonicalize rhoReflectivePresentation target' =
        canonicalize rhoReflectivePresentation target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
  intro source target step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, rfl, inputEq, outputEq, channels, rfl⟩ |
    ⟨smaller, elements, termRest, index, indexBound, candidate, fuelEq, rfl, innerStep, rfl⟩
  · -- COMM: the canonical input and output communicate as a pair
    have pairStep : RhoStepAt 1
        (.collection .hashBag
          [.apply "PInput" [canonicalize rhoReflectivePresentation inputChannel,
              .lambda binder (canonicalize rhoReflectivePresentation body)],
            .apply "POutput" [canonicalize rhoReflectivePresentation outputChannel,
              canonicalize rhoReflectivePresentation payload]] none)
        (.collection .hashBag
          [substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
              (canonicalize rhoReflectivePresentation payload)])
            (canonicalize rhoReflectivePresentation body)] none) :=
      rhoStepAt_comm_at (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl
        (by rw [canonicalize_idempotent, canonicalize_idempotent]; exact channels)
    have extracted : elements.Perm (elements[inputIndex] ::
        (elements.eraseIdx inputIndex)[outputIndex] ::
          (elements.eraseIdx inputIndex).eraseIdx outputIndex) :=
      ((List.getElem_cons_eraseIdx_perm outputBound).cons _ |>.trans
        (List.getElem_cons_eraseIdx_perm inputBound)).symm
    rw [inputEq, outputEq] at extracted
    have mapped := extracted.map (canonicalize rhoReflectivePresentation)
    rw [List.map_cons, List.map_cons, canonicalize_input, canonicalize_output] at mapped
    have contractum : canonicalize rhoReflectivePresentation
          (.collection .hashBag
            [substituteReflective rhoReflectivePresentation 0
              (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
                (canonicalize rhoReflectivePresentation payload)])
              (canonicalize rhoReflectivePresentation body)] none) =
        canonicalize rhoReflectivePresentation
          (substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation payload]) body) :=
      (canonicalize_parallel_singleton _ _).trans (canonicalize_commContractum body payload).symm
    cases termRest with
    | some rest =>
        rw [canonicalize_hashBag_rest]
        obtain ⟨target', targetStep, same⟩ := lift_bag pairStep
          (others := ((elements.eraseIdx inputIndex).eraseIdx outputIndex).map
            (canonicalize rhoReflectivePresentation)) mapped (some rest)
        refine ⟨target', targetStep, same.trans (canonicalize_hashBag_eq_of_perm ?_)⟩
        rw [contents_cons, contents_cons, contractum, map_canonicalize_twice]
    | none =>
        have contents : (normalizeParallelElements rhoReflectivePresentation
            (elements.map (canonicalize rhoReflectivePresentation))).Perm
            ([.apply "PInput" [canonicalize rhoReflectivePresentation inputChannel,
                .lambda binder (canonicalize rhoReflectivePresentation body)],
              .apply "POutput" [canonicalize rhoReflectivePresentation outputChannel,
                canonicalize rhoReflectivePresentation payload]] ++
              parallelContents rhoReflectivePresentation
                (((elements.eraseIdx inputIndex).eraseIdx outputIndex).map
                  (canonicalize rhoReflectivePresentation))) := by
          rw [normalizeParallelElements_eq_sort_parallelContents]
          refine (sortPatterns_perm _).trans ((parallelContents_perm _ mapped).trans ?_)
          rw [show ∀ (first second : Pattern) (rest : List Pattern),
              first :: second :: rest = [first, second] ++ rest from fun _ _ _ => rfl,
            parallelContents_append, parallelContents_of_plain]
          intro member found
          simp only [List.mem_cons, List.not_mem_nil, or_false] at found
          rcases found with rfl | rfl <;> exact ⟨by simp, by simp⟩
        rw [canonicalize_hashBag, collapseParallel_eq_collection_of_length_ge_two _
          (by rw [contents.length_eq]; simp)]
        obtain ⟨target', targetStep, same⟩ := lift_bag pairStep contents none
        refine ⟨target', targetStep, same.trans (canonicalize_hashBag_eq_of_perm ?_)⟩
        rw [contents_cons, contents_cons, contractum, contents_contents]
  · -- ParCong: the member's canonical form steps, and its step survives flattening
    cases fuelEq
    obtain ⟨candidate', ⟨fuel', canonicalStep⟩, candidateSame⟩ := ih innerStep
    have extracted : elements.Perm (elements[index] :: elements.eraseIdx index) :=
      (List.getElem_cons_eraseIdx_perm indexBound).symm
    have mapped := extracted.map (canonicalize rhoReflectivePresentation)
    rw [List.map_cons] at mapped
    have finish : ∀ others : List Pattern,
        (parallelContents rhoReflectivePresentation
            (others.map (canonicalize rhoReflectivePresentation))).Perm
          (parallelContents rhoReflectivePresentation
            ((elements.eraseIdx index).map (canonicalize rhoReflectivePresentation))) →
        canonicalize rhoReflectivePresentation (.collection .hashBag (candidate' :: others) none) =
          canonicalize rhoReflectivePresentation
            (.collection .hashBag (candidate :: elements.eraseIdx index) none) := by
      intro others same
      apply canonicalize_hashBag_eq_of_perm
      rw [contents_cons, contents_cons, candidateSame]
      exact same.append_left _
    cases termRest with
    | some rest =>
        rw [canonicalize_hashBag_rest]
        obtain ⟨target', targetStep, same⟩ := lift_member canonicalStep mapped (some rest)
        exact ⟨target', targetStep, same.trans (finish _ (by rw [map_canonicalize_twice]))⟩
    | none =>
        have residueFixed := contents_contents (elements.eraseIdx index)
        have contents : (normalizeParallelElements rhoReflectivePresentation
            (elements.map (canonicalize rhoReflectivePresentation))).Perm
            (parallelContents rhoReflectivePresentation
                [canonicalize rhoReflectivePresentation elements[index]] ++
              parallelContents rhoReflectivePresentation
                ((elements.eraseIdx index).map (canonicalize rhoReflectivePresentation))) := by
          rw [normalizeParallelElements_eq_sort_parallelContents]
          refine (sortPatterns_perm _).trans ((parallelContents_perm _ mapped).trans ?_)
          rw [← List.singleton_append, parallelContents_append]
        rw [canonicalize_hashBag]
        obtain ⟨inner, innerRest, shape⟩ := rhoStepAt_source_bag canonicalStep
        cases innerRest with
        | none =>
            have canonical := canonicalize_isCanonical rhoReflectivePresentation elements[index]
            rw [shape] at canonical
            obtain ⟨two, -, plain⟩ := canonical.2 ⟨rfl, rfl⟩
            have innerContents : parallelContents rhoReflectivePresentation
                [.collection .hashBag inner none] = inner := by
              unfold parallelContents
              simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, parallelSplice]
              exact List.filter_eq_self.mpr fun member found => decide_eq_true (plain member found).1
            rw [shape, innerContents] at contents
            rw [collapseParallel_eq_collection_of_length_ge_two _
              (by rw [contents.length_eq, List.length_append]; omega)]
            rw [shape] at canonicalStep
            obtain ⟨target', targetStep, same⟩ := lift_bag canonicalStep contents none
            exact ⟨target', targetStep, same.trans (finish _ (by rw [residueFixed]))⟩
        | some rest =>
            have single : parallelContents rhoReflectivePresentation
                [canonicalize rhoReflectivePresentation elements[index]] =
                  [canonicalize rhoReflectivePresentation elements[index]] := by
              rw [shape]
              exact parallelContents_of_plain fun member found => by
                simp only [List.mem_singleton] at found
                subst found
                exact ⟨by simp, by simp⟩
            rw [single, List.singleton_append] at contents
            by_cases many : 2 ≤ (normalizeParallelElements rhoReflectivePresentation
                (elements.map (canonicalize rhoReflectivePresentation))).length
            · rw [collapseParallel_eq_collection_of_length_ge_two _ many]
              obtain ⟨target', targetStep, same⟩ := lift_member canonicalStep contents none
              exact ⟨target', targetStep, same.trans (finish _ (by rw [residueFixed]))⟩
            · have lengths := contents.length_eq
              simp only [List.length_cons] at lengths
              have residueNil : parallelContents rhoReflectivePresentation
                  ((elements.eraseIdx index).map (canonicalize rhoReflectivePresentation)) = [] :=
                List.eq_nil_of_length_eq_zero (by omega)
              rw [residueNil, List.perm_singleton] at contents
              rw [contents]
              refine ⟨candidate', ⟨fuel', canonicalStep⟩, ?_⟩
              refine (canonicalize_parallel_singleton _ candidate').symm.trans (finish [] ?_)
              rw [residueNil]
              exact List.Perm.refl _

/-- **Coherence**, for the least step relation. -/
theorem rhoStep_canonicalize {source target : Pattern} (step : RhoStep source target) :
    ∃ target', RhoStep (canonicalize rhoReflectivePresentation source) target' ∧
      canonicalize rhoReflectivePresentation target' =
        canonicalize rhoReflectivePresentation target := by
  obtain ⟨_, bounded⟩ := step
  exact rhoStepAt_canonicalize bounded

/-! ## Rewriting modulo the equations -/

/-- One step of our calculus, read at the canonical form of its target: from a
canonical form, the next canonical form. -/
def CanonicalStep (source target : Pattern) : Prop :=
  ∃ result, RhoStep source result ∧ canonicalize rhoReflectivePresentation result = target

/-- A step from some term with the same canonical form as `source`. -/
def StepModulo (source target : Pattern) : Prop :=
  ∃ representative, canonicalize rhoReflectivePresentation representative =
    canonicalize rhoReflectivePresentation source ∧ RhoStep representative target

/-- **Completeness of the canonical representative.** A step modulo the
equations is matched by a step from the canonical form, up to the equations. -/
theorem stepModulo_complete {source target : Pattern} (step : StepModulo source target) :
    ∃ result, RhoStep (canonicalize rhoReflectivePresentation source) result ∧
      canonicalize rhoReflectivePresentation result =
        canonicalize rhoReflectivePresentation target := by
  obtain ⟨representative, same, representativeStep⟩ := step
  rw [← same]
  exact rhoStep_canonicalize representativeStep

/-- Rewriting modulo the equations, read up to the equations, is exactly the
canonical step on canonical forms. -/
theorem stepModulo_iff_canonicalStep (source target : Pattern) :
    (∃ target', StepModulo source target' ∧
        canonicalize rhoReflectivePresentation target' =
          canonicalize rhoReflectivePresentation target) ↔
      CanonicalStep (canonicalize rhoReflectivePresentation source)
        (canonicalize rhoReflectivePresentation target) := by
  constructor
  · rintro ⟨target', step, same⟩
    obtain ⟨result, resultStep, resultSame⟩ := stepModulo_complete step
    exact ⟨result, resultStep, resultSame.trans same⟩
  · rintro ⟨result, resultStep, same⟩
    exact ⟨result, ⟨_, canonicalize_idempotent _ source, resultStep⟩,
      (canonicalize_idempotent _ result).symm.trans (congrArg _ same) |>.trans
        (canonicalize_idempotent _ target)⟩

/-! ## Separation: the raw step relation is not closed under the equations -/

/-- The name `@0`. -/
def quotedZero : Pattern := .apply "NQuote" [.apply "PZero" []]

/-- `for (@0) 0`. -/
def waitingInput : Pattern := .apply "PInput" [quotedZero, .lambda none (.apply "PZero" [])]

/-- `@0!(0)`. -/
def offeredOutput : Pattern := .apply "POutput" [quotedZero, .apply "PZero" []]

/-- `{{@0!(0), 0}, for (@0) 0}`: the output and the unit in an inner bag, beside
an input on the same channel. -/
def nestedRedex : Pattern :=
  .collection .hashBag
    [.collection .hashBag [offeredOutput, .apply "PZero" []] none, waitingInput] none

/-- `{for (@0) 0, @0!(0)}`: the same redex in one bag. -/
def flatRedex : Pattern := .collection .hashBag [waitingInput, offeredOutput] none

private theorem no_step_of_not_bag {fuel : Nat} {source target : Pattern}
    (notBag : ∀ elements termRest, source ≠ .collection .hashBag elements termRest) :
    ¬ RhoStepAt fuel source target := fun step => by
  obtain ⟨elements, termRest, sourceEq⟩ := rhoStepAt_source_bag step
  exact notBag elements termRest sourceEq

private theorem no_step_output_unit {fuel : Nat} {target : Pattern} :
    ¬ RhoStepAt fuel (.collection .hashBag [offeredOutput, .apply "PZero" []] none) target := by
  intro step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, _, _, _, _, _, _, _, sourceEq, inputEq, _⟩ |
    ⟨_, elements, termRest, index, indexBound, _, _, sourceEq, innerStep, _⟩
  · simp only [Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    match inputIndex, inputBound, inputEq with
    | 0, _, inputEq => simp [offeredOutput] at inputEq
    | 1, _, inputEq => simp at inputEq
  · simp only [Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    match index, indexBound, innerStep with
    | 0, _, innerStep => exact no_step_of_not_bag (by simp [offeredOutput]) innerStep
    | 1, _, innerStep => exact no_step_of_not_bag (by simp) innerStep

/-- `nestedRedex` has no step. -/
theorem nestedRedex_stuck (target : Pattern) : ¬ RhoStep nestedRedex target := by
  rintro ⟨fuel, step⟩
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, _, _, _, _, _,
      sourceEq, inputEq, outputEq, _⟩ |
    ⟨_, elements, termRest, index, indexBound, _, _, sourceEq, innerStep, _⟩
  · simp only [nestedRedex, Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    match inputIndex, inputBound, outputIndex, outputBound, inputEq, outputEq with
    | 0, _, _, _, inputEq, _ => simp at inputEq
    | 1, _, 0, _, _, outputEq => simp at outputEq
  · simp only [nestedRedex, Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    match index, indexBound, innerStep with
    | 0, _, innerStep => exact no_step_output_unit innerStep
    | 1, _, innerStep => exact no_step_of_not_bag (by simp [waitingInput]) innerStep

private theorem waitingInput_canonical :
    canonicalize rhoReflectivePresentation waitingInput = waitingInput := by
  simp [waitingInput, quotedZero, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

private theorem offeredOutput_canonical :
    canonicalize rhoReflectivePresentation offeredOutput = offeredOutput := by
  simp [offeredOutput, quotedZero, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

private theorem plain_single {pattern : Pattern} (plain : Plain pattern) :
    parallelContents rhoReflectivePresentation [pattern] = [pattern] :=
  parallelContents_of_plain fun member found => by
    simp only [List.mem_singleton] at found
    exact found ▸ plain

private theorem waitingInput_plain : Plain waitingInput := ⟨by simp [waitingInput], by
  simp [waitingInput]⟩

private theorem offeredOutput_plain : Plain offeredOutput := ⟨by simp [offeredOutput], by
  simp [offeredOutput]⟩

/-- The two spellings have the same canonical form. -/
theorem canonicalize_nestedRedex :
    canonicalize rhoReflectivePresentation nestedRedex =
      canonicalize rhoReflectivePresentation flatRedex := by
  apply canonicalize_hashBag_eq_of_perm
  rw [contents_cons, List.map_singleton]
  refine ((contents_canonicalize_hashBag _).append_right _).trans ?_
  have unitNone : parallelContents rhoReflectivePresentation
      [canonicalize rhoReflectivePresentation (.apply "PZero" [])] = [] := by
    simp [parallelContents, parallelSplice, canonicalize, canonicalizeList,
      finishNormalizeReflectiveApply, rhoReflectivePresentation]
  have emptyContents : parallelContents rhoReflectivePresentation [] = [] := rfl
  simp only [contents_cons, List.map_nil, emptyContents, List.append_nil, unitNone,
    waitingInput_canonical, offeredOutput_canonical, plain_single waitingInput_plain,
    plain_single offeredOutput_plain]
  exact List.Perm.swap _ _ []

/-- The flat redex communicates, and its contractum is the unit. -/
theorem flatRedex_steps :
    RhoStep flatRedex (.collection .hashBag [.apply "PZero" []] none) :=
  ⟨1, rhoStepAt_comm_at (elements := [waitingInput, offeredOutput]) (termRest := none)
    (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl rfl⟩

/-- From the canonical form of `nestedRedex` the redex communicates, landing on
the unit. -/
theorem nestedRedex_canonical_steps :
    CanonicalStep (canonicalize rhoReflectivePresentation nestedRedex) (.apply "PZero" []) := by
  obtain ⟨result, step, same⟩ := rhoStep_canonicalize flatRedex_steps
  refine ⟨result, canonicalize_nestedRedex ▸ step, same.trans ?_⟩
  refine (canonicalize_parallel_singleton rhoReflectivePresentation (.apply "PZero" [])).trans ?_
  simp [canonicalize, canonicalizeList, finishNormalizeReflectiveApply, rhoReflectivePresentation]

/-- `nestedRedex` steps modulo the equations. -/
theorem nestedRedex_stepModulo :
    StepModulo nestedRedex (.collection .hashBag [.apply "PZero" []] none) :=
  ⟨flatRedex, canonicalize_nestedRedex.symm, flatRedex_steps⟩

/-- **Separation.** The raw step relation is not closed under the equations: two
terms with the same canonical form, one of which steps and one of which has no
step. The responsible laws are the parallel unit and nesting of parallel
composition, which `ParCong` and COMM do not apply. -/
theorem rhoStep_not_closed_under_canonical_equality :
    ∃ source representative target : Pattern,
      canonicalize rhoReflectivePresentation source =
          canonicalize rhoReflectivePresentation representative ∧
        RhoStep representative target ∧ ∀ result, ¬ RhoStep source result :=
  ⟨nestedRedex, flatRedex, _, canonicalize_nestedRedex, flatRedex_steps, nestedRedex_stuck⟩

/-! ## Separation: a top-level COMM needs ground syntax -/

/-- `{{for (@0) 0, @0!(0) | r}, *@0}`: a redex inside a bag with a rest
variable, beside a drop. -/
def restRedex : Pattern :=
  .collection .hashBag
    [.collection .hashBag [waitingInput, offeredOutput] (some "r"), .apply "PDrop" [quotedZero]] none

private theorem restRedex_contents :
    (normalizeParallelElements rhoReflectivePresentation
      ([.collection .hashBag [waitingInput, offeredOutput] (some "r"),
        .apply "PDrop" [quotedZero]].map (canonicalize rhoReflectivePresentation))).Perm
      [.collection .hashBag [waitingInput, offeredOutput] (some "r"), .apply "PDrop" [quotedZero]] := by
  rw [normalizeParallelElements_eq_sort_parallelContents]
  refine (sortPatterns_perm _).trans ?_
  have dropCanonical : canonicalize rhoReflectivePresentation (.apply "PDrop" [quotedZero]) =
      .apply "PDrop" [quotedZero] := by
    simp [quotedZero, canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
      rhoReflectivePresentation]
  rw [List.map_cons, List.map_singleton, canonicalize_hashBag_rest, List.map_cons,
    List.map_singleton, waitingInput_canonical, offeredOutput_canonical, dropCanonical,
    parallelContents_of_plain]
  intro member found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with rfl | rfl <;> exact ⟨by simp, by simp⟩

/-- **Separation.** A step from a term with a rest variable need not be matched
by a COMM at the top of its canonical form: canonicalization does not flatten a
bag with a rest variable, so the matching step is a `ParCong` step. This is why
`CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep`, whose
conclusion is a COMM at the top, assumes closed well-sorted syntax, while
coherence (`rhoStep_canonicalize`) needs no hypothesis. -/
theorem top_comm_fails_with_rest :
    (∃ target, RhoStep restRedex target) ∧
      ∀ target, ¬ RhoStepAt 1 (canonicalize rhoReflectivePresentation restRedex) target := by
  refine ⟨⟨_, ⟨2, rhoStepAt_par_at (index := 0) (by simp)
    (rhoStepAt_comm_at (elements := [waitingInput, offeredOutput]) (termRest := some "r")
      (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl rfl)⟩⟩, ?_⟩
  intro target step
  have members := restRedex_contents
  have shape : canonicalize rhoReflectivePresentation restRedex =
      .collection .hashBag (normalizeParallelElements rhoReflectivePresentation
        ([.collection .hashBag [waitingInput, offeredOutput] (some "r"),
          .apply "PDrop" [quotedZero]].map (canonicalize rhoReflectivePresentation))) none := by
    rw [restRedex, canonicalize_hashBag]
    exact collapseParallel_eq_collection_of_length_ge_two _ (by rw [members.length_eq]; simp)
  rw [shape] at step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, _, _, _, _, _, _, _, sourceEq, inputEq, _⟩ |
    ⟨smaller, _, _, _, _, _, fuelEq, _, innerStep, _⟩
  · simp only [Pattern.collection.injEq] at sourceEq
    obtain ⟨-, rfl, -⟩ := sourceEq
    have found := members.subset (List.getElem_mem inputBound)
    rw [inputEq] at found
    simp at found
  · cases fuelEq
    cases innerStep

#print axioms rhoStepAt_cases
#print axioms rhoStepAt_comm_at
#print axioms rhoStepAt_par_at
#print axioms canonicalize_substituteResolved_congr
#print axioms canonicalize_commContractum
#print axioms rhoStep_canonicalize
#print axioms stepModulo_complete
#print axioms stepModulo_iff_canonicalStep
#print axioms nestedRedex_stuck
#print axioms nestedRedex_canonical_steps
#print axioms rhoStep_not_closed_under_canonical_equality
#print axioms top_comm_fails_with_rest

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
