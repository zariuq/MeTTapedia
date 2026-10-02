import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairReflectiveFraming
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec

/-!
# Coverage of actual synchronous COMM matcher choices

The actual reflective matcher selects two occurrences, preserving the input
binder annotation, both original channel terms and the exact remaining list.
This evidence reconstructs a minimal pair and its authored parallel frame.
Object-pattern admission excludes an unresolved target collection rest.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairMatchCoverage

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Invert the executable matcher without replacing its output by a
separately chosen interaction. The output index is in the input-erased list. -/
theorem matched_pair_positions {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoSyncCommRewrite source) :
    ∃ (elements : List Pattern) (termRest : Option String)
      (inputIndex : Nat) (inputBound : inputIndex < elements.length)
      (outputIndex : Nat) (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
      (inputChannel body : Pattern) (inputBinder : Option String)
      (outputChannel sent after : Pattern),
      source = .collection .hashBag elements termRest ∧
      elements[inputIndex] = .apply "PInput" [inputChannel, .lambda inputBinder body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] = .apply "POutputK" [outputChannel, sent, after] ∧
      canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true ∧
      bindings = [("k", after), ("q", sent),
        ("rest", .collection .hashBag ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
        ("p", body), ("n", inputChannel)] := by
  rw [matchPatternForRuleUsing_iff_matchRelWith_of_presentation
    (show matchingPresentationForRule? rhoReflectionProfile rhoSyncCommRewrite =
      some rhoReflectivePresentation from rfl)] at matched
  cases matched
  rename_i elements termRest notVector bagMatch
  cases bagMatch
  rename_i inputBindings tailBindings inputIndex inputBound inputMatch tailMatch mergeAll
  generalize inputTermEq : elements[inputIndex] = inputTerm at inputMatch
  cases inputMatch
  rename_i inputArguments inputLength inputArgsMatch
  obtain ⟨inputChannel, inputLambda, inputArgumentsEq⟩ := List.length_eq_two.mp inputLength.symm
  subst inputArguments
  cases inputArgsMatch
  rename_i headBindings tailInputBindings channelMatch inputTailMatch mergeInput
  cases channelMatch
  cases inputTailMatch
  rename_i lambdaBindings noInputBindings lambdaMatch inputArgsRest mergeLambda
  generalize inputLambdaEq : inputLambda = inputLambdaTerm at lambdaMatch
  cases lambdaMatch
  rename_i inputBinder bodyMatch
  cases bodyMatch
  rename_i bodyTerm
  cases inputArgsRest
  cases tailMatch
  rename_i outputBindings restBindings outputIndex outputBound outputMatch restMatch mergeTail
  generalize outputTermEq : (elements.eraseIdx inputIndex)[outputIndex] = outputTerm at outputMatch
  cases outputMatch
  rename_i outputArguments outputLength outputArgsMatch
  obtain ⟨outputChannel, sentTerm, afterTerm, outputArgumentsEq⟩ :=
    List.length_eq_three.mp outputLength.symm
  subst outputArguments
  cases outputArgsMatch
  rename_i outputHeadBindings outputTailBindings outputChannelMatch outputTailMatch mergeOutput
  cases outputChannelMatch
  cases outputTailMatch
  rename_i payloadBindings continuationBindings payloadMatch continuationMatch mergePayload
  cases payloadMatch
  cases continuationMatch
  rename_i afterBindings noOutputBindings afterMatch outputArgsRest mergeAfter
  cases afterMatch
  cases outputArgsRest
  cases restMatch
  rw [inputLambdaEq] at inputTermEq
  simp [mergeBindingsWith] at mergeLambda mergeAfter
  subst tailInputBindings
  subst continuationBindings
  simp [mergeBindingsWith] at mergePayload
  subst outputTailBindings
  simp [mergeBindingsWith] at mergeInput mergeOutput
  subst inputBindings
  subst outputBindings
  simp [mergeBindingsWith] at mergeTail
  subst tailBindings
  refine ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, bodyTerm, inputBinder, outputChannel, sentTerm, afterTerm,
    rfl, inputTermEq, outputTermEq, ?_⟩
  simp [mergeBindingsWith] at mergeAll
  exact ⟨mergeAll.1, mergeAll.2.symm⟩

/-- Extracted occurrences move to the front by a permutation, retaining
every other occurrence and its multiplicity. -/
theorem extract_two_perm (elements : List Pattern) (first second : Nat)
    (firstBound : first < elements.length)
    (secondBound : second < (elements.eraseIdx first).length) :
    elements.Perm (elements[first] :: (elements.eraseIdx first)[second] ::
      (elements.eraseIdx first).eraseIdx second) := by
  exact (List.getElem_cons_eraseIdx_perm firstBound).symm.trans
    ((List.getElem_cons_eraseIdx_perm secondBound).symm.cons _)

/-- The two actual selected operands, with the input annotation retained. -/
def selectedPair (inputBinder : Option String)
    (inputChannel outputChannel body sent after : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "PInput" [inputChannel, .lambda inputBinder body],
     .apply "POutputK" [outputChannel, sent, after]] none

private theorem minimal_match (inputBinder : Option String)
    (inputChannel outputChannel body sent after : Pattern)
    (channels : canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true) :
    [("k", after), ("q", sent), ("rest", .collection .hashBag [] none),
      ("p", body), ("n", inputChannel)] ∈
    matchPatternForRuleUsing rhoReflectionProfile rhoSyncCommRewrite
      (selectedPair inputBinder inputChannel outputChannel body sent after) := by
  rw [matchPatternForRuleUsing,
    show matchingPresentationForRule? rhoReflectionProfile rhoSyncCommRewrite =
      some rhoReflectivePresentation from rfl]
  simp [rhoSyncCommRewrite, selectedPair, matchPatternWith, matchArgsWith,
    matchBagWith, mergeBindingsWith, channels]

/-- Retaining the original binder annotation does not change the source
rule's actual reflective firing or its compiled contractum. -/
theorem selected_pair_step (inputBinder : Option String)
    (inputChannel outputChannel body sent after : Pattern)
    (channels : canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true) :
    Step ActivePairReflectiveFraming.interpretation ActivePairReflectiveFraming.base rhoSyncCalc
      (selectedPair inputBinder inputChannel outputChannel body sent after)
      (ActivePairReflectiveFraming.flatResidual body sent after []) := by
  refine ⟨1, .rule (rule := rhoSyncCommRewrite)
    (initialBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag [] none),
      ("p", body), ("n", inputChannel)])
    (finalBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag [] none),
      ("p", body), ("n", inputChannel)]) List.mem_cons_self ?_ (.nil _) ?_⟩
  · exact minimal_match inputBinder inputChannel outputChannel body sent after channels
  · exact ActivePairReflectiveFraming.original_contractum_with_rest inputChannel body sent after []

/-- Every actual source match on an object term yields a source-authorized
minimal pair and external frame. No interaction witnesses are assumed.
The chosen binder, channels and remainder are extracted from that match. -/
theorem actual_match_factorization {source : Pattern} {bindings : Bindings}
    (object : isObjectPattern source = true)
    (matched : bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoSyncCommRewrite source) :
    ∃ (inputBinder : Option String) (inputChannel outputChannel body sent after : Pattern)
      (rest : List Pattern),
      canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true ∧
      canonicalize rhoReflectivePresentation source =
        canonicalize rhoReflectivePresentation
          (.collection .hashBag
            (selectedPair inputBinder inputChannel outputChannel body sent after :: rest) none) ∧
      Step ActivePairReflectiveFraming.interpretation ActivePairReflectiveFraming.base rhoSyncCalc
        (selectedPair inputBinder inputChannel outputChannel body sent after)
        (ActivePairReflectiveFraming.flatResidual body sent after []) ∧
      Step ActivePairReflectiveFraming.interpretation ActivePairReflectiveFraming.base rhoSyncCalc
        (.collection .hashBag
          (selectedPair inputBinder inputChannel outputChannel body sent after :: rest) none)
        (.collection .hashBag (ActivePairReflectiveFraming.flatResidual body sent after [] :: rest) none) ∧
      applyBindingsForRuleUsing rhoReflectionProfile rhoSyncCommRewrite bindings =
        ActivePairReflectiveFraming.flatResidual body sent after rest ∧
      canonicalize rhoReflectivePresentation
        (applyBindingsForRuleUsing rhoReflectionProfile rhoSyncCommRewrite bindings) =
        canonicalize rhoReflectivePresentation
          (.collection .hashBag (ActivePairReflectiveFraming.flatResidual body sent after [] :: rest) none) := by
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, sent, after, sourceEq,
    inputEq, outputEq, channels, bindingsEq⟩ := matched_pair_positions matched
  have noRest : termRest = none := by
    rw [sourceEq] at object
    cases termRest with
    | none => rfl
    | some name => simp [isObjectPattern] at object
  let rest := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have permutation := extract_two_perm elements inputIndex outputIndex inputBound outputBound
  rw [inputEq, outputEq] at permutation
  have sourceCanonical : canonicalize rhoReflectivePresentation source =
      canonicalize rhoReflectivePresentation (.collection .hashBag
        (selectedPair inputBinder inputChannel outputChannel body sent after :: rest) none) := by
    rw [sourceEq, noRest]
    exact (canonicalize_parallel_permutation rhoReflectivePresentation permutation).trans
      (ActivePairFraming.canonicalize_grouped_head rhoReflectivePresentation
        [.apply "PInput" [inputChannel, .lambda inputBinder body],
         .apply "POutputK" [outputChannel, sent, after]] rest).symm
  have minimal := selected_pair_step inputBinder inputChannel outputChannel body sent after channels
  have targetEq : applyBindingsForRuleUsing rhoReflectionProfile rhoSyncCommRewrite bindings =
      ActivePairReflectiveFraming.flatResidual body sent after rest := by
    rw [bindingsEq]
    exact ActivePairReflectiveFraming.original_contractum_with_rest inputChannel body sent after rest
  refine ⟨inputBinder, inputChannel, outputChannel, body, sent, after, rest,
    channels, sourceCanonical, minimal,
    ActivePairReflectiveFraming.source_parallel_step rest minimal, targetEq, ?_⟩
  rw [targetEq]
  exact (ActivePairFraming.canonicalize_grouped_head rhoReflectivePresentation
    [ActivePairReflectiveFraming.activatedBody body sent, after] rest).symm

/-- The raw matcher accepts an unresolved target remainder; the object-term
premise in the coverage theorem is therefore a real admission boundary. -/
theorem unresolved_target_rest_boundary :
    let input : Pattern := .apply "PInput" [.fvar "c", .lambda (some "kept") (.fvar "body")]
    let output : Pattern := .apply "POutputK" [.fvar "c", .fvar "sent", .fvar "after"]
    let source := Pattern.collection .hashBag [input, output] (some "unresolved")
    isObjectPattern source = false ∧
    matchPatternForRuleUsing rhoReflectionProfile rhoSyncCommRewrite source ≠ [] := by
  decide +kernel

#print axioms matched_pair_positions
#print axioms actual_match_factorization

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairMatchCoverage
