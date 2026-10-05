import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairFraming
import Mettapedia.OSLF.MeTTaIL.MatchWithSpec

/-!
# Reflective source COMM with external rest

The actual source reflection profile compares the two channels canonically
and interprets the explicit substitution with its reflective operation.
Arbitrary ambient remainder occurrences factor through the original ParCong
rule and the source canonicalizer's parallel grouping laws. The operation on
the input body is not replaced by ordinary de Bruijn substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectiveFraming

open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution

abbrev base := ActivePairContext.base
abbrev interpretation : RuleInterpretation := .reflection rhoReflectionProfile

def flatSource (inputChannel outputChannel body sent after : Pattern)
    (rest : List Pattern) : Pattern := .collection .hashBag
  (.apply "PInput" [inputChannel, .lambda none body] ::
    .apply "POutputK" [outputChannel, sent, after] :: rest) none

/-- The exact operation selected by the source's existing annotation. -/
def activatedBody (body sent : Pattern) : Pattern :=
  substituteReflective rhoReflectivePresentation 0
    (normalizeReflectiveReplacement rhoReflectivePresentation (.apply "NQuote" [sent])) body

def flatResidual (body sent after : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag (activatedBody body sent :: after :: rest) none

private theorem selected_matching : matchingPresentationForRule? rhoReflectionProfile
    rhoSyncCommRewrite = some rhoReflectivePresentation := rfl

private theorem selected_substitution : substitutionPresentationForRule? rhoReflectionProfile
    rhoSyncCommRewrite = some rhoReflectivePresentation := rfl

/-- Exact original source matching, retaining both channel terms and every
unmatched occurrence. Only their declared canonical equality is required. -/
theorem original_match_with_rest (inputChannel outputChannel body sent after : Pattern)
    (rest : List Pattern)
    (channels : canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true) :
    [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", inputChannel)] ∈
    matchPatternForRuleUsing rhoReflectionProfile rhoSyncCommRewrite
      (flatSource inputChannel outputChannel body sent after rest) := by
  rw [matchPatternForRuleUsing, selected_matching]
  have input : MatchRelWith (canonicalEquivalent rhoReflectivePresentation)
      (.apply "PInput" [.fvar "n", .lambda none (.fvar "p")])
      (.apply "PInput" [inputChannel, .lambda none body])
      [("p", body), ("n", inputChannel)] := by
    apply matchPatternWith_iff_matchRelWith.mp
    simp [matchPatternWith, matchArgsWith, mergeBindingsWith]
  have output : MatchRelWith (canonicalEquivalent rhoReflectivePresentation)
      (.apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"])
      (.apply "POutputK" [outputChannel, sent, after])
      [("q", sent), ("k", after), ("n", outputChannel)] := by
    apply matchPatternWith_iff_matchRelWith.mp
    simp [matchPatternWith, matchArgsWith, mergeBindingsWith]
  apply matchPatternWith_iff_matchRelWith.mpr
  apply MatchRelWith.collection (by decide)
  apply MatchBagRelWith.cons
    (tailBindings := [("rest", .collection .hashBag rest none),
      ("q", sent), ("k", after), ("n", outputChannel)]) 0 (by simp) input
  · apply MatchBagRelWith.cons 0 (by simp) output MatchBagRelWith.nilRest
    simp [mergeBindingsWith]
  · simp [mergeBindingsWith, channels]

/-- The instantiated source RHS keeps the exact reflective body operation;
its optional collection rest splices the unchanged remainder. -/
theorem original_contractum_with_rest (inputChannel body sent after : Pattern)
    (rest : List Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoSyncCommRewrite
      [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
        ("p", body), ("n", inputChannel)] = flatResidual body sent after rest := by
  rw [applyBindingsForRuleUsing, selected_substitution]
  simp [rhoSyncCommRewrite, applyBindingsReflective, applyBindingsReflectiveList,
    flatResidual, activatedBody]

/-- A source reflective step with any ambient remainder. -/
theorem original_step_with_rest (inputChannel outputChannel body sent after : Pattern)
    (rest : List Pattern)
    (channels : canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true) :
    Step interpretation base rhoSyncCalc
      (flatSource inputChannel outputChannel body sent after rest)
      (flatResidual body sent after rest) := by
  refine ⟨1, .rule (rule := rhoSyncCommRewrite)
    (initialBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", inputChannel)])
    (finalBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", inputChannel)]) List.mem_cons_self ?_ (.nil _) ?_⟩
  · exact original_match_with_rest inputChannel outputChannel body sent after rest channels
  · exact original_contractum_with_rest inputChannel body sent after rest

/-- Reflection remains selected on COMM; ParCong is the same original
ordinary contextual rule around that reflected step. -/
theorem source_parallel_step {source target : Pattern} (rest : List Pattern)
    (step : Step interpretation base rhoSyncCalc source target) :
    Step interpretation base rhoSyncCalc (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  apply step_of_single_congruence_rule (rule := rhoParCongRewrite)
    (initialBindings := [("rest", .collection .hashBag rest none), ("S", source)])
    (finalBindings := [("T", target), ("rest", .collection .hashBag rest none), ("S", source)])
    (premiseBindings := [("T", target)])
    (premiseSource := .fvar "S") (premiseTarget := .fvar "T") (candidate := target)
  · simp [rhoSyncCalc]
  · change [("rest", .collection .hashBag rest none), ("S", source)] ∈
      matchPattern rhoParCongRewrite.left (.collection .hashBag (source :: rest) none)
    apply matchPattern_iff_matchRel.mpr
    exact .collection (by decide) (.cons 0 (by simp) .fvar .nilRest rfl)
  · rfl
  · simpa [applyBindings] using step
  · simp [matchPattern]
  · rfl
  · change applyRuleBindings rhoParCongRewrite _ = _
    simp [rhoParCongRewrite, applyRuleBindings, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, restSplice]
    simp [show liftBVars 0 0 = id from funext (fun p => liftBVars_zero p 0)]

/-- Flat reflected COMM and the contextualized minimal pair are actual
source steps and agree at both source canonical endpoints. -/
theorem original_rest_factorization (inputChannel outputChannel body sent after : Pattern)
    (rest : List Pattern)
    (channels : canonicalEquivalent rhoReflectivePresentation inputChannel outputChannel = true) :
    Step interpretation base rhoSyncCalc
      (flatSource inputChannel outputChannel body sent after rest)
      (flatResidual body sent after rest) ∧
    Step interpretation base rhoSyncCalc
      (.collection .hashBag (flatSource inputChannel outputChannel body sent after [] :: rest) none)
      (.collection .hashBag (flatResidual body sent after [] :: rest) none) ∧
    canonicalize rhoReflectivePresentation
      (.collection .hashBag (flatSource inputChannel outputChannel body sent after [] :: rest) none) =
      canonicalize rhoReflectivePresentation
        (flatSource inputChannel outputChannel body sent after rest) ∧
    canonicalize rhoReflectivePresentation
      (.collection .hashBag (flatResidual body sent after [] :: rest) none) =
      canonicalize rhoReflectivePresentation (flatResidual body sent after rest) := by
  refine ⟨original_step_with_rest inputChannel outputChannel body sent after rest channels,
    source_parallel_step rest
      (original_step_with_rest inputChannel outputChannel body sent after [] channels), ?_, ?_⟩
  · exact ActivePairFraming.canonicalize_grouped_head rhoReflectivePresentation _ rest
  · exact ActivePairFraming.canonicalize_grouped_head rhoReflectivePresentation _ rest

/-- Reflective activation really differs from ordinary instantiateBVar:
a replaced dropped name releases its quoted process. -/
theorem reflective_body_not_ordinary :
    activatedBody (.apply "PDrop" [.bvar 0]) (.apply "PZero" []) = .apply "PZero" [] ∧
    instantiateBVar (.apply "NQuote" [.apply "PZero" []]) (.apply "PDrop" [.bvar 0]) ≠
      activatedBody (.apply "PDrop" [.bvar 0]) (.apply "PZero" []) := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairReflectiveFraming
