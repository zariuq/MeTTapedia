import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairScoped
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Administrative context for already funded continuation steps

The generated binary contact retains the residual code beside its remaining
funding. An explicit left-context rule exposes already funded steps in that
code. It neither lifts an unmetered source contraction nor opens a quotation or
a purse. A recursive firing still checks and consumes its own funding.

This module establishes generated syntax and interpreted contextual execution.
An interpretation of the generated apparatus in the separate raw Cost runtime
is an additional obligation; constructor names do not supply that comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairContext

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine

abbrev base := Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
  Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty

def withFunding (code stack : Pattern) : Pattern := .apply costContactConstructorName
  [code, .apply costFundingConstructorName [stack]]

/-- Administrative closure of an already admitted target-language step.
The unchanged frame is explicitly a funding term, and only code is active. -/
def leftRule : RewriteRule where
  name := "$cost:rewrite:funded-left-context"
  typeContext :=
    [("frame-source", .base costWrappedSortName),
     ("frame-target", .base costWrappedSortName),
     ("frame-stack", .base costTokenStackSortName)]
  premises := [.congruence (.fvar "frame-source") (.fvar "frame-target")]
  left := withFunding (.fvar "frame-source") (.fvar "frame-stack")
  right := withFunding (.fvar "frame-target") (.fvar "frame-stack")
  bindings := some { dependencies :=
    [("frame-source", []), ("frame-target", []), ("frame-stack", [])] }

def language : LanguageDef :=
  { ActivePair.language with rewrites := [ActivePair.rule, ActivePair.parallelRule, leftRule] }

theorem left_rule_valid : LanguageDef.validateRewrite language leftRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence
    (source := "frame-source") (target := "frame-target") <;>
    first
    | rfl
    | decide +kernel
    | (rule_patterns [leftRule, withFunding]
       decide +kernel)

theorem language_valid : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      ActivePair.language ActivePair.language_valid
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      ActivePair.language ActivePair.language_valid
  · exact LanguageDef.equationNames_nodup_of_validate_eq_nil
      ActivePair.language ActivePair.language_valid
  · decide +kernel
  · intro term member
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _
      ActivePair.language_valid term member
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_validate_eq_nil _
      ActivePair.language_valid equation member
  · intro rewrite member
    have cases : rewrite = ActivePair.rule ∨ rewrite = ActivePair.parallelRule ∨
        rewrite = leftRule := by simpa [language] using member
    rcases cases with rfl | rfl | rfl
    · exact ActivePair.rule_valid
    · exact ActivePair.parallel_valid
    · exact left_rule_valid

theorem binding_declarations_valid : bindingDeclarationsValid language = true := by
  unfold bindingDeclarationsValid
  rw [language_valid]
  decide +kernel

def presentation : ValidatedReflectiveLanguageDef where
  core := ⟨language, language_valid⟩
  reflection := ⟨ActivePair.presentation.reflection.1, by decide +kernel⟩

abbrev interpretation : RuleInterpretation := .reflection presentation.reflection.1

def leftContext : OneHoleContext := .apply costContactConstructorName [] .hole
  [.apply costFundingConstructorName [.fvar "frame-stack"]]

theorem exact_left_context : compileRuleContexts leftRule = [leftContext] := by decide +kernel

/-- Arbitrary already funded contextual execution lifts through the code
argument, preserving the complete external stack literally. -/
theorem funded_left_step {code result : Pattern} (stack : Pattern)
    (inner : Step interpretation base language code result) :
    Step interpretation base language (withFunding code stack) (withFunding result stack) := by
  apply step_of_single_congruence_rule (rule := leftRule)
    (initialBindings := [("frame-stack", stack), ("frame-source", code)])
    (finalBindings := [("frame-target", result), ("frame-stack", stack), ("frame-source", code)])
    (premiseBindings := [("frame-target", result)])
    (premiseSource := .fvar "frame-source") (premiseTarget := .fvar "frame-target")
    (candidate := result)
  · simp [language]
  · change [("frame-stack", stack), ("frame-source", code)] ∈
      matchPattern leftRule.left (withFunding code stack)
    simp [leftRule, withFunding, matchPattern, matchArgs, mergeBindings]
  · rfl
  · simpa [applyBindings] using inner
  · simp [matchPattern]
  · simp [mergeBindings]
  · change applyRuleBindings leftRule
      [("frame-target", result), ("frame-stack", stack), ("frame-source", code)] = _
    simp [applyRuleBindings, leftRule, withFunding, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- The output continuation is itself a closed funded interaction. -/
def activeContinuationSource : Pattern := ActivePair.fundedPair
  FiniteWhole.canonicalChannel FiniteWhole.localBody FiniteWhole.zero FiniteWhole.source
  FiniteWhole.unitSignature FiniteWhole.retainedTail

def trappedResidual : Pattern := withFunding
  (.collection .hashBag [FiniteWhole.zero, FiniteWhole.source] none) FiniteWhole.retainedTail

def continuedResidual : Pattern := withFunding
  (.collection .hashBag [FiniteWhole.target, FiniteWhole.zero] none) FiniteWhole.retainedTail

theorem continuation_source_typed : HasSort language FreeTypeContext.empty []
    activeContinuationSource costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem trapped_residual_typed : HasSort language FreeTypeContext.empty []
    trappedResidual costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem continued_residual_typed : HasSort language FreeTypeContext.empty []
    continuedResidual costWrappedSortName := checkHasType_sound (by decide +kernel)

/-- The active continuation really is released by the original corrected
funded pair, so this boundary is not a fabricated unreachable term. -/
theorem reaches_trapped_residual : rewriteStepWithReflection ActivePair.presentation.reflection.1
    ActivePair.language activeContinuationSource = [trappedResidual] := by decide +kernel

/-- Without the administrative context, the actual released continuation
cannot be reached by any amount of contextual compiler fuel. -/
theorem trapped_without_context (fuel : Nat) :
    rewriteAt (.reflection ActivePair.presentation.reflection.1) base
      ActivePair.language fuel trappedResidual = [] := by
  have first : matchPatternForRuleUsing ActivePair.presentation.reflection.1
      ActivePair.rule trappedResidual = [] := by decide +kernel
  have second : matchPatternForRuleUsing ActivePair.presentation.reflection.1
      ActivePair.parallelRule trappedResidual = [] := by decide +kernel
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [rewriteAt, ActivePair.language, applyRuleUsing, RuleInterpretation.reflection,
        first, second]

/-- The left-context rule and authored parallel context expose an actual
second funded firing; the external frame stack is unchanged. -/
theorem resumes_continuation : rewriteAt interpretation base language 3
    trappedResidual = [continuedResidual] := by decide +kernel

def unfundedInner : Pattern := withFunding
  (.collection .hashBag [FiniteWhole.zero, FiniteWhole.sourceWithStack FiniteWhole.emptyStack] none)
  FiniteWhole.retainedTail

def wrongKeyInner : Pattern := withFunding
  (.collection .hashBag [FiniteWhole.zero, FiniteWhole.sourceWithStack FiniteWhole.wrongStack] none)
  FiniteWhole.retainedTail

theorem unfunded_inner_typed : HasSort language FreeTypeContext.empty []
    unfundedInner costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem wrong_key_inner_typed : HasSort language FreeTypeContext.empty []
    wrongKeyInner costWrappedSortName := checkHasType_sound (by decide +kernel)

/-- The external purse cannot pay for an inner unfunded interaction. -/
theorem no_external_funding_borrow : rewriteAt interpretation base language 3
    unfundedInner = [] := by decide +kernel

/-- External matching signatures cannot repair the inner purse's wrong key. -/
theorem inner_key_still_checked : rewriteAt interpretation base language 3
    wrongKeyInner = [] := by decide +kernel

def quotedActive : Pattern := .apply (costWrappedConstructorName "NQuote")
  [activeContinuationSource]

theorem quoted_active_typed : HasSort language FreeTypeContext.empty []
    quotedActive (costBaseSortName "Name") := checkHasType_sound (by decide +kernel)

private theorem match_apply_other (profile : ReflectionProfile) (rule : RewriteRule)
    (leftName rightName : String) (leftArguments rightArguments : List Pattern)
    (shape : rule.left = .apply leftName leftArguments) (different : leftName ≠ rightName) :
    matchPatternForRuleUsing profile rule (.apply rightName rightArguments) = [] := by
  unfold matchPatternForRuleUsing
  split <;> simp [shape, matchPattern, matchPatternWith, different]

private theorem match_collection_apply (profile : ReflectionProfile) (rule : RewriteRule)
    (kind : CollType) (elements : List Pattern) (rest : Option String)
    (name : String) (arguments : List Pattern)
    (shape : rule.left = .collection kind elements rest) :
    matchPatternForRuleUsing profile rule (.apply name arguments) = [] := by
  unfold matchPatternForRuleUsing
  split <;> simp [shape, matchPattern, matchPatternWith]

/-- An application headed by any constructor other than contact is not an
active context. This excludes signed code, quotations, and funding itself. -/
theorem no_unlisted_constructor_descent (fuel : Nat) (name : String) (arguments : List Pattern)
    (different : costContactConstructorName ≠ name) :
    rewriteAt interpretation base language fuel (.apply name arguments) = [] := by
  have first := match_apply_other presentation.reflection.1 ActivePair.rule
    costContactConstructorName name _ arguments rfl different
  have second := match_collection_apply presentation.reflection.1 ActivePair.parallelRule
    .hashBag _ _ name arguments rfl
  have third := match_apply_other presentation.reflection.1 leftRule
    costContactConstructorName name _ arguments rfl different
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [rewriteAt, language, applyRuleUsing, interpretation, RuleInterpretation.reflection,
        first, second, third]

/-- No contextual depth exposes code protected by a quotation. -/
theorem no_quotation_descent (fuel : Nat) (code : Pattern) :
    rewriteAt interpretation base language fuel
      (.apply (costWrappedConstructorName "NQuote") [code]) = [] :=
  no_unlisted_constructor_descent fuel _ _ (by decide +kernel)

/-- Funding is never itself a reduction context, independently of its
contents. The executable language has no right-hand contact context. -/
theorem no_funding_descent (fuel : Nat) (stack : Pattern) :
    rewriteAt interpretation base language fuel
      (.apply costFundingConstructorName [stack]) = [] :=
  no_unlisted_constructor_descent fuel _ _ (by decide +kernel)

/-- Signed code can only be opened by the funded active-pair rule. -/
theorem no_signed_descent (fuel : Nat) (code signature : Pattern) :
    rewriteAt interpretation base language fuel
      (.apply costSignedConstructorName [code, signature]) = [] :=
  no_unlisted_constructor_descent fuel _ _ (by decide +kernel)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairContext
