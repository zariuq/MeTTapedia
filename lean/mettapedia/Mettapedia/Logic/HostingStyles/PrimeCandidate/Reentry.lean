import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ChoiceExtension

/-!
# One rewrite that lifts the bound on reductions

A host of the rule-table evaluator has a term that reduces to itself
(`ContextMap.cycle_of_preserves`).  The probe has a rank, so it has none, for
any evaluator of its premises.  This module shows that the rank is the
property of six rewrites and not of the presentation style: the probe with
one more rewrite has a cyclic reduction.

The added rewrite (`reentryRewrite`) is evaluation by small steps: an
evaluation request whose answer is demanded again in the same space,

    zero-evaluate space subject  ⟶  zero-evaluate space answer.

Under the evaluator of the premises that answers an evaluation with its
subject (`inertEvaluator`: the reading of evaluation in a space that
interprets nothing) every request reduces to itself (`reentry_step`,
`reentry_cycle`), so the extended presentation has no rank
(`reentry_not_rank`).

This lifts one obstruction and gives no hosting map: the extended
presentation still fires its rules at the root alone, has no binder, and its
contexts still have a linear size (`reentryLinearSize`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-- **Evaluation by small steps**: the answer of an evaluation is demanded
again in the same space. -/
def reentryRewrite : RewriteRule :=
  { name := "prime-reenter"
    typeContext :=
      [("space", .base "Space"), ("subject", .base "Atom"), ("answer", .base "Atom")]
    premises := [.relationQuery "ZeroEvaluate" [.fvar "space", .fvar "subject", .fvar "answer"]]
    left := .apply "zero-evaluate" [.fvar "space", .fvar "subject"]
    right := .apply "zero-evaluate" [.fvar "space", .fvar "answer"] }

/-- **The probe with evaluation by small steps.** -/
def probeWithReentry : LanguageDef :=
  { language with
    name := "metta-prime-spec-probe-with-reentry"
    rewrites := language.rewrites ++ [reentryRewrite] }

theorem probeWithReentry_typeNames : probeWithReentry.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"] := by
  decide

theorem probeWithReentry_signatures :
    RewriteValidationCertificate.constructorSignatures probeWithReentry =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1)] := by
  decide

theorem probeWithReentry_labels :
    RewriteValidationCertificate.constructorLabels probeWithReentry =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt"] := by
  decide

theorem probeWithReentry_rewrites : probeWithReentry.rewrites =
    [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite, needRewrite,
      needReturnRewrite, reflectedDemandRewrite, reentryRewrite] :=
  rfl

/-- Every rewrite of the extension passes its row of the declaration gate. -/
theorem probeWithReentry_rewrites_checked :
    ∀ rewrite ∈ probeWithReentry.rewrites,
      RewriteValidationCertificate.check probeWithReentry rewrite = true := by
  intro rewrite member
  rw [probeWithReentry_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      probeWithReentry_typeNames, probeWithReentry_signatures, probeWithReentry_labels,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, needRewrite, evaluationDemandRewrite,
      needReturnRewrite, reflectedDemandRewrite, reentryRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      MeTTaZero.metavariable,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The probe with evaluation by small steps passes the declaration
gate.** -/
theorem probeWithReentry_validate : probeWithReentry.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := probeWithReentry)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) probeWithReentry_rewrites_checked

/-- The probe with evaluation by small steps, as a presentation. -/
def reentryPresentation : ValidatedLanguageDef := ⟨probeWithReentry, probeWithReentry_validate⟩

/-- **The evaluator of the premises of a space that interprets nothing**: an
evaluation answers with its subject, and no other relation has an answer. -/
def inertEvaluator : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "ZeroEvaluate" [_, subject, .fvar answer] =>
      [(answer, applyBindings bindings subject) :: bindings]
  | _ => []

/-- **Under that evaluator every evaluation request reduces to itself.** -/
theorem reentry_step (space subject : Pattern) :
    Step inertEvaluator probeWithReentry (.apply "zero-evaluate" [space, subject])
      (.apply "zero-evaluate" [space, subject]) := by
  refine ⟨1, .rule (rule := reentryRewrite)
    (initialBindings := [("subject", subject), ("space", space)])
    (finalBindings := [("answer", subject), ("subject", subject), ("space", space)])
    (by rw [probeWithReentry_rewrites]; simp) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, reentryRewrite, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    simp [inertEvaluator, applyBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [reentryRewrite, applyBindings]

/-- An evaluation request for the unit atom, at one space. -/
def reentryTerm : Contexts.Term probeWithReentry openProcess :=
  ⟨.apply "zero-evaluate" [.bvar 0, unitAtom], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The extended presentation has a cyclic reduction.** -/
theorem reentry_cycle :
    Relation.TransGen (contextTheory inertEvaluator reentryPresentation).rewrites reentryTerm
      reentryTerm :=
  .single ⟨reentryTerm, reentryTerm, Relation.EqvGen.refl _, reentry_step _ _,
    Relation.EqvGen.refl _⟩

/-- **So it has no rank**, under that evaluator. -/
theorem reentry_not_rank : IsEmpty (contextTheory inertEvaluator reentryPresentation).Rank :=
  ⟨fun ranked => ranked.not_cycle reentry_cycle⟩

/-- Its static equivalence is that of the probe. -/
theorem probeWithReentry_quoteDropOnly : QuoteDropOnly probeWithReentry :=
  ⟨rfl, by decide, by decide, by decide⟩

/-- **Its contexts still have a linear size**: the rewrite lifts the bound on
reductions and nothing else. -/
def reentryLinearSize (base : BasePremiseEvaluator) :
    (contextTheory base reentryPresentation).LinearSize :=
  QuoteDropOnly.linearSize reentryPresentation probeWithReentry_quoteDropOnly base

#print axioms probeWithReentry_validate
#print axioms reentry_step
#print axioms reentry_cycle
#print axioms reentry_not_rank
#print axioms reentryLinearSize

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
