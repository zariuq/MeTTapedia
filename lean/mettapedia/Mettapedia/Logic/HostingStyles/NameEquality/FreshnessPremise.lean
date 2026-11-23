import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.WeakEvaluators
import Mettapedia.Logic.HostingStyles.AtomsReduce.Language
import Batteries.Tactic.OpenPrivate

/-!
# The test of two names as a premise

The engine of language definitions has a third way to tell two names apart:
the **freshness premise**.  With names read as free variables, the premise
"the name bound to `x` is fresh for what is bound to `y`" (`differPremise`)
holds exactly when the two names differ (`freshness_iff_differ`), so one
rewrite with that premise does the work of the family of the rules of two
different names: the engine applies it to the atom on two names exactly when
they differ (`differRewrite_fires`).  "Same" comes from the matcher, which
compares the two values of a repeated variable (`matchPattern_repeated`).  The
premise is kept by the injective renamings of the two names
(`freshness_injective_iff`), and not when two names are made one
(`freshness_examples`).

All of this is at the level of the engine: its clause for the premise, its
application of one rewrite, and the classes of evaluators.  No table of the
equality of data and no check of a certificate is built over the premise.

The matching evaluator of the candidates answers no freshness premise
(`matchingEvaluator_freshness`).  This module asks what an evaluator that
answers it keeps and what it loses, of two properties: respecting the static
equivalence (`RespectsStatics`), and answering the root step of a run by the
rules that the space stores (`AnswersByStoredRules`, the weak evaluator).

| evaluator | respects the static equivalence | weak |
|---|---|---|
| the matching evaluator | yes | yes |
| the premise read as the engine reads it (`freshnessEvaluator`) | **no**, where a rewrite has the premise (`freshnessEvaluator_not_respectsStatics`); on the candidate, which has no such rewrite, nothing changes (`freshnessEvaluator_respectsStatics_candidate`) | yes (`freshnessEvaluator_weak`) |
| the premise read through the contraction (`contractingEvaluator`) | yes (`contractingEvaluator_respectsStatics`) | yes (`contractingEvaluator_weak`) |
| the test answered at the root step of a run (`answersWithTest`) | yes (`answersWithTest_respectsStatics`) | **no** (`answersWithTest_not_weak`) |

* The engine resolves the name of the premise only when the bound value is
  written as a variable.  A name written as the quotation of its dropping is
  the same name for the static equivalence, and the premise fails on it
  (`freshness_quoted_fails`).  So the clause of the engine does not respect
  the static equivalence, and the clause that first contracts what is bound
  does.
* Either clause leaves the answers to the root step of a run as they are:
  the evaluator stays weak.  What changes is the presentation, which gets a
  rewrite with a premise (`withDifferPremise`, which passes the declaration
  gate: `withDifferPremise_validate`); a space cannot store that rewrite,
  since a stored atom is an equation without premise.
* If instead the evaluator answers the test itself at the root step of a run,
  it respects the static equivalence and is no longer weak: it answers in the
  space that stores nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AuthoredEvaluators
  (AnswersByStoredRules AnswersRunBy runEvaluator matching_answersByStoredRules
    runEvaluator_contracting_respectsStatics)

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

/-! ## The premise holds exactly when the names differ -/

/-- **The premise that two names differ**: the name bound to `x` is fresh for
what is bound to `y`. -/
def differPremise : Premise := .freshness ⟨"x", .fvar "y"⟩

/-- Two values, bound to the two variables of the premise. -/
def pairBindings (first second : Pattern) : Bindings := [("x", first), ("y", second)]

/-- **The freshness premise of the engine, on two names read as free
variables, holds exactly when the names differ.** -/
theorem freshness_iff_differ (relations : RelationEnv) (lang : LanguageDef)
    (first second : String) :
    premiseStepWithEnv relations lang (pairBindings (.fvar first) (.fvar second)) differPremise =
      if first = second then [] else [pairBindings (.fvar first) (.fvar second)] := by
  by_cases same : first = second
  · subst same
    simp [premiseStepWithEnv, differPremise, pairBindings, resolveFreshVarName, Bindings.lookup,
      applyBindings, checkFreshness, isFresh, freeVars]
  · simp [premiseStepWithEnv, differPremise, pairBindings, resolveFreshVarName, Bindings.lookup,
      applyBindings, checkFreshness, isFresh, freeVars, same]

/-- **Positive and negative**: the premise holds of `a` and `b`, and not of
`a` with itself. -/
theorem freshness_examples (relations : RelationEnv) (lang : LanguageDef) :
    premiseStepWithEnv relations lang (pairBindings (.fvar "a") (.fvar "b")) differPremise =
        [pairBindings (.fvar "a") (.fvar "b")] ∧
      premiseStepWithEnv relations lang (pairBindings (.fvar "a") (.fvar "a")) differPremise =
        [] := by
  rw [freshness_iff_differ, freshness_iff_differ]
  exact ⟨by decide, by decide⟩

/-- **Negative**: the engine does not read a name that is written as the
quotation of its dropping.  The premise fails on it, whatever the other
name. -/
theorem freshness_quoted_fails (relations : RelationEnv) (lang : LanguageDef)
    (first : String) (second : Pattern) :
    premiseStepWithEnv relations lang
      (pairBindings (quoted (dropped (.fvar first))) second) differPremise = [] := by
  simp [premiseStepWithEnv, differPremise, pairBindings, resolveFreshVarName, Bindings.lookup,
    quoted]

/-- **The premise is kept by an injective renaming of the two names**: it
holds of the images exactly when it holds of the names.  A renaming that makes
two names one does not keep it: the premise holds of `a` and `b` and not of
`a` with itself (`freshness_examples`). -/
theorem freshness_injective_iff (relations : RelationEnv) (lang : LanguageDef)
    {naming : String → String} (injective : Function.Injective naming) (first second : String) :
    premiseStepWithEnv relations lang
        (pairBindings (.fvar (naming first)) (.fvar (naming second))) differPremise = [] ↔
      premiseStepWithEnv relations lang (pairBindings (.fvar first) (.fvar second))
        differPremise = [] := by
  rw [freshness_iff_differ, freshness_iff_differ]
  by_cases same : first = second
  · simp [same]
  · simp [same, injective.ne same]

/-- **The matcher of the engine has "same"**: a left side that repeats a
variable matches two names read as free variables exactly when they are one
name. -/
theorem matchPattern_repeated (first second : String) :
    matchPattern (.apply "prime-same" [.fvar "x", .fvar "x"])
        (.apply "prime-same" [.fvar first, .fvar second]) =
      if first = second then [[("x", .fvar first)]] else [] := by
  by_cases same : first = second
  · subst same
    simp [matchPattern, matchArgs, mergeBindings]
  · simp [matchPattern, matchArgs, mergeBindings, same]

/-- **The matching evaluator answers no freshness premise.** -/
theorem matchingEvaluator_freshness (lang : LanguageDef) (bindings : Bindings)
    (condition : FreshnessCondition) :
    matchingEvaluator lang bindings (.freshness condition) = [] := rfl

/-! ## Respecting a static equivalence of quotation and dropping -/

/-- Where the static equivalence is that of quotation and dropping, an
evaluator respects it when it answers a premise alike, up to contraction, on
bindings whose values have the same contractions. -/
theorem respectsStatics_of_contractions {base : BasePremiseEvaluator} {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (each : ∀ premise ∈ presentedPremises lang, ∀ {first second : Bindings},
      BindingsRelated (fun left right => contract left = contract right) first second →
        ∀ result ∈ base lang first premise, ∃ other ∈ base lang second premise,
          BindingsRelated (fun left right => contract left = contract right) result other) :
    RespectsStatics base lang := by
  intro premise member first second related result answered
  obtain ⟨other, found, same⟩ := each premise member
    (related.mono fun _ _ equivalent => only.equationEquiv_iff.mp equivalent) result answered
  exact ⟨other, found, same.mono fun _ _ equal => only.equationEquiv_iff.mpr equal⟩

/-- And conversely. -/
theorem contractions_of_respectsStatics {base : BasePremiseEvaluator} {lang : LanguageDef}
    (only : QuoteDropOnly lang) (respects : RespectsStatics base lang) {premise : Premise}
    (member : premise ∈ presentedPremises lang) {first second : Bindings}
    (related : BindingsRelated (fun left right => contract left = contract right) first second)
    {result : Bindings} (answered : result ∈ base lang first premise) :
    ∃ other ∈ base lang second premise,
      BindingsRelated (fun left right => contract left = contract right) result other := by
  obtain ⟨other, found, same⟩ := respects premise member
    (related.mono fun _ _ equal => only.equationEquiv_iff.mpr equal) result answered
  exact ⟨other, found, same.mono fun _ _ equivalent => only.equationEquiv_iff.mp equivalent⟩

/-! ## A presentation with the premise -/

/-- The constructor of the atom that asks whether two names differ. -/
def differConstructor : GrammarRule :=
  plainConstructor "prime-differ" "Atom"
    [.simple "x" (.base "CandidateName"), .simple "y" (.base "CandidateName")]

/-- **A rewrite with the premise**: the atom `(prime-differ x y)` rewrites to
the unit atom when the two names differ. -/
def differRewrite : RewriteRule :=
  { name := "NamesDiffer"
    typeContext := [("x", .base "CandidateName"), ("y", .base "CandidateName")]
    premises := [differPremise]
    left := .apply "prime-differ" [.fvar "x", .fvar "y"]
    right := unitAtom }

/-- **The candidate in which atoms reduce, with one constructor and one
rewrite more**: the atom that asks whether two names differ, and the rewrite
of the premise.  It serves as a presentation that hands the premise to its
evaluator; it is not offered as a candidate. -/
def withDifferPremise : LanguageDef :=
  { atomsReduce with
    terms := atomsReduce.terms ++ [differConstructor]
    rewrites := atomsReduce.rewrites ++ [differRewrite] }

/-- Its static equivalence is that of quotation and dropping. -/
theorem withDifferPremise_quoteDropOnly : QuoteDropOnly withDifferPremise :=
  ⟨rfl, by decide, by decide, by decide⟩

/-- Its three types. -/
theorem withDifferPremise_typeNames :
    withDifferPremise.typeNames = ["Atom", "Space", "CandidateName"] := by
  decide

/-- Its constructors with their numbers of arguments: those of the candidate,
and the atom of the premise. -/
theorem withDifferPremise_signatures :
    RewriteValidationCertificate.constructorSignatures withDifferPremise =
      [("=", 2), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("prime-symbol", 1), ("prime-run", 2), ("App", 2), ("Lam", 2), ("Pi", 2),
        ("prime-differ", 2)] := by
  decide

/-- The labels of its constructors. -/
theorem withDifferPremise_labels :
    RewriteValidationCertificate.constructorLabels withDifferPremise =
      ["=", "prime-unit", "prime-quote", "prime-drop", "prime-space-empty", "prime-space-add",
        "prime-variable", "prime-symbol", "prime-run", "App", "Lam", "Pi", "prime-differ"] := by
  decide

/-- Every rewrite passes its row of the declaration gate. -/
theorem withDifferPremise_rewrites_checked :
    ∀ rewrite ∈ withDifferPremise.rewrites,
      RewriteValidationCertificate.check withDifferPremise rewrite = true := by
  intro rewrite member
  have listed : rewrite ∈
      [betaRule, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule, lamDomainRule,
        lamBodyRule, releaseRule, runSubjectRule, runRewrite, runAppFunctionRule,
        runAppArgumentRule, runPiDomainRule, runPiBodyRule, runLamDomainRule, runLamBodyRule,
        differRewrite] := member
  clear member
  rename' listed => member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
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
      withDifferPremise_typeNames, withDifferPremise_signatures, withDifferPremise_labels,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft, releaseRule, runSubjectRule,
      runRewrite, runAppFunctionRule, runAppArgumentRule, runPiDomainRule, runPiBodyRule,
      runLamDomainRule, runLamBodyRule, runPattern, differRewrite, differPremise, unitAtom,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **It passes the declaration gate.** -/
theorem withDifferPremise_validate : withDifferPremise.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := withDifferPremise)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) withDifferPremise_rewrites_checked

/-- Its premises are those of the candidate and the premise of the new
rewrite. -/
theorem mem_presentedPremises_withDifferPremise {premise : Premise} :
    premise ∈ presentedPremises withDifferPremise ↔
      premise ∈ presentedPremises atomsReduce ∨ premise = differPremise := by
  simp only [presentedPremises, withDifferPremise, List.flatMap_append, List.mem_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, differRewrite, List.mem_singleton]
  tauto

/-- **Positive**: it hands the premise to its evaluator.  **Negative**: the
candidate does not. -/
theorem differPremise_presented :
    differPremise ∈ presentedPremises withDifferPremise ∧
      differPremise ∉ presentedPremises atomsReduce := by
  refine ⟨mem_presentedPremises_withDifferPremise.mpr (.inr rfl), fun member => ?_⟩
  rcases atomsReduce_premises _ member with listed | ⟨source, target, same⟩
  · rw [presentedPremises_probeWithRun] at listed
    simp [differPremise, runPremise] at listed
  · cases same

/-- **One rewrite for the whole family**: the engine applies the rewrite of the
premise to the atom on two names read as free variables exactly when the names
differ, and then it gives the unit atom. -/
theorem differRewrite_fires (relations : RelationEnv) (first second : String) :
    applyRuleWithPremisesUsing relations withDifferPremise differRewrite
        (.apply "prime-differ" [.fvar first, .fvar second]) =
      if first = second then [] else [unitAtom] := by
  have aligned : ∀ bindings : Bindings,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule withDifferPremise
        differRewrite bindings = applyBindings bindings differRewrite.right :=
    fun bindings => applyBindingsForRule_eq_applyBindings _ _ bindings (by decide)
  unfold applyRuleWithPremisesUsing
  simp only [matchPatternForRule_eq_syntactic, aligned]
  by_cases same : first = second
  · subst same
    simp [differRewrite, matchPattern, matchArgs, mergeBindings, applyPremisesWithEnv,
      premiseStepWithEnv, differPremise, resolveFreshVarName, Bindings.lookup, applyBindings,
      checkFreshness, isFresh, freeVars]
  · simp [differRewrite, matchPattern, matchArgs, mergeBindings, applyPremisesWithEnv,
      premiseStepWithEnv, differPremise, resolveFreshVarName, Bindings.lookup, applyBindings,
      checkFreshness, isFresh, freeVars, same, unitAtom]

/-! ## The premise as the engine reads it -/

/-- **The evaluator that answers a freshness premise as the engine does**, and
every other premise as the matching evaluator does. -/
def freshnessEvaluator : BasePremiseEvaluator := fun lang bindings premise =>
  match premise with
  | .freshness condition =>
      premiseStepWithEnv RelationEnv.empty lang bindings (.freshness condition)
  | other => matchingEvaluator lang bindings other

/-- It answers the root step of a run as the matching evaluator does. -/
theorem freshnessEvaluator_answersRunBy :
    AnswersRunBy freshnessEvaluator fun space subject =>
      matchResults (contract space) (contract subject) := fun _ _ => rfl

/-- **It stays weak**: its answers to the root step of a run are the instances
of the rules that the space stores. -/
theorem freshnessEvaluator_weak :
    ∃ answers : Pattern → Pattern → List Pattern,
      AnswersByStoredRules answers ∧ AnswersRunBy freshnessEvaluator answers :=
  ⟨_, matching_answersByStoredRules, freshnessEvaluator_answersRunBy⟩

/-- **Read as the engine reads it, the premise does not respect the static
equivalence**, in a language whose static equivalence is that of quotation and
dropping and that has a rewrite with the premise.  The names `a` and `b`
differ, and with `a` written as the quotation of its dropping the premise
fails. -/
theorem freshnessEvaluator_not_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (presented : differPremise ∈ presentedPremises lang) :
    ¬ RespectsStatics freshnessEvaluator lang := by
  intro respects
  have related : BindingsRelated (fun left right => contract left = contract right)
      (pairBindings (.fvar "a") (.fvar "b"))
      (pairBindings (quoted (dropped (.fvar "a"))) (.fvar "b")) :=
    .cons ⟨rfl, (contract_quoted_dropped _).symm⟩ (.cons ⟨rfl, rfl⟩ .nil)
  have answered : pairBindings (.fvar "a") (.fvar "b") ∈
      freshnessEvaluator lang (pairBindings (.fvar "a") (.fvar "b")) differPremise := by
    have shape : freshnessEvaluator lang (pairBindings (.fvar "a") (.fvar "b")) differPremise =
        premiseStepWithEnv RelationEnv.empty lang (pairBindings (.fvar "a") (.fvar "b"))
          differPremise := rfl
    rw [shape, (freshness_examples RelationEnv.empty lang).1]
    exact List.mem_singleton.mpr rfl
  obtain ⟨other, found, -⟩ :=
    contractions_of_respectsStatics only respects presented related answered
  have none : freshnessEvaluator lang (pairBindings (quoted (dropped (.fvar "a"))) (.fvar "b"))
      differPremise = [] := freshness_quoted_fails RelationEnv.empty lang "a" (.fvar "b")
  rw [none] at found
  cases found

/-- So it does not in the language that has the rewrite of the premise. -/
theorem freshnessEvaluator_not_respectsStatics_withDifferPremise :
    ¬ RespectsStatics freshnessEvaluator withDifferPremise :=
  freshnessEvaluator_not_respectsStatics withDifferPremise_quoteDropOnly differPremise_presented.1

/-- On a premise of the candidate it answers as the matching evaluator
does. -/
theorem freshnessEvaluator_eq_matching {premise : Premise}
    (member : premise ∈ presentedPremises atomsReduce) (lang : LanguageDef) (bindings : Bindings) :
    freshnessEvaluator lang bindings premise = matchingEvaluator lang bindings premise := by
  rcases atomsReduce_premises premise member with listed | ⟨source, target, rfl⟩
  · rw [presentedPremises_probeWithRun] at listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- **On the candidate nothing changes**: the candidate has no rewrite with a
freshness premise, and the evaluator respects its static equivalence. -/
theorem freshnessEvaluator_respectsStatics_candidate :
    RespectsStatics freshnessEvaluator atomsReduce := by
  refine respectsStatics_of_contractions atomsReduce_quoteDropOnly ?_
  intro premise member first second related result answered
  rw [freshnessEvaluator_eq_matching member] at answered ⊢
  exact contractions_of_respectsStatics atomsReduce_quoteDropOnly atomsReduce_respectsStatics
    member related answered

/-! ## The premise read through the contraction -/

/-- The bindings with every value contracted. -/
def contractBindings (bindings : Bindings) : Bindings :=
  bindings.map fun binding => (binding.1, contract binding.2)

/-- Bindings whose values have the same contractions are one list once
contracted. -/
theorem contractBindings_eq {first second : Bindings}
    (related : BindingsRelated (fun left right => contract left = contract right) first second) :
    contractBindings first = contractBindings second := by
  unfold BindingsRelated at related
  induction related with
  | nil => rfl
  | cons pair _ ih =>
      simp only [contractBindings, List.map_cons, List.cons.injEq, Prod.mk.injEq]
      exact ⟨⟨pair.1, pair.2⟩, ih⟩

/-- **The evaluator that answers a freshness premise on the contractions of
the bound values**: it keeps the bindings when the engine's premise holds of
their contractions.  Every other premise it answers as the matching evaluator
does. -/
def contractingEvaluator : BasePremiseEvaluator := fun lang bindings premise =>
  match premise with
  | .freshness condition =>
      if (premiseStepWithEnv RelationEnv.empty lang (contractBindings bindings)
          (.freshness condition)).isEmpty then [] else [bindings]
  | other => matchingEvaluator lang bindings other

/-- **Positive**: on the name `a`, written as the quotation of its dropping,
and the name `b` the premise holds.  **Negative**: on `a` written so and `a`
it does not. -/
theorem contractingEvaluator_examples (lang : LanguageDef) :
    contractingEvaluator lang (pairBindings (quoted (dropped (.fvar "a"))) (.fvar "b"))
        differPremise = [pairBindings (quoted (dropped (.fvar "a"))) (.fvar "b")] ∧
      contractingEvaluator lang (pairBindings (quoted (dropped (.fvar "a"))) (.fvar "a"))
        differPremise = [] := by
  have contracted : ∀ second : String,
      contractBindings (pairBindings (quoted (dropped (.fvar "a"))) (.fvar second)) =
        pairBindings (.fvar "a") (.fvar second) := by
    intro second
    simp [contractBindings, pairBindings, contract_quoted_dropped, contract]
  constructor
  · show (if (premiseStepWithEnv RelationEnv.empty lang (contractBindings _) differPremise).isEmpty
      then [] else [_]) = _
    rw [contracted, freshness_iff_differ]
    rfl
  · show (if (premiseStepWithEnv RelationEnv.empty lang (contractBindings _) differPremise).isEmpty
      then [] else [_]) = _
    rw [contracted, freshness_iff_differ]
    rfl

/-- It answers the root step of a run as the matching evaluator does. -/
theorem contractingEvaluator_answersRunBy :
    AnswersRunBy contractingEvaluator fun space subject =>
      matchResults (contract space) (contract subject) := fun _ _ => rfl

/-- **It stays weak.** -/
theorem contractingEvaluator_weak :
    ∃ answers : Pattern → Pattern → List Pattern,
      AnswersByStoredRules answers ∧ AnswersRunBy contractingEvaluator answers :=
  ⟨_, matching_answersByStoredRules, contractingEvaluator_answersRunBy⟩

/-- On a premise of the candidate it answers as the matching evaluator
does. -/
theorem contractingEvaluator_eq_matching {premise : Premise}
    (member : premise ∈ presentedPremises atomsReduce) (lang : LanguageDef) (bindings : Bindings) :
    contractingEvaluator lang bindings premise = matchingEvaluator lang bindings premise := by
  rcases atomsReduce_premises premise member with listed | ⟨source, target, rfl⟩
  · rw [presentedPremises_probeWithRun] at listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- **Read through the contraction, the premise respects the static
equivalence**, in the language that has the rewrite of the premise. -/
theorem contractingEvaluator_respectsStatics :
    RespectsStatics contractingEvaluator withDifferPremise := by
  refine respectsStatics_of_contractions withDifferPremise_quoteDropOnly ?_
  intro premise member first second related result answered
  rcases mem_presentedPremises_withDifferPremise.mp member with old | rfl
  · have moved : result ∈ matchingEvaluator atomsReduce first premise := by
      rw [contractingEvaluator_eq_matching old] at answered
      exact answered
    obtain ⟨other, found, same⟩ := contractions_of_respectsStatics atomsReduce_quoteDropOnly
      atomsReduce_respectsStatics old related moved
    refine ⟨other, ?_, same⟩
    rw [contractingEvaluator_eq_matching old]
    exact found
  · have shape : ∀ bindings : Bindings, contractingEvaluator withDifferPremise bindings
        differPremise = if (premiseStepWithEnv RelationEnv.empty withDifferPremise
          (contractBindings bindings) differPremise).isEmpty then [] else [bindings] :=
      fun _ => rfl
    rw [shape] at answered
    rw [shape, ← contractBindings_eq related]
    split at answered
    · cases answered
    · next holds =>
      obtain rfl := List.mem_singleton.mp answered
      rw [if_neg holds]
      exact ⟨second, List.mem_singleton.mpr rfl, related⟩

/-! ## The test answered at the root step of a run -/

/-- **The answer of a built-in test**: for a subject that is the atom
`(prime-differ a b)` on two names read as free variables, the unit atom when
the names differ. -/
def builtinTestAnswers (subject : Pattern) : List Pattern :=
  match subject with
  | .apply "prime-differ" [.fvar first, .fvar second] => if first = second then [] else [unitAtom]
  | _ => []

/-- **The answers of the stored rules, and those of the built-in test.** -/
def answersWithTest (space subject : Pattern) : List Pattern :=
  matchResults (contract space) (contract subject) ++ builtinTestAnswers (contract subject)

/-- **Positive and negative**: in the space that stores nothing it answers
the test of `a` and `b`, and not the test of `a` with itself. -/
theorem answersWithTest_examples :
    answersWithTest emptySpace (.apply "prime-differ" [.fvar "a", .fvar "b"]) = [unitAtom] ∧
      answersWithTest emptySpace (.apply "prime-differ" [.fvar "a", .fvar "a"]) = [] := by
  decide

/-- **It respects the static equivalence**: it reads the space and the subject
through their contractions. -/
theorem answersWithTest_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) :
    RespectsStatics (runEvaluator answersWithTest) lang :=
  runEvaluator_contracting_respectsStatics only rules fun space subject =>
    matchResults space subject ++ builtinTestAnswers subject

/-- **It is not weak**: its answers are the instances of the rules that the
stored atoms are read as for no reading, since it answers in the space that
stores nothing. -/
theorem answersWithTest_not_weak : ¬ AnswersByStoredRules answersWithTest := by
  intro weak
  have bound := weak.length_le emptySpace (.apply "prime-differ" [.fvar "a", .fvar "b"])
  rw [answersWithTest_examples.1] at bound
  revert bound
  decide

#print axioms freshness_iff_differ
#print axioms freshness_injective_iff
#print axioms matchPattern_repeated
#print axioms freshness_quoted_fails
#print axioms respectsStatics_of_contractions
#print axioms withDifferPremise_validate
#print axioms differRewrite_fires
#print axioms differPremise_presented
#print axioms freshnessEvaluator_weak
#print axioms freshnessEvaluator_not_respectsStatics
#print axioms freshnessEvaluator_not_respectsStatics_withDifferPremise
#print axioms freshnessEvaluator_respectsStatics_candidate
#print axioms contractingEvaluator_examples
#print axioms contractingEvaluator_weak
#print axioms contractingEvaluator_respectsStatics
#print axioms answersWithTest_respectsStatics
#print axioms answersWithTest_not_weak

end Mettapedia.Logic.HostingStyles.NameEquality
