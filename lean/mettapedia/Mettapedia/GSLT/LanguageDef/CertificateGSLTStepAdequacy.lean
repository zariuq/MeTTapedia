import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepTraceLanguage
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Step adequacy: the generated trace checker meets the declarative semantics

The weld between the proof lane and the operational lane, on a language
exercising both fragment features: a ground rewrite `a → b` and an authored
congruence rule `f p → f q` whose single premise is
`Premise.congruence p q`.

For the generated trace definition of this language:

* **soundness** — every checked `Step` derivation is a declarative
  `langReduces` step, and every checked `Steps` derivation is a reflexive-
  transitive reduction;
* **completeness** — every declarative step from a well-formed term has a
  checked `Step` derivation, and likewise for reduction sequences;
* **the modal weld** — `derivedDiamond` over the language's reduction span
  holds exactly when a checked one-step certificate to the target predicate
  exists; the `derivedBox` constraint follows from checked predecessor
  certificates.

Well-formedness (top-level groundness plus canonical binder metadata) is the
checker's argument discipline; steps preserve it, so it is a hypothesis on
sources only.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## The fixture language -/

private def genType : TypeDecl := TypeDecl.plain "GP"

private def genA : GrammarRule :=
  { label := "gen-a", category := "GP", params := []
    syntaxPattern := [] }

private def genB : GrammarRule :=
  { label := "gen-b", category := "GP", params := []
    syntaxPattern := [] }

private def genF : GrammarRule :=
  { label := "gen-f", category := "GP"
    params := [.simple "arg" (.base "GP")]
    syntaxPattern := [] }

private def termA : Pattern := .apply "gen-a" []
private def termB : Pattern := .apply "gen-b" []
private def termF (argument : Pattern) : Pattern := .apply "gen-f" [argument]

private def stepJ (source target : Pattern) : Pattern :=
  .apply "Step" [source, target]

private def stepsJ (source target : Pattern) : Pattern :=
  .apply "Steps" [source, target]

private def rewriteAB : RewriteRule :=
  { name := "ab"
    typeContext := []
    premises := []
    left := termA
    right := termB }

private def congruenceF : RewriteRule :=
  { name := "cong-f"
    typeContext := [("p", .base "GP"), ("q", .base "GP")]
    premises := [.congruence (.fvar "p") (.fvar "q")]
    left := termF (.fvar "p")
    right := termF (.fvar "q") }

private def stepLanguage : LanguageDef :=
  { name := "certificate-gslt-step-adequacy-fixture"
    types := [genType]
    terms := [genA, genB, genF]
    equations := []
    rewrites := [rewriteAB, congruenceF] }

private theorem stepPremisesSupported :
    LanguageDef.directTraceSupported stepLanguage = true := by
  rfl

private def directStepLanguage : DirectTraceLanguage :=
  ⟨stepLanguage, stepPremisesSupported⟩

/-! ## Admission of the generated definition -/

private theorem abRule_id_spelling :
    ("step-rewrite-" ++ "ab" : String) = "step-rewrite-ab" := rfl

private theorem congFRule_id_spelling :
    ("step-rewrite-" ++ "cong-f" : String) = "step-rewrite-cong-f" := rfl

private theorem stepAdequacy_validate :
    (stepTraceDefinition directStepLanguage).toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepTraceDefinition, directStepLanguage, stepLanguage, genType, genA, genB, genF,
      LanguageDef.typeNames, TermParam.typeExpr, TypeExpr.baseNames,
      TypeDecl.plain]

private theorem stepAdequacy_valid :
    (stepTraceDefinition directStepLanguage).isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [stepAdequacy_validate]
  simp [stepTraceDefinition, directStepLanguage, stepLanguage, genType, genA, genB, genF,
    rewriteAB, congruenceF, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, termA, termB, termF,
    abRule_id_spelling, congFRule_id_spelling,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.ruleIds, RuleSchema.isValidIn,
    CalculusLanguageDef.judgmentSchemaValid, CalculusLanguageDef.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private def traceValidated : ValidatedCalculusLanguageDef :=
  ⟨stepTraceDefinition directStepLanguage, stepAdequacy_valid⟩

/-! ## Well-formed terms: the checker's argument discipline -/

private def wellFormed (term : Pattern) : Prop :=
  Pattern.isGroundAt 0 term = true ∧
    term.hasCanonicalBinderMetadata = true

private theorem wellFormed_termA : wellFormed termA := by
  constructor <;> rfl

private theorem wellFormed_termB : wellFormed termB := by
  constructor <;> rfl

private theorem wellFormed_termF_iff (argument : Pattern) :
    wellFormed (termF argument) ↔ wellFormed argument := by
  simp [wellFormed, termF, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Matcher computations on the fixture patterns -/

private theorem matchPattern_termA_inversion {source : Pattern}
    {bindings : Bindings}
    (member : bindings ∈ matchPattern termA source) :
    source = termA ∧ bindings = [] := by
  cases source with
  | apply constructor arguments =>
      simp only [termA, matchPattern] at member
      split at member
      case isTrue guard =>
        simp only [Bool.and_eq_true, beq_iff_eq] at guard
        obtain ⟨headEq, lengthEq⟩ := guard
        have argumentsEmpty : arguments = [] := by
          cases arguments with
          | nil => rfl
          | cons head tail => simp at lengthEq
        subst headEq
        subst argumentsEmpty
        simp [matchArgs] at member
        simp [termA, member]
      case isFalse => simp at member
  | bvar index => simp [termA, matchPattern] at member
  | fvar name => simp [termA, matchPattern] at member
  | lambda binder body => simp [termA, matchPattern] at member
  | multiLambda arity binders body => simp [termA, matchPattern] at member
  | subst body replacement => simp [termA, matchPattern] at member
  | collection collectionType elements rest =>
      simp [termA, matchPattern] at member

private theorem matchPattern_congF_forward (argument : Pattern) :
    matchPattern (termF (.fvar "p")) (termF argument) =
      [[("p", argument)]] := by
  simp [termF, matchPattern, matchArgs, mergeBindings]

private theorem matchPattern_congF_inversion {source : Pattern}
    {bindings : Bindings}
    (member : bindings ∈ matchPattern (termF (.fvar "p")) source) :
    ∃ argument, source = termF argument ∧ bindings = [("p", argument)] := by
  cases source with
  | apply constructor arguments =>
      simp only [termF, matchPattern] at member
      split at member
      case isTrue guard =>
        simp only [Bool.and_eq_true, beq_iff_eq] at guard
        obtain ⟨headEq, lengthEq⟩ := guard
        obtain ⟨argument, argumentsShape⟩ : ∃ a, arguments = [a] := by
          cases arguments with
          | nil => simp at lengthEq
          | cons head tail =>
              cases tail with
              | nil => exact ⟨head, rfl⟩
              | cons second rest => simp at lengthEq
        subst headEq
        subst argumentsShape
        simp [matchArgs, matchPattern, mergeBindings] at member
        exact ⟨argument, by simp [termF], member⟩
      case isFalse => simp at member
  | bvar index => simp [termF, matchPattern] at member
  | fvar name => simp [termF, matchPattern] at member
  | lambda binder body => simp [termF, matchPattern] at member
  | multiLambda arity binders body => simp [termF, matchPattern] at member
  | subst body replacement => simp [termF, matchPattern] at member
  | collection collectionType elements rest =>
      simp [termF, matchPattern] at member

private theorem mergeBindings_p_q (first second : Pattern) :
    mergeBindings [("p", first)] [("q", second)] =
      some [("q", second), ("p", first)] := by
  simp [mergeBindings, List.foldlM, List.find?]

private theorem applyBindings_fvar_p (first : Pattern) :
    applyBindings [("p", first)] (.fvar "p") = first := by
  simp [applyBindings, List.find?]

/-! ## Engine computations on the fixture rules -/

private theorem matchRule_ab_inversion {source : Pattern}
    {bindings : Bindings}
    (member : bindings ∈ matchPatternForRule stepLanguage rewriteAB source) :
    source = termA ∧ bindings = [] := by
  rw [matchPatternForRule_eq_syntactic]
    at member
  exact matchPattern_termA_inversion member

private theorem matchRule_congF_inversion {source : Pattern}
    {bindings : Bindings}
    (member :
      bindings ∈ matchPatternForRule stepLanguage congruenceF source) :
    ∃ argument, source = termF argument ∧ bindings = [("p", argument)] := by
  rw [matchPatternForRule_eq_syntactic]
    at member
  exact matchPattern_congF_inversion member

private theorem applyRule_ab :
    applyBindingsForRule stepLanguage rewriteAB [] = termB := by
  rw [applyBindingsForRule_eq_syntactic]
  simp [rewriteAB, termB, applyBindings]

private theorem applyRule_congF (first second : Pattern) :
    applyBindingsForRule stepLanguage congruenceF
        [("q", second), ("p", first)] = termF second := by
  rw [applyBindingsForRule_eq_syntactic]
  simp [congruenceF, termF, applyBindings, List.find?]

/-- The authored ground step is a declarative reduction. -/
private theorem ab_langReduces : langReduces stepLanguage termA termB := by
  refine ⟨1, .rule (rule := rewriteAB) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [stepLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    simp [rewriteAB, termA, matchPattern, matchArgs]
  · exact .nil []
  · exact applyRule_ab

/-! ## Instantiation of the generated schemas -/

private def abInstance : RuleInstance := ⟨⟨"step-rewrite-ab"⟩, []⟩

private def congFInstance (first second : Pattern) : RuleInstance :=
  ⟨⟨"step-rewrite-cong-f"⟩, [first, second]⟩

private def reflInstance (point : Pattern) : RuleInstance :=
  ⟨⟨"steps-refl"⟩, [point]⟩

private def transInstance (source middle target : Pattern) : RuleInstance :=
  ⟨⟨"steps-trans"⟩, [source, middle, target]⟩

private theorem ab_instantiates :
    instantiateRule? traceValidated abInstance =
      some ([], stepJ termA termB) := by
  simp [instantiateRule?, traceValidated, stepTraceDefinition, directStepLanguage, stepLanguage,
    rewriteAB, congruenceF, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, abInstance, stepJ, termA, termB,
    abRule_id_spelling, congFRule_id_spelling, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem congF_instantiates (first second : Pattern)
    (wfFirst : wellFormed first) (wfSecond : wellFormed second) :
    instantiateRule? traceValidated (congFInstance first second) =
      some ([stepJ first second], stepJ (termF first) (termF second)) := by
  obtain ⟨firstGround, firstBinder⟩ := wfFirst
  obtain ⟨secondGround, secondBinder⟩ := wfSecond
  simp [instantiateRule?, traceValidated, stepTraceDefinition, directStepLanguage, stepLanguage,
    rewriteAB, congruenceF, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, congFInstance, stepJ, termF,
    abRule_id_spelling, congFRule_id_spelling, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, firstGround, firstBinder,
    secondGround, secondBinder, lookupArgumentAt?, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem refl_instantiates (point : Pattern)
    (wfPoint : wellFormed point) :
    instantiateRule? traceValidated (reflInstance point) =
      some ([], stepsJ point point) := by
  obtain ⟨pointGround, pointBinder⟩ := wfPoint
  simp [instantiateRule?, traceValidated, stepTraceDefinition, directStepLanguage, stepLanguage,
    rewriteAB, congruenceF, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, reflInstance, stepsJ,
    abRule_id_spelling, congFRule_id_spelling, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, pointGround, pointBinder,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem trans_instantiates (source middle target : Pattern)
    (wfSource : wellFormed source) (wfMiddle : wellFormed middle)
    (wfTarget : wellFormed target) :
    instantiateRule? traceValidated (transInstance source middle target) =
      some ([stepJ source middle, stepsJ middle target],
        stepsJ source target) := by
  obtain ⟨sourceGround, sourceBinder⟩ := wfSource
  obtain ⟨middleGround, middleBinder⟩ := wfMiddle
  obtain ⟨targetGround, targetBinder⟩ := wfTarget
  simp [instantiateRule?, traceValidated, stepTraceDefinition, directStepLanguage, stepLanguage,
    rewriteAB, congruenceF, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, transInstance, stepJ, stepsJ,
    abRule_id_spelling, congFRule_id_spelling, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, sourceGround, sourceBinder,
    middleGround, middleBinder, targetGround, targetBinder,
    lookupArgumentAt?, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

/-! ## Shape of every admitted rule application -/

private theorem argumentsValidAt_one_inversion {name : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt [(name, 0)] arguments = true) :
    ∃ argument, arguments = [argument] ∧ wellFormed argument := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons argument rest =>
      cases rest with
      | nil =>
          simp only [argumentsValidAt, argumentValidAt, Bool.and_eq_true]
            at valid
          exact ⟨argument, rfl, valid.1.1, valid.1.2⟩
      | cons second rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_two_inversion
    {firstName secondName : String} {arguments : List Pattern}
    (valid :
      argumentsValidAt [(firstName, 0), (secondName, 0)] arguments = true) :
    ∃ first second, arguments = [first, second] ∧
      wellFormed first ∧ wellFormed second := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil =>
              simp only [argumentsValidAt, argumentValidAt,
                Bool.and_eq_true] at valid
              exact ⟨first, second, rfl, ⟨valid.1.1, valid.1.2⟩,
                valid.2.1.1, valid.2.1.2⟩
          | cons third rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_three_inversion
    {firstName secondName thirdName : String} {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0)] arguments = true) :
    ∃ first second third, arguments = [first, second, third] ∧
      wellFormed first ∧ wellFormed second ∧ wellFormed third := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil =>
                  simp only [argumentsValidAt, argumentValidAt,
                    Bool.and_eq_true] at valid
                  exact ⟨first, second, third, rfl,
                    ⟨valid.1.1, valid.1.2⟩, ⟨valid.2.1.1, valid.2.1.2⟩,
                    valid.2.2.1.1, valid.2.2.1.2⟩
              | cons fourth rest => simp [argumentsValidAt] at valid

/-- Every admitted rule application of the generated definition is one of
the four generated schemas, with well-formed arguments and the schema's
instantiated premises and conclusion. -/
private theorem application_shape {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application :
      RuleApplication traceValidated ruleInstance premises conclusion) :
    (premises = [] ∧ conclusion = stepJ termA termB) ∨
    (∃ first second, wellFormed first ∧ wellFormed second ∧
      premises = [stepJ first second] ∧
      conclusion = stepJ (termF first) (termF second)) ∨
    (∃ point, wellFormed point ∧ premises = [] ∧
      conclusion = stepsJ point point) ∨
    (∃ source middle target, wellFormed source ∧ wellFormed middle ∧
      wellFormed target ∧ premises = [stepJ source middle,
        stepsJ middle target] ∧ conclusion = stepsJ source target) := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : traceValidated.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have ruleCases :
          rule = rewriteStepRule rewriteAB ∨
          rule = rewriteStepRule congruenceF ∨
          rule = stepReflRule ∨ rule = stepTransRule := by
        have := lookup
        simp only [traceValidated, stepTraceDefinition, directStepLanguage, stepLanguage,
          CalculusLanguageDef.lookupRule?, List.map] at this
        all_goals simp_all
        rcases this with ⟨_, ruleEq⟩ | ⟨_, ⟨_, ruleEq⟩ | ⟨_, ⟨_, ruleEq⟩ |
          ⟨_, _, ruleEq⟩⟩⟩
        · exact Or.inl ruleEq.symm
        · exact Or.inr (Or.inl ruleEq.symm)
        · exact Or.inr (Or.inr (Or.inl ruleEq.symm))
        · exact Or.inr (Or.inr (Or.inr ruleEq.symm))
      rcases ruleCases with abCase | congFCase | reflCase | transCase
      · subst abCase
        refine Or.inl ?_
        have argumentsEmpty : ruleInstance.arguments = [] := by
          by_cases valid : argumentsValidAt
              (rewriteStepRule rewriteAB).metavariables
              ruleInstance.arguments = true
          · simp only [rewriteStepRule, rewriteAB] at valid
            cases arguments : ruleInstance.arguments with
            | nil => rfl
            | cons head tail =>
                rw [arguments] at valid
                simp [argumentsValidAt] at valid
          · simp [valid] at executable
        rw [argumentsEmpty] at executable
        simp [rewriteStepRule, rewriteAB, rewritePremiseJudgments,
          argumentsValidAt, instantiateSchemas?, instantiateSchema?,
          instantiateSchemaAt?, instantiateSchemasAt?, termA,
          termB] at executable
        exact ⟨executable.1, executable.2.symm⟩
      · subst congFCase
        refine Or.inr (Or.inl ?_)
        by_cases valid : argumentsValidAt
            (rewriteStepRule congruenceF).metavariables
            ruleInstance.arguments = true
        · have inversion := argumentsValidAt_two_inversion
            (by simpa [rewriteStepRule, congruenceF] using valid)
          obtain ⟨first, second, argumentsShape, wfFirst, wfSecond⟩ :=
            inversion
          rw [argumentsShape] at executable
          simp [rewriteStepRule, congruenceF, rewritePremiseJudgments,
            argumentsValidAt, argumentValidAt, wfFirst.1, wfFirst.2,
            wfSecond.1, wfSecond.2, lookupArgumentAt?,
            instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
            instantiateSchemasAt?, termF] at executable
          exact ⟨first, second, wfFirst, wfSecond,
            executable.1.symm, executable.2.symm⟩
        · simp [valid] at executable
      · subst reflCase
        refine Or.inr (Or.inr (Or.inl ?_))
        by_cases valid : argumentsValidAt stepReflRule.metavariables
            ruleInstance.arguments = true
        · have inversion := argumentsValidAt_one_inversion
            (by simpa [stepReflRule] using valid)
          obtain ⟨point, argumentsShape, wfPoint⟩ := inversion
          rw [argumentsShape] at executable
          simp [stepReflRule, argumentsValidAt, argumentValidAt,
            wfPoint.1, wfPoint.2, lookupArgumentAt?, instantiateSchemas?,
            instantiateSchema?, instantiateSchemaAt?,
            instantiateSchemasAt?] at executable
          exact ⟨point, wfPoint, executable.1, executable.2.symm⟩
        · simp [valid] at executable
      · subst transCase
        refine Or.inr (Or.inr (Or.inr ?_))
        by_cases valid : argumentsValidAt stepTransRule.metavariables
            ruleInstance.arguments = true
        · have inversion := argumentsValidAt_three_inversion
            (by simpa [stepTransRule] using valid)
          obtain ⟨source, middle, target, argumentsShape, wfSource,
            wfMiddle, wfTarget⟩ := inversion
          rw [argumentsShape] at executable
          simp [stepTransRule, argumentsValidAt, argumentValidAt,
            wfSource.1, wfSource.2, wfMiddle.1, wfMiddle.2, wfTarget.1,
            wfTarget.2, lookupArgumentAt?, instantiateSchemas?,
            instantiateSchema?, instantiateSchemaAt?,
            instantiateSchemasAt?] at executable
          exact ⟨source, middle, target, wfSource, wfMiddle, wfTarget,
            executable.1.symm, executable.2.symm⟩
        · simp [valid] at executable

/-! ## Soundness: checked derivations are declarative reductions -/

private abbrev soundClaim (goal : Pattern) : Prop :=
  (∀ source target, goal = stepJ source target →
    langReduces stepLanguage source target) ∧
  (∀ source target, goal = stepsJ source target →
    Relation.ReflTransGen (langReduces stepLanguage) source target)

mutual

private def derivationHeight :
    {goal : Pattern} → Derivation traceValidated goal → Nat
  | _, .byRule _ _ children => childrenHeight children + 1

private def childrenHeight :
    {goals : List Pattern} → DerivationList traceValidated goals → Nat
  | _, .nil => 0
  | _, .cons head tail => derivationHeight head + childrenHeight tail

end

private theorem sound_bounded :
    ∀ (bound : Nat) {goal : Pattern}
      (derivation : Derivation traceValidated goal),
      derivationHeight derivation ≤ bound → soundClaim goal := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound inductionHypothesis =>
      intro goal derivation heightBound
      cases derivation with
      | byRule ruleInstance application children =>
      rcases application_shape application with
        ⟨premisesShape, conclusionShape⟩ |
        ⟨first, second, _wfFirst, _wfSecond, premisesShape,
          conclusionShape⟩ |
        ⟨point, _wfPoint, premisesShape, conclusionShape⟩ |
        ⟨source₀, middle₀, target₀, _wfS, _wfM, _wfT, premisesShape,
          conclusionShape⟩
      · subst conclusionShape
        constructor
        · intro source target goalEq
          simp only [stepJ, termA, termB, Pattern.apply.injEq,
            List.cons.injEq, and_true, true_and] at goalEq
          obtain ⟨sourceEq, targetEq⟩ := goalEq
          rw [← sourceEq, ← targetEq]
          exact ab_langReduces
        · intro source target goalEq
          simp [stepJ, stepsJ] at goalEq
      · subst premisesShape
        subst conclusionShape
        cases children with
        | cons head tail =>
        have headHeight :
            derivationHeight head + 1 ≤ bound := by
          have expand : derivationHeight
              (Derivation.byRule ruleInstance application
                (.cons head tail)) =
              derivationHeight head + childrenHeight tail + 1 := rfl
          rw [expand] at heightBound
          omega
        have headFact := inductionHypothesis (derivationHeight head)
          (by omega) head (Nat.le_refl _)
        have headReduces := headFact.1 first second rfl
        obtain ⟨fuel, stepEvidence⟩ := headReduces
        have congruenceStep :
            langReduces stepLanguage (termF first) (termF second) := by
          refine ⟨fuel + 1, .rule (rule := congruenceF)
            (initialBindings := [("p", first)])
            (finalBindings := [("q", second), ("p", first)])
            ?_ ?_ ?_ ?_⟩
          · simp [stepLanguage]
          · rw [matchPatternForRule_eq_syntactic]
            show [("p", first)] ∈
              matchPattern (termF (.fvar "p")) (termF first)
            rw [matchPattern_congF_forward]
            exact List.mem_singleton.mpr rfl
          · refine .cons (.congruence (candidate := second)
              (premiseBindings := [("q", second)]) ?_ ?_ ?_) (.nil _)
            · rw [applyBindings_fvar_p]
              exact stepEvidence
            · simp [matchPattern]
            · exact mergeBindings_p_q first second
          · exact applyRule_congF first second
        constructor
        · intro source target goalEq
          simp only [stepJ, termF, Pattern.apply.injEq,
            List.cons.injEq, and_true, true_and] at goalEq
          obtain ⟨sourceEq, targetEq⟩ := goalEq
          rw [← sourceEq, ← targetEq]
          exact congruenceStep
        · intro source target goalEq
          simp [stepJ, stepsJ] at goalEq
      · subst conclusionShape
        constructor
        · intro source target goalEq
          simp [stepJ, stepsJ] at goalEq
        · intro source target goalEq
          simp only [stepsJ, Pattern.apply.injEq, List.cons.injEq,
            and_true, true_and] at goalEq
          obtain ⟨sourceEq, targetEq⟩ := goalEq
          rw [← sourceEq, ← targetEq]
      · subst premisesShape
        subst conclusionShape
        cases children with
        | cons headStep tailOne =>
        cases tailOne with
        | cons headSteps tailNil =>
        have heights :
            derivationHeight headStep + 1 ≤ bound ∧
              derivationHeight headSteps + 1 ≤ bound := by
          have expand : derivationHeight
              (Derivation.byRule ruleInstance application
                (.cons headStep (.cons headSteps tailNil))) =
              derivationHeight headStep +
                (derivationHeight headSteps + childrenHeight tailNil) +
                  1 := rfl
          rw [expand] at heightBound
          omega
        have stepFact := (inductionHypothesis (derivationHeight headStep)
          (by omega) headStep (Nat.le_refl _)).1 source₀ middle₀ rfl
        have starFact := (inductionHypothesis (derivationHeight headSteps)
          (by omega) headSteps (Nat.le_refl _)).2 middle₀ target₀ rfl
        constructor
        · intro source target goalEq
          simp [stepJ, stepsJ] at goalEq
        · intro source target goalEq
          simp only [stepsJ, Pattern.apply.injEq, List.cons.injEq,
            and_true, true_and] at goalEq
          obtain ⟨sourceEq, targetEq⟩ := goalEq
          rw [← sourceEq, ← targetEq]
          exact Relation.ReflTransGen.head stepFact starFact

private theorem sound_derivation {goal : Pattern}
    (derivation : Derivation traceValidated goal) : soundClaim goal :=
  sound_bounded (derivationHeight derivation) derivation (Nat.le_refl _)

/-! ## Completeness: declarative reductions have checked derivations -/

private theorem complete_stepAt :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (engineBasePremises RelationEnv.empty) stepLanguage fuel
        source target →
      wellFormed source →
      Nonempty (Derivation traceValidated (stepJ source target)) ∧
        wellFormed target := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel inductionHypothesis =>
      intro source target evidence wfSource
      cases evidence with
      | rule ruleMember matchMember premisesEvidence applyEq =>
          rename_i innerFuel rule initialBindings finalBindings
          have ruleCases : rule = rewriteAB ∨ rule = congruenceF := by
            simpa [stepLanguage] using ruleMember
          rcases ruleCases with abCase | congFCase
          · subst abCase
            obtain ⟨sourceEq, initialEq⟩ :=
              matchRule_ab_inversion matchMember
            subst sourceEq
            subst initialEq
            cases premisesEvidence with
            | nil =>
                rw [applyRule_ab] at applyEq
                subst applyEq
                exact ⟨⟨.byRule abInstance
                  (instantiateRule?_eq_some_iff_application.mp
                    ab_instantiates) .nil⟩, wellFormed_termB⟩
          · subst congFCase
            obtain ⟨argument, sourceEq, initialEq⟩ :=
              matchRule_congF_inversion matchMember
            subst sourceEq
            subst initialEq
            have wfArgument : wellFormed argument :=
              (wellFormed_termF_iff argument).mp wfSource
            cases premisesEvidence with
            | cons premiseEvidence restEvidence =>
                cases premiseEvidence with
                | congruence stepEvidence matchTarget merged =>
                    rename_i candidate
                    rw [applyBindings_fvar_p] at stepEvidence
                    have targetBindings := matchTarget
                    simp only [matchPattern, List.mem_singleton]
                      at targetBindings
                    subst targetBindings
                    rw [mergeBindings_p_q] at merged
                    have middleEq := Option.some.inj merged
                    subst middleEq
                    cases restEvidence with
                    | nil =>
                        rw [applyRule_congF] at applyEq
                        subst applyEq
                        obtain ⟨⟨childDerivation⟩, wfCandidate⟩ :=
                          inductionHypothesis innerFuel (by omega)
                            stepEvidence wfArgument
                        refine ⟨⟨.byRule (congFInstance argument candidate)
                          (instantiateRule?_eq_some_iff_application.mp
                            (congF_instantiates argument candidate
                              wfArgument wfCandidate))
                          (.cons childDerivation .nil)⟩, ?_⟩
                        exact (wellFormed_termF_iff candidate).mpr
                          wfCandidate

/-! ## The adequacy interface -/

/-- A checked `Step` certificate from a well-formed source exists exactly
when the language takes the declarative step. -/
theorem step_adequacy {source target : Pattern}
    (wfSource : wellFormed source) :
    Nonempty (Derivation traceValidated (stepJ source target)) ↔
      langReduces stepLanguage source target := by
  constructor
  · rintro ⟨derivation⟩
    exact (sound_derivation derivation).1 source target rfl
  · rintro ⟨fuel, evidence⟩
    exact (complete_stepAt fuel evidence wfSource).1

private theorem step_preserves_wellFormed {source target : Pattern}
    (step : langReduces stepLanguage source target)
    (wfSource : wellFormed source) : wellFormed target := by
  obtain ⟨fuel, evidence⟩ := step
  exact (complete_stepAt fuel evidence wfSource).2

private theorem star_complete {source target : Pattern}
    (star : Relation.ReflTransGen (langReduces stepLanguage) source target)
    (wfSource : wellFormed source) :
    Nonempty (Derivation traceValidated (stepsJ source target)) ∧
      wellFormed target := by
  revert wfSource
  induction star using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro wfTarget
      exact ⟨⟨.byRule (reflInstance target)
        (instantiateRule?_eq_some_iff_application.mp
          (refl_instantiates target wfTarget)) .nil⟩, wfTarget⟩
  | head headStep restStar restHypothesis =>
      rename_i headSource headMiddle
      intro wfHead
      have wfMiddle := step_preserves_wellFormed headStep wfHead
      obtain ⟨⟨restDerivation⟩, wfTarget⟩ := restHypothesis wfMiddle
      obtain ⟨fuel, evidence⟩ := headStep
      obtain ⟨⟨stepDerivation⟩, -⟩ := complete_stepAt fuel evidence wfHead
      exact ⟨⟨.byRule (transInstance headSource headMiddle target)
        (instantiateRule?_eq_some_iff_application.mp
          (trans_instantiates headSource headMiddle target wfHead
            wfMiddle wfTarget))
        (.cons stepDerivation (.cons restDerivation .nil))⟩, wfTarget⟩

/-- A checked `Steps` certificate from a well-formed source exists exactly
when the language takes a reflexive-transitive reduction sequence. -/
theorem steps_adequacy {source target : Pattern}
    (wfSource : wellFormed source) :
    Nonempty (Derivation traceValidated (stepsJ source target)) ↔
      Relation.ReflTransGen (langReduces stepLanguage) source target := by
  constructor
  · rintro ⟨derivation⟩
    exact (sound_derivation derivation).2 source target rfl
  · intro star
    exact (star_complete star wfSource).1

/-! ## The modal weld -/

/-- The derived step-future modality over a language's reduction span is
existence of a reduct satisfying the predicate. -/
theorem derivedDiamond_langSpanUsing_iff
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (φ : Pattern → Prop) (source : Pattern) :
    derivedDiamond (langSpanUsing relEnv language) φ source ↔
      ∃ target, langReducesUsing relEnv language source target ∧ φ target := by
  constructor
  · rintro ⟨edge, sourceEq, φTarget⟩
    exact ⟨edge.val.2, sourceEq ▸ edge.property, φTarget⟩
  · rintro ⟨target, reduces, φTarget⟩
    exact ⟨⟨(source, target), reduces⟩, rfl, φTarget⟩

/-- OSLF's ◇ is exactly the existence of a checked one-step certificate to
the predicate: the proof-relevant reading of the derived modality. -/
theorem diamond_iff_checked_witness {source : Pattern}
    (wfSource : wellFormed source) (φ : Pattern → Prop) :
    derivedDiamond (langSpan stepLanguage) φ source ↔
      ∃ target,
        Nonempty (Derivation traceValidated (stepJ source target)) ∧
          φ target := by
  rw [langSpan, derivedDiamond_langSpanUsing_iff]
  exact exists_congr fun target =>
    and_congr_left fun _ => (step_adequacy wfSource).symm

/-- The derived step-past modality constrains every checked predecessor
certificate: the sound direction of the box weld.  The converse needs
evidence about ill-formed predecessors and is deliberately not claimed. -/
theorem box_constrains_checked_predecessors {target : Pattern}
    (φ : Pattern → Prop)
    (box : derivedBox (langSpan stepLanguage) φ target) :
    ∀ source, wellFormed source →
      Nonempty (Derivation traceValidated (stepJ source target)) →
        φ source := by
  intro source wfSource witness
  obtain ⟨derivation⟩ := witness
  have reduces := (sound_derivation derivation).1 source target rfl
  exact box ⟨(source, target), reduces⟩ rfl

/-! ## The finite-certificate floor -/

/-- General, any definition and goal: a judgment is derivable exactly
when some finite raw proof is accepted by the Boolean checker.  This is the
certificate-existence shape associated with semidecidability.  A literal
arithmetical-hierarchy classification additionally requires an effective
coding and enumeration of `RawProof`; no such classification is claimed
here. -/
theorem derivation_nonempty_iff_certificate
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔
      ∃ proof : RawProof, checkRaw definition goal proof = true := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase, checkRaw_erase derivation⟩
  · rintro ⟨proof, accepted⟩
    exact checkRaw_soundness accepted

/-- On the adequacy fixture, the step relation is exactly existence of an
accepted finite certificate. -/
theorem step_iff_exists_checked_certificate {source target : Pattern}
    (wfSource : wellFormed source) :
    langReduces stepLanguage source target ↔
      ∃ proof : RawProof,
        checkRaw traceValidated (stepJ source target) proof = true :=
  (step_adequacy wfSource).symm.trans
    (derivation_nonempty_iff_certificate traceValidated _)

/-- On the adequacy fixture, reachability is exactly existence of an accepted
trace certificate. -/
theorem reachability_iff_exists_checked_certificate {source target : Pattern}
    (wfSource : wellFormed source) :
    Relation.ReflTransGen (langReduces stepLanguage) source target ↔
      ∃ proof : RawProof,
        checkRaw traceValidated (stepsJ source target) proof = true :=
  (steps_adequacy wfSource).symm.trans
    (derivation_nonempty_iff_certificate traceValidated _)

/-! ## Compression: certificates grow without bound, one induction covers
them all -/

private def fTower : Nat → Pattern → Pattern
  | 0, base => base
  | n + 1, base => termF (fTower n base)

private theorem wellFormed_fTower (n : Nat) {base : Pattern}
    (wfBase : wellFormed base) : wellFormed (fTower n base) := by
  induction n with
  | zero => exact wfBase
  | succ n inductionHypothesis =>
      exact (wellFormed_termF_iff _).mpr inductionHypothesis

/-- The authored congruence rule lifts any step through `f`. -/
private theorem congF_lifts {first second : Pattern}
    (step : langReduces stepLanguage first second) :
    langReduces stepLanguage (termF first) (termF second) := by
  obtain ⟨fuel, evidence⟩ := step
  refine ⟨fuel + 1, .rule (rule := congruenceF)
    (initialBindings := [("p", first)])
    (finalBindings := [("q", second), ("p", first)]) ?_ ?_ ?_ ?_⟩
  · simp [stepLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    show [("p", first)] ∈ matchPattern (termF (.fvar "p")) (termF first)
    rw [matchPattern_congF_forward]
    exact List.mem_singleton.mpr rfl
  · refine .cons (.congruence (candidate := second)
      (premiseBindings := [("q", second)]) ?_ ?_ ?_) (.nil _)
    · rw [applyBindings_fvar_p]
      exact evidence
    · simp [matchPattern]
    · exact mergeBindings_p_q first second
  · exact applyRule_congF first second

/-- One parametric induction covers the whole infinite family of tower steps;
no single member's trace certificate states that uniform fact. -/
theorem tower_reachable (n : Nat) :
    langReduces stepLanguage (fTower n termA) (fTower n termB) := by
  induction n with
  | zero => exact ab_langReduces
  | succ n inductionHypothesis => exact congF_lifts inductionHypothesis

/-- Every tower step has an accepted certificate. -/
theorem tower_certificate_exists (n : Nat) :
    ∃ proof : RawProof,
      checkRaw traceValidated
        (stepJ (fTower n termA) (fTower n termB)) proof = true :=
  (step_iff_exists_checked_certificate
    (wellFormed_fTower n wellFormed_termA)).mp
    (tower_reachable n)

mutual

/-- Rule nodes of a closed raw proof. -/
def rawRuleNodes : RawProof → Nat
  | .node _ children => rawRuleNodeList children + 1

/-- Rule nodes across ordered children. -/
def rawRuleNodeList : List RawProof → Nat
  | [] => 0
  | proof :: proofs => rawRuleNodes proof + rawRuleNodeList proofs

end

/-- The compression lower bound: every accepted certificate for the n-th
tower step carries at least n + 1 rule nodes.  Certificate cost grows
without bound over the family that `tower_reachable` covers in one
induction. -/
theorem tower_certificate_lower_bound :
    ∀ (n : Nat) (proof : RawProof),
      checkRaw traceValidated
          (stepJ (fTower n termA) (fTower n termB)) proof = true →
      n + 1 ≤ rawRuleNodes proof := by
  intro n
  induction n with
  | zero =>
      intro proof _accepted
      cases proof with
      | node ruleInstance children =>
          simp [rawRuleNodes]
  | succ n inductionHypothesis =>
      intro proof accepted
      cases proof with
      | node ruleInstance children =>
          simp only [checkRaw] at accepted
          cases instantiated : instantiateRule? traceValidated
              ruleInstance with
          | none => rw [instantiated] at accepted; simp at accepted
          | some result =>
              rcases result with ⟨premises, conclusion⟩
              rw [instantiated] at accepted
              simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
              obtain ⟨conclusionEq, childrenOk⟩ := accepted
              have application :=
                instantiateRule?_eq_some_iff_application.mp instantiated
              rcases application_shape application with
                ⟨premisesShape, conclusionShape⟩ |
                ⟨first, second, _wfFirst, _wfSecond, premisesShape,
                  conclusionShape⟩ |
                ⟨point, _wfPoint, premisesShape, conclusionShape⟩ |
                ⟨sourceT, middleT, targetT, _wfS, _wfM, _wfT,
                  premisesShape, conclusionShape⟩
              · rw [conclusionShape] at conclusionEq
                simp [stepJ, termA, termB, termF, fTower] at conclusionEq
              · rw [conclusionShape] at conclusionEq
                simp only [stepJ, fTower, termF, Pattern.apply.injEq,
                  List.cons.injEq, and_true, true_and] at conclusionEq
                obtain ⟨firstEq, secondEq⟩ := conclusionEq
                rw [premisesShape] at childrenOk
                cases children with
                | nil => simp [checkRawChildren] at childrenOk
                | cons child rest =>
                    cases rest with
                    | cons extra rest' =>
                        simp [checkRawChildren] at childrenOk
                    | nil =>
                        simp only [checkRawChildren, Bool.and_eq_true]
                          at childrenOk
                        obtain ⟨childOk, -⟩ := childrenOk
                        rw [firstEq, secondEq] at childOk
                        have childBound :=
                          inductionHypothesis child childOk
                        simp only [rawRuleNodes, rawRuleNodeList]
                        omega
              · rw [conclusionShape] at conclusionEq
                simp [stepJ, stepsJ] at conclusionEq
              · rw [conclusionShape] at conclusionEq
                simp [stepJ, stepsJ] at conclusionEq

/-! ## Budgeted verification: exhaustion is not refutation -/

/-- Verdicts of budgeted certificate checking.  There is deliberately no
`refuted`: running out of budget says nothing about the claim. -/
inductive BudgetVerdict where
  | established
  | undetermined
deriving Repr, DecidableEq

/-- Accept a certificate only when it both fits the rule-node budget and
passes the Boolean checker. -/
def checkWithinBudget (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) (budget : Nat) (proof : RawProof) : BudgetVerdict :=
  if rawRuleNodes proof ≤ budget ∧
      checkRaw definition goal proof = true then
    .established
  else
    .undetermined

/-- Established verdicts are sound: the certificate really checks. -/
theorem established_sound {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {budget : Nat} {proof : RawProof}
    (established : checkWithinBudget definition goal budget proof =
      .established) :
    checkRaw definition goal proof = true := by
  unfold checkWithinBudget at established
  split at established
  case isTrue condition => exact condition.2
  case isFalse => cases established

/-- Raising the budget never demotes an established verdict. -/
theorem established_budget_mono {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {budget budget' : Nat} {proof : RawProof}
    (le : budget ≤ budget')
    (established : checkWithinBudget definition goal budget proof =
      .established) :
    checkWithinBudget definition goal budget' proof = .established := by
  unfold checkWithinBudget at established ⊢
  split at established
  case isTrue condition =>
      rw [if_pos ⟨Nat.le_trans condition.1 le, condition.2⟩]
  case isFalse => cases established

/-- Budget exhaustion is not refutation, witnessed: the tower step at
height one is true, yet at budget one every certificate — accepted or not
— comes back undetermined, because every accepted certificate needs at
least two rule nodes. -/
theorem budget_exhaustion_is_not_refutation :
    langReduces stepLanguage (fTower 1 termA) (fTower 1 termB) ∧
      ∀ proof : RawProof,
        checkWithinBudget traceValidated
          (stepJ (fTower 1 termA) (fTower 1 termB)) 1 proof =
            .undetermined := by
  refine ⟨tower_reachable 1, fun proof => ?_⟩
  unfold checkWithinBudget
  split
  case isTrue condition =>
      exfalso
      have bound := tower_certificate_lower_bound 1 proof condition.2
      omega
  case isFalse => rfl

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepAdequacy
