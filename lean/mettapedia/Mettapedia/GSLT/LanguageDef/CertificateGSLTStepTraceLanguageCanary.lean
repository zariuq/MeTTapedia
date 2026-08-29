import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepTraceLanguage
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# The generated trace checker, its faithfulness boundary, and the judgment it cannot speak

The fixture language has one ground rewrite `a → b` and constructors `f`,
`g`.  Three compiled boundaries:

* the generated definition is admitted by the generic checker with no
  authored inference rules, and derives the authored step `a → b`;
* congruence is **not** free: the language's declarative reduction has no
  step `f a → f b`, because MeTTaIL grants contextual authority only
  through authored congruence premises.  This counterexample is what
  removed the earlier per-constructor congruence emission from the
  generator;
* a definition with the nullary judgment `Truth` is admitted and
  inhabited by the full checker, and is provably not the generated trace
  definition of any language — full proof judgments strictly exceed
  uniform trace checking.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepTraceLanguageCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## A language, not a proof system -/

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

private def genG : GrammarRule :=
  { label := "gen-g", category := "GP"
    params := [.simple "left" (.base "GP"), .simple "right" (.base "GP")]
    syntaxPattern := [] }

private def termA : Pattern := .apply "gen-a" []
private def termB : Pattern := .apply "gen-b" []
private def termF (argument : Pattern) : Pattern := .apply "gen-f" [argument]

private def rewriteAB : RewriteRule :=
  { name := "ab"
    typeContext := []
    premises := []
    left := termA
    right := termB }

private def genLanguage : LanguageDef :=
  { name := "certificate-gslt-generated-step-fixture"
    types := [genType]
    terms := [genA, genB, genF, genG]
    equations := []
    rewrites := [rewriteAB] }

private theorem genPremisesSupported :
    LanguageDef.directTraceSupported genLanguage = true := by
  rfl

private def genTraceLanguage : DirectTraceLanguage :=
  ⟨genLanguage, genPremisesSupported⟩

theorem supported_language_admitted :
    DirectTraceLanguage.ofLanguage? genLanguage = some genTraceLanguage :=
  DirectTraceLanguage.ofLanguage?_eq_some genTraceLanguage

private def relationPremiseRule : RewriteRule :=
  { name := "requires-relation"
    typeContext := []
    premises := [.relationQuery "Available" []]
    left := termA
    right := termB }

private def unsupportedLanguage : LanguageDef :=
  { genLanguage with rewrites := [relationPremiseRule] }

/-- Unsupported premise kinds fail before a trace definition can be
constructed; they are never silently erased into a stronger rule. -/
theorem relation_premise_language_rejected :
    DirectTraceLanguage.ofLanguage? unsupportedLanguage = none := by
  apply DirectTraceLanguage.ofLanguage?_eq_none_of_unsupported
  rfl

/-! ## The generated trace checker is admitted with no authored rules -/

private theorem abRule_id_spelling :
    ("step-rewrite-" ++ "ab" : String) = "step-rewrite-ab" := rfl

private theorem genStep_validate :
    (stepTraceDefinition genTraceLanguage).toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepTraceDefinition, genTraceLanguage, genLanguage, genType, genA, genB, genF, genG,
      LanguageDef.typeNames, TermParam.typeExpr, TypeExpr.baseNames,
      TypeDecl.plain]

theorem generated_step_trace_definition_valid :
    (stepTraceDefinition genTraceLanguage).isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [genStep_validate]
  simp [stepTraceDefinition, genTraceLanguage, genLanguage, genType, genA, genB, genF, genG,
    rewriteAB, rewriteStepRule, rewritePremiseJudgments, stepReflRule,
    stepTransRule, termA, termB, abRule_id_spelling,
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

private def genValidated : ValidatedCalculusLanguageDef :=
  ⟨stepTraceDefinition genTraceLanguage, generated_step_trace_definition_valid⟩

private def abInstance : RuleInstance := ⟨⟨"step-rewrite-ab"⟩, []⟩

private theorem ab_instantiates :
    instantiateRule? genValidated abInstance =
      some ([], .apply "Step" [termA, termB]) := by
  simp [instantiateRule?, genValidated, stepTraceDefinition, genTraceLanguage, genLanguage,
    rewriteAB, rewriteStepRule, rewritePremiseJudgments, stepReflRule,
    stepTransRule, abInstance, termA, termB, abRule_id_spelling,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

/-- The generated checker derives the authored step, with no authored
inference rules anywhere. -/
def generatedStepAB :
    Derivation genValidated (.apply "Step" [termA, termB]) :=
  .byRule abInstance
    (instantiateRule?_eq_some_iff_application.mp ab_instantiates) .nil

/-! ## Congruence is not free -/

/-- The authored ground step is a declarative reduction of the language. -/
theorem ab_langReduces : langReduces genLanguage termA termB := by
  refine ⟨1, .rule (rule := rewriteAB) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [genLanguage]
  · simp [genLanguage, rewriteAB, termA, matchPattern, matchArgs]
  · exact .nil []
  · simp [genLanguage, rewriteAB, termB, applyBindings]

/-- The compiled faithfulness counterexample: the language has no step
`f a → f b`, because MeTTaIL grants no representation-wide congruence.  A
trace definition that emitted per-constructor congruence schemas would
derive this exact non-step; this theorem is why the generator translates
only authored congruence premises. -/
theorem congruence_is_not_free :
    ¬ langReduces genLanguage (termF termA) (termF termB) := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have ruleShape : rule = rewriteAB := by
    simpa [genLanguage] using member
  subst ruleShape
  simp [genLanguage, rewriteAB, termA, termF, matchPattern]

/-! ## The judgment no trace checker declares -/

private def truthRule : RuleSchema :=
  { id := ⟨"truth-intro"⟩
    metavariables := []
    premises := []
    conclusion := .apply "Truth" [] }

private def truthDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "certificate-gslt-truth-fixture")
    { judgments := [{ head := "Truth", arity := 0 }]
      rules := [truthRule] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem truthDefinition_valid :
    truthDefinition.isValid = true := by
  simp [truthDefinition, CalculusLanguageDef.isValid,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.hasValidLocalRules, CalculusLanguageDef.ruleIds, emptyLanguage_validate,
    truthRule, RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def truthValidated : ValidatedCalculusLanguageDef :=
  ⟨truthDefinition, truthDefinition_valid⟩

private theorem truth_instantiates :
    instantiateRule? truthValidated ⟨⟨"truth-intro"⟩, []⟩ =
      some ([], .apply "Truth" []) := by
  simp [instantiateRule?, truthValidated, truthDefinition, truthRule,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

/-- The full checker admits and inhabits the nullary judgment. -/
def truthDerivation : Derivation truthValidated (.apply "Truth" []) :=
  .byRule ⟨⟨"truth-intro"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp truth_instantiates) .nil

/-- The golden difference, witnessed: the admitted, inhabited `Truth`
definition is not the generated step definition of any language. -/
theorem truth_is_no_trace_checker :
    ∀ source : DirectTraceLanguage,
      stepTraceDefinition source ≠ truthDefinition := by
  apply not_stepTraceDefinition_of_judgments
  simp [truthDefinition]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.StepTraceLanguageCanary
