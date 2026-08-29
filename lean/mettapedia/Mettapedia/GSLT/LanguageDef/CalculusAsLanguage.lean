import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Proof calculi as proof-search GSLTs

A proof calculus is not an extra collection of fields in its object language,
and its declarations must not be serialized into that object's five fields.
It nevertheless has its own `(T,E,R)` semantics at the meta-level.  The
authored calculus syntax is the GSLT in
`InferenceExtension.calculusSyntaxGSLT`; its elaboration yields a
`ProofCalculus`, which is admitted only together with an exact five-field
`LanguageDef`.

An admitted definition nevertheless induces a genuine GSLT: its terms are
ordered proof-obligation lists and one rewrite replaces the first obligation
by the premises of one admitted rule application.  This is a semantic
construction, not a representation trick:

* the rewrite relation is equivalent to the checker's independent
  `RuleApplication` relation;
* a goal rewrites to the empty obligation list exactly when it has a
  type-valued derivation;
* an admitted definition with no rules has no proof-search steps.

Thus inference rules are rewrite rules at the meta-level of proof obligations.
They are not object-language rewrites, equations, grammar constructors, or
extra fields of `LanguageDef`.
-/

namespace Mettapedia.GSLT.LanguageDef.CalculusAsLanguage

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- A proof-search state is an ordered list of outstanding judgments. -/
abbrev GoalState := List Pattern

/-- One backward proof-search step.  The first outstanding conclusion is
replaced by the ordered premises of one admitted rule instance. -/
def Resolves (definition : ValidatedCalculusLanguageDef) :
    GoalState → GoalState → Prop :=
  fun source target =>
    ∃ ruleInstance premises conclusion rest,
      instantiateRule? definition ruleInstance =
        some (premises, conclusion) ∧
      source = conclusion :: rest ∧
      target = premises ++ rest

/-- The proof-search GSLT induced by one validated calculus language. -/
def proofSearchGSLT (definition : ValidatedCalculusLanguageDef) : GSLT where
  Term := GoalState
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := Resolves definition
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The GSLT step is exactly executable local rule instantiation. -/
theorem proofSearchGSLT_step_iff_instantiation
    (definition : ValidatedCalculusLanguageDef) (source target : GoalState) :
    (proofSearchGSLT definition).Step source target ↔
      ∃ ruleInstance premises conclusion rest,
        instantiateRule? definition ruleInstance =
          some (premises, conclusion) ∧
        source = conclusion :: rest ∧
        target = premises ++ rest :=
  Iff.rfl

/-- The same step relation stated independently of the executable
instantiator. -/
theorem proofSearchGSLT_step_iff_application
    (definition : ValidatedCalculusLanguageDef) (source target : GoalState) :
    (proofSearchGSLT definition).Step source target ↔
      ∃ ruleInstance premises conclusion rest,
        RuleApplication definition ruleInstance premises conclusion ∧
        source = conclusion :: rest ∧
        target = premises ++ rest := by
  simp only [proofSearchGSLT_step_iff_instantiation,
    instantiateRule?_eq_some_iff_application]

/-- Resolving obligations is stable under an untouched suffix. -/
theorem Resolves.append_right {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (step : Resolves definition source target) (suffix : GoalState) :
    Resolves definition (source ++ suffix) (target ++ suffix) := by
  rcases step with
    ⟨ruleInstance, premises, conclusion, rest, instantiated, rfl, rfl⟩
  refine ⟨ruleInstance, premises, conclusion, rest ++ suffix,
    instantiated, ?_, ?_⟩
  · rfl
  · simp [List.append_assoc]

/-- Multi-step proof search is stable under an untouched suffix. -/
def multiStep_append_right {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (steps : (proofSearchGSLT definition).MultiStep source target)
    (suffix : GoalState) :
    (proofSearchGSLT definition).MultiStep
      (source ++ suffix) (target ++ suffix) :=
  match steps with
  | .refl state => by
      change GoalState at state
      exact @GSLT.MultiStep.refl (proofSearchGSLT definition)
        (state ++ suffix)
  | .step first rest =>
      .step (first.append_right suffix)
        (multiStep_append_right rest suffix)

/-- Transitivity of the reflexive-transitive proof-search closure. -/
def multiStep_trans {definition : ValidatedCalculusLanguageDef}
    {first second third : GoalState}
    (firstSecond :
      (proofSearchGSLT definition).MultiStep first second)
    (secondThird :
      (proofSearchGSLT definition).MultiStep second third) :
    (proofSearchGSLT definition).MultiStep first third :=
  match firstSecond with
  | .refl _ => secondThird
  | .step first rest =>
      .step first (multiStep_trans rest secondThird)

/-- Concatenate derivations for two ordered obligation lists. -/
def derivationListAppend {definition : ValidatedCalculusLanguageDef}
    {first second : List Pattern}
    (left : DerivationList definition first)
    (right : DerivationList definition second) :
    DerivationList definition (first ++ second) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (derivationListAppend tail right)

/-- Split derivations at an authored list boundary. -/
def derivationListSplitAppend {definition : ValidatedCalculusLanguageDef}
    (first second : List Pattern) :
    DerivationList definition (first ++ second) →
      DerivationList definition first ×
        DerivationList definition second :=
  match first with
  | [] => fun derivations => (.nil, derivations)
  | _ :: rest => fun derivations =>
      match derivations with
      | .cons head tail =>
          let divided := derivationListSplitAppend rest second tail
          (.cons head divided.1, divided.2)

mutual

/-- A derivation discharges its singleton obligation by proof-search
rewriting. -/
def derivationToProofSearch
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    (proofSearchGSLT definition).MultiStep [goal] [] :=
  match derivation with
  | @Derivation.byRule _ ruleInstance premises conclusion application children => by
      have first :
          (proofSearchGSLT definition).Step [conclusion] premises := by
        apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
        refine ⟨ruleInstance, premises, conclusion, [], ?_, rfl, by simp⟩
        exact instantiateRule?_eq_some_iff_application.mpr application
      exact .step first (derivationListToProofSearch children)

/-- An ordered derivation list discharges exactly its obligation list. -/
def derivationListToProofSearch
    {definition : ValidatedCalculusLanguageDef} {goals : List Pattern}
    (derivations : DerivationList definition goals) :
    (proofSearchGSLT definition).MultiStep goals [] :=
  match derivations with
  | .nil => @GSLT.MultiStep.refl (proofSearchGSLT definition) []
  | .cons head tail =>
      multiStep_trans
        (multiStep_append_right (derivationToProofSearch head) _)
        (derivationListToProofSearch tail)

end

/-- One proof-search step transports derivation-list inhabitation backwards. -/
theorem nonemptyDerivationList_of_step
    {definition : ValidatedCalculusLanguageDef} {source target : GoalState}
    (step : (proofSearchGSLT definition).Step source target)
    (targetInhabited : Nonempty (DerivationList definition target)) :
    Nonempty (DerivationList definition source) := by
  obtain ⟨targetDerivations⟩ := targetInhabited
  rcases step with
    ⟨ruleInstance, premises, conclusion, suffix,
      instantiated, sourceShape, targetShape⟩
  subst sourceShape
  subst targetShape
  let divided :=
    derivationListSplitAppend premises suffix targetDerivations
  exact ⟨.cons
    (.byRule ruleInstance
      (instantiateRule?_eq_some_iff_application.mp instantiated)
      divided.1)
    divided.2⟩

/-- Proof search preserves inhabitation backwards: derivations of the final
obligations and a search trace together yield derivations of the initial
obligations.  The conclusion is kept in `Prop` via `Nonempty`, so no proof in
`Prop` is illicitly eliminated into computational data. -/
theorem nonemptyDerivationList_of_multiStep
    {definition : ValidatedCalculusLanguageDef} {source target : GoalState}
    (steps : (proofSearchGSLT definition).MultiStep source target) :
    Nonempty (DerivationList definition target) →
      Nonempty (DerivationList definition source) := by
  let motive : ∀ (first last : GoalState),
      (proofSearchGSLT definition).MultiStep first last → Prop :=
    fun first last _ =>
      Nonempty (DerivationList definition last) →
        Nonempty (DerivationList definition first)
  exact GSLT.MultiStep.rec (motive := motive)
    (fun _ inhabited => inhabited)
    (fun first _ inductionHypothesis targetInhabited =>
      nonemptyDerivationList_of_step first
        (inductionHypothesis targetInhabited))
    steps

/-- **Adequacy.**  Derivability of an ordered goal list is equivalent to
reachability of the empty proof-obligation state. -/
theorem derivationList_nonempty_iff_proofSearch
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    Nonempty (DerivationList definition goals) ↔
      (proofSearchGSLT definition).MultiStep goals [] := by
  constructor
  · rintro ⟨derivations⟩
    exact derivationListToProofSearch derivations
  · intro steps
    exact nonemptyDerivationList_of_multiStep steps ⟨.nil⟩

/-- Singleton form of adequacy: a judgment is derivable exactly when backward
proof search reaches no outstanding obligations. -/
theorem derivation_nonempty_iff_proofSearch
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔
      (proofSearchGSLT definition).MultiStep [goal] [] := by
  constructor
  · rintro ⟨derivation⟩
    exact derivationToProofSearch derivation
  · intro steps
    obtain ⟨derivations⟩ :=
      nonemptyDerivationList_of_multiStep steps ⟨.nil⟩
    cases derivations with
    | cons head tail => exact ⟨head⟩

/-! ## Positive and negative canaries -/

private def canaryLanguage : LanguageDef :=
  { name := "proof-search-canary"
    types := [TypeDecl.plain "Term"]
    terms :=
      [{ label := "A", category := "Term", params := [], syntaxPattern := [] }]
    equations := []
    rewrites := [] }

private def canaryGoal : Pattern :=
  .apply "Provable" [.apply "A" []]

private def canaryRule : RuleSchema :=
  { id := ⟨"axiom-A"⟩
    metavariables := []
    premises := []
    conclusion := canaryGoal }

private def canaryDefinition : CalculusLanguageDef :=
  { toLanguageDef := canaryLanguage
    judgments := [{ head := "Provable", arity := 1 }]
    rules := [canaryRule] }

private theorem canaryDefinition_valid :
    canaryDefinition.isValid = true := by
  have languageValid : canaryLanguage.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly canaryLanguage <;>
      simp [canaryLanguage, LanguageDef.typeNames, TypeDecl.plain,
        TermParam.typeExpr]
  have definitionLanguageValid : canaryDefinition.toLanguageDef.validate = [] := by
    simpa [canaryDefinition] using languageValid
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [definitionLanguageValid]
  simp [canaryDefinition, canaryLanguage, canaryRule, canaryGoal,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

private def canaryValidated : ValidatedCalculusLanguageDef :=
  ⟨canaryDefinition, canaryDefinition_valid⟩

/-- Positive canary: a zero-premise rule discharges its singleton goal in one
genuine GSLT step. -/
example :
    (proofSearchGSLT canaryValidated).Step [canaryGoal] [] := by
  apply
    (proofSearchGSLT_step_iff_instantiation
      canaryValidated [canaryGoal] []).mpr
  refine ⟨{ ruleId := ⟨"axiom-A"⟩, arguments := [] },
    [], canaryGoal, [], ?_, rfl, rfl⟩
  simp [instantiateRule?, canaryValidated, canaryDefinition, canaryRule,
    canaryGoal, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?]

private def emptyDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "proof-search-empty" }

private theorem emptyDefinition_valid :
    emptyDefinition.isValid = true := by
  have languageValid :
      (LanguageDef.empty "proof-search-empty").validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [LanguageDef.empty, LanguageDef.typeNames]
  simp [emptyDefinition, CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid, languageValid]

private def emptyValidated : ValidatedCalculusLanguageDef :=
  ⟨emptyDefinition, emptyDefinition_valid⟩

/-- Negative canary: an admitted calculus with no rules has no proof-search
step, even though its base language remains a valid five-field definition. -/
theorem empty_calculus_has_no_step (source target : GoalState) :
    ¬ (proofSearchGSLT emptyValidated).Step source target := by
  intro step
  obtain ⟨ruleInstance, premises, conclusion, rest, instantiated, _, _⟩ :=
    (proofSearchGSLT_step_iff_instantiation
      emptyValidated source target).mp step
  have application :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  cases application with
  | intro rule lookup _ _ _ _ =>
      have impossible : False := by
        simp [emptyValidated, emptyDefinition,
          CalculusLanguageDef.lookupRule?] at lookup
      exact impossible.elim

end Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
