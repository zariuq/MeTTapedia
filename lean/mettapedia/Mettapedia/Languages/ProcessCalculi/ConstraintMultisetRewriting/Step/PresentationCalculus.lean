import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationExecution
import Mettapedia.GSLT.LanguageDef.InferenceExtraction
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Inference judgments extracted from the authored transition

The same authored rewrite supplies the rule identity, premise order and both
endpoints of an inference schema. Relation queries become premise judgments;
they are not axioms or host-issued certificates. A semantic interpretation
must establish each of them. Extraction refuses unsupported premise forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Calculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtraction

def profile : EvidenceProfile where
  checkHead := "Request"
  okHead := "At"
  proofCategory := "Firing"
  evidenceCategory := "State"
  derivedHead := "$tcalc.transition"
  relationHeadPrefix := "$tcalc."

def extractRule (rule : RewriteRule) : Option RuleSchema := do
  let premises ← rule.premises.mapM (sidePremiseJudgment? profile)
  let draft : RuleSchema :=
    { id := ⟨rule.name⟩, metavariables := [], premises,
      conclusion := .apply "$tcalc.transition" [rule.left, rule.right] }
  pure { draft with metavariables := occurrenceEraseDups (RuleSchema.occurrences draft) }

def rules : List RuleSchema :=
  (language.rewrites.mapM extractRule).get (by decide +kernel)

def definition : CalculusLanguageDef :=
  CalculusLanguageDef.extend language
    { judgments := { head := "$tcalc.transition", arity := 2 } ::
        (relationJudgmentDecls profile language).eraseDups,
      rules }

theorem extracted : language.rewrites.mapM extractRule = some rules := by decide +kernel

theorem base_valid : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndCertifiedRewrites
  all_goals first | decide +kernel | skip
  change (LanguageDef.validateRewrite language
    { name := "Execute", typeContext := [],
      premises := [.relationQuery "prepared" [.fvar "s", .fvar "f", .fvar "t"],
        .relationQuery "permitted" [.fvar "s", .fvar "f"]],
      left := .apply "Request" [.fvar "s", .fvar "f"],
      right := .apply "At" [.fvar "t"] }).isEmpty && true = true
  simp [LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.patternFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams]
  decide +kernel

theorem admitted : definition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  · change language.validate.isEmpty = true
    rw [base_valid]
    rfl
  all_goals decide +kernel

def validated : ValidatedCalculusLanguageDef := ⟨definition, admitted⟩

def prepared (s f t : Pattern) : Pattern := .apply "$tcalc.prepared" [s, f, t]
def permitted (s f : Pattern) : Pattern := .apply "$tcalc.permitted" [s, f]
def transition (s f t : Pattern) : Pattern :=
  .apply "$tcalc.transition" [request s f, atState t]

theorem rule_identity : rules.map (fun rule => rule.id.value) =
    language.rewrites.map (·.name) := by decide +kernel

theorem rule_shape : rules.length = 1 ∧ rules[0].premises =
    [prepared (.fvar "s") (.fvar "f") (.fvar "t"), permitted (.fvar "s") (.fvar "f")] ∧
    rules[0].conclusion = transition (.fvar "s") (.fvar "f") (.fvar "t") := by
  decide +kernel

def meaning (queries : Queries) : Pattern → Prop
  | .apply "$tcalc.prepared" [s, f, t] => queries.prepare s f = some t
  | .apply "$tcalc.permitted" [s, f] => queries.permit s f = true
  | .apply "$tcalc.transition" [.apply "Request" [s, f], .apply "At" [t]] =>
      atState t ∈ rewriteStepWithPremisesUsing queries.relations language (request s f)
  | _ => False

theorem execute_meaning (queries : Queries) (s f t : Pattern)
    (preparation : meaning queries (prepared s f t))
    (permission : meaning queries (permitted s f)) :
    meaning queries (transition s f t) := by
  change queries.prepare s f = some t at preparation
  change queries.permit s f = true at permission
  change atState t ∈ rewriteStepWithPremisesUsing queries.relations language (request s f)
  rw [execution, preparation, permission]
  exact List.mem_singleton_self _

private def schema : RuleSchema := rules[0]

private theorem schema_formals : schema.metavariables = [("s", 0), ("f", 0), ("t", 0)] := by
  change occurrenceEraseDups (patternsMetavariableOccurrencesAt 0
    [prepared (.fvar "s") (.fvar "f") (.fvar "t"), permitted (.fvar "s") (.fvar "f"),
      transition (.fvar "s") (.fvar "f") (.fvar "t")]) = _
  simp [patternsMetavariableOccurrencesAt, patternMetavariableOccurrencesAt,
    prepared, permitted, transition, request, atState, occurrenceEraseDups,
    occurrenceEraseDupsAux, occurrenceContains, metavariableOccurrenceEq]

def invocation (s f t : Pattern) : InferenceChecker.RuleInstance := ⟨schema.id, [s, f, t]⟩

theorem instantiate_invocation (s f t : Pattern) :
    instantiateRule? validated (invocation s f t) =
      if argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] then
        some ([prepared s f t, permitted s f], transition s f t)
      else none := by
  have lookup : validated.val.lookupRule? (invocation s f t).ruleId = some schema := rfl
  unfold instantiateRule?
  rw [lookup]
  simp only [schema_formals, invocation]
  split
  ·
    change (do
      let premises ← instantiateSchemas? [("s", 0), ("f", 0), ("t", 0)] [s, f, t]
        [prepared (.fvar "s") (.fvar "f") (.fvar "t"), permitted (.fvar "s") (.fvar "f")]
      let conclusion ← instantiateSchema? [("s", 0), ("f", 0), ("t", 0)] [s, f, t]
        (transition (.fvar "s") (.fvar "f") (.fvar "t"))
      pure (premises, conclusion)) = _
    simp [instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?, prepared, permitted, transition, request, atState]
  · rfl

theorem invocation_application (s f t : Pattern)
    (valid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] = true) :
    RuleApplication validated (invocation s f t)
      [prepared s f t, permitted s f] (transition s f t) := by
  apply instantiateRule?_eq_some_iff_application.mp
  rw [instantiate_invocation, valid]
  rfl

private theorem lookup_only (id : RuleId) (rule : RuleSchema)
    (found : validated.val.lookupRule? id = some rule) : rule = schema ∧ id = schema.id := by
  change ([schema].find? (fun r => decide (r.id = id))) = some rule at found
  by_cases same : schema.id = id
  · simp [same] at found
    exact ⟨found.symm, same.symm⟩
  · simp [same] at found

theorem application_shape {instanceData : InferenceChecker.RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication validated instanceData premises conclusion) :
    ∃ s f t, instanceData = invocation s f t ∧
      premises = [prepared s f t, permitted s f] ∧ conclusion = transition s f t := by
  have evaluated := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule lookup valid _ _ _ =>
      obtain ⟨sameRule, sameId⟩ := lookup_only _ _ lookup
      subst rule
      have length := (argumentsValidAt_length valid).symm
      rw [schema_formals] at length
      change instanceData.arguments.length = 3 at length
      obtain ⟨s, f, t, arguments⟩ := List.length_eq_three.mp length
      have same : instanceData = invocation s f t := by
        cases instanceData
        simp_all [invocation]
      rw [same, instantiate_invocation] at evaluated
      have argumentValid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] = true := by
        simpa only [arguments, schema_formals] using valid
      rw [if_pos argumentValid] at evaluated
      have parts := Prod.mk.inj (Option.some.inj evaluated)
      exact ⟨s, f, t, same, parts.1.symm, parts.2.symm⟩

theorem application_sound (queries : Queries)
    (instanceData : InferenceChecker.RuleInstance) (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication validated instanceData premises conclusion)
    (premisesSound : ∀ premise ∈ premises, meaning queries premise) : meaning queries conclusion := by
  obtain ⟨s, f, t, _, rfl, rfl⟩ := application_shape application
  exact execute_meaning queries s f t
    (premisesSound _ (by simp)) (premisesSound _ (by simp))

open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- The existing open proof checker is sound under independently interpreted premises. -/
theorem checked_article_sound (queries : Queries) (context : List Pattern) (goal : Pattern)
    (proof : RawOpenProof) (contextSound : ∀ premise ∈ context, meaning queries premise)
    (accepted : checkOpenRaw validated context goal proof = true) : meaning queries goal := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation accepted
  exact derivation.sound_of_ruleApplications (meaning queries) (application_sound queries) contextSound

def article (s f t : Pattern) : RawOpenProof :=
  .node (invocation s f t) [.premise 0, .premise 1]

theorem article_checked (s f t : Pattern)
    (valid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] = true) :
    checkOpenRaw validated [prepared s f t, permitted s f] (transition s f t)
      (article s f t) = true := by
  simp [article, checkOpenRaw, instantiate_invocation, valid, checkOpenRawChildren]

def meaningDecidable (queries : Queries) (judgment : Pattern) : Decidable (meaning queries judgment) := by
  unfold meaning
  split <;> infer_instance

def checkMeaning (queries : Queries) (judgment : Pattern) : Bool :=
  @decide (meaning queries judgment) (meaningDecidable queries judgment)

@[simp] theorem checkMeaning_iff (queries : Queries) (judgment : Pattern) :
    checkMeaning queries judgment = true ↔ meaning queries judgment := by
  simp only [checkMeaning, decide_eq_true_eq]

/-- Premise truth and finite proof checking are separate checks at this boundary. -/
def checkArticle (queries : Queries) (context : List Pattern) (goal : Pattern)
    (proof : RawOpenProof) : Bool :=
  context.all (checkMeaning queries) && checkOpenRaw validated context goal proof

theorem checkArticle_sound (queries : Queries) (context : List Pattern) (goal : Pattern)
    (proof : RawOpenProof) (accepted : checkArticle queries context goal proof = true) :
    meaning queries goal := by
  simp only [checkArticle, Bool.and_eq_true] at accepted
  obtain ⟨premises, checked⟩ := accepted
  apply checked_article_sound queries context goal proof _ checked
  intro premise member
  exact (checkMeaning_iff queries premise).mp ((List.all_eq_true.mp premises) _ member)

theorem execute_article (queries : Queries) (s f t : Pattern)
    (valid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] = true)
    (preparation : queries.prepare s f = some t) (permission : queries.permit s f = true) :
    checkArticle queries [prepared s f t, permitted s f] (transition s f t)
      (article s f t) = true := by
  unfold checkArticle
  rw [article_checked s f t valid]
  simp only [Bool.and_true, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    checkMeaning_iff]
  exact ⟨preparation, permission⟩

theorem transition_meaning_iff (queries : Queries) (s f t : Pattern) :
    meaning queries (transition s f t) ↔
      meaning queries (prepared s f t) ∧ meaning queries (permitted s f) := by
  change atState t ∈ rewriteStepWithPremisesUsing queries.relations language (request s f) ↔
    queries.prepare s f = some t ∧ queries.permit s f = true
  rw [execution]
  cases preparation : queries.prepare s f <;> cases permission : queries.permit s f <;>
    simp [atState, eq_comm]

/-- The presented rule has an accepted finite article exactly for its executions,
on the generic checker's explicitly stated closed-argument domain. -/
theorem article_iff_execution (queries : Queries) (s f t : Pattern)
    (valid : argumentsValidAt [("s", 0), ("f", 0), ("t", 0)] [s, f, t] = true) :
    checkArticle queries [prepared s f t, permitted s f] (transition s f t)
      (article s f t) = true ↔
      atState t ∈ rewriteStepWithPremisesUsing queries.relations language (request s f) := by
  constructor
  · exact checkArticle_sound queries _ _ _
  · intro executed
    obtain ⟨preparation, permission⟩ := (transition_meaning_iff queries s f t).mp executed
    exact execute_article queries s f t valid preparation permission

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Calculus
