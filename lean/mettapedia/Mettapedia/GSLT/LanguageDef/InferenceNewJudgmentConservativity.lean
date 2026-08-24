import Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension
import Mettapedia.GSLT.LanguageDef.ExtensionGluing

/-!
# Derivation conservativity for new-judgment extensions

`newJudgmentsOnly` is an executable root policy: every added rule concludes a
judgment head absent from the base.  This file proves its derivation-level
meaning.  A target derivation whose goal belongs to the base judgment
signature uses only retained base rules, recursively, and therefore reflects
to a base derivation with the same raw proof tree.

The result does not apply to `extendsBaseJudgments`; that policy deliberately
permits new derivations of old judgments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
open Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension
open Mettapedia.GSLT.LanguageDef.ExtensionGluing

/-! ## Instantiation preserves premise judgment shapes -/

/-- Pointwise judgment-shape preservation for an instantiated ordered
premise vector. -/
theorem InstantiatesListAt.results_haveJudgmentShape
    {presentation : Presentation} {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat}
    {schemas results : List Pattern}
    (instantiates :
      InstantiatesListAt formals arguments depth schemas results)
    (schemaShapes : ∀ schema ∈ schemas,
      presentation.hasJudgmentShape schema = true) :
    ∀ result ∈ results, presentation.hasJudgmentShape result = true := by
  induction schemas generalizing results with
  | nil =>
      cases instantiates
      simp
  | cons schema schemas inductionHypothesis =>
      cases instantiates with
      | cons head tail =>
          intro candidate membership
          simp only [List.mem_cons] at membership
          rcases membership with rfl | membership
          · exact head.preservesJudgmentShape
              (schemaShapes schema (by simp))
          · exact inductionHypothesis tail
              (fun item itemMember =>
                schemaShapes item (by simp [itemMember]))
              candidate membership

/-- Every instantiated premise of a base rule application remains in the
base judgment signature. -/
theorem RuleApplication.premises_haveJudgmentShape
    {presentation : ValidatedPresentation} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    ∀ premise ∈ premises,
      presentation.1.hasJudgmentShape premise = true := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have valid := rule_isValidIn_of_lookup presentation lookup
      have patternShapes :
          ∀ pattern ∈ RuleSchema.patterns rule,
            presentation.1.hasJudgmentShape pattern = true := by
        intro pattern member
        have schemasValid :
            (RuleSchema.patterns rule).all
                presentation.1.judgmentSchemaValid = true := by
          simp only [RuleSchema.isValidIn, Bool.and_eq_true] at valid
          exact valid.2.1
        exact presentation.1.hasJudgmentShape_of_judgmentSchemaValid
          ((List.all_eq_true.mp schemasValid) pattern member)
      exact
        InferenceNewJudgmentConservativity.InstantiatesListAt.results_haveJudgmentShape
          premisesInstantiate
        (fun schema member => patternShapes schema (by
          simp [RuleSchema.patterns, member]))

/-! ## Added rules cannot derive base judgments -/

theorem ValidatedExtension.addedRule_not_baseShaped
    {base : ValidatedPresentation} (extension : ValidatedExtension base)
    (policy : extension.policy = .newJudgmentsOnly)
    {rule : RuleSchema} (member : rule ∈ extension.extension.newRules)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup :
      extension.target.1.lookupRule? ruleInstance.ruleId = some rule)
    (application :
      RuleApplication extension.target ruleInstance premises conclusion)
    (baseShape : base.1.hasJudgmentShape conclusion = true) : False := by
  cases application with
  | intro actualRule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have ruleEquality : actualRule = rule := by
        rw [actualLookup] at lookup
        exact Option.some.inj lookup
      subst rule
      have policyHolds := extension.policyHolds
      rw [policy] at policyHolds
      have actualPolicy :=
        (List.all_eq_true.mp (by
          simpa [PresentationExtension.policyHolds] using policyHolds))
          actualRule member
      rcases actualRule with
        ⟨ruleId, metavariables, rulePremises, ruleConclusion,
          sideConditions⟩
      cases conclusionInstantiates with
      | @apply constructor schemas results depth items =>
          have foundResult :
              (base.1.lookupJudgment?
                constructor results.length).isSome = true := by
            simpa [Presentation.hasJudgmentShape] using baseShape
          have foundSchema :
              (base.1.lookupJudgment?
                constructor schemas.length).isSome = true := by
            simpa [items.length_eq] using foundResult
          have declared := mem_judgmentHeads_of_lookup foundSchema
          have noneDeclared :
              ∀ declaration ∈ base.1.judgments,
                declaration.head ≠ constructor := by
            simpa using actualPolicy
          rcases List.mem_map.mp declared with
            ⟨declaration, declarationMember, declarationHead⟩
          exact noneDeclared declaration declarationMember declarationHead
      | bvar => simp at actualPolicy
      | fvar => simp at actualPolicy
      | lambda => simp at actualPolicy
      | multiLambda => simp at actualPolicy
      | subst => simp at actualPolicy
      | collection => simp at actualPolicy

/-! ## Derivation-level conservativity -/

mutual

/-- A raw proof of an old judgment accepted by a `newJudgmentsOnly` target is
accepted unchanged by the base presentation. -/
theorem ValidatedExtension.checkRaw_true_base_of_newJudgmentsOnly
    {base : ValidatedPresentation} (extension : ValidatedExtension base)
    (policy : extension.policy = .newJudgmentsOnly)
    {goal : Pattern} (baseShape : base.1.hasJudgmentShape goal = true)
    {proof : RawProof}
    (accepted : checkRaw extension.target goal proof = true) :
    checkRaw base goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at accepted ⊢
      cases targetLocal :
          instantiateRule? extension.target ruleInstance with
      | none => simp [targetLocal] at accepted
      | some localResult =>
        rcases localResult with ⟨premises, conclusion⟩
        simp only [targetLocal, Bool.and_eq_true, decide_eq_true_eq] at accepted
        rcases accepted with ⟨conclusionEq, childrenAccepted⟩
        subst goal
        have application :
            RuleApplication extension.target ruleInstance premises conclusion :=
          instantiateRule?_eq_some_iff_application.mp targetLocal
        rcases
            InferenceSemanticExtension.SemanticExtension.target_application_classifies
              application with
          baseApplication | ⟨rule, member, lookup⟩
        · have baseLocal :
              instantiateRule? base ruleInstance = some (premises, conclusion) :=
            instantiateRule?_eq_some_iff_application.mpr baseApplication
          simp only [baseLocal, decide_true, Bool.true_and]
          exact
            InferenceNewJudgmentConservativity.ValidatedExtension.checkRawChildren_true_base_of_newJudgmentsOnly
              extension policy
              (InferenceNewJudgmentConservativity.RuleApplication.premises_haveJudgmentShape
                baseApplication)
              childrenAccepted
        · exact False.elim
            (InferenceNewJudgmentConservativity.ValidatedExtension.addedRule_not_baseShaped
              extension policy member lookup application baseShape)
termination_by sizeOf proof

/-- Ordered premise proofs accepted by the target reflect pointwise to the
base checker when every premise belongs to the base judgment signature. -/
theorem ValidatedExtension.checkRawChildren_true_base_of_newJudgmentsOnly
    {base : ValidatedPresentation} (extension : ValidatedExtension base)
    (policy : extension.policy = .newJudgmentsOnly)
    {premises : List Pattern}
    (baseShapes : ∀ premise ∈ premises,
      base.1.hasJudgmentShape premise = true)
    {proofs : List RawProof}
    (accepted :
      checkRawChildren extension.target premises proofs = true) :
    checkRawChildren base premises proofs = true := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => simp [checkRawChildren]
      | cons proof proofs => simp [checkRawChildren] at accepted
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkRawChildren] at accepted
      | cons proof proofs =>
          simp only [checkRawChildren, Bool.and_eq_true] at accepted ⊢
          exact ⟨
            InferenceNewJudgmentConservativity.ValidatedExtension.checkRaw_true_base_of_newJudgmentsOnly
              extension policy (baseShapes premise (by simp)) accepted.1,
            InferenceNewJudgmentConservativity.ValidatedExtension.checkRawChildren_true_base_of_newJudgmentsOnly
              extension policy
              (fun candidate membership =>
                baseShapes candidate (by simp [membership]))
              accepted.2⟩
termination_by sizeOf proofs

decreasing_by
  all_goals simp_all <;> omega

end

/-- A target derivation of an old judgment has a base derivation with exactly
the same raw proof tree.  Existence is stated in `Prop`, so classifying a rule
application cannot leak proof choices into computation. -/
theorem ValidatedExtension.exists_reflectedBaseDerivation
    {base : ValidatedPresentation} (extension : ValidatedExtension base)
    (policy : extension.policy = .newJudgmentsOnly)
    {goal : Pattern} (baseShape : base.1.hasJudgmentShape goal = true)
    (derivation : Derivation extension.target goal) :
    ∃ reflected : Derivation base goal, reflected.erase = derivation.erase := by
  have targetAccepted := checkRaw_erase derivation
  have baseAccepted :=
    InferenceNewJudgmentConservativity.ValidatedExtension.checkRaw_true_base_of_newJudgmentsOnly
      extension policy baseShape targetAccepted
  exact G2_checkRaw_iff_exists_derivation_erases_to.mp baseAccepted

/-- **Derivation-level conservativity.** On every base-shaped goal, target
acceptance under `newJudgmentsOnly` is exactly base acceptance for the same
raw proof artifact. -/
theorem ValidatedExtension.checkRaw_iff_base_of_newJudgmentsOnly
    {base : ValidatedPresentation} (extension : ValidatedExtension base)
    (policy : extension.policy = .newJudgmentsOnly)
    {goal : Pattern} (baseShape : base.1.hasJudgmentShape goal = true)
    (proof : RawProof) :
    checkRaw extension.target goal proof = true ↔
      checkRaw base goal proof = true := by
  constructor
  · exact
      InferenceNewJudgmentConservativity.ValidatedExtension.checkRaw_true_base_of_newJudgmentsOnly
        extension policy baseShape
  · exact checkRaw_true_of_ruleLookupRefines extension.refines

/-! ## Sharpness: audited old-judgment extension is non-conservative -/

namespace ExtendsBaseCounterexample

private def oldJudgment (payload : Pattern) : Pattern :=
  .apply "Old" [payload]

private def basePresentation : Presentation :=
  { language := LanguageDef.empty "old-judgment-base"
    calculus :=
      { judgments := [{ head := "Old", arity := 1 }]
        rules := [] } }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem basePresentation_valid :
    basePresentation.isValidV2 = true := by
  have validate : basePresentation.language.validate = [] := by
    simpa [basePresentation] using emptyLanguage_validate "old-judgment-base"
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [validate]
  simp [basePresentation, Presentation.ruleIds,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.conversionDeclarationValid, LanguageDef.empty,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

private def base : ValidatedPresentation :=
  ⟨basePresentation, basePresentation_valid⟩

private def addedOldRule : RuleSchema :=
  { id := ⟨"added-old-fact"⟩
    metavariables := [("payload", 0)]
    premises := []
    conclusion := oldJudgment (.fvar "payload") }

private def delta : PresentationExtension :=
  { newTerms := []
    newJudgments := []
    newRules := [addedOldRule] }

private theorem delta_disjoint : delta.disjointFrom base.1 = true := by
  decide

private theorem delta_policy :
    delta.policyHolds base.1 (.extendsBaseJudgments ["Old"]) = true := by
  decide

private theorem target_valid : (delta.apply base.1).isValidV2 = true := by
  have validate : (delta.apply base.1).language.validate = [] := by
    simpa [delta, PresentationExtension.apply, base, basePresentation] using
      emptyLanguage_validate "old-judgment-base"
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [validate]
  simp [delta, PresentationExtension.apply, base, basePresentation,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, addedOldRule, oldJudgment,
    RuleSchema.isValidIn, Presentation.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, LanguageDef.empty]
  decide

private def extension : ValidatedExtension base where
  extension := delta
  policy := .extendsBaseJudgments ["Old"]
  disjoint := delta_disjoint
  policyHolds := delta_policy
  valid := target_valid

private def payload : Pattern := .apply "payload" []

private def addedProof : RawProof :=
  .node { ruleId := addedOldRule.id, arguments := [payload] } []

/-- `extendsBaseJudgments` deliberately permits a strict proof extension:
the target accepts this old-shaped judgment while the base rejects the exact
same raw artifact. -/
theorem target_accepts_old_proof_base_rejects :
    checkRaw extension.target (oldJudgment payload) addedProof = true ∧
      checkRaw base (oldJudgment payload) addedProof = false := by
  simp [extension, ValidatedExtension.target, delta,
    PresentationExtension.apply, base, basePresentation, addedOldRule,
    addedProof, oldJudgment, payload, checkRaw, checkRawChildren,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Consequently the bidirectional conservativity theorem cannot be widened
from `newJudgmentsOnly` to every validated extension. -/
theorem old_judgment_checkers_disagree :
    ¬ (checkRaw extension.target (oldJudgment payload) addedProof = true ↔
      checkRaw base (oldJudgment payload) addedProof = true) := by
  rw [target_accepts_old_proof_base_rejects.1,
    target_accepts_old_proof_base_rejects.2]
  simp

end ExtendsBaseCounterexample

#print axioms RuleApplication.premises_haveJudgmentShape
#print axioms ValidatedExtension.addedRule_not_baseShaped
#print axioms ValidatedExtension.exists_reflectedBaseDerivation
#print axioms ValidatedExtension.checkRaw_iff_base_of_newJudgmentsOnly
#print axioms ExtendsBaseCounterexample.old_judgment_checkers_disagree

end Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity
