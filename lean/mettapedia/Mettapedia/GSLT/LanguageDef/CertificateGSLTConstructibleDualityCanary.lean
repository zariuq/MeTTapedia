import Mettapedia.GSLT.LanguageDef.CertificateGSLTConstructibleDuality

/-!
# The evidence database: Belnap's four cells, without explosion

An evidence database over four atoms, assembled as the join of a positive
table (`Holds`) and a negative table (`Denied`):

* `alpha` — evidence on both sides: **conflicted**;
* `beta`  — positive evidence only: **established**;
* `delta` — negative evidence only: **refuted**;
* `gamma` — no evidence at all: **undetermined**.

The compiled centerpiece is the ex-falso half of the closure parallel:

* `no_explosion` — despite checked conflict at `alpha`, the unrelated
  `gamma` stays underivable: no implicit ex-falso rule spreads the
  contradiction;
* `explosion_is_authorable` — an ex-falso instance is expressible on demand: adding
  one authored rule from the conflict to `gamma` makes `gamma` derivable,
  with the base's own conflict certificates transported along the strict
  injection and fed to the new rule.

Together with `congruence_is_not_free` this completes a precise pair: free
contextual congruence and implicit ex falso are absent by default, while
both principles can be represented by authored rules.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.ConstructibleDualityCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## The core language and the two evidence tables -/

private def evidenceType : TypeDecl := TypeDecl.plain "EV"

private def atomRule (label : String) : GrammarRule :=
  { label := label, category := "EV", params := [], syntaxPattern := [] }

private def atomAlpha : Pattern := .apply "atom-alpha" []
private def atomBeta : Pattern := .apply "atom-beta" []
private def atomGamma : Pattern := .apply "atom-gamma" []
private def atomDelta : Pattern := .apply "atom-delta" []

private def holdsJ (atom : Pattern) : Pattern := .apply "Holds" [atom]
private def deniedJ (atom : Pattern) : Pattern := .apply "Denied" [atom]

private def evidenceCore : LanguageDef :=
  { name := "certificate-gslt-evidence-database"
    types := [evidenceType]
    terms := [atomRule "atom-alpha", atomRule "atom-beta",
      atomRule "atom-gamma", atomRule "atom-delta"]
    equations := []
    rewrites := [] }

private def evidenceCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments :=
      [{ head := "Holds", arity := 1 }, { head := "Denied", arity := 1 }] }

private def holdsAlphaRule : RuleSchema :=
  { id := ⟨"holds-alpha"⟩, metavariables := [], premises := []
    conclusion := holdsJ atomAlpha }

private def holdsBetaRule : RuleSchema :=
  { id := ⟨"holds-beta"⟩, metavariables := [], premises := []
    conclusion := holdsJ atomBeta }

private def deniedAlphaRule : RuleSchema :=
  { id := ⟨"denied-alpha"⟩, metavariables := [], premises := []
    conclusion := deniedJ atomAlpha }

private def deniedDeltaRule : RuleSchema :=
  { id := ⟨"denied-delta"⟩, metavariables := [], premises := []
    conclusion := deniedJ atomDelta }

private def holdsRules : List RuleSchema := [holdsAlphaRule, holdsBetaRule]

private def deniedRules : List RuleSchema :=
  [deniedAlphaRule, deniedDeltaRule]

/-! ## The database is the join of the two tables -/

private theorem evidenceCore_validate (rules : List RuleSchema) :
    (rulesPresentation evidenceCore evidenceCalculus rules).language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [rulesPresentation, evidenceCore, evidenceType, atomRule,
      LanguageDef.typeNames, TypeDecl.plain]

private theorem holds_valid :
    (rulesPresentation evidenceCore evidenceCalculus holdsRules).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [evidenceCore_validate]
  simp [rulesPresentation, evidenceCore, evidenceType, atomRule,
    holdsRules, holdsAlphaRule, holdsBetaRule, holdsJ,
    atomAlpha, atomBeta,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private theorem denied_valid :
    (rulesPresentation evidenceCore evidenceCalculus deniedRules).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [evidenceCore_validate]
  simp [rulesPresentation, evidenceCore, evidenceType, atomRule,
    deniedRules, deniedAlphaRule, deniedDeltaRule, deniedJ,
    atomAlpha, atomDelta,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private theorem database_valid :
    (rulesPresentation evidenceCore evidenceCalculus
      (holdsRules ++ deniedRules)).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [evidenceCore_validate]
  simp [rulesPresentation, evidenceCore, evidenceType, atomRule,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, holdsJ, deniedJ,
    atomAlpha, atomBeta, atomDelta,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private def database : ValidatedPresentation :=
  ⟨rulesPresentation evidenceCore evidenceCalculus (holdsRules ++ deniedRules),
    database_valid⟩

/-- The positive and negative tables genuinely amalgamate: both inject
into the database along the join arrows. -/
theorem tables_amalgamate :
    RuleLookupRefines
        ⟨rulesPresentation evidenceCore evidenceCalculus holdsRules, holds_valid⟩ database ∧
      RuleLookupRefines
        ⟨rulesPresentation evidenceCore evidenceCalculus deniedRules, denied_valid⟩
          database := by
  constructor
  · exact join_refines_left
  · exact join_refines_right (by
      intro leftRule leftMem rightRule rightMem
      simp only [holdsRules, List.mem_cons,
        List.not_mem_nil, or_false] at leftMem
      simp only [deniedRules, List.mem_cons,
        List.not_mem_nil, or_false] at rightMem
      rcases leftMem with rfl | rfl <;> rcases rightMem with rfl | rfl <;>
        decide)

/-! ## The four cells, inhabited -/

private theorem holdsAlpha_instantiates :
    instantiateRule? database ⟨⟨"holds-alpha"⟩, []⟩ =
      some ([], holdsJ atomAlpha) := by
  simp [instantiateRule?, database, rulesPresentation, evidenceCore,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, holdsJ, atomAlpha,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem holdsBeta_instantiates :
    instantiateRule? database ⟨⟨"holds-beta"⟩, []⟩ =
      some ([], holdsJ atomBeta) := by
  simp [instantiateRule?, database, rulesPresentation, evidenceCore,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, holdsJ, atomBeta,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem deniedAlpha_instantiates :
    instantiateRule? database ⟨⟨"denied-alpha"⟩, []⟩ =
      some ([], deniedJ atomAlpha) := by
  simp [instantiateRule?, database, rulesPresentation, evidenceCore,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, deniedJ, atomAlpha,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem deniedDelta_instantiates :
    instantiateRule? database ⟨⟨"denied-delta"⟩, []⟩ =
      some ([], deniedJ atomDelta) := by
  simp [instantiateRule?, database, rulesPresentation, evidenceCore,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, deniedJ, atomDelta,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private def holdsAlphaDerivation : Derivation database (holdsJ atomAlpha) :=
  .byRule ⟨⟨"holds-alpha"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp holdsAlpha_instantiates)
    .nil

private def holdsBetaDerivation : Derivation database (holdsJ atomBeta) :=
  .byRule ⟨⟨"holds-beta"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp holdsBeta_instantiates)
    .nil

private def deniedAlphaDerivation :
    Derivation database (deniedJ atomAlpha) :=
  .byRule ⟨⟨"denied-alpha"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp deniedAlpha_instantiates)
    .nil

private def deniedDeltaDerivation :
    Derivation database (deniedJ atomDelta) :=
  .byRule ⟨⟨"denied-delta"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp deniedDelta_instantiates)
    .nil

/-! ## Every admitted application concludes one of the four facts -/

private theorem database_application_shape {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application :
      RuleApplication database ruleInstance premises conclusion) :
    premises = [] ∧
      (conclusion = holdsJ atomAlpha ∨ conclusion = holdsJ atomBeta ∨
        conclusion = deniedJ atomAlpha ∨ conclusion = deniedJ atomDelta) := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  simp only [instantiateRule?] at executable
  cases lookup : database.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at executable
  | some rule =>
      simp only [lookup] at executable
      have ruleCases :
          rule = holdsAlphaRule ∨ rule = holdsBetaRule ∨
            rule = deniedAlphaRule ∨ rule = deniedDeltaRule := by
        have := lookup
        simp only [database, rulesPresentation, evidenceCore, holdsRules,
          deniedRules, Presentation.lookupRule?,
          Presentation.rules] at this
        all_goals simp_all
        rcases this with ⟨_, ruleEq⟩ | ⟨_, ⟨_, ruleEq⟩ | ⟨_, ⟨_, ruleEq⟩ |
          ⟨_, _, ruleEq⟩⟩⟩
        · exact Or.inl ruleEq.symm
        · exact Or.inr (Or.inl ruleEq.symm)
        · exact Or.inr (Or.inr (Or.inl ruleEq.symm))
        · exact Or.inr (Or.inr (Or.inr ruleEq.symm))
      have argumentsEmpty (metavarsEmpty : rule.metavariables = []) :
          ruleInstance.arguments = [] := by
        by_cases valid : argumentsValidAt rule.metavariables
            ruleInstance.arguments = true
        · rw [metavarsEmpty] at valid
          cases arguments : ruleInstance.arguments with
          | nil => rfl
          | cons head tail =>
              rw [arguments] at valid
              simp [argumentsValidAt] at valid
        · simp [valid] at executable
      rcases ruleCases with ruleEq | ruleEq | ruleEq | ruleEq <;>
        subst ruleEq <;>
        rw [argumentsEmpty rfl] at executable <;>
        simp [holdsAlphaRule, holdsBetaRule, deniedAlphaRule,
          deniedDeltaRule, argumentsValidAt, instantiateSchemas?,
          instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?,
          holdsJ, deniedJ, atomAlpha, atomBeta, atomDelta] at executable
      · exact ⟨executable.1, Or.inl executable.2.symm⟩
      · exact ⟨executable.1, Or.inr (Or.inl executable.2.symm)⟩
      · exact ⟨executable.1, Or.inr (Or.inr (Or.inl executable.2.symm))⟩
      · exact ⟨executable.1, Or.inr (Or.inr (Or.inr executable.2.symm))⟩

private theorem underivable_of_not_listed {goal : Pattern}
    (notAlpha : goal ≠ holdsJ atomAlpha) (notBeta : goal ≠ holdsJ atomBeta)
    (notDeniedAlpha : goal ≠ deniedJ atomAlpha)
    (notDeniedDelta : goal ≠ deniedJ atomDelta) :
    ¬ Nonempty (Derivation database goal) := by
  rintro ⟨derivation⟩
  cases derivation with
  | byRule ruleInstance application children =>
      rcases database_application_shape application with
        ⟨-, conclusionCases⟩
      rcases conclusionCases with h | h | h | h
      · exact notAlpha h
      · exact notBeta h
      · exact notDeniedAlpha h
      · exact notDeniedDelta h

/-! ## No explosion: conflict at alpha leaves gamma untouched -/

/-- The ex-falso half of the closure parallel, compiled: the database
holds checked evidence both for and against `alpha`, yet the unrelated
`gamma` acquires no derivation.  Contradiction does not spread without an
authored rule. -/
theorem no_explosion :
    (Nonempty (Derivation database (holdsJ atomAlpha)) ∧
      Nonempty (Derivation database (deniedJ atomAlpha))) ∧
    ¬ Nonempty (Derivation database (holdsJ atomGamma)) := by
  refine ⟨⟨⟨holdsAlphaDerivation⟩, ⟨deniedAlphaDerivation⟩⟩, ?_⟩
  apply underivable_of_not_listed <;>
    simp [holdsJ, deniedJ, atomAlpha, atomBeta, atomGamma, atomDelta]

/-- Belnap's square, fully inhabited by one small database: conflicted at
`alpha`, established at `beta`, refuted at `delta`, undetermined at
`gamma`. -/
theorem belnap_square :
    (Nonempty (Derivation database (holdsJ atomAlpha)) ∧
      Nonempty (Derivation database (deniedJ atomAlpha))) ∧
    (Nonempty (Derivation database (holdsJ atomBeta)) ∧
      ¬ Nonempty (Derivation database (deniedJ atomBeta))) ∧
    (¬ Nonempty (Derivation database (holdsJ atomDelta)) ∧
      Nonempty (Derivation database (deniedJ atomDelta))) ∧
    (¬ Nonempty (Derivation database (holdsJ atomGamma)) ∧
      ¬ Nonempty (Derivation database (deniedJ atomGamma))) := by
  refine ⟨⟨⟨holdsAlphaDerivation⟩, ⟨deniedAlphaDerivation⟩⟩,
    ⟨⟨holdsBetaDerivation⟩, ?_⟩, ⟨?_, ⟨deniedDeltaDerivation⟩⟩, ?_, ?_⟩ <;>
    (apply underivable_of_not_listed <;>
      simp [holdsJ, deniedJ, atomAlpha, atomBeta, atomGamma, atomDelta])

/-- The four-valued verdict computed on the database's own certificates
reports the conflict as checked evidence, not as collapse. -/
theorem alpha_verdict_conflicted :
    pairedVerdict database (holdsJ atomAlpha) (deniedJ atomAlpha)
      (some holdsAlphaDerivation.erase)
      (some deniedAlphaDerivation.erase) = .conflicted := by
  simp [pairedVerdict, laneAccepted, fourOfLanes, checkRaw_erase]

/-! ## Explosion is authorable: ex falso as an opt-in rule -/

private def explosionRule : RuleSchema :=
  { id := ⟨"alpha-conflict-yields-gamma"⟩
    metavariables := []
    premises := [holdsJ atomAlpha, deniedJ atomAlpha]
    conclusion := holdsJ atomGamma }

private theorem exploded_valid :
    (rulesPresentation evidenceCore evidenceCalculus
      ((holdsRules ++ deniedRules) ++ [explosionRule])).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [evidenceCore_validate]
  simp [rulesPresentation, evidenceCore, evidenceType, atomRule,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, explosionRule, holdsJ, deniedJ,
    atomAlpha, atomBeta, atomDelta, atomGamma,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.ruleIds, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Presentation.conversionDeclarationValid]
  decide

private def exploded : ValidatedPresentation :=
  ⟨rulesPresentation evidenceCore evidenceCalculus
    ((holdsRules ++ deniedRules) ++ [explosionRule]), exploded_valid⟩

private theorem database_refines_exploded :
    RuleLookupRefines database exploded := by
  apply RuleLookupRefines.of_rules_eq_append [explosionRule]
  rfl

private theorem explosion_instantiates :
    instantiateRule? exploded ⟨⟨"alpha-conflict-yields-gamma"⟩, []⟩ =
      some ([holdsJ atomAlpha, deniedJ atomAlpha], holdsJ atomGamma) := by
  simp [instantiateRule?, exploded, rulesPresentation, evidenceCore,
    holdsRules, deniedRules, holdsAlphaRule, holdsBetaRule,
    deniedAlphaRule, deniedDeltaRule, explosionRule, holdsJ, deniedJ,
    atomAlpha, atomGamma, Presentation.lookupRule?, argumentsValidAt,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

/-- One ex-falso instance is expressible on demand: an authored rule from the conflict
to `gamma`, fed by the base's own conflict certificates transported along
the strict injection, derives what the base provably could not.  Closure
under the chosen rule theory, like congruence, is authored rather than
implicit. -/
theorem explosion_is_authorable :
    Nonempty (Derivation exploded (holdsJ atomGamma)) :=
  ⟨.byRule ⟨⟨"alpha-conflict-yields-gamma"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp explosion_instantiates)
    (.cons (holdsAlphaDerivation.transport database_refines_exploded)
      (.cons (deniedAlphaDerivation.transport database_refines_exploded)
        .nil))⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.ConstructibleDualityCanary
