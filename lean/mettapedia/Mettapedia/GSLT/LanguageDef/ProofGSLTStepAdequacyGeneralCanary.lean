import Mettapedia.GSLT.LanguageDef.ProofGSLTStepAdequacyGeneral

/-!
# Canaries for general trace adequacy

Positive side: a language whose rewrite rules carry a binder-containing
reduct and a rule with **two** congruence premises, admitted by the
adequate-fragment gate, with checked certificates obtained **through the
general adequacy theorem** — not through a hand-built fixture proof.

Negative side, one compiled counterexample per fragment gate:

* **modedness** — a rule whose right side reads an unbound metavariable is
  rejected by the gate; its generated presentation proves a ground step the
  language cannot take (soundness would fail);
* **explicit substitution** — a rule whose right side is a `.subst` node is
  rejected by the gate; `applyBindings` evaluates the node while schema
  instantiation preserves it, so the checked target is not the declarative
  target (soundness would fail);
* **collections** — a rule with a rest-free bag pattern is rejected by the
  gate; bag matching is multiset-commutative while instantiation is
  positional, so a declarative step through a permuted match has no
  certificate (completeness would fail);
* **unsupported premises** — a relation-query premise is rejected by the
  gate exactly as by `DirectTraceLanguage.ofLanguage?`.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.StepAdequacyGeneralCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT

/-! ## The positive language: binders and a two-premise congruence rule -/

private def genType : TypeDecl := TypeDecl.plain "GT"

private def genUnit : GrammarRule :=
  { label := "gen-unit", category := "GT", params := []
    syntaxPattern := [] }

private def genThunk : GrammarRule :=
  { label := "gen-thunk", category := "GT"
    params := [.simple "body" (.base "GT")]
    syntaxPattern := [] }

private def genPair : GrammarRule :=
  { label := "gen-pair", category := "GT"
    params := [.simple "first" (.base "GT"), .simple "second" (.base "GT")]
    syntaxPattern := [] }

private def termUnit : Pattern := .apply "gen-unit" []

/-- A binder-carrying value: a thunked identity. -/
private def termThunkIdentity : Pattern :=
  .apply "gen-thunk" [.lambda none (.bvar 0)]

private def termPair (first second : Pattern) : Pattern :=
  .apply "gen-pair" [first, second]

/-- Ground rule whose reduct contains a binder literal. -/
private def mkRule : RewriteRule :=
  { name := "mk"
    typeContext := []
    premises := []
    left := termUnit
    right := termThunkIdentity }

/-- Two authored congruence premises in one rule. -/
private def pairCongRule : RewriteRule :=
  { name := "pair-cong"
    typeContext := [("p", .base "GT"), ("pAfter", .base "GT"),
      ("q", .base "GT"), ("qAfter", .base "GT")]
    premises := [.congruence (.fvar "p") (.fvar "pAfter"),
      .congruence (.fvar "q") (.fvar "qAfter")]
    left := termPair (.fvar "p") (.fvar "q")
    right := termPair (.fvar "pAfter") (.fvar "qAfter") }

private def pairLanguage : LanguageDef :=
  { name := "proof-gslt-general-adequacy-canary"
    types := [genType]
    terms := [genUnit, genThunk, genPair]
    equations := []
    rewrites := [mkRule, pairCongRule] }

/-- The gate admits the language. -/
private theorem pairAdequate :
    languageDirectTraceAdequate pairLanguage = true := by
  simp [languageDirectTraceAdequate, pairLanguage, mkRule, pairCongRule,
    rewriteDirectTraceAdequate, tracePremisesModed, patternHoleSkeleton,
    patternsHoleSkeleton, patternClosedSkeleton,
    patternOccurrenceNames, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, termUnit, termThunkIdentity, termPair]

private def directCanary : DirectTraceLanguage :=
  ⟨pairLanguage, directTracePresentable_of_adequate pairAdequate⟩

private theorem mkId_spelling :
    ("step-rewrite-" ++ "mk" : String) = "step-rewrite-mk" := rfl

private theorem pairCongId_spelling :
    ("step-rewrite-" ++ "pair-cong" : String) = "step-rewrite-pair-cong" := rfl

private theorem canary_validate :
    (stepPresentation directCanary).language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepPresentation, directCanary, pairLanguage, genType, genUnit,
      genThunk, genPair, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

private theorem canary_valid :
    (stepPresentation directCanary).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [canary_validate]
  simp [stepPresentation, directCanary, pairLanguage, genType, genUnit,
    genThunk, genPair, mkRule, pairCongRule, rewriteStepRule,
    rewritePremiseJudgments, stepReflRule, stepTransRule, termUnit,
    termThunkIdentity, termPair, mkId_spelling, pairCongId_spelling,
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

/-! ## Declarative steps -/

private theorem mk_langReduces :
    langReduces pairLanguage termUnit termThunkIdentity := by
  refine ⟨1, .rule (rule := mkRule) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [pairLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    simp [mkRule, termUnit, matchPattern, matchArgs]
  · exact .nil []
  · rw [applyBindingsForRule_eq_syntactic]
    simp [mkRule, termThunkIdentity, applyBindings]

private theorem merge_pq :
    mergeBindings [("q", termUnit), ("p", termUnit)]
        [("pAfter", termThunkIdentity)] =
      some [("pAfter", termThunkIdentity), ("q", termUnit),
        ("p", termUnit)] := by
  simp [mergeBindings, List.foldlM, List.find?]

private theorem merge_pq' :
    mergeBindings
        [("pAfter", termThunkIdentity), ("q", termUnit), ("p", termUnit)]
        [("qAfter", termThunkIdentity)] =
      some [("qAfter", termThunkIdentity), ("pAfter", termThunkIdentity),
        ("q", termUnit), ("p", termUnit)] := by
  simp [mergeBindings, List.foldlM, List.find?]

/-- One rule application discharging two congruence premises, each stepping
to a binder-carrying value. -/
private theorem pair_langReduces :
    langReduces pairLanguage (termPair termUnit termUnit)
      (termPair termThunkIdentity termThunkIdentity) := by
  obtain ⟨fuel, mkEvidence⟩ := mk_langReduces
  refine ⟨fuel + 1, .rule (rule := pairCongRule)
    (initialBindings := [("q", termUnit), ("p", termUnit)])
    (finalBindings := [("qAfter", termThunkIdentity),
      ("pAfter", termThunkIdentity), ("q", termUnit), ("p", termUnit)])
    ?_ ?_ ?_ ?_⟩
  · simp [pairLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    simp [pairCongRule, termPair, termUnit, matchPattern, matchArgs,
      mergeBindings, List.foldlM, List.find?]
  · refine .cons
      (middle := [("pAfter", termThunkIdentity), ("q", termUnit),
        ("p", termUnit)])
      (.congruence (candidate := termThunkIdentity)
        (premiseBindings := [("pAfter", termThunkIdentity)]) ?_ ?_ ?_)
      (.cons
        (middle := [("qAfter", termThunkIdentity),
          ("pAfter", termThunkIdentity), ("q", termUnit), ("p", termUnit)])
        (.congruence (candidate := termThunkIdentity)
          (premiseBindings := [("qAfter", termThunkIdentity)]) ?_ ?_ ?_)
        (.nil _))
    · show StepAt _ _ _
        (applyBindings [("q", termUnit), ("p", termUnit)] (.fvar "p")) _
      simpa [applyBindings, List.find?] using mkEvidence
    · simp [matchPattern]
    · exact merge_pq
    · show StepAt _ _ _
        (applyBindings [("pAfter", termThunkIdentity), ("q", termUnit),
          ("p", termUnit)] (.fvar "q")) _
      simpa [applyBindings, List.find?] using mkEvidence
    · simp [matchPattern]
    · exact merge_pq'
  · rw [applyBindingsForRule_eq_syntactic]
    simp [pairCongRule, termPair, applyBindings, List.find?]

/-! ## Certificates through the general theorem -/

private theorem wellFormed_termUnit : wellFormedTerm termUnit := by
  constructor <;> rfl

private theorem wellFormed_pairUnit :
    wellFormedTerm (termPair termUnit termUnit) := by
  constructor <;> rfl

/-- A binder-carrying reduct has a checked certificate, obtained from the
general adequacy theorem. -/
theorem mk_certificate :
    Nonempty (Derivation (generatedValidated directCanary canary_valid)
      (stepJudgment termUnit termThunkIdentity)) :=
  (directTrace_step_adequacy directCanary pairAdequate canary_valid
    wellFormed_termUnit).mpr mk_langReduces

/-- A two-congruence-premise application has a checked certificate,
obtained from the general adequacy theorem. -/
theorem pair_certificate :
    Nonempty (Derivation (generatedValidated directCanary canary_valid)
      (stepJudgment (termPair termUnit termUnit)
        (termPair termThunkIdentity termThunkIdentity))) :=
  (directTrace_step_adequacy directCanary pairAdequate canary_valid
    wellFormed_pairUnit).mpr pair_langReduces

/-- The corresponding trace certificate. -/
theorem pair_trace_certificate :
    Nonempty (Derivation (generatedValidated directCanary canary_valid)
      (stepsJudgment (termPair termUnit termUnit)
        (termPair termThunkIdentity termThunkIdentity))) :=
  (directTrace_steps_adequacy directCanary pairAdequate canary_valid
    wellFormed_pairUnit).mpr (Relation.ReflTransGen.single pair_langReduces)

/-- Soundness concretely: the generated presentation cannot certify a step
the language does not take. -/
theorem no_unit_to_pair_certificate :
    ¬ Nonempty (Derivation (generatedValidated directCanary canary_valid)
      (stepJudgment termUnit (termPair termUnit termUnit))) := by
  intro witness
  have reduces := (directTrace_step_adequacy directCanary pairAdequate
    canary_valid wellFormed_termUnit).mp witness
  obtain ⟨fuel, evidence⟩ := reduces
  cases evidence with
  | rule ruleMember matchMember premisesEvidence applyEq =>
      rename_i innerFuel rule initialBindings finalBindings
      have ruleCases : rule = mkRule ∨ rule = pairCongRule := by
        simpa [directCanary, pairLanguage] using ruleMember
      rcases ruleCases with rfl | rfl
      · rw [matchPatternForRule_eq_syntactic] at matchMember
        simp [mkRule, termUnit, matchPattern, matchArgs] at matchMember
        subst matchMember
        cases premisesEvidence with
        | nil =>
            rw [applyBindingsForRule_eq_syntactic] at applyEq
            simp [mkRule, termThunkIdentity, termPair, termUnit,
              applyBindings] at applyEq
      · rw [matchPatternForRule_eq_syntactic] at matchMember
        simp [pairCongRule, termPair, termUnit, matchPattern] at matchMember

private theorem option_some_bind {α β : Type _} (value : α)
    (rest : α → Option β) : (some value >>= rest) = rest value := rfl

/-! ## Falsifier: sequential modedness is necessary -/

private def orphanRule : RewriteRule :=
  { name := "orphan"
    typeContext := [("x", .base "GT")]
    premises := []
    left := termUnit
    right := .fvar "x" }

private def orphanLanguage : LanguageDef :=
  { name := "proof-gslt-general-adequacy-orphan"
    types := [genType]
    terms := [genUnit, genThunk, genPair]
    equations := []
    rewrites := [orphanRule] }

/-- The gate rejects the unbound right-side metavariable. -/
theorem orphan_gate_rejects :
    languageDirectTraceAdequate orphanLanguage = false := by
  simp [languageDirectTraceAdequate, orphanLanguage, orphanRule,
    rewriteDirectTraceAdequate, tracePremisesModed, patternHoleSkeleton,
    patternOccurrenceNames, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, termUnit]

private theorem orphanPresentable :
    LanguageDef.directTracePresentable orphanLanguage = true := rfl

private def orphanDirect : DirectTraceLanguage :=
  ⟨orphanLanguage, orphanPresentable⟩

private theorem orphanId_spelling :
    ("step-rewrite-" ++ "orphan" : String) = "step-rewrite-orphan" := rfl

private theorem orphan_validate :
    (stepPresentation orphanDirect).language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepPresentation, orphanDirect, orphanLanguage, genType, genUnit,
      genThunk, genPair, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

private theorem orphan_valid :
    (stepPresentation orphanDirect).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [orphan_validate]
  simp [stepPresentation, orphanDirect, orphanLanguage, genType, genUnit,
    genThunk, genPair, orphanRule, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, termUnit, orphanId_spelling,
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

private theorem orphan_instantiates :
    instantiateRule? (generatedValidated orphanDirect orphan_valid)
        ⟨⟨"step-rewrite-orphan"⟩, [termUnit]⟩ =
      some ([], stepJudgment termUnit termUnit) := by
  simp [instantiateRule?, generatedValidated, stepPresentation, orphanDirect,
    orphanLanguage, orphanRule, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, orphanId_spelling, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, termUnit, lookupArgumentAt?,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, stepJudgment, RuleSchema.sideConditionsHold,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- The generated presentation accepts a ground certificate for
`unit → unit`. -/
theorem orphan_certificate :
    Nonempty (Derivation (generatedValidated orphanDirect orphan_valid)
      (stepJudgment termUnit termUnit)) :=
  ⟨.byRule ⟨⟨"step-rewrite-orphan"⟩, [termUnit]⟩
    (instantiateRule?_eq_some_iff_application.mp orphan_instantiates) .nil⟩

/-- The language itself steps `unit` only to the free variable, never to
`unit`. -/
theorem orphan_no_step : ¬ langReduces orphanLanguage termUnit termUnit := by
  rintro ⟨fuel, evidence⟩
  cases evidence with
  | rule ruleMember matchMember premisesEvidence applyEq =>
      rename_i innerFuel rule initialBindings finalBindings
      have ruleEq : rule = orphanRule := by
        simpa [orphanLanguage] using ruleMember
      subst ruleEq
      rw [matchPatternForRule_eq_syntactic] at matchMember
      simp [orphanRule, termUnit, matchPattern, matchArgs] at matchMember
      subst matchMember
      cases premisesEvidence with
      | nil =>
          rw [applyBindingsForRule_eq_syntactic] at applyEq
          simp [orphanRule, termUnit, applyBindings] at applyEq

/-- **Modedness is necessary**: an unmoded rule is gate-rejected, and its
generated presentation certifies a ground step the language cannot take. -/
theorem moded_gate_necessary :
    languageDirectTraceAdequate orphanLanguage = false ∧
    Nonempty (Derivation (generatedValidated orphanDirect orphan_valid)
      (stepJudgment termUnit termUnit)) ∧
    ¬ langReduces orphanLanguage termUnit termUnit :=
  ⟨orphan_gate_rejects, orphan_certificate, orphan_no_step⟩

/-! ## Falsifier: excluding explicit substitution is necessary -/

private def substTarget : Pattern := .subst (.bvar 0) termUnit

private def substRule : RewriteRule :=
  { name := "subst-step"
    typeContext := []
    premises := []
    left := termUnit
    right := substTarget }

private def substLanguage : LanguageDef :=
  { name := "proof-gslt-general-adequacy-subst"
    types := [genType]
    terms := [genUnit, genThunk, genPair]
    equations := []
    rewrites := [substRule] }

/-- The gate rejects the explicit-substitution node. -/
theorem subst_gate_rejects :
    languageDirectTraceAdequate substLanguage = false := by
  simp [languageDirectTraceAdequate, substLanguage, substRule,
    rewriteDirectTraceAdequate, patternHoleSkeleton, substTarget, termUnit]

private theorem substPresentable :
    LanguageDef.directTracePresentable substLanguage = true := rfl

private def substDirect : DirectTraceLanguage :=
  ⟨substLanguage, substPresentable⟩

private theorem substId_spelling :
    ("step-rewrite-" ++ "subst-step" : String) = "step-rewrite-subst-step" :=
  rfl

private theorem subst_validate :
    (stepPresentation substDirect).language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepPresentation, substDirect, substLanguage, genType, genUnit,
      genThunk, genPair, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

private theorem subst_valid :
    (stepPresentation substDirect).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [subst_validate]
  simp [stepPresentation, substDirect, substLanguage, genType, genUnit,
    genThunk, genPair, substRule, substTarget, rewriteStepRule,
    rewritePremiseJudgments, stepReflRule, stepTransRule, termUnit,
    substId_spelling,
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

private theorem subst_instantiates :
    instantiateRule? (generatedValidated substDirect subst_valid)
        ⟨⟨"step-rewrite-subst-step"⟩, []⟩ =
      some ([], stepJudgment termUnit substTarget) := by
  simp [instantiateRule?, generatedValidated, stepPresentation, substDirect,
    substLanguage, substRule, substTarget, rewriteStepRule,
    rewritePremiseJudgments, stepReflRule, stepTransRule, substId_spelling,
    Presentation.lookupRule?, argumentsValidAt, termUnit,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, stepJudgment, RuleSchema.sideConditionsHold]

/-- The checker certifies the raw substitution node as the target. -/
theorem subst_certificate :
    Nonempty (Derivation (generatedValidated substDirect subst_valid)
      (stepJudgment termUnit substTarget)) :=
  ⟨.byRule ⟨⟨"step-rewrite-subst-step"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp subst_instantiates) .nil⟩

/-- The language evaluates the substitution: its target is `unit`, never
the raw substitution node. -/
theorem subst_no_raw_step :
    ¬ langReduces substLanguage termUnit substTarget := by
  rintro ⟨fuel, evidence⟩
  cases evidence with
  | rule ruleMember matchMember premisesEvidence applyEq =>
      rename_i innerFuel rule initialBindings finalBindings
      have ruleEq : rule = substRule := by
        simpa [substLanguage] using ruleMember
      subst ruleEq
      rw [matchPatternForRule_eq_syntactic] at matchMember
      simp [substRule, termUnit, matchPattern, matchArgs] at matchMember
      subst matchMember
      cases premisesEvidence with
      | nil =>
          rw [applyBindingsForRule_eq_syntactic] at applyEq
          simp [substRule, substTarget, termUnit, applyBindings,
            instantiateBVar, instantiateBVarAt, liftBVars] at applyEq

/-- **Excluding `.subst` is necessary**: `applyBindings` evaluates the node
while schema instantiation preserves it, so the checked target and the
declarative target disagree. -/
theorem subst_gate_necessary :
    languageDirectTraceAdequate substLanguage = false ∧
    Nonempty (Derivation (generatedValidated substDirect subst_valid)
      (stepJudgment termUnit substTarget)) ∧
    ¬ langReduces substLanguage termUnit substTarget :=
  ⟨subst_gate_rejects, subst_certificate, subst_no_raw_step⟩

/-! ## Falsifier: excluding collection patterns is necessary -/

private def bagRule : RewriteRule :=
  { name := "bag-pair"
    typeContext := [("x", .base "GT"), ("y", .base "GT")]
    premises := []
    left := .collection .hashBag [.fvar "x", .fvar "y"] none
    right := termPair (.fvar "x") (.fvar "y") }

private def bagLanguage : LanguageDef :=
  { name := "proof-gslt-general-adequacy-bag"
    types := [genType]
    terms := [genUnit, genThunk, genPair]
    equations := []
    rewrites := [bagRule] }

private def bagSource : Pattern :=
  .collection .hashBag [termUnit, termThunkIdentity] none

/-- The gate rejects the collection pattern. -/
theorem bag_gate_rejects :
    languageDirectTraceAdequate bagLanguage = false := by
  simp [languageDirectTraceAdequate, bagLanguage, bagRule,
    rewriteDirectTraceAdequate, patternHoleSkeleton]

private theorem bagPresentable :
    LanguageDef.directTracePresentable bagLanguage = true := rfl

private def bagDirect : DirectTraceLanguage := ⟨bagLanguage, bagPresentable⟩

private theorem bagId_spelling :
    ("step-rewrite-" ++ "bag-pair" : String) = "step-rewrite-bag-pair" := rfl

private theorem bag_validate :
    (stepPresentation bagDirect).language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [stepPresentation, bagDirect, bagLanguage, genType, genUnit,
      genThunk, genPair, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

private theorem bag_valid :
    (stepPresentation bagDirect).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [bag_validate]
  simp [stepPresentation, bagDirect, bagLanguage, genType, genUnit,
    genThunk, genPair, bagRule, rewriteStepRule, rewritePremiseJudgments,
    stepReflRule, stepTransRule, termPair, bagId_spelling,
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

/-- The language takes the permuted step: bag matching may bind `x` to the
second element and `y` to the first. -/
theorem bag_swap_step :
    langReduces bagLanguage bagSource
      (termPair termThunkIdentity termUnit) := by
  refine ⟨1, .rule (rule := bagRule)
    (initialBindings := [("y", termUnit), ("x", termThunkIdentity)])
    (finalBindings := [("y", termUnit), ("x", termThunkIdentity)])
    ?_ ?_ ?_ ?_⟩
  · simp [bagLanguage]
  · rw [matchPatternForRule_eq_syntactic]
    simp [bagRule, bagSource, matchPattern, matchBag, mergeBindings,
      List.foldlM, List.find?, List.zipIdx, List.eraseIdx, termUnit,
      termThunkIdentity]
  · exact .nil _
  · rw [applyBindingsForRule_eq_syntactic]
    simp [bagRule, termPair, applyBindings, List.find?]

private theorem argumentsValidAt_two_inversion
    {firstName secondName : String} {arguments : List Pattern}
    (valid :
      argumentsValidAt [(firstName, 0), (secondName, 0)] arguments = true) :
    ∃ first second, arguments = [first, second] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp [argumentsValidAt] at valid

/-- The permuted step has no certificate: instantiation is positional, so
every accepted conclusion pairs the elements in match order. -/
theorem bag_swap_no_certificate :
    ¬ Nonempty (Derivation (generatedValidated bagDirect bag_valid)
      (stepJudgment bagSource (termPair termThunkIdentity termUnit))) := by
  rintro ⟨derivation⟩
  cases derivation with
  | byRule ruleInstance application children =>
      have executable :=
        instantiateRule?_eq_some_iff_application.mpr application
      simp only [instantiateRule?, generatedValidated_fst] at executable
      cases lookup :
          (stepPresentation bagDirect).lookupRule? ruleInstance.ruleId with
      | none => simp [lookup] at executable
      | some rule =>
          simp only [lookup] at executable
          rcases generated_lookup_inversion bagDirect lookup with
            ⟨rewrite, rewriteMember, rfl⟩ | rfl | rfl
          · have rewriteEq : rewrite = bagRule := by
              simpa [bagDirect, bagLanguage] using rewriteMember
            subst rewriteEq
            by_cases argumentsValid : argumentsValidAt
                (rewriteStepRule bagRule).metavariables
                ruleInstance.arguments = true
            · obtain ⟨first, second, argumentsEq⟩ :=
                argumentsValidAt_two_inversion
                  (by simpa [rewriteStepRule, bagRule] using argumentsValid)
              rw [if_pos argumentsValid, argumentsEq] at executable
              simp [bagRule, rewriteStepRule, rewritePremiseJudgments,
                RuleSchema.sideConditionsHold, instantiateSchemas?,
                instantiateSchema?, instantiateSchemasAt?,
                instantiateSchemaAt?, lookupArgumentAt?, option_some_bind,
                stepJudgment, bagSource, termPair, termUnit,
                termThunkIdentity] at executable
              obtain ⟨-, ⟨firstEq, secondEq⟩, pairEq⟩ := executable
              rw [firstEq, secondEq] at pairEq
              simp at pairEq
            · rw [if_neg argumentsValid] at executable
              simp at executable
          · by_cases argumentsValid : argumentsValidAt
                stepReflRule.metavariables ruleInstance.arguments = true
            · obtain ⟨point, argumentsEq, wfPoint⟩ :=
                argumentsValidAt_one_inversion
                  (by simpa [stepReflRule] using argumentsValid)
              rw [if_pos argumentsValid, argumentsEq] at executable
              simp [stepReflRule, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?,
                instantiateSchemasAt?, instantiateSchemaAt?,
                lookupArgumentAt?, option_some_bind,
                stepJudgment] at executable
            · rw [if_neg argumentsValid] at executable
              simp at executable
          · by_cases argumentsValid : argumentsValidAt
                stepTransRule.metavariables ruleInstance.arguments = true
            · obtain ⟨s, m, t, argumentsEq, wfS, wfM, wfT⟩ :=
                argumentsValidAt_three_inversion
                  (by simpa [stepTransRule] using argumentsValid)
              rw [if_pos argumentsValid, argumentsEq] at executable
              simp [stepTransRule, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?,
                instantiateSchemasAt?, instantiateSchemaAt?,
                lookupArgumentAt?, option_some_bind,
                stepJudgment] at executable
            · rw [if_neg argumentsValid] at executable
              simp at executable

/-- **Excluding collection patterns is necessary**: bag matching commutes
elements while instantiation is positional, so a declarative step through a
permuted match has no certificate. -/
theorem bag_gate_necessary :
    languageDirectTraceAdequate bagLanguage = false ∧
    langReduces bagLanguage bagSource
      (termPair termThunkIdentity termUnit) ∧
    ¬ Nonempty (Derivation (generatedValidated bagDirect bag_valid)
      (stepJudgment bagSource (termPair termThunkIdentity termUnit))) :=
  ⟨bag_gate_rejects, bag_swap_step, bag_swap_no_certificate⟩

/-! ## Unsupported premises stay rejected at both gates -/

private def queryRule : RewriteRule :=
  { name := "query-step"
    typeContext := [("x", .base "GT")]
    premises := [.relationQuery "Rel" [.fvar "x"]]
    left := termUnit
    right := .fvar "x" }

private def queryLanguage : LanguageDef :=
  { name := "proof-gslt-general-adequacy-query"
    types := [genType]
    terms := [genUnit, genThunk, genPair]
    equations := []
    rewrites := [queryRule] }

/-- A relation-query premise fails the adequate gate. -/
theorem query_gate_rejects :
    languageDirectTraceAdequate queryLanguage = false := by
  simp [languageDirectTraceAdequate, queryLanguage, queryRule,
    rewriteDirectTraceAdequate, tracePremisesModed, patternHoleSkeleton,
    termUnit]

/-- The same premise already fails direct-trace admission. -/
theorem query_ofLanguage?_none :
    DirectTraceLanguage.ofLanguage? queryLanguage = none :=
  DirectTraceLanguage.ofLanguage?_eq_none_of_unsupported
    (by simp [LanguageDef.directTracePresentable,
      RewriteRule.directTracePresentable, queryLanguage, queryRule])

end Mettapedia.GSLT.LanguageDef.ProofGSLT.StepAdequacyGeneralCanary
