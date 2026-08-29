import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral

/-!
# Conversion elimination as a definition morphism

Lean4Less translates Lean into a smaller theory by *eliminating definitional
equalities* — proof irrelevance and K-like reduction — replacing each silent
use of them with an explicit typecast carrying a propositional equality
proof.  This module expresses that move in \GSLT{} terms, on the smallest
fixture that exhibits it, and records what it costs the present framework.

The pattern, stated definition-theoretically:

```
  extensional definition            intensional definition
  conversion is silent                conversion is evidence
  ------------------------            ------------------------
  Typed(a, T p)                       Typed(a, T p)   EqT(T p, T q)
  ------------- irrel                 ---------------------------- cast
  Typed(a, T q)                       Typed(cast a, T q)
```

Both theories reach the same *type*.  They do not reach the same *term*: the
intensional side must insert `cast`.  That is not an artefact of this
fixture; it is the whole content of an extensional-to-intensional
translation, and the reason such translations carry a patching function on
terms rather than only on proofs.

The consequence for this framework is sharp and is proved below.  A
judgment-preserving interpretation may implement one source rule by a
composite target derivation, but it must land on the *same* conclusion.
Conversion elimination cannot: `conversionElimination_needs_term_translation`
shows the intensional definition proves the cast conclusion and provably
does **not** prove the original one.  So this translation is not expressible
as a strict arrow, and not as a judgment-preserving interpretation either.
It is a concrete, industrially motivated demand for the syntax- and
judgment-translating layer that the framework currently lists as future
work — the first such demand that does not come from a fixture built to
motivate it.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.ConversionElimination

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## Shared syntax

Two proofs of one proposition, a family over them, a value, and the cast
constructor the intensional side needs. -/

private def tmType : TypeDecl := TypeDecl.plain "Tm"

private def constructor0 (label : String) : GrammarRule :=
  { label := label, category := "Tm", params := [], syntaxPattern := [] }

private def constructor1 (label : String) : GrammarRule :=
  { label := label, category := "Tm"
    params := [.simple "arg" (.base "Tm")], syntaxPattern := [] }

private def proofOne : Pattern := .apply "ce-pf-one" []
private def proofTwo : Pattern := .apply "ce-pf-two" []
private def theValue : Pattern := .apply "ce-val" []
private def family (argument : Pattern) : Pattern := .apply "ce-fam" [argument]
private def castTerm (argument : Pattern) : Pattern := .apply "ce-cast" [argument]

private def typed (term type : Pattern) : Pattern := .apply "Typed" [term, type]
private def eqT (left right : Pattern) : Pattern := .apply "EqT" [left, right]

private def sharedTerms : List GrammarRule :=
  [constructor0 "ce-pf-one", constructor0 "ce-pf-two", constructor0 "ce-val",
    constructor1 "ce-fam", constructor1 "ce-cast"]

private def sharedJudgments : List JudgmentDecl :=
  [{ head := "Typed", arity := 2 }, { head := "EqT", arity := 2 }]

/-! ## The two definitions -/

/-- The value inhabits the family at the first proof.  Shared. -/
private def axValue : RuleSchema :=
  { id := ⟨"ce-ax-value"⟩
    metavariables := []
    premises := []
    conclusion := typed theValue (family proofOne) }

/-- **Extensional side.**  Proof irrelevance is silent: the same term
changes type with no evidence recorded. -/
private def irrelevanceSilent : RuleSchema :=
  { id := ⟨"ce-irrel-silent"⟩
    metavariables := []
    premises := [typed theValue (family proofOne)]
    conclusion := typed theValue (family proofTwo) }

/-- **Intensional side.**  The same fact, but as an equality judgment. -/
private def irrelevanceEvidence : RuleSchema :=
  { id := ⟨"ce-irrel-evidence"⟩
    metavariables := []
    premises := []
    conclusion := eqT (family proofOne) (family proofTwo) }

/-- **Intensional side.**  Transport along recorded equality, which changes
the term. -/
private def castRule : RuleSchema :=
  { id := ⟨"ce-cast"⟩
    metavariables := [("ceTerm", 0), ("ceFrom", 0), ("ceTo", 0)]
    premises := [typed (.fvar "ceTerm") (.fvar "ceFrom"),
      eqT (.fvar "ceFrom") (.fvar "ceTo")]
    conclusion := typed (castTerm (.fvar "ceTerm")) (.fvar "ceTo") }

private def extensionalLanguage : LanguageDef :=
  { name := "conversion-elimination-extensional"
    types := [tmType]
    terms := sharedTerms
    equations := []
    rewrites := [] }

private def extensionalCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := sharedJudgments
    rules := [axValue, irrelevanceSilent] }

private def intensionalLanguage : LanguageDef :=
  { name := "conversion-elimination-intensional"
    types := [tmType]
    terms := sharedTerms
    equations := []
    rewrites := [] }

private def intensionalCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := sharedJudgments
    rules := [axValue, irrelevanceEvidence, castRule] }

private def extensional : CalculusLanguageDef :=
  CalculusLanguageDef.extend extensionalLanguage extensionalCalculus
private def intensional : CalculusLanguageDef :=
  CalculusLanguageDef.extend intensionalLanguage intensionalCalculus

private theorem extensional_validate :
    extensional.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [extensional, extensionalLanguage, tmType, sharedTerms,
      constructor0, constructor1, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

private theorem intensional_validate :
    intensional.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [intensional, intensionalLanguage, tmType, sharedTerms,
      constructor0, constructor1, LanguageDef.typeNames, TermParam.typeExpr,
      TypeExpr.baseNames, TypeDecl.plain]

theorem extensional_valid : extensional.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [extensional_validate]
  simp [extensional, extensionalCalculus, extensionalLanguage, tmType, sharedTerms, constructor0,
    constructor1, axValue, irrelevanceSilent, typed, theValue, family,
    proofOne, proofTwo, sharedJudgments,
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

theorem intensional_valid : intensional.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [intensional_validate]
  simp [intensional, intensionalCalculus, intensionalLanguage, tmType, sharedTerms, constructor0,
    constructor1, axValue, irrelevanceEvidence, castRule, typed, eqT,
    theValue, family, castTerm, proofOne, proofTwo, sharedJudgments,
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

def extensionalValidated : ValidatedCalculusLanguageDef :=
  ⟨extensional, extensional_valid⟩

def intensionalValidated : ValidatedCalculusLanguageDef :=
  ⟨intensional, intensional_valid⟩

/-! ## What each side proves -/

private def castInstance : RuleInstance :=
  ⟨⟨"ce-cast"⟩, [theValue, family proofOne, family proofTwo]⟩

private theorem axValue_instantiates :
    instantiateRule? intensionalValidated ⟨⟨"ce-ax-value"⟩, []⟩ =
      some ([], typed theValue (family proofOne)) := by
  simp [instantiateRule?, intensionalValidated, intensional, intensionalCalculus,
    intensionalLanguage, axValue, irrelevanceEvidence, castRule,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, typed, theValue, family, proofOne]

private theorem irrelevanceEvidence_instantiates :
    instantiateRule? intensionalValidated ⟨⟨"ce-irrel-evidence"⟩, []⟩ =
      some ([], eqT (family proofOne) (family proofTwo)) := by
  simp [instantiateRule?, intensionalValidated, intensional, intensionalCalculus,
    intensionalLanguage, axValue, irrelevanceEvidence, castRule,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, eqT, family, proofOne, proofTwo]

private theorem cast_instantiates :
    instantiateRule? intensionalValidated castInstance =
      some ([typed theValue (family proofOne),
        eqT (family proofOne) (family proofTwo)],
        typed (castTerm theValue) (family proofTwo)) := by
  simp [instantiateRule?, intensionalValidated, intensional, intensionalCalculus,
    intensionalLanguage, axValue, irrelevanceEvidence, castRule, castInstance,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    lookupArgumentAt?, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    typed, eqT, theValue, family, castTerm, proofOne, proofTwo,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- **The intensional side reaches the type — at a different term.**  This is
the translated form: transport along recorded equality. -/
theorem intensional_proves_cast :
    Nonempty (Derivation intensionalValidated
      (typed (castTerm theValue) (family proofTwo))) :=
  ⟨.byRule castInstance
    (instantiateRule?_eq_some_iff_application.mp cast_instantiates)
    (.cons
      (.byRule ⟨⟨"ce-ax-value"⟩, []⟩
        (instantiateRule?_eq_some_iff_application.mp axValue_instantiates) .nil)
      (.cons
        (.byRule ⟨⟨"ce-irrel-evidence"⟩, []⟩
          (instantiateRule?_eq_some_iff_application.mp
            irrelevanceEvidence_instantiates) .nil)
        .nil))⟩

private theorem irrelevanceSilent_instantiates :
    instantiateRule? extensionalValidated ⟨⟨"ce-irrel-silent"⟩, []⟩ =
      some ([typed theValue (family proofOne)],
        typed theValue (family proofTwo)) := by
  simp [instantiateRule?, extensionalValidated, extensional, extensionalCalculus,
    extensionalLanguage, axValue, irrelevanceSilent, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    typed, theValue, family, proofOne, proofTwo]

private theorem extensional_axValue_instantiates :
    instantiateRule? extensionalValidated ⟨⟨"ce-ax-value"⟩, []⟩ =
      some ([], typed theValue (family proofOne)) := by
  simp [instantiateRule?, extensionalValidated, extensional, extensionalCalculus,
    extensionalLanguage, axValue, irrelevanceSilent, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    typed, theValue, family, proofOne]

/-- **The extensional side reaches it at the original term**, silently. -/
theorem extensional_proves_uncast :
    Nonempty (Derivation extensionalValidated
      (typed theValue (family proofTwo))) :=
  ⟨.byRule ⟨⟨"ce-irrel-silent"⟩, []⟩
    (instantiateRule?_eq_some_iff_application.mp irrelevanceSilent_instantiates)
    (.cons
      (.byRule ⟨⟨"ce-ax-value"⟩, []⟩
        (instantiateRule?_eq_some_iff_application.mp
          extensional_axValue_instantiates) .nil)
      .nil)⟩

/-! ## The cost: the term must change -/

/-- **The intensional side provably does not reach the original term.**
Every rule concluding a typing judgment either fixes the family at the first
proof, or concludes at a cast term; neither matches. -/
theorem intensional_does_not_prove_uncast :
    ¬ Nonempty (Derivation intensionalValidated
      (typed theValue (family proofTwo))) := by
  rintro ⟨derivation⟩
  cases derivation with
  | byRule ruleInstance application children =>
      have executable :=
        instantiateRule?_eq_some_iff_application.mpr application
      simp only [instantiateRule?] at executable
      cases lookup : intensionalValidated.1.lookupRule? ruleInstance.ruleId with
      | none => simp [lookup] at executable
      | some rule =>
          simp only [lookup] at executable
          have ruleCases : rule = axValue ∨ rule = irrelevanceEvidence ∨
              rule = castRule := by
            have member := List.mem_of_find?_eq_some lookup
            simpa [intensionalValidated, intensional, intensionalCalculus,
              intensionalLanguage]
              using member
          rcases ruleCases with rfl | rfl | rfl
          · by_cases valid : argumentsValidAt axValue.metavariables
                ruleInstance.arguments = true
            · rw [if_pos valid] at executable
              simp [axValue, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
                instantiateSchemaAt?, typed, theValue, family, proofOne,
                proofTwo] at executable
            · rw [if_neg valid] at executable; simp at executable
          · by_cases valid : argumentsValidAt irrelevanceEvidence.metavariables
                ruleInstance.arguments = true
            · rw [if_pos valid] at executable
              simp [irrelevanceEvidence, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
                instantiateSchemaAt?, typed, eqT, family, proofOne,
                proofTwo] at executable
            · rw [if_neg valid] at executable; simp at executable
          · by_cases valid : argumentsValidAt castRule.metavariables
                ruleInstance.arguments = true
            · obtain ⟨a, b, c, argumentsEq, -, -, -⟩ :=
                argumentsValidAt_three_inversion
                  (by simpa [castRule] using valid)
              rw [if_pos valid, argumentsEq] at executable
              simp [castRule, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
                instantiateSchemaAt?, lookupArgumentAt?, typed, eqT, theValue,
                castTerm, family] at executable
            · rw [if_neg valid] at executable; simp at executable

/-- **The finding.**  The two definitions prove the same typing *fact* and
provably not the same typing *judgment*: the intensional side must change the
term.  A judgment-preserving interpretation cannot express this translation,
so conversion elimination is a demand for the syntax- and judgment-translating
layer rather than an instance of the present one. -/
theorem conversionElimination_needs_term_translation :
    Nonempty (Derivation extensionalValidated
      (typed theValue (family proofTwo))) ∧
    Nonempty (Derivation intensionalValidated
      (typed (castTerm theValue) (family proofTwo))) ∧
    ¬ Nonempty (Derivation intensionalValidated
      (typed theValue (family proofTwo))) :=
  ⟨extensional_proves_uncast, intensional_proves_cast,
    intensional_does_not_prove_uncast⟩

/-- Nor is it a strict arrow: the silent rule has no counterpart to retain. -/
theorem no_strict_arrow_from_extensional :
    intensional.lookupRule? ⟨"ce-irrel-silent"⟩ = none := by
  simp [intensional, intensionalCalculus, intensionalLanguage,
    CalculusLanguageDef.lookupRule?, axValue,
    irrelevanceEvidence, castRule]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.ConversionElimination
