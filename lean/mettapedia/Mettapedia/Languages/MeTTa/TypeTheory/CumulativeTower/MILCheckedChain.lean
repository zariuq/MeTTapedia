import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILSchemaElaboration
import Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension

open Mettapedia.GSLT.LanguageDef

/-!
# A checked MIL chain over a validated calculus-language extension

This is the finite bridge canary between the intrinsic Prime metarule and the
generic proof checker.  The base definition declares the relational judgment
but proves no facts.  A proposed learned extension adds two observed facts and
the generic chain rule.  The ordinary structural checker accepts the exact
proof tree for `alice -> carol`; an independently stated reachability semantics
supplies its meaning.

The learned rule remains a calculus-language extension, not a new Prime primitive.
Its semantic use is governed by `InferenceSemanticExtension.SemanticExtension`.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedChain

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension

private def entityConstructor (label : String) : GrammarRule :=
  { label
    category := "Entity"
    params := []
    syntaxPattern := [] }

def alice : Pattern := .apply "Alice" []
def bob : Pattern := .apply "Bob" []
def carol : Pattern := .apply "Carol" []

def relates (source target : Pattern) : Pattern :=
  .apply "MIL.Rel" [source, target]

private def relationLanguage : LanguageDef :=
  { name := "prime-mil-chain"
    types := [TypeDecl.plain "Entity"]
    terms :=
      [entityConstructor "Alice", entityConstructor "Bob",
        entityConstructor "Carol"]
    equations := []
    rewrites := [] }

private def baseDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend relationLanguage
    { judgments := [{ head := "MIL.Rel", arity := 2 }]
      rules := [] }

private theorem relationLanguage_validate :
    relationLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly relationLanguage <;>
    simp [relationLanguage, entityConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr]

private theorem baseDefinition_valid :
    baseDefinition.isValid = true := by
  have hvalidate : baseDefinition.toLanguageDef.validate = [] := by
    simpa [baseDefinition] using relationLanguage_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [baseDefinition, relationLanguage, entityConstructor,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

def base : ValidatedCalculusLanguageDef :=
  ⟨baseDefinition, baseDefinition_valid⟩

def motherRule : RuleSchema :=
  { id := ⟨"mil-mother-alice-bob"⟩
    metavariables := []
    premises := []
    conclusion := relates alice bob }

def fatherRule : RuleSchema :=
  { id := ⟨"mil-father-bob-carol"⟩
    metavariables := []
    premises := []
    conclusion := relates bob carol }

/-- The authored MIL chain schema at the checker boundary.  Its three ordered
arguments are the source, retained intermediate, and target occurrences. -/
def chainRule : RuleSchema :=
  { id := ⟨"mil-chain"⟩
    metavariables := [("source", 0), ("middle", 0), ("target", 0)]
    premises :=
      [relates (.fvar "source") (.fvar "middle"),
        relates (.fvar "middle") (.fvar "target")]
    conclusion := relates (.fvar "source") (.fvar "target") }

def learnedDelta : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments := []
    newRules := [motherRule, fatherRule, chainRule] }

private theorem learned_disjoint :
    learnedDelta.disjointFrom base.1 = true := by
  simp [learnedDelta, CalculusLanguageExtension.disjointFrom, base,
    baseDefinition, relationLanguage, motherRule, fatherRule, chainRule]

private theorem learned_policy :
    learnedDelta.policyHolds base.1
      (.extendsBaseJudgments ["MIL.Rel"]) = true := by
  simp [learnedDelta, CalculusLanguageExtension.policyHolds, base,
    baseDefinition, motherRule, fatherRule, chainRule, relates]

private theorem learned_target_valid :
    (learnedDelta.apply base.1).isValid = true := by
  have hvalidate : (learnedDelta.apply base.1).toLanguageDef.validate = [] := by
    simpa [learnedDelta, CalculusLanguageExtension.apply, base,
      baseDefinition] using relationLanguage_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [learnedDelta, CalculusLanguageExtension.apply, base, baseDefinition,
    relationLanguage, entityConstructor, motherRule, fatherRule, chainRule,
    relates, alice, bob, carol, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid, CalculusLanguageDef.lookupJudgment?,
    RuleSchema.isValidIn, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

def learned : ValidatedCalculusLanguageExtension base where
  extension := learnedDelta
  policy := .extendsBaseJudgments ["MIL.Rel"]
  disjoint := learned_disjoint
  policyHolds := learned_policy
  valid := learned_target_valid

def motherProof : RawProof :=
  .node { ruleId := motherRule.id, arguments := [] } []

def fatherProof : RawProof :=
  .node { ruleId := fatherRule.id, arguments := [] } []

def grandparentProof : RawProof :=
  .node
    { ruleId := chainRule.id
      arguments := [alice, bob, carol] }
    [motherProof, fatherProof]

/-- The generic checker accepts the exact learned chain tree. -/
theorem grandparentProof_checked :
    checkRaw learned.target (relates alice carol) grandparentProof = true := by
  simp [checkRaw, checkRawChildren, grandparentProof, motherProof, fatherProof,
    learned, ValidatedCalculusLanguageExtension.target, learnedDelta,
    CalculusLanguageExtension.apply, base, baseDefinition, motherRule,
    fatherRule, chainRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, relates, alice, bob, carol, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- Exact proof-relevant reconstruction of the accepted learned chain. -/
theorem grandparentProof_has_derivation :
    Nonempty (Derivation learned.target (relates alice carol)) :=
  checkRaw_soundness grandparentProof_checked

/-- Independent relational meaning for the calculus language. -/
inductive Reach : Pattern → Pattern → Prop where
  | mother : Reach alice bob
  | father : Reach bob carol
  | chain {source middle target : Pattern} :
      Reach source middle → Reach middle target → Reach source target

def Meaning : Pattern → Prop
  | .apply "MIL.Rel" [source, target] => Reach source target
  | _ => False

/-- The checked goal has an independently constructed semantic witness. -/
theorem grandparentProof_meaning : Meaning (relates alice carol) :=
  Reach.chain Reach.mother Reach.father

/-- The three proposed rules are independently sound for reachability.  The
base case is vacuous because the base declares the judgment but has no rules;
the learned facts and chain are discharged one schema at a time. -/
def learnedSemantics : SemanticExtension base learned Meaning where
  baseRuleSound := by
    intro ruleInstance premises conclusion application premisesMeaning
    cases application with
    | intro rule lookup =>
        simp [base, baseDefinition, CalculusLanguageDef.lookupRule?] at lookup
  addedRuleSound := by
    intro rule member ruleInstance premises conclusion lookup argumentsValid
      sideConditionsValid premisesInstantiate conclusionInstantiates
      premisesMeaning
    simp only [learned, learnedDelta, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | cons argument arguments =>
          simp [motherRule, argumentsValidAt] at argumentsValid
      | nil =>
          have conclusionResult :=
            instantiateSchemaAt?_complete conclusionInstantiates
          simp [motherRule, instantiateSchemaAt?, instantiateSchemasAt?,
            relates, alice, bob] at conclusionResult
          subst conclusion
          exact Reach.mother
    · rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | cons argument arguments =>
          simp [fatherRule, argumentsValidAt] at argumentsValid
      | nil =>
          have conclusionResult :=
            instantiateSchemaAt?_complete conclusionInstantiates
          simp [fatherRule, instantiateSchemaAt?, instantiateSchemasAt?,
            relates, bob, carol] at conclusionResult
          subst conclusion
          exact Reach.father
    · rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | nil => simp [chainRule, argumentsValidAt] at argumentsValid
      | cons source remaining =>
        cases remaining with
        | nil => simp [chainRule, argumentsValidAt] at argumentsValid
        | cons middle remaining =>
          cases remaining with
          | nil => simp [chainRule, argumentsValidAt] at argumentsValid
          | cons target remaining =>
            cases remaining with
            | cons extra tail =>
                simp [chainRule, argumentsValidAt] at argumentsValid
            | nil =>
                have premisesResult :=
                  instantiateSchemasAt?_complete premisesInstantiate
                have conclusionResult :=
                  instantiateSchemaAt?_complete conclusionInstantiates
                simp [chainRule, instantiateSchemasAt?,
                  instantiateSchemaAt?, lookupArgumentAt?,
                  relates] at premisesResult conclusionResult
                subst premises
                subst conclusion
                exact Reach.chain
                  (premisesMeaning (relates source middle) (by simp [relates]))
                  (premisesMeaning (relates middle target) (by simp [relates]))

/-- The accepted artifact receives its semantics through the general learned-
extension theorem. -/
theorem grandparentProof_sound_via_extension :
    Meaning (relates alice carol) := by
  obtain ⟨derivation⟩ := grandparentProof_has_derivation
  exact learnedSemantics.derivation_sound derivation

/-- Negative control: changing the retained middle occurrence makes the exact
proof tree fail rather than silently selecting another chain. -/
def wrongMiddleProof : RawProof :=
  .node
    { ruleId := chainRule.id
      arguments := [alice, carol, bob] }
    [motherProof, fatherProof]

theorem wrongMiddleProof_rejected :
    checkRaw learned.target (relates alice bob) wrongMiddleProof = false := by
  simp [checkRaw, checkRawChildren, wrongMiddleProof, motherProof, fatherProof,
    learned, ValidatedCalculusLanguageExtension.target, learnedDelta,
    CalculusLanguageExtension.apply, base, baseDefinition, motherRule,
    fatherRule, chainRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, relates, alice, bob, carol, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

#print axioms grandparentProof_checked
#print axioms grandparentProof_has_derivation
#print axioms grandparentProof_meaning
#print axioms grandparentProof_sound_via_extension
#print axioms wrongMiddleProof_rejected

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedChain
