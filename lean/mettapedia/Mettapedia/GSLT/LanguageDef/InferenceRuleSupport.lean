import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Proof-local rule support for the generic inference checker

A fixed raw proof queries a finite collection of rule identifiers, including
all its children. Agreement on their complete lookup results preserves the
actual checker verdict, both success and failure. Unused rules can differ;
agreement on the root rule alone is insufficient.

This is a locality theorem for one existing checker. Each definition still
requires its own validation, and inference-rule meaning remains independent.
The support is a sufficient syntactic manifest, not a least semantic kernel,
a dependency analysis for foreign checkers, or an STT/DTT conservativity
theorem. The instantiation and side-condition algorithms are shared unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceRuleSupport

open Mettapedia.OSLF.MeTTaIL.Syntax
open InferenceChecker

mutual

/-- Every rule name retained by the proof, including repeated occurrences. -/
def ruleSupport : RawProof → List RuleId
  | .node ruleInstance children => ruleInstance.ruleId :: childrenSupport children
termination_by proof => sizeOf proof

def childrenSupport : List RawProof → List RuleId
  | [] => []
  | proof :: proofs => ruleSupport proof ++ childrenSupport proofs
termination_by proofs => sizeOf proofs

end

/-- Exact lookup agreement includes absence and all schema/side-condition
data, not merely the retained rule names. -/
def Agreement (source target : ValidatedCalculusLanguageDef)
    (support : List RuleId) : Prop :=
  ∀ id ∈ support, target.1.lookupRule? id = source.1.lookupRule? id

/-- A finite executable manifest check for this checker's rule dependencies. -/
def agreementCheck (source target : ValidatedCalculusLanguageDef)
    (support : List RuleId) : Bool :=
  support.all fun id => decide (target.1.lookupRule? id = source.1.lookupRule? id)

@[simp] theorem agreementCheck_iff (source target : ValidatedCalculusLanguageDef)
    (support : List RuleId) :
    agreementCheck source target support = true ↔ Agreement source target support := by
  simp [agreementCheck, Agreement]

theorem instantiateRule_eq_of_lookup
    {source target : ValidatedCalculusLanguageDef} (ruleInstance : RuleInstance)
    (agree : target.1.lookupRule? ruleInstance.ruleId = source.1.lookupRule? ruleInstance.ruleId) :
    instantiateRule? target ruleInstance = instantiateRule? source ruleInstance := by
  simp only [instantiateRule?, agree]

mutual

/-- A fixed proof has exactly the same verdict under locally agreeing rule
tables; this covers malformed or unsuccessful proofs as well as successes. -/
theorem checkRaw_eq_of_agreement
    {source target : ValidatedCalculusLanguageDef} (goal : Pattern) (proof : RawProof)
    (agree : Agreement source target (ruleSupport proof)) :
    checkRaw target goal proof = checkRaw source goal proof := by
  cases proof with
  | node ruleInstance children =>
      have localAgreement := instantiateRule_eq_of_lookup ruleInstance
        (agree ruleInstance.ruleId (by simp [ruleSupport]))
      simp only [checkRaw, localAgreement]
      cases instantiateRule? source ruleInstance with
      | none => rfl
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          dsimp only
          rw [checkRawChildren_eq_of_agreement premises children (fun id member =>
            agree id (by simp [ruleSupport, member]))]
termination_by sizeOf proof

theorem checkRawChildren_eq_of_agreement
    {source target : ValidatedCalculusLanguageDef}
    (premises : List Pattern) (proofs : List RawProof)
    (agree : Agreement source target (childrenSupport proofs)) :
    checkRawChildren target premises proofs = checkRawChildren source premises proofs := by
  cases premises with
  | nil => cases proofs <;> simp only [checkRawChildren]
  | cons premise premises =>
      cases proofs with
      | nil => simp only [checkRawChildren]
      | cons proof proofs =>
          simp only [checkRawChildren]
          rw [checkRaw_eq_of_agreement premise proof (fun id member =>
            agree id (by simp [childrenSupport, member]))]
          rw [checkRawChildren_eq_of_agreement premises proofs (fun id member =>
            agree id (by simp [childrenSupport, member]))]
termination_by sizeOf proofs

decreasing_by
  all_goals simp_all <;> omega

end

theorem checkRaw_eq_of_agreementCheck
    {source target : ValidatedCalculusLanguageDef} (goal : Pattern) (proof : RawProof)
    (checked : agreementCheck source target (ruleSupport proof) = true) :
    checkRaw target goal proof = checkRaw source goal proof :=
  checkRaw_eq_of_agreement goal proof ((agreementCheck_iff _ _ _).mp checked)

/-- Local reuse retains the identical raw artifact. No global extension or
claim about every other proof is required. -/
def reuseCheckedProof {source target : ValidatedCalculusLanguageDef} {goal : Pattern}
    (proof : CheckedProof source goal)
    (checked : agreementCheck source target (ruleSupport proof.1) = true) :
    CheckedProof target goal :=
  ⟨proof.1, (checkRaw_eq_of_agreementCheck goal proof.1 checked).trans proof.2⟩

/-- An accepted local manifest transfers a genuine derivation with the same
proof tree, not merely a Boolean assertion of derivability. -/
theorem exists_reused_derivation
    {source target : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation source goal)
    (checked : agreementCheck source target (ruleSupport derivation.erase) = true) :
    ∃ targetDerivation : Derivation target goal,
      targetDerivation.erase = derivation.erase := by
  apply checkRaw_exists_derivation_with_exact_erasure
  exact (checkRaw_eq_of_agreementCheck goal derivation.erase checked).trans
    (checkRaw_erase derivation)

namespace Examples

def seed : RuleSchema where
  id := ⟨"seed"⟩
  metavariables := [("x", 0)]
  premises := []
  conclusion := .apply "Seed" [.fvar "x"]

def lift : RuleSchema where
  id := ⟨"lift"⟩
  metavariables := [("x", 0)]
  premises := [.apply "Seed" [.fvar "x"]]
  conclusion := .apply "Verified" [.fvar "x"]

def unused : RuleSchema where
  id := ⟨"unused"⟩
  metavariables := [("x", 0)]
  premises := []
  conclusion := .apply "Extra" [.fvar "x"]

def definition (rules : List RuleSchema) : CalculusLanguageDef where
  toLanguageDef := LanguageDef.empty "proof-local-support"
  judgments := [⟨"Seed", 1⟩, ⟨"Verified", 1⟩, ⟨"Extra", 1⟩]
  rules := rules

private theorem language_valid :
    (LanguageDef.empty "proof-local-support").validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem definition_valid (rules : List RuleSchema)
    (localRules : rules.all RuleSchema.isLocallyValid = true)
    (shapes : rules.all (RuleSchema.isValidIn (definition rules)) = true)
    (distinct : ((rules.map RuleSchema.id).eraseDups.length ==
      (rules.map RuleSchema.id).length) = true) :
    (definition rules).isValid = true := by
  have judgmentValid : (definition rules).judgmentSignatureValid = true := by
    change (definition []).judgmentSignatureValid = true
    decide
  have conversionValid : (definition rules).conversionDeclarationValid = true := by
    change (definition []).conversionDeclarationValid = true
    decide
  have localValid : (definition rules).hasValidLocalRules = true := by
    simp only [CalculusLanguageDef.hasValidLocalRules,
      show (definition rules).toLanguageDef = LanguageDef.empty "proof-local-support" from rfl,
      language_valid]
    change ((true && rules.all RuleSchema.isLocallyValid) &&
      ((rules.map RuleSchema.id).eraseDups.length ==
        (rules.map RuleSchema.id).length)) = true
    rw [localRules, distinct]
    rfl
  simp only [CalculusLanguageDef.isValid, localValid, judgmentValid, conversionValid,
    show (definition rules).rules = rules from rfl, shapes, Bool.and_self]

private theorem selectedDefinitions_valid :
    (definition [seed, lift, unused]).isValid = true ∧
      (definition [seed, lift]).isValid = true ∧
      (definition [lift]).isValid = true := by
  constructor
  · apply definition_valid
    all_goals
      simp [definition, seed, lift, unused, RuleSchema.isLocallyValid,
        RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
        RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
        CalculusLanguageDef.lookupJudgment?, patternMetavariableOccurrencesAt,
        patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
        patternsHaveNoCollectionRest, fixedConstructorsValid, fixedConstructorListsValid,
        Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      decide
  · constructor <;> apply definition_valid
    all_goals
      simp [definition, seed, lift, RuleSchema.isLocallyValid,
        RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
        RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
        CalculusLanguageDef.lookupJudgment?, patternMetavariableOccurrencesAt,
        patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
        patternsHaveNoCollectionRest, fixedConstructorsValid, fixedConstructorListsValid,
        Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      decide

def full : ValidatedCalculusLanguageDef :=
  ⟨definition [seed, lift, unused], selectedDefinitions_valid.1⟩
def selected : ValidatedCalculusLanguageDef :=
  ⟨definition [seed, lift], selectedDefinitions_valid.2.1⟩
def missingChild : ValidatedCalculusLanguageDef :=
  ⟨definition [lift], selectedDefinitions_valid.2.2⟩

def value : Pattern := .apply "Value" []
def goal : Pattern := .apply "Verified" [value]
def proof : RawProof := .node ⟨lift.id, [value]⟩ [.node ⟨seed.id, [value]⟩ []]

theorem support_includes_child : ruleSupport proof = [lift.id, seed.id] := by
  simp [ruleSupport, childrenSupport, proof]

/-- An unused capability can actually be removed while retaining the proof. -/
theorem smaller_table_reuses_proof :
    agreementCheck full selected (ruleSupport proof) = true ∧
      checkRaw full goal proof = true ∧ checkRaw selected goal proof = true := by
  rw [support_includes_child]
  simp [agreementCheck, checkRaw, checkRawChildren,
    proof, full, selected, definition, seed, lift, unused, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, value, goal, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-- The table is genuinely smaller: it is not a global lookup extension. -/
theorem smaller_is_not_global_extension : ¬ RuleLookupRefines full selected := by
  apply not_ruleLookupRefines_of_missing (ruleId := unused.id) (rule := unused)
  · rfl
  · rfl

/-- Keeping the conclusion and root rule cannot conceal a missing premise
rule. The original proof succeeds and the truncated profile rejects it. -/
theorem root_agreement_does_not_suffice :
    missingChild.1.lookupRule? lift.id = full.1.lookupRule? lift.id ∧
      checkRaw full goal proof = true ∧ checkRaw missingChild goal proof = false ∧
      agreementCheck full missingChild (ruleSupport proof) = false := by
  rw [support_includes_child]
  simp [agreementCheck, checkRaw, checkRawChildren,
    proof, full, missingChild, definition, seed, lift, unused, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, value, goal, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

end Examples

#print axioms checkRaw_eq_of_agreement
#print axioms checkRaw_eq_of_agreementCheck
#print axioms reuseCheckedProof
#print axioms exists_reused_derivation
#print axioms Examples.smaller_table_reuses_proof
#print axioms Examples.smaller_is_not_global_extension
#print axioms Examples.root_agreement_does_not_suffice

end Mettapedia.GSLT.LanguageDef.InferenceRuleSupport
