import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenDAG

/-!
# A primitive rule genuinely requiring a composite interpretation

The strict rule-retaining category cannot express every semantics-preserving
translation.  This executable fixture has one source rule `A ⊢ C`, while the
target derives the same step only through `A ⊢ B` followed by `B ⊢ C`.
Consequently no strict arrow exists, but a derivation-valued interpretation
does.  The counterexample makes open proof templates load-bearing rather than
an optional generalization.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.InterpretationCanary

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

def judgmentA : Pattern := .apply "CertificateGSLT-A" []
def judgmentB : Pattern := .apply "CertificateGSLT-B" []
def judgmentC : Pattern := .apply "CertificateGSLT-C" []

private def sourceRule : RuleSchema :=
  { id := ⟨"certificate-gslt-a-c"⟩
    metavariables := []
    premises := [judgmentA]
    conclusion := judgmentC }

private def targetRuleAB : RuleSchema :=
  { id := ⟨"certificate-gslt-a-b"⟩
    metavariables := []
    premises := [judgmentA]
    conclusion := judgmentB }

private def targetRuleBC : RuleSchema :=
  { id := ⟨"certificate-gslt-b-c"⟩
    metavariables := []
    premises := [judgmentB]
    conclusion := judgmentC }

private def targetRuleShare : RuleSchema :=
  { id := ⟨"certificate-gslt-share-b"⟩
    metavariables := []
    premises := [judgmentB, judgmentB]
    conclusion := judgmentC }

private def sourcePresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "certificate-gslt-source")
    { judgments :=
        [{ head := "CertificateGSLT-A", arity := 0 },
         { head := "CertificateGSLT-C", arity := 0 }]
      rules := [sourceRule] }

private def targetPresentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "certificate-gslt-target")
    { judgments :=
        [{ head := "CertificateGSLT-A", arity := 0 },
         { head := "CertificateGSLT-B", arity := 0 },
         { head := "CertificateGSLT-C", arity := 0 }]
      rules := [targetRuleAB, targetRuleBC, targetRuleShare] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem emptyLanguage_terms (name : String) :
    (LanguageDef.empty name).terms = [] :=
  rfl

private theorem sourcePresentation_valid :
    sourcePresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [sourcePresentation, emptyLanguage_validate, emptyLanguage_terms,
    sourceRule, judgmentA, judgmentC,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private theorem targetPresentation_valid :
    targetPresentation.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [targetPresentation, emptyLanguage_validate, emptyLanguage_terms,
    targetRuleAB, targetRuleBC, targetRuleShare,
    judgmentA, judgmentB, judgmentC,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private def sourceValidated : ValidatedCalculusLanguageDef :=
  ⟨sourcePresentation, sourcePresentation_valid⟩

private def targetValidated : ValidatedCalculusLanguageDef :=
  ⟨targetPresentation, targetPresentation_valid⟩

def sourceObject : Object := ⟨sourceValidated⟩
def targetObject : Object := ⟨targetValidated⟩

private def sourceInstance : RuleInstance :=
  ⟨⟨"certificate-gslt-a-c"⟩, []⟩

private def targetInstanceAB : RuleInstance :=
  ⟨⟨"certificate-gslt-a-b"⟩, []⟩

private def targetInstanceBC : RuleInstance :=
  ⟨⟨"certificate-gslt-b-c"⟩, []⟩

private def targetInstanceShare : RuleInstance :=
  ⟨⟨"certificate-gslt-share-b"⟩, []⟩

private theorem source_instantiates :
    instantiateRule? sourceValidated sourceInstance =
      some ([judgmentA], judgmentC) := by
  simp [instantiateRule?, sourceValidated, sourcePresentation, sourceRule,
    sourceInstance, judgmentA, judgmentC, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_ab_instantiates :
    instantiateRule? targetValidated targetInstanceAB =
      some ([judgmentA], judgmentB) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceAB, judgmentA, judgmentB,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_bc_instantiates :
    instantiateRule? targetValidated targetInstanceBC =
      some ([judgmentB], judgmentC) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceBC, judgmentB, judgmentC,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_share_instantiates :
    instantiateRule? targetValidated targetInstanceShare =
      some ([judgmentB, judgmentB], judgmentC) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceShare, judgmentB, judgmentC,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private def targetABOpen :
    OpenDerivation targetValidated [judgmentA] judgmentB :=
  .byRule targetInstanceAB
    (instantiateRule?_eq_some_iff_application.mp target_ab_instantiates)
    (.cons (.assumption ⟨0, by simp⟩) .nil)

private def targetACOpen :
    OpenDerivation targetValidated [judgmentA] judgmentC :=
  .byRule targetInstanceBC
    (instantiateRule?_eq_some_iff_application.mp target_bc_instantiates)
    (.cons targetABOpen .nil)

private theorem source_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication sourceValidated ruleInstance
      premises conclusion) :
    ruleInstance = sourceInstance ∧
      premises = [judgmentA] ∧ conclusion = judgmentC := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [sourceValidated, sourcePresentation, sourceRule,
        CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | cons argument arguments =>
          simp [argumentsValidAt] at argumentsValid
      | nil =>
          have reconstructed :
              RuleApplication sourceValidated sourceInstance
                premises conclusion :=
            .intro sourceRule (by rfl) argumentsValid sideConditions
              premisesInstantiate conclusionInstantiates
          have canonical :
              RuleApplication sourceValidated sourceInstance
                [judgmentA] judgmentC :=
            instantiateRule?_eq_some_iff_application.mp source_instantiates
          have outputs := reconstructed.outputs_unique canonical
          exact ⟨rfl, outputs.1, outputs.2⟩

private theorem target_application_conclusion
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication targetValidated ruleInstance
      premises conclusion) :
    conclusion = judgmentB ∨ conclusion = judgmentC := by
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [targetValidated, targetPresentation, targetRuleAB, targetRuleBC,
        targetRuleShare, CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨_, rfl⟩ | ⟨_, remaining⟩
      · cases conclusionInstantiates with
        | apply items =>
            cases items
            exact Or.inl rfl
      · rcases remaining with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
        · cases conclusionInstantiates with
          | apply items =>
              cases items
              exact Or.inr rfl
        · cases conclusionInstantiates with
          | apply items =>
              cases items
              exact Or.inr rfl

/-! ## An independent two-valued model of the fixture -/

/-- The model makes `B` and `C` true and `A` false.  It is defined directly
on judgments, independently of generated derivability. -/
def semanticMeaning (claim : Pattern) : Prop :=
  claim = judgmentB ∨ claim = judgmentC

/-- The source rule preserves the independent model. -/
theorem source_rules_preserve_semanticMeaning :
    ∀ ruleInstance premises conclusion,
      RuleApplication sourceObject.definition ruleInstance premises
          conclusion →
        (∀ premise, premise ∈ premises → semanticMeaning premise) →
          semanticMeaning conclusion := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication sourceValidated ruleInstance premises conclusion at application
  have shape := source_application_shape ruleInstance application
  rw [shape.2.2]
  exact Or.inr rfl

/-- Every target rule also preserves the same independent model. -/
theorem target_rules_preserve_semanticMeaning :
    ∀ ruleInstance premises conclusion,
      RuleApplication targetObject.definition ruleInstance premises
          conclusion →
        (∀ premise, premise ∈ premises → semanticMeaning premise) →
          semanticMeaning conclusion := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication targetValidated ruleInstance premises conclusion at application
  exact target_application_conclusion ruleInstance application

/-- Positive semantic control: `B` is true in the independent model. -/
theorem judgmentB_has_semanticMeaning : semanticMeaning judgmentB :=
  Or.inl rfl

/-- Negative semantic control: `A` is false in the independent model. -/
theorem judgmentA_lacks_semanticMeaning : ¬ semanticMeaning judgmentA := by
  simp [semanticMeaning, judgmentA, judgmentB, judgmentC]

/-- Interpret the sole source rule by one chosen target implementation.  The
decidable shape test keeps the interpretation computable on concrete rule
applications, so distinct implementations remain provably distinct. -/
private def interpretationTo
    (implementation : OpenDerivation targetValidated [judgmentA] judgmentC) :
    Interpretation sourceObject targetObject where
  onRule := fun ruleInstance {premises} {conclusion} application =>
    if shapes : premises = [judgmentA] ∧ conclusion = judgmentC then by
      rw [shapes.1, shapes.2]
      exact implementation
    else
      absurd
        ⟨(source_application_shape ruleInstance application).2.1,
          (source_application_shape ruleInstance application).2.2⟩
        shapes

/-- Evaluating at the canonical source rule application returns exactly the
chosen implementation. -/
private theorem interpretationTo_onRule_canonical
    (implementation : OpenDerivation targetValidated [judgmentA] judgmentC) :
    (interpretationTo implementation).onRule sourceInstance
        (instantiateRule?_eq_some_iff_application.mp source_instantiates) =
      implementation := by
  rfl

/-- The genuine interpretation replaces the primitive source rule by the
two-node target derivation. -/
def sourceToTarget : Interpretation sourceObject targetObject :=
  interpretationTo targetACOpen

/-- Positive side: a general certificate-GSLT interpretation exists. -/
theorem general_interpretation_exists :
    Nonempty (sourceObject ⟶ targetObject) :=
  ⟨sourceToTarget⟩

/-- Negative side: exact rule retention cannot express the same translation,
because the target intentionally contains no rule under the source identifier. -/
theorem strict_rule_retaining_interpretation_is_empty :
    IsEmpty
      (RuleRetaining.ofDefinition sourceValidated ⟶
        RuleRetaining.ofDefinition targetValidated) := by
  apply RuleRetaining.hom_isEmpty_of_missing
      (ruleId := ⟨"certificate-gslt-a-c"⟩) (rule := sourceRule)
  · rfl
  · rfl

/-- The target implementation is genuinely composite, not a renamed
primitive rule. -/
theorem target_implementation_has_two_rule_nodes :
    targetACOpen.ruleCount = 2 := by
  rfl

private def targetShareOpen :
    OpenDerivation targetValidated [judgmentA] judgmentC :=
  .byRule targetInstanceShare
    (instantiateRule?_eq_some_iff_application.mp target_share_instantiates)
    (.cons targetABOpen (.cons targetABOpen .nil))

/-- A second interpretation of the same primitive rule, through the target
sharing rule; its expanded implementation has three rule nodes. -/
def sourceToTargetShared : Interpretation sourceObject targetObject :=
  interpretationTo targetShareOpen

theorem target_shared_implementation_has_three_rule_nodes :
    targetShareOpen.ruleCount = 3 := by
  rfl

/-- The two parallel interpretations of the same source rule are distinct:
their implementations have different primitive rule counts. -/
theorem parallel_interpretations_distinct :
    sourceToTarget ≠ sourceToTargetShared := by
  intro equal
  have counts := congrArg
    (fun interpretation : Interpretation sourceObject targetObject =>
      (interpretation.onRule sourceInstance
        (instantiateRule?_eq_some_iff_application.mp
          source_instantiates)).ruleCount) equal
  simp only [sourceToTarget, sourceToTargetShared,
    interpretationTo_onRule_canonical] at counts
  exact absurd counts (by decide)

/-- The interpretation category is provably not thin: this hom-type has two
extensionally different inhabitants. -/
theorem interpretation_hom_not_subsingleton :
    ¬ Subsingleton (sourceObject ⟶ targetObject) := fun collapsed =>
  parallel_interpretations_distinct
    (collapsed.allEq sourceToTarget sourceToTargetShared)

/-! ## Sharing-sensitive DAG evidence -/

private def sharedNodeAB : OpenDAGNode :=
  { id := 0
    ruleInstance := targetInstanceAB
    children := [.premise 0] }

private def sharedNodeC : OpenDAGNode :=
  { id := 1
    ruleInstance := targetInstanceShare
    children := [.node 0, .node 0] }

private def sharedBlocks : List (List OpenDAGNode) :=
  [[sharedNodeAB, sharedNodeC]]

private def sharedExpanded : RawOpenProof :=
  .node targetInstanceShare
    [.node targetInstanceAB [.premise 0],
     .node targetInstanceAB [.premise 0]]

/-- One derived `B` node may be cited twice by the target rule. -/
theorem shared_open_dag_accepts :
    checkOpenDAGBlocks targetValidated [judgmentA] judgmentC 1
      sharedBlocks = true := by
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, sharedBlocks, sharedNodeAB,
    sharedNodeC, target_ab_instantiates, target_share_instantiates, judgmentA]

/-- The ghost expansion is exact and visibly duplicates the shared subtree. -/
theorem shared_open_dag_expands_exactly :
    expandOpenDAGBlocks? targetValidated [judgmentA] judgmentC 1
      sharedBlocks = some sharedExpanded := by
  simp [expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    findOpenDAGEntry?, sharedBlocks, sharedNodeAB, sharedNodeC, sharedExpanded,
    target_ab_instantiates, target_share_instantiates, judgmentA]

/-- DAG accounting and expanded-tree accounting are intentionally distinct:
two submitted rule nodes expand to three rule occurrences. -/
theorem sharing_changes_rule_occurrence_count :
    sharedBlocks.flatten.length = 2 ∧ sharedExpanded.ruleCount = 3 := by
  simp [sharedBlocks, sharedExpanded, RawOpenProof.ruleCount]

/-- An out-of-range premise position fails closed. -/
theorem missing_premise_rejects :
    checkOpenDAGBlocks targetValidated [judgmentA] judgmentB 0
      [[{ sharedNodeAB with children := [.premise 1] }]] = false := by
  simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, sharedNodeAB,
    target_ab_instantiates, judgmentA]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.InterpretationCanary
