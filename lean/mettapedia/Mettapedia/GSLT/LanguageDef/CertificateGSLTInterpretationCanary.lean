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

private def judgmentA : Pattern := .apply "CertificateGSLT-A" []
private def judgmentB : Pattern := .apply "CertificateGSLT-B" []
private def judgmentC : Pattern := .apply "CertificateGSLT-C" []

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

private def sourcePresentation : Presentation :=
  { language := LanguageDef.empty "certificate-gslt-source"
    calculus :=
      { judgments :=
          [{ head := "CertificateGSLT-A", arity := 0 },
           { head := "CertificateGSLT-C", arity := 0 }]
        rules := [sourceRule] } }

private def targetPresentation : Presentation :=
  { language := LanguageDef.empty "certificate-gslt-target"
    calculus :=
      { judgments :=
          [{ head := "CertificateGSLT-A", arity := 0 },
           { head := "CertificateGSLT-B", arity := 0 },
           { head := "CertificateGSLT-C", arity := 0 }]
        rules := [targetRuleAB, targetRuleBC, targetRuleShare] } }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem sourcePresentation_valid :
    sourcePresentation.isValidV2 = true := by
  simp [sourcePresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds, emptyLanguage_validate,
    sourceRule, judgmentA, judgmentC, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private theorem targetPresentation_valid :
    targetPresentation.isValidV2 = true := by
  simp [targetPresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds, emptyLanguage_validate,
    targetRuleAB, targetRuleBC, targetRuleShare,
    judgmentA, judgmentB, judgmentC,
    RuleSchema.isValidIn, Presentation.judgmentSchemaValid,
    Presentation.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def sourceValidated : ValidatedPresentation :=
  ⟨sourcePresentation, sourcePresentation_valid⟩

private def targetValidated : ValidatedPresentation :=
  ⟨targetPresentation, targetPresentation_valid⟩

private def sourceObject : Object := ⟨sourceValidated⟩
private def targetObject : Object := ⟨targetValidated⟩

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
    sourceInstance, judgmentA, judgmentC, Presentation.lookupRule?,
    argumentsValidAt, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_ab_instantiates :
    instantiateRule? targetValidated targetInstanceAB =
      some ([judgmentA], judgmentB) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceAB, judgmentA, judgmentB,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_bc_instantiates :
    instantiateRule? targetValidated targetInstanceBC =
      some ([judgmentB], judgmentC) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceBC, judgmentB, judgmentC,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_share_instantiates :
    instantiateRule? targetValidated targetInstanceShare =
      some ([judgmentB, judgmentB], judgmentC) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRuleAB,
    targetRuleBC, targetRuleShare, targetInstanceShare, judgmentB, judgmentC,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchemas?,
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
        Presentation.lookupRule?] at lookup
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
      (RuleRetaining.ofPresentation sourceValidated ⟶
        RuleRetaining.ofPresentation targetValidated) := by
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
