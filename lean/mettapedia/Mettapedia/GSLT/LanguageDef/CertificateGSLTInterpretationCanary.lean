import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenDAG
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOccurrencePreservingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalInterpretation
import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

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

open _root_.CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

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

/-- The two-step implementation of the source rule uses its single premise
exactly once, so this interpretation preserves every open proof's ordered
premise-use ledger. -/
theorem sourceToTarget_preservesOrderedPremises :
    sourceToTarget.PreservesOrderedPremises := by
  intro ruleInstance premises conclusion application
  obtain ⟨rfl, rfl, rfl⟩ :=
    source_application_shape ruleInstance application
  change OpenSearchMachine.holeOccurrences targetACOpen =
    List.finRange 1
  rfl

/-- The sharing interpretation is valid as a proof translation but not as
an ordered-linear resource translation: its one source premise is used twice. -/
theorem sourceToTargetShared_not_preservesOrderedPremises :
    ¬ sourceToTargetShared.PreservesOrderedPremises := by
  intro linear
  have uses := linear sourceInstance
    (instantiateRule?_eq_some_iff_application.mp source_instantiates)
  have lengths := congrArg List.length uses
  change (2 : Nat) = 1 at lengths
  omega

/-- The non-primitive, two-step target implementation preserves the exact
ordered premise-use ledger for every source open derivation. -/
theorem sourceToTarget_preserves_all_open_occurrences
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation sourceValidated context goal) :
    OpenSearchMachine.holeOccurrences
        (sourceToTarget.mapOpen derivation) =
      OpenSearchMachine.holeOccurrences derivation :=
  Interpretation.holeOccurrences_mapOpen sourceToTarget
    sourceToTarget_preservesOrderedPremises derivation

theorem target_shared_implementation_has_three_rule_nodes :
    targetShareOpen.ruleCount = 3 := by
  rfl

/-! ## The same translation viewed as operational proof search -/

/-- The primitive source rule performs one backward-search step. -/
theorem source_operational_step :
    (proofSearchGSLT sourceValidated).Step [judgmentC] [judgmentA] := by
  apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
  exact ⟨sourceInstance, [judgmentA], judgmentC, [],
    source_instantiates, rfl, rfl⟩

/-- The target implements the source transition through the intermediate
`B` obligation, preserving its actual two-step operational route. -/
theorem target_operational_two_steps :
    (proofSearchGSLT targetValidated).MultiStep [judgmentC] [judgmentA] := by
  have first : (proofSearchGSLT targetValidated).Step
      [judgmentC] [judgmentB] := by
    apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
    exact ⟨targetInstanceBC, [judgmentB], judgmentC, [],
      target_bc_instantiates, rfl, rfl⟩
  have second : (proofSearchGSLT targetValidated).Step
      [judgmentB] [judgmentA] := by
    apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
    exact ⟨targetInstanceAB, [judgmentA], judgmentB, [],
      target_ab_instantiates, rfl, rfl⟩
  exact .step first (.step second
    (@Mettapedia.GSLT.GSLT.MultiStep.refl
      (proofSearchGSLT targetValidated) [judgmentA]))

/-- The target has no primitive `C`-to-`A` transition. Its two-step
implementation is not a falsely renamed one-step rule. -/
theorem target_no_direct_operational_step :
    ¬ (proofSearchGSLT targetValidated).Step [judgmentC] [judgmentA] := by
  intro step
  obtain ⟨ruleInstance, premises, conclusion, rest,
      instantiated, sourceShape, targetShape⟩ :=
    (proofSearchGSLT_step_iff_instantiation _ _ _).mp step
  cases rest with
  | cons head tail => simp at sourceShape
  | nil =>
      have conclusionShape : conclusion = judgmentC := by
        simpa using sourceShape.symm
      have premisesShape : premises = [judgmentA] := by
        simpa using targetShape.symm
      subst conclusion
      subst premises
      rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
      by_cases ab : ruleId = "certificate-gslt-a-b"
      · subst ruleId
        simp [instantiateRule?, targetValidated, targetPresentation,
          targetRuleAB, targetRuleBC, targetRuleShare,
          CalculusLanguageDef.lookupRule?,
          judgmentA, judgmentB, judgmentC] at instantiated
        have noArguments : arguments = [] := by
          have size := argumentsValidAt_length instantiated.1
          exact List.length_eq_zero_iff.mp size.symm
        subst arguments
        simp [argumentsValidAt, instantiateSchemasAt?, instantiateSchemaAt?,
          instantiateSchemas?, instantiateSchema?] at instantiated
      by_cases bc : ruleId = "certificate-gslt-b-c"
      · subst ruleId
        simp [instantiateRule?, targetValidated, targetPresentation,
          targetRuleAB, targetRuleBC, targetRuleShare,
          CalculusLanguageDef.lookupRule?,
          judgmentA, judgmentB, judgmentC] at instantiated
        have noArguments : arguments = [] := by
          have size := argumentsValidAt_length instantiated.1
          exact List.length_eq_zero_iff.mp size.symm
        subst arguments
        simp [argumentsValidAt, instantiateSchemasAt?, instantiateSchemaAt?,
          instantiateSchemas?, instantiateSchema?] at instantiated
      by_cases shared : ruleId = "certificate-gslt-share-b"
      · subst ruleId
        simp [instantiateRule?, targetValidated, targetPresentation,
          targetRuleAB, targetRuleBC, targetRuleShare,
          CalculusLanguageDef.lookupRule?,
          judgmentA, judgmentB, judgmentC] at instantiated
        have noArguments : arguments = [] := by
          have size := argumentsValidAt_length instantiated.1
          exact List.length_eq_zero_iff.mp size.symm
        subst arguments
        simp [argumentsValidAt, instantiateSchemasAt?, instantiateSchemaAt?,
          instantiateSchemas?, instantiateSchema?] at instantiated
      simp [instantiateRule?, targetValidated, targetPresentation,
        targetRuleAB, targetRuleBC, targetRuleShare,
        CalculusLanguageDef.lookupRule?, List.find?, eq_comm,
        ab, bc, shared] at instantiated

/-- The ordinary head-only proof-search GSLT cannot advance once an
unresolved open assumption `A` reaches the head. It cannot then process
another pending goal behind that assumption. -/
theorem target_head_assumption_blocks
    (suffix targetGoals : List Pattern) :
    ¬ (proofSearchGSLT targetValidated).Step
      (judgmentA :: suffix) targetGoals := by
  intro step
  obtain ⟨ruleInstance, premises, conclusion, rest,
      instantiated, sourceShape, _⟩ :=
    (proofSearchGSLT_step_iff_instantiation _ _ _).mp step
  have application : RuleApplication targetValidated ruleInstance
      premises conclusion :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  have conclusionIsA : conclusion = judgmentA :=
    (List.cons.inj sourceShape).1.symm
  rcases target_application_conclusion ruleInstance application with
    conclusionIsB | conclusionIsC
  · have impossible := conclusionIsA.symm.trans conclusionIsB
    simp [judgmentA, judgmentB] at impossible
  · have impossible := conclusionIsA.symm.trans conclusionIsC
    simp [judgmentA, judgmentC] at impossible

/-- Once the first branch leaves an open `A`, the old head-only search
cannot continue to process the second `B` and produce two `A` leaves.
The open-search machine's discharged-occurrence register is necessary. -/
theorem headOnly_cannot_resume_after_assumption :
    ¬ (proofSearchGSLT targetValidated).MultiStep
      [judgmentA, judgmentB] [judgmentA, judgmentA] := by
  intro route
  let motive : ∀ first last,
      (proofSearchGSLT targetValidated).MultiStep first last → Prop :=
    fun first last _ => first = [judgmentA, judgmentB] →
      last = [judgmentA, judgmentB]
  have onlySelf : motive [judgmentA, judgmentB]
      [judgmentA, judgmentA] route :=
    Mettapedia.GSLT.GSLT.MultiStep.rec (motive := motive)
      (fun _ equal => equal)
      (fun first _ _ equal =>
        False.elim (target_head_assumption_blocks [judgmentB] _
          (equal ▸ first))) route
  have same := onlySelf rfl
  have different : judgmentA = judgmentB :=
    (List.cons.inj (List.cons.inj same).2).1
  simp [judgmentA, judgmentB] at different

/-- The source's sole rule determines the exact head transition; a proof of
`Step` itself does not retain the rule instance as computational data. -/
private theorem source_operational_step_shape
    {sourceTerm targetTerm : List Pattern}
    (step : (proofSearchGSLT sourceValidated).Step sourceTerm targetTerm) :
    ∃ rest, sourceTerm = judgmentC :: rest ∧
      targetTerm = judgmentA :: rest := by
  obtain ⟨ruleInstance, premises, conclusion, rest,
      instantiated, sourceShape, targetShape⟩ :=
    (proofSearchGSLT_step_iff_instantiation _ _ _).mp step
  have application : RuleApplication sourceValidated ruleInstance
      premises conclusion :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  obtain ⟨_, premisesShape, conclusionShape⟩ :=
    source_application_shape ruleInstance application
  exact ⟨rest, by simpa [conclusionShape] using sourceShape,
    by simpa [premisesShape] using targetShape⟩

/-- With the untouched suffix given as data, the target route is an exact
two-edge execution, not merely a proposition asserting reachability. -/
def targetOperationalRoute (rest : List Pattern) :
    ExecutionPath (proofSearchGSLT targetValidated)
      (judgmentC :: rest) (judgmentA :: rest) := by
  have first : (proofSearchGSLT targetValidated).Step
      (judgmentC :: rest) (judgmentB :: rest) := by
    apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
    exact ⟨targetInstanceBC, [judgmentB], judgmentC, rest,
      target_bc_instantiates, rfl, rfl⟩
  have second : (proofSearchGSLT targetValidated).Step
      (judgmentB :: rest) (judgmentA :: rest) := by
    apply (proofSearchGSLT_step_iff_instantiation _ _ _).mpr
    exact ⟨targetInstanceAB, [judgmentA], judgmentB, rest,
      target_ab_instantiates, rfl, rfl⟩
  exact .cons ⟨first⟩ (.cons ⟨second⟩ (.refl _))

@[simp] theorem targetOperationalRoute_length (rest : List Pattern) :
    (targetOperationalRoute rest).length = 2 := by
  rfl

/-- With the source rule instance and untouched suffix retained as data,
the lowering to a target execution path is constructive. Only the later
wrapper from bare `GSLT.Step` needs choice. -/
def certifiedSourceStepRoute
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) (rest : List Pattern)
    (instantiated : instantiateRule? sourceValidated ruleInstance =
      some (premises, conclusion)) :
    { path : ExecutionPath (proofSearchGSLT targetValidated)
        (conclusion :: rest) (premises ++ rest) // path.length = 2 } := by
  have application : RuleApplication sourceValidated ruleInstance
      premises conclusion :=
    instantiateRule?_eq_some_iff_application.mp instantiated
  obtain ⟨_, premisesShape, conclusionShape⟩ :=
    source_application_shape ruleInstance application
  subst premises
  subst conclusion
  exact ⟨targetOperationalRoute rest, targetOperationalRoute_length rest⟩

@[simp] theorem certifiedSourceStepRoute_length
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) (rest : List Pattern)
    (instantiated : instantiateRule? sourceValidated ruleInstance =
      some (premises, conclusion)) :
    (certifiedSourceStepRoute ruleInstance premises conclusion rest
      instantiated).val.length = 2 :=
  (certifiedSourceStepRoute ruleInstance premises conclusion rest
    instantiated).property

/-- A Prop-valued source `Step` can supply the suffix only through choice
when asked for a Type-valued execution. The chosen path carries its exact
length as part of the returned data. An executable compiler instead needs
the retained rule-instance certificate. -/
private noncomputable def chosenTargetPath
    {sourceTerm targetTerm : List Pattern}
    (step : (proofSearchGSLT sourceValidated).Step sourceTerm targetTerm) :
    { path : ExecutionPath (proofSearchGSLT targetValidated)
        sourceTerm targetTerm // path.length = 2 } :=
  Classical.choice (by
    obtain ⟨ruleInstance, premises, conclusion, rest,
        instantiated, sourceShape, targetShape⟩ :=
      (proofSearchGSLT_step_iff_instantiation _ _ _).mp step
    subst sourceTerm
    subst targetTerm
    exact ⟨certifiedSourceStepRoute ruleInstance premises conclusion rest
      instantiated⟩)

/-- The path-valued operational companion works for every source step and
arbitrary trailing goals. It is noncomputable because the generic GSLT step
relation hides its rule-instance witness in `Prop`, unlike the explicit
`targetOperationalRoute` above. -/
noncomputable def sourceToTargetOperational :
    OperationalRealization (proofSearchGSLT sourceValidated)
      (proofSearchGSLT targetValidated) where
  mapTerm := id
  mapEquiv := by
    intro left right equivalent
    exact equivalent
  mapStep := fun step => (chosenTargetPath step).val

/-- Every simulated source step expands to exactly two retained operational
edges in this fixture. The length is data in the path, unlike `MultiStep`. -/
theorem sourceToTargetOperational_step_length
    {sourceTerm targetTerm : List Pattern}
    (step : (proofSearchGSLT sourceValidated).Step sourceTerm targetTerm) :
    (sourceToTargetOperational.mapStep step).length = 2 := by
  exact (chosenTargetPath step).property

/-- At the primitive target-step scale, the OSLF exact-target diamond does
not claim the simulated `C`-to-`A` transition. -/
theorem primitive_target_modal_rejects_direct :
    ¬ (gsltOSLF (proofSearchGSLT targetValidated)).satisfies
        [judgmentC]
        (exactTargetNativeType (proofSearchGSLT targetValidated)
          [judgmentA]).pred := by
  intro observed
  exact target_no_direct_operational_step
    ((satisfies_exactTargetNativeType_iff_step _ _ _).mp observed)

/-- At the finite-path macro-step scale, the same source transition does
inhabit the target closure's OSLF exact-target diamond. The two modalities
therefore have intentionally different observations. -/
theorem closure_target_modal_accepts_macro_step :
    (gsltOSLF (proofSearchGSLT targetValidated).closure).satisfies
      [judgmentC]
      (exactTargetNativeType (proofSearchGSLT targetValidated).closure
        [judgmentA]).pred := by
  apply (satisfies_exactTargetNativeType_iff_step _ _ _).mpr
  exact sourceToTargetOperational.toClosureTranslation.mapStep
    source_operational_step

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

/-! ## The proof-bearing presheaf on this concrete interpretation -/

private def sourceACOpen :
    OpenDerivation sourceValidated [judgmentA] judgmentC :=
  .byRule sourceInstance
    (instantiateRule?_eq_some_iff_application.mp source_instantiates)
    (.cons (.assumption ⟨0, by simp⟩) .nil)

/-- The source has no rule concluding `B`, and its only context assumption
is `A`. This independent predicate gives a negative derivability control. -/
theorem source_B_open_empty :
    IsEmpty (OpenDerivation sourceValidated [judgmentA] judgmentB) := by
  refine ⟨fun derivation => ?_⟩
  have avoidsB : judgmentB ≠ judgmentB :=
    OpenDerivation.sound_of_ruleApplications
      (definition := sourceValidated) (context := [judgmentA])
      (fun claim => claim ≠ judgmentB)
      (by
        intro ruleInstance premises conclusion application _
        have shape := source_application_shape ruleInstance application
        rw [shape.2.2]
        simp [judgmentB, judgmentC])
      (by
        intro premise member
        simp only [List.mem_singleton] at member
        subst premise
        simp [judgmentA, judgmentB])
      derivation
  exact avoidsB rfl

/-- The first interpretation computes the exact two-node target proof, not
merely another derivation of the same goal. -/
theorem sourceToTarget_mapOpen_sourceAC :
    sourceToTarget.mapOpen sourceACOpen = targetACOpen := by
  simp only [sourceACOpen, Interpretation.mapOpen,
    sourceToTarget, interpretationTo_onRule_canonical]
  exact OpenDerivation.bind_assumptionEnvironment targetACOpen

/-- The other interpretation computes the shared implementation exactly. -/
theorem sourceToTargetShared_mapOpen_sourceAC :
    sourceToTargetShared.mapOpen sourceACOpen = targetShareOpen := by
  simp only [sourceACOpen, Interpretation.mapOpen,
    sourceToTargetShared, interpretationTo_onRule_canonical]
  exact OpenDerivation.bind_assumptionEnvironment targetShareOpen

/-- A valid proof-term interpretation need not preserve premise-use
multiplicity. Both target proofs discharge the same source position, but the
sharing implementation uses it twice. -/
theorem parallel_interpretations_change_discharge_ledger :
    OpenSearchMachine.holeOccurrences
        (sourceToTarget.mapOpen sourceACOpen) ≠
      OpenSearchMachine.holeOccurrences
        (sourceToTargetShared.mapOpen sourceACOpen) := by
  rw [sourceToTarget_mapOpen_sourceAC,
    sourceToTargetShared_mapOpen_sourceAC]
  intro same
  have counts := congrArg List.length same
  change (1 : Nat) = 2 at counts
  omega

/-- The open-search machine retains the source rule and its one ordered
premise-discharge event. -/
theorem source_open_search_has_two_events :
    (OpenSearchMachine.runToCompletion sourceACOpen).length = 2 := by
  rfl

/-- The source proof exists at the exact one-use ledger in the closure
modality, but no single primitive search event reaches that completed state. -/
theorem source_modal_completion_is_not_primitive :
    gsltDiamond
        (OpenSearchModalAdequacy.theory sourceValidated [judgmentA]).closure
        (fun candidate => candidate =
          (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA]))
        ⟨[judgmentC], []⟩ ∧
      ¬ gsltDiamond
        (OpenSearchModalAdequacy.theory sourceValidated [judgmentA])
        (fun candidate => candidate =
          (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA]))
        ⟨[judgmentC], []⟩ := by
  constructor
  · apply (OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
      sourceValidated [judgmentA] judgmentC [(0 : Fin 1)]).mp
    exact ⟨⟨sourceACOpen, rfl⟩⟩
  · intro primitive
    have step := (gsltDiamond_singleton_iff_step
      (OpenSearchModalAdequacy.theory sourceValidated [judgmentA])
      (⟨[judgmentC], []⟩ : OpenSearchMachine.State [judgmentA])
      (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA])).mp
      primitive
    exact OpenSearchModalAdequacy.primitiveCannotCompleteUnmatchedGoal
      sourceValidated [judgmentA] judgmentC [(0 : Fin 1)]
      (by simp [judgmentA, judgmentC]) (by simp) step

/-- The ordered-linear, two-step rule interpretation carries the exact
one-use source completion to a target closure-modal completion. -/
theorem target_modal_from_linear_source :
    gsltDiamond
        (OpenSearchModalAdequacy.theory targetValidated [judgmentA]).closure
        (fun candidate => candidate =
          (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA]))
        ⟨[judgmentC], []⟩ :=
  Interpretation.preservesExactCompletionDiamond sourceToTarget
    sourceToTarget_preservesOrderedPremises
    [judgmentA] judgmentC [(0 : Fin 1)]
    source_modal_completion_is_not_primitive.1

/-- The forward modal transport is not a reflection: the target's extra
`A ⊢ B` rule supplies an exact one-use completion absent from the source. -/
theorem target_B_modal_not_reflected :
    gsltDiamond
        (OpenSearchModalAdequacy.theory targetValidated [judgmentA]).closure
        (fun candidate => candidate =
          (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA]))
        ⟨[judgmentB], []⟩ ∧
      ¬ gsltDiamond
        (OpenSearchModalAdequacy.theory sourceValidated [judgmentA]).closure
        (fun candidate => candidate =
          (⟨[], [(0 : Fin 1)]⟩ : OpenSearchMachine.State [judgmentA]))
        ⟨[judgmentB], []⟩ := by
  constructor
  · apply (OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
      targetValidated [judgmentA] judgmentB [(0 : Fin 1)]).mp
    exact ⟨⟨targetABOpen, rfl⟩⟩
  · intro sourceReachable
    obtain ⟨⟨derivation, _⟩⟩ :=
      (OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
        sourceValidated [judgmentA] judgmentB [(0 : Fin 1)]).mpr
        sourceReachable
    exact source_B_open_empty.false derivation

/-- The two-node target implementation adds one operational rule event
while retaining the same single premise discharge. -/
theorem target_open_search_has_three_events :
    (OpenSearchMachine.runToCompletion targetACOpen).length = 3 := by
  rfl

/-- The generic ordered-linear compiler produces the same concrete
three-event target execution from the certified source proof. -/
theorem linear_target_route_has_three_events :
    (sourceToTarget.runTranslated sourceToTarget_preservesOrderedPremises
      sourceACOpen).length = 3 := by
  rfl

/-- Sharing one premise in the target DAG yields two distinct discharge
events in the expanded open derivation, not a single erased occurrence. -/
theorem shared_open_search_has_five_events :
    (OpenSearchMachine.runToCompletion targetShareOpen).length = 5 := by
  rfl

theorem shared_open_search_discharge_count :
    (OpenSearchMachine.holeOccurrences targetShareOpen).length = 2 := by
  rfl

/-- The generic displayed theory translation is exercised by the source
rule whose target implementation has two nodes. -/
theorem displayed_translation_has_two_rule_nodes :
    ((sourceToTarget.derivationTotalMap).app
      (Opposite.op (⟨[judgmentA]⟩ : ClassifyingContext sourceValidated))
      ⟨judgmentC, sourceACOpen⟩).2.ruleCount = 2 := by
  change (sourceToTarget.mapOpen sourceACOpen).ruleCount = 2
  simp only [sourceACOpen, Interpretation.mapOpen,
    sourceToTarget, interpretationTo_onRule_canonical]
  change (targetACOpen.bind
    (assumptionEnvironment targetValidated [judgmentA])).ruleCount = 2
  rw [OpenDerivation.bind_assumptionEnvironment]
  exact target_implementation_has_two_rule_nodes

/-- A different declared interpretation keeps the goal while recording a
different, three-node proof implementation. The displayed map does not
collapse these intensional routes to their common conclusion. -/
theorem displayed_shared_translation_has_three_rule_nodes :
    ((sourceToTargetShared.derivationTotalMap).app
      (Opposite.op (⟨[judgmentA]⟩ : ClassifyingContext sourceValidated))
      ⟨judgmentC, sourceACOpen⟩).2.ruleCount = 3 := by
  change (sourceToTargetShared.mapOpen sourceACOpen).ruleCount = 3
  simp only [sourceACOpen, Interpretation.mapOpen,
    sourceToTargetShared, interpretationTo_onRule_canonical]
  change (targetShareOpen.bind
    (assumptionEnvironment targetValidated [judgmentA])).ruleCount = 3
  rw [OpenDerivation.bind_assumptionEnvironment]
  exact target_shared_implementation_has_three_rule_nodes

/-- The same source proof and goal have two distinct translated evidence
objects. Forgetting to the goal identifies them; the total presheaf does not. -/
theorem displayed_parallel_translations_distinct :
    (sourceToTarget.derivationTotalMap).app
        (Opposite.op (⟨[judgmentA]⟩ : ClassifyingContext sourceValidated))
        ⟨judgmentC, sourceACOpen⟩ ≠
      (sourceToTargetShared.derivationTotalMap).app
        (Opposite.op (⟨[judgmentA]⟩ : ClassifyingContext sourceValidated))
        ⟨judgmentC, sourceACOpen⟩ := by
  intro equal
  have counts := congrArg
    (fun answer : (derivationTotalFace targetValidated).obj
      (Opposite.op (⟨[judgmentA]⟩ : ClassifyingContext targetValidated)) =>
      answer.2.ruleCount) equal
  have firstCount := displayed_translation_has_two_rule_nodes
  have secondCount := displayed_shared_translation_has_three_rule_nodes
  change (sourceToTarget.mapOpen sourceACOpen).ruleCount =
    (sourceToTargetShared.mapOpen sourceACOpen).ruleCount at counts
  change (sourceToTarget.mapOpen sourceACOpen).ruleCount = 2 at firstCount
  change (sourceToTargetShared.mapOpen sourceACOpen).ruleCount = 3 at secondCount
  omega

private def sourceDerivationPoint :
    (derivationFamily sourceValidated).Elements :=
  derivationPoint sourceValidated ⟨[judgmentA]⟩ judgmentC sourceACOpen

/-- The translated canonical dependent variable reads the actual two-node
proof, not a freshly searched proof of the same goal. -/
theorem translated_last_variable_has_two_nodes :
    ((_root_.Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension.lastVariable
      (derivationFamily targetValidated)).1
      (sourceToTarget.derivationComprehensionFunctor.obj
        sourceDerivationPoint)).ruleCount = 2 := by
  change (sourceToTarget.mapOpen sourceACOpen).ruleCount = 2
  exact displayed_translation_has_two_rule_nodes

/-- Choosing the other declared interpretation changes the retained
dependent variable's proof route while leaving its goal observation fixed. -/
theorem translated_shared_last_variable_has_three_nodes :
    ((_root_.Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension.lastVariable
      (derivationFamily targetValidated)).1
      (sourceToTargetShared.derivationComprehensionFunctor.obj
        sourceDerivationPoint)).ruleCount = 3 := by
  change (sourceToTargetShared.mapOpen sourceACOpen).ruleCount = 3
  exact displayed_shared_translation_has_three_rule_nodes

#print axioms source_operational_step
#print axioms target_operational_two_steps
#print axioms target_no_direct_operational_step
#print axioms headOnly_cannot_resume_after_assumption
#print axioms targetOperationalRoute_length
#print axioms certifiedSourceStepRoute_length
#print axioms sourceToTargetOperational_step_length
#print axioms primitive_target_modal_rejects_direct
#print axioms closure_target_modal_accepts_macro_step
#print axioms translated_last_variable_has_two_nodes
#print axioms translated_shared_last_variable_has_three_nodes
#print axioms source_open_search_has_two_events
#print axioms source_modal_completion_is_not_primitive
#print axioms target_modal_from_linear_source
#print axioms source_B_open_empty
#print axioms target_B_modal_not_reflected
#print axioms target_open_search_has_three_events
#print axioms linear_target_route_has_three_events
#print axioms shared_open_search_has_five_events
#print axioms shared_open_search_discharge_count
#print axioms sourceToTarget_preservesOrderedPremises
#print axioms sourceToTargetShared_not_preservesOrderedPremises
#print axioms sourceToTarget_preserves_all_open_occurrences

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.InterpretationCanary
