import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.CompiledPlanLowering

/-!
# Lowering admitted calculus languages to compiled plans

This module connects the generic calculus-language authority to the exact
compiled finite-Horn carrier.  The admitted fragment is discovered locally:

* rule schemas satisfy the ordinary V1 binding checks;
* every metavariable occurs at depth zero;
* conclusions and premises contain applications and free metavariables only;
* rule side conditions are absent; and
* names and physical variable counts fit the compiled carrier.

Unsupported binder, substitution, collection, and side-condition forms fail
closed.  They remain valid calculus languages and may be handled by a
richer generated machine; they are not silently assigned finite-Horn meaning.

The final theorem composes this recognizer with independent translation
validation and exact `CGP1` admission: every emitted packet reconstructs the
meaning obtained from the admitted source definition.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering

open Mettapedia.OSLF.MeTTaIL.Syntax
open InferenceChecker
open CompiledPlanWireFormat
open CompiledPlanAdmission
open CompiledPlanLowering

def stringBytes (value : String) : List UInt8 :=
  value.toList.flatMap String.utf8EncodeChar

theorem stringBytes_toByteArray (value : String) :
    (stringBytes value).toByteArray = value.toUTF8 := by
  simpa [stringBytes, List.utf8Encode, String.toUTF8_eq_toByteArray] using
    (String.utf8Encode_toList (b := value))

def physicalName? (value : String) : Option (List UInt8) :=
  let bytes := stringBytes value
  if bytesNonempty bytes && textEncodable? bytes then some bytes else none

/-- Resolve one authored metavariable name to its declared physical slot.
`RuleSchema.isLocallyValid` supplies uniqueness; this function additionally checks
the depth-zero and `UInt32` boundaries of the finite-Horn realization. -/
def variableSlot? (formals : List (String × Nat))
    (name : String) : Option UInt32 := do
  let index <- formals.findIdx? (fun formal => decide (formal.1 = name))
  if index < UInt32.size then
    match formals[index]? with
    | some (_, 0) => some (UInt32.ofNat index)
    | _ => none
  else
    none

mutual

def lowerPattern? (formals : List (String × Nat)) :
    Pattern → Option Term
  | .fvar name => do
      let slot <- variableSlot? formals name
      some (.variable slot)
  | .apply head arguments => do
      let headBytes <- physicalName? head
      let lowered <- lowerPatterns? formals arguments
      some (.application headBytes (Terms.ofList lowered))
  | .bvar _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ |
      .collection _ _ _ => none
termination_by pattern => sizeOf pattern

def lowerPatterns? (formals : List (String × Nat)) :
    List Pattern → Option (List Term)
  | [] => some []
  | pattern :: patterns => do
      let head <- lowerPattern? formals pattern
      let tail <- lowerPatterns? formals patterns
      some (head :: tail)
termination_by patterns => sizeOf patterns

end

mutual

/-- Source-shape support for a compiled term without retaining the lowered
payload. -/
def patternSupported (formals : List (String × Nat)) : Pattern → Bool
  | .fvar name => (variableSlot? formals name).isSome
  | .apply head arguments =>
      (physicalName? head).isSome && patternsSupported formals arguments
  | .bvar _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ |
      .collection _ _ _ => false
termination_by pattern => sizeOf pattern

def patternsSupported (formals : List (String × Nat)) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      patternSupported formals pattern && patternsSupported formals patterns
termination_by patterns => sizeOf patterns

end

mutual

theorem lowerPattern?_isSome (formals : List (String × Nat)) :
    ∀ pattern,
      (lowerPattern? formals pattern).isSome =
        patternSupported formals pattern := by
  intro pattern
  cases pattern with
  | bvar index => simp [lowerPattern?, patternSupported]
  | fvar name =>
      cases slot : variableSlot? formals name <;>
        simp [lowerPattern?, patternSupported, slot]
  | apply head arguments =>
      cases name : physicalName? head with
      | none => simp [lowerPattern?, patternSupported, name]
      | some bytes =>
          cases argumentsResult : lowerPatterns? formals arguments <;>
            simpa [lowerPattern?, patternSupported, name, argumentsResult]
              using lowerPatterns?_isSome formals arguments
  | lambda binder body => simp [lowerPattern?, patternSupported]
  | multiLambda arity binders body => simp [lowerPattern?, patternSupported]
  | subst body replacement => simp [lowerPattern?, patternSupported]
  | collection collectionType elements rest =>
      simp [lowerPattern?, patternSupported]
termination_by pattern => sizeOf pattern

theorem lowerPatterns?_isSome (formals : List (String × Nat)) :
    ∀ patterns,
      (lowerPatterns? formals patterns).isSome =
        patternsSupported formals patterns := by
  intro patterns
  cases patterns with
  | nil => simp [lowerPatterns?, patternsSupported]
  | cons pattern patterns =>
      cases head : lowerPattern? formals pattern with
      | none =>
          have headSupport := lowerPattern?_isSome formals pattern
          rw [head] at headSupport
          simp at headSupport
          simp [lowerPatterns?, patternsSupported, head, headSupport]
      | some term =>
          have headSupport := lowerPattern?_isSome formals pattern
          rw [head] at headSupport
          simp at headSupport
          cases tail : lowerPatterns? formals patterns <;>
            simpa [lowerPatterns?, patternsSupported, head, tail, headSupport]
              using lowerPatterns?_isSome formals patterns
termination_by patterns => sizeOf patterns

end

/-- Whether successful lowering of one source pattern has an application at
its root, computed without retaining that lowered term. -/
def applicationPatternSupported (formals : List (String × Nat)) :
    Pattern → Bool
  | .apply head arguments =>
      (physicalName? head).isSome && patternsSupported formals arguments
  | _ => false

theorem lowerPattern?_application (formals : List (String × Nat))
    (pattern : Pattern) :
    Option.any Term.isApplication (lowerPattern? formals pattern) =
      applicationPatternSupported formals pattern := by
  cases pattern with
  | apply head arguments =>
      cases name : physicalName? head with
      | none => simp [lowerPattern?, applicationPatternSupported, name]
      | some bytes =>
          cases argumentsResult : lowerPatterns? formals arguments <;>
            simpa [lowerPattern?, applicationPatternSupported, name,
              argumentsResult, Term.isApplication]
              using lowerPatterns?_isSome formals arguments
  | bvar index => simp [lowerPattern?, applicationPatternSupported]
  | fvar name =>
      cases slot : variableSlot? formals name <;>
        simp [lowerPattern?, applicationPatternSupported, slot,
          Term.isApplication]
  | lambda binder body => simp [lowerPattern?, applicationPatternSupported]
  | multiLambda arity binders body =>
      simp [lowerPattern?, applicationPatternSupported]
  | subst body replacement =>
      simp [lowerPattern?, applicationPatternSupported]
  | collection collectionType elements rest =>
      simp [lowerPattern?, applicationPatternSupported]

def applicationPatternsSupported (formals : List (String × Nat)) :
    List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      applicationPatternSupported formals pattern &&
        applicationPatternsSupported formals patterns

theorem lowerPatterns?_applications (formals : List (String × Nat)) :
    ∀ patterns,
      Option.any (fun terms => terms.all Term.isApplication)
          (lowerPatterns? formals patterns) =
        applicationPatternsSupported formals patterns := by
  intro patterns
  cases patterns with
  | nil => simp [lowerPatterns?, applicationPatternsSupported]
  | cons pattern patterns =>
      cases head : lowerPattern? formals pattern with
      | none =>
          have headApplication := lowerPattern?_application formals pattern
          rw [head] at headApplication
          simp at headApplication
          simp [lowerPatterns?, applicationPatternsSupported, head,
            headApplication]
      | some term =>
          have headApplication := lowerPattern?_application formals pattern
          rw [head] at headApplication
          simp at headApplication
          cases tail : lowerPatterns? formals patterns with
          | none =>
              have tailApplication := lowerPatterns?_applications formals patterns
              rw [tail] at tailApplication
              simp at tailApplication
              simp [lowerPatterns?, applicationPatternsSupported, head, tail,
                tailApplication]
          | some terms =>
              have tailApplication := lowerPatterns?_applications formals patterns
              rw [tail] at tailApplication
              simp at tailApplication
              simp [lowerPatterns?, applicationPatternsSupported, head, tail,
                headApplication, tailApplication]
termination_by patterns => sizeOf patterns

/-- Lower a rule whose source binding validity has already been admitted.  The
checks here are exactly the additional properties required by this physical
realization. -/
def lowerAdmittedRule? (rule : RuleSchema) : Option TypedRule := do
  if rule.sideConditions.isEmpty &&
      decide (rule.metavariables.length < UInt32.size) then
    let name <- physicalName? rule.id.value
    let head <- lowerPattern? rule.metavariables rule.conclusion
    let body <- lowerPatterns? rule.metavariables rule.premises
    if !head.isApplication || !body.all Term.isApplication then none else
    some
      { name
        head
        body
        variableCount := UInt32.ofNat rule.metavariables.length }
  else
    none

/-- Executable local fragment predicate which discards lowered payloads. -/
def admittedRuleSupported (rule : RuleSchema) : Bool :=
  rule.sideConditions.isEmpty &&
    decide (rule.metavariables.length < UInt32.size) &&
    (physicalName? rule.id.value).isSome &&
    applicationPatternSupported rule.metavariables rule.conclusion &&
    applicationPatternsSupported rule.metavariables rule.premises

theorem lowerAdmittedRule?_isSome (rule : RuleSchema) :
    (lowerAdmittedRule? rule).isSome = admittedRuleSupported rule := by
  by_cases sideConditions : rule.sideConditions.isEmpty = true
  · by_cases variableCount : rule.metavariables.length < UInt32.size
    · cases name : physicalName? rule.id.value with
      | none =>
          simp [lowerAdmittedRule?, admittedRuleSupported, sideConditions,
            variableCount, name]
      | some nameBytes =>
          cases head : lowerPattern? rule.metavariables rule.conclusion with
          | none =>
              have headApplication :=
                lowerPattern?_application rule.metavariables rule.conclusion
              rw [head] at headApplication
              simp at headApplication
              simp [lowerAdmittedRule?, admittedRuleSupported, sideConditions,
                variableCount, name, head, headApplication]
          | some headTerm =>
              have headApplication :=
                lowerPattern?_application rule.metavariables rule.conclusion
              rw [head] at headApplication
              simp at headApplication
              cases body : lowerPatterns? rule.metavariables rule.premises with
              | none =>
                  have bodyApplications :=
                    lowerPatterns?_applications rule.metavariables rule.premises
                  rw [body] at bodyApplications
                  simp at bodyApplications
                  simp [lowerAdmittedRule?, admittedRuleSupported,
                    sideConditions, variableCount, name, head, body,
                    bodyApplications]
              | some bodyTerms =>
                  have bodyApplications :=
                    lowerPatterns?_applications rule.metavariables rule.premises
                  rw [body] at bodyApplications
                  simp at bodyApplications
                  cases headSupport :
                      applicationPatternSupported rule.metavariables
                        rule.conclusion <;>
                    cases bodySupport :
                      applicationPatternsSupported rule.metavariables
                        rule.premises <;>
                    simp_all [lowerAdmittedRule?, admittedRuleSupported,
                      List.all_eq_true, List.all_eq_false]
    · simp [lowerAdmittedRule?, admittedRuleSupported, sideConditions,
        variableCount]
  · have sideConditionsFalse : rule.sideConditions.isEmpty = false :=
      Bool.eq_false_of_not_eq_true sideConditions
    simp [lowerAdmittedRule?, admittedRuleSupported, sideConditionsFalse]

theorem mapM_isSome_eq_all (f : α → Option β) :
    ∀ values : List α,
      (values.mapM f).isSome = values.all (fun value => (f value).isSome) := by
  intro values
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      cases head : f value with
      | none => simp [head]
      | some result =>
          cases tail : values.mapM f <;>
            simpa [head, tail] using inductionHypothesis

/-- Standalone rule entry point.  V1 validity remains the source binding
authority rather than being inferred from a successful physical lowering. -/
def lowerRule? (rule : RuleSchema) : Option TypedRule :=
  if InferenceChecker.RuleSchema.isLocallyValid rule then
    lowerAdmittedRule? rule
  else
    none

/-- Fragment recognition for an already admitted calculus language. -/
def lowerValidatedDefinition?
    (definition : ValidatedCalculusLanguageDef) : Option TypedProgram :=
  definition.1.rules.mapM lowerAdmittedRule?

theorem lowerValidatedDefinition?_isSome
    (definition : ValidatedCalculusLanguageDef) :
    (lowerValidatedDefinition? definition).isSome =
      definition.1.rules.all admittedRuleSupported := by
  simp [lowerValidatedDefinition?, mapM_isSome_eq_all,
    lowerAdmittedRule?_isSome]

/-- Whole-language admission precedes fragment recognition. -/
def lowerDefinition? (definition : CalculusLanguageDef) : Option TypedProgram :=
  if valid : definition.isValid = true then
    lowerValidatedDefinition? ⟨definition, valid⟩
  else
    none

def admittedMeaning? (definition : CalculusLanguageDef) : Option AdmittedProgram :=
  (lowerDefinition? definition).map TypedProgram.toAdmitted

def admittedValidatedMeaning?
    (definition : ValidatedCalculusLanguageDef) : Option AdmittedProgram :=
  (lowerValidatedDefinition? definition).map TypedProgram.toAdmitted

def compileValidatedBytes?
    (definition : ValidatedCalculusLanguageDef) : Option (List UInt8) := do
  let source <- lowerValidatedDefinition? definition
  CompiledPlanLowering.compileBytes? source

def compileBytes? (definition : CalculusLanguageDef) : Option (List UInt8) := do
  let source <- lowerDefinition? definition
  CompiledPlanLowering.compileBytes? source

theorem lowerDefinition?_success_valid
    {definition : CalculusLanguageDef} {source : TypedProgram}
    (success : lowerDefinition? definition = some source) :
    definition.isValid = true := by
  unfold lowerDefinition? at success
  by_cases valid : definition.isValid = true
  · exact valid
  · simp [valid] at success

/-- Source-to-packet soundness for the recognized finite-Horn fragment. -/
theorem compileBytes?_sound
    {definition : CalculusLanguageDef} {bytes : List UInt8}
    (success : compileBytes? definition = some bytes) :
    admitBytes? bytes = admittedMeaning? definition := by
  unfold compileBytes? at success
  cases lowered : lowerDefinition? definition with
  | none =>
      simp [lowered] at success
  | some source =>
      rw [lowered] at success
      have packetSound :=
        CompiledPlanLowering.compileBytes?_sound success
      simp [admittedMeaning?, lowered, packetSound]

/-- The validated-definition entry point preserves the independently
reconstructed source meaning without repeating source admission. -/
theorem compileValidatedBytes?_sound
    {definition : ValidatedCalculusLanguageDef} {bytes : List UInt8}
    (success : compileValidatedBytes? definition = some bytes) :
    admitBytes? bytes = admittedValidatedMeaning? definition := by
  unfold compileValidatedBytes? at success
  cases lowered : lowerValidatedDefinition? definition with
  | none =>
      simp [lowered] at success
  | some source =>
      rw [lowered] at success
      have packetSound :=
        CompiledPlanLowering.compileBytes?_sound success
      simp [admittedValidatedMeaning?, lowered, packetSound]

/-! ## Positive and negative witnesses -/

def binaryRule : RuleSchema :=
  { id := ⟨"pair"⟩
    metavariables := [("x", 0), ("y", 0)]
    premises := []
    conclusion := .apply "pair" [.fvar "x", .fvar "y"] }

def binaryDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "compiled-plan-binary")
    { judgments := [{ head := "pair", arity := 2 }]
      rules := [binaryRule] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

theorem binaryDefinition_valid :
    binaryDefinition.isValid = true := by
  simp [binaryDefinition, CalculusLanguageDef.extend,
    CalculusLanguageDef.isValid,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.ruleIds,
    emptyLanguage_validate, binaryRule,
    InferenceChecker.RuleSchema.isValidIn,
    CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?,
    InferenceChecker.fixedConstructorListsValid,
    InferenceChecker.fixedConstructorsValid,
    InferenceChecker.RuleSchema.isLocallyValid,
    InferenceChecker.RuleSchema.metavariableNames,
    InferenceChecker.RuleSchema.occurrences,
    InferenceChecker.RuleSchema.patterns,
    InferenceChecker.patternMetavariableOccurrencesAt,
    InferenceChecker.patternsMetavariableOccurrencesAt,
    InferenceChecker.patternHasNoCollectionRest,
    InferenceChecker.patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

theorem lowerRule?_binaryRule :
    lowerRule? binaryRule = some binaryTypedRule := by
  simp [lowerRule?, lowerAdmittedRule?, binaryRule, binaryTypedRule,
    physicalName?, stringBytes,
    variableSlot?, lowerPattern?, lowerPatterns?,
    InferenceChecker.RuleSchema.isLocallyValid,
    InferenceChecker.RuleSchema.metavariableNames,
    InferenceChecker.RuleSchema.occurrences,
    InferenceChecker.RuleSchema.patterns,
    InferenceChecker.patternMetavariableOccurrencesAt,
    InferenceChecker.patternsMetavariableOccurrencesAt,
    InferenceChecker.patternHasNoCollectionRest,
    InferenceChecker.patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, textEncodable?, bytesNulFree,
    bytesNonempty, Term.isApplication]
  decide

theorem lowerDefinition?_binaryDefinition :
    lowerDefinition? binaryDefinition = some binaryTypedProgram := by
  unfold lowerDefinition?
  rw [dif_pos binaryDefinition_valid]
  simp [lowerValidatedDefinition?, binaryDefinition,
    CalculusLanguageDef.extend,
    lowerAdmittedRule?, binaryRule, binaryTypedProgram, physicalName?,
    stringBytes, variableSlot?, lowerPattern?, lowerPatterns?,
    textEncodable?, bytesNulFree, bytesNonempty, Term.isApplication]
  decide

theorem compileBytes?_binaryDefinition :
    compileBytes? binaryDefinition = some binaryBytes := by
  simp [compileBytes?, lowerDefinition?_binaryDefinition,
    CompiledPlanLowering.compileBytes?_binary_typed_program]

def binderRule : RuleSchema :=
  { id := ⟨"binder"⟩
    metavariables := [("body", 1)]
    premises := []
    conclusion := .apply "holds" [.lambda none (.fvar "body")] }

theorem binderRule_validV1 :
    InferenceChecker.RuleSchema.isLocallyValid binderRule = true := by
  simp [binderRule, InferenceChecker.RuleSchema.isLocallyValid,
    InferenceChecker.RuleSchema.metavariableNames,
    InferenceChecker.RuleSchema.occurrences,
    InferenceChecker.RuleSchema.patterns,
    InferenceChecker.patternMetavariableOccurrencesAt,
    InferenceChecker.patternsMetavariableOccurrencesAt,
    InferenceChecker.patternHasNoCollectionRest,
    InferenceChecker.patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

theorem lowerRule?_rejects_binderRule : lowerRule? binderRule = none := by
  simp [lowerRule?, lowerAdmittedRule?, binderRule, physicalName?,
    stringBytes, lowerPattern?, lowerPatterns?, textEncodable?, bytesNulFree,
    bytesNonempty]

def sideConditionRule : RuleSchema :=
  { id := ⟨"side-condition"⟩
    metavariables := [("body", 1), ("replacement", 0), ("result", 0)]
    premises := []
    conclusion := .apply "substitutes"
      [.fvar "body", .fvar "replacement", .fvar "result"]
    sideConditions := [.explicitSubstitution 0 0 1 2] }

theorem lowerRule?_rejects_sideConditionRule :
    lowerRule? sideConditionRule = none := by
  simp [lowerRule?, lowerAdmittedRule?, sideConditionRule]

end Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
