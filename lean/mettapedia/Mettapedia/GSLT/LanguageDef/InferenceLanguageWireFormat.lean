import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# Exact wire semantics for inference languages

`CertificateGSLTWireFormat` gives chronological proof articles a canonical symbolic
wire carrier.  This module gives the checker-facing projection of an admitted
inference definition the same treatment.  The projection retains every
field consulted by generic replay: constructor arities, judgment arities,
ordered rules, exact metavariable occurrence depths, generic side conditions,
and the rooted conversion declaration.

The versioned carrier deliberately retains the final two items so a guarded
definition cannot serialize as its unguarded counterpart.  There is no
reduced executable schema beside it: every checker-facing language uses the
same lossless carrier.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- The part of a term declaration consulted by the generic inference
checker.  Grammar categories and syntax remain authority-source data;
native replay needs the stable constructor head and exact arity. -/
structure ConstructorSignature where
  head : String
  arity : Nat
deriving Repr, DecidableEq

/-- Exact checker-facing projection of one inference definition. -/
structure RuntimeInferenceLanguage where
  constructors : List ConstructorSignature
  judgments : List JudgmentDecl
  rules : List RuleSchema
  conversion : Option ConversionDecl
deriving Repr, DecidableEq

def ConstructorSignature.ofGrammarRule
    (declaration : GrammarRule) : ConstructorSignature :=
  { head := declaration.label, arity := declaration.params.length }

def RuntimeInferenceLanguage.ofDefinition
    (definition : CalculusLanguageDef) : RuntimeInferenceLanguage :=
  { constructors :=
      definition.toLanguageDef.terms.map ConstructorSignature.ofGrammarRule
    judgments := definition.judgments
    rules := definition.rules
    conversion := definition.conversion }

@[simp] theorem RuntimeInferenceLanguage.ofDefinition_rules
    (definition : CalculusLanguageDef) :
    (RuntimeInferenceLanguage.ofDefinition definition).rules =
      definition.rules :=
  rfl

@[simp] theorem RuntimeInferenceLanguage.ofDefinition_conversion
    (definition : CalculusLanguageDef) :
    (RuntimeInferenceLanguage.ofDefinition definition).conversion =
      definition.conversion :=
  rfl

/-! ## Canonical encoders -/

def encodeConstructor (declaration : ConstructorSignature) : WireTerm :=
  .list [.symbol "WConstructor", .symbol declaration.head,
    .natural declaration.arity]

def encodeJudgment (declaration : JudgmentDecl) : WireTerm :=
  .list [.symbol "WJudgment", .symbol declaration.head,
    .natural declaration.arity]

def encodeFormal (formal : String × Nat) : WireTerm :=
  .list [.symbol "WFormal", .symbol formal.1, .natural formal.2]

def encodeSideCondition : RuleSideCondition → WireTerm
  | .explicitSubstitution ambientDepth bodyArgument replacementArgument
      resultArgument =>
      .list [.symbol "WExplicitSubstitution", .natural ambientDepth,
        .natural bodyArgument, .natural replacementArgument,
        .natural resultArgument]
  | .unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      .list [.symbol "WUnusedBinderElimination", .natural ambientDepth,
        .natural bodyArgument, .natural resultArgument]

def encodeRule (rule : RuleSchema) : WireTerm :=
  .list [.symbol "WRule", .symbol rule.id.value,
    .list (rule.metavariables.map encodeFormal),
    .list (encodePatternList rule.premises),
    encodePattern rule.conclusion,
    .list (rule.sideConditions.map encodeSideCondition)]

def encodeConversion : Option ConversionDecl → WireTerm
  | none => .symbol "WNoConversion"
  | some declaration =>
      .list [.symbol "WConversion", .symbol declaration.judgmentHead,
        .symbol declaration.version]

/-- Version one is the first definition carrier that retains generic side
conditions and rooted conversion identity. -/
def inferenceLanguageWireVersion : Nat := 1

def encodeRuntimeInferenceLanguage (definition : RuntimeInferenceLanguage) : WireTerm :=
  .list [.symbol "WInferenceLanguage", .natural inferenceLanguageWireVersion,
    .list (definition.constructors.map encodeConstructor),
    .list (definition.judgments.map encodeJudgment),
    .list (definition.rules.map encodeRule),
    encodeConversion definition.conversion]

def encodeDefinition (definition : CalculusLanguageDef) : WireTerm :=
  encodeRuntimeInferenceLanguage (RuntimeInferenceLanguage.ofDefinition definition)

/-! ## Fail-closed decoders -/

def decodeList (decode : WireTerm → Option α) :
    List WireTerm → Option (List α)
  | [] => some []
  | item :: items => do
      let head ← decode item
      let tail ← decodeList decode items
      some (head :: tail)

def decodeConstructor : WireTerm → Option ConstructorSignature
  | .list [.symbol "WConstructor", .symbol head, .natural arity] =>
      some ⟨head, arity⟩
  | _ => none

def decodeJudgment : WireTerm → Option JudgmentDecl
  | .list [.symbol "WJudgment", .symbol head, .natural arity] =>
      some ⟨head, arity⟩
  | _ => none

def decodeFormal : WireTerm → Option (String × Nat)
  | .list [.symbol "WFormal", .symbol name, .natural depth] =>
      some (name, depth)
  | _ => none

def decodeSideCondition : WireTerm → Option RuleSideCondition
  | .list [.symbol "WExplicitSubstitution", .natural ambientDepth,
      .natural bodyArgument, .natural replacementArgument,
      .natural resultArgument] =>
      some (.explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument)
  | .list [.symbol "WUnusedBinderElimination", .natural ambientDepth,
      .natural bodyArgument, .natural resultArgument] =>
      some (.unusedBinderElimination ambientDepth bodyArgument resultArgument)
  | _ => none

def decodeRule : WireTerm → Option RuleSchema
  | .list [.symbol "WRule", .symbol id, .list formals, .list premises,
      conclusion, .list sideConditions] => do
      let decodedFormals ← decodeList decodeFormal formals
      let decodedPremises ← decodePatternList premises
      let decodedConclusion ← decodePattern conclusion
      let decodedSideConditions ←
        decodeList decodeSideCondition sideConditions
      some
        { id := ⟨id⟩
          metavariables := decodedFormals
          premises := decodedPremises
          conclusion := decodedConclusion
          sideConditions := decodedSideConditions }
  | _ => none

def decodeConversion : WireTerm → Option (Option ConversionDecl)
  | .symbol "WNoConversion" => some none
  | .list [.symbol "WConversion", .symbol judgmentHead, .symbol version] =>
      some (some ⟨judgmentHead, version⟩)
  | _ => none

def decodeRuntimeInferenceLanguage : WireTerm → Option RuntimeInferenceLanguage
  | .list [.symbol "WInferenceLanguage", .natural version,
      .list constructors, .list judgments, .list rules, conversion] => do
      if version != inferenceLanguageWireVersion then none
      let decodedConstructors ← decodeList decodeConstructor constructors
      let decodedJudgments ← decodeList decodeJudgment judgments
      let decodedRules ← decodeList decodeRule rules
      let decodedConversion ← decodeConversion conversion
      some
        { constructors := decodedConstructors
          judgments := decodedJudgments
          rules := decodedRules
          conversion := decodedConversion }
  | _ => none

/-! ## Round trip and identity -/

theorem decodeList_map_encode (decode : WireTerm → Option α)
    (encode : α → WireTerm)
    (roundTrip : ∀ value, decode (encode value) = some value)
    (values : List α) :
    decodeList decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [decodeList, roundTrip, inductionHypothesis]

@[simp] theorem decodeConstructor_encodeConstructor
    (declaration : ConstructorSignature) :
    decodeConstructor (encodeConstructor declaration) = some declaration := by
  cases declaration
  rfl

@[simp] theorem decodeJudgment_encodeJudgment
    (declaration : JudgmentDecl) :
    decodeJudgment (encodeJudgment declaration) = some declaration := by
  cases declaration
  rfl

@[simp] theorem decodeFormal_encodeFormal (formal : String × Nat) :
    decodeFormal (encodeFormal formal) = some formal := by
  cases formal
  rfl

@[simp] theorem decodeSideCondition_encodeSideCondition
    (condition : RuleSideCondition) :
    decodeSideCondition (encodeSideCondition condition) = some condition := by
  cases condition <;> rfl

@[simp] theorem decodeRule_encodeRule (rule : RuleSchema) :
    decodeRule (encodeRule rule) = some rule := by
  cases rule
  simp [encodeRule, decodeRule, decodeList_map_encode]

@[simp] theorem decodeConversion_encodeConversion
    (conversion : Option ConversionDecl) :
    decodeConversion (encodeConversion conversion) = some conversion := by
  cases conversion with
  | none => rfl
  | some declaration => cases declaration; rfl

@[simp] theorem decodeRuntimeInferenceLanguage_encodeRuntimeInferenceLanguage
    (definition : RuntimeInferenceLanguage) :
    decodeRuntimeInferenceLanguage (encodeRuntimeInferenceLanguage definition) =
      some definition := by
  cases definition
  simp [encodeRuntimeInferenceLanguage, decodeRuntimeInferenceLanguage,
    inferenceLanguageWireVersion, decodeList_map_encode]

@[simp] theorem decodeRuntimeInferenceLanguage_encodeDefinition
    (definition : CalculusLanguageDef) :
    decodeRuntimeInferenceLanguage (encodeDefinition definition) =
      some (RuntimeInferenceLanguage.ofDefinition definition) := by
  simp [encodeDefinition]

/-- Canonical wire identity is collision-free for checker projections. -/
theorem encodeRuntimeInferenceLanguage_inj
    {left right : RuntimeInferenceLanguage}
    (encodingEq :
      encodeRuntimeInferenceLanguage left = encodeRuntimeInferenceLanguage right) :
    left = right := by
  have decoded := decodeRuntimeInferenceLanguage_encodeRuntimeInferenceLanguage left
  rw [encodingEq, decodeRuntimeInferenceLanguage_encodeRuntimeInferenceLanguage right]
    at decoded
  exact Option.some.inj decoded.symm

/-- Rule wire identity is collision-free, including its side conditions. -/
theorem encodeRule_inj {left right : RuleSchema}
    (encodingEq : encodeRule left = encodeRule right) :
    left = right := by
  have decoded := decodeRule_encodeRule left
  rw [encodingEq, decodeRule_encodeRule right] at decoded
  exact Option.some.inj decoded.symm

theorem encodeRuntimeInferenceLanguage_inj_iff
    (left right : RuntimeInferenceLanguage) :
    encodeRuntimeInferenceLanguage left = encodeRuntimeInferenceLanguage right ↔
      left = right := by
  constructor
  · exact encodeRuntimeInferenceLanguage_inj
  · intro equality
    rw [equality]

/-! ## Closed-payload runtime profile

The generic inference checker deliberately leaves metavariable payload
carriers open.  Native catalog replay uses a stricter, explicitly named
profile in which every structural application in a proof argument belongs to
the definition's constructor signature.  An undeclared nullary application
remains open atom data, but a declared head is structural and must retain its
declared arity.  Authorities constrain open atoms through ordinary premises,
signatures, and environments.  Keeping this policy here prevents a physical
vocabulary check from being mistaken for universal NIK semantics.
-/

def RuntimeInferenceLanguage.lookupRule? (definition : RuntimeInferenceLanguage)
    (id : RuleId) : Option RuleSchema :=
  definition.rules.find? fun rule => decide (rule.id = id)

def RuntimeInferenceLanguage.hasConstructorArity
    (definition : RuntimeInferenceLanguage) (head : String) (arity : Nat) : Bool :=
  match definition.constructors.filter fun declaration =>
      declaration.head == head with
  | [declaration] => declaration.arity == arity
  | _ => false

/-- Classify one application relative to an admitted constructor signature.
An undeclared nullary head is opaque data.  A uniquely declared head must use
its declared arity, and duplicate declarations fail closed. -/
def RuntimeInferenceLanguage.constructorApplicationValid
    (definition : RuntimeInferenceLanguage) (head : String) (arity : Nat) : Bool :=
  match definition.constructors.filter fun declaration =>
      declaration.head == head with
  | [] => arity == 0
  | [declaration] => declaration.arity == arity
  | _ => false

mutual

/-- Closed structural-constructor validation for a ground proof argument. -/
def RuntimeInferenceLanguage.fixedConstructorsValid
    (definition : RuntimeInferenceLanguage) : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply head arguments =>
      definition.constructorApplicationValid head arguments.length &&
        definition.fixedConstructorListsValid arguments
  | .lambda _ body => definition.fixedConstructorsValid body
  | .multiLambda _ _ body => definition.fixedConstructorsValid body
  | .subst body replacement =>
      definition.fixedConstructorsValid body &&
        definition.fixedConstructorsValid replacement
  | .collection _ elements _ =>
      definition.fixedConstructorListsValid elements
termination_by pattern => sizeOf pattern

def RuntimeInferenceLanguage.fixedConstructorListsValid
    (definition : RuntimeInferenceLanguage) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      definition.fixedConstructorsValid pattern &&
        definition.fixedConstructorListsValid patterns
termination_by patterns => sizeOf patterns

end

def RuntimeInferenceLanguage.argumentValidAt
    (definition : RuntimeInferenceLanguage) (depth : Nat)
    (argument : Pattern) : Bool :=
  InferenceChecker.argumentValidAt depth argument &&
    definition.fixedConstructorsValid argument

def RuntimeInferenceLanguage.argumentsValidAt
    (definition : RuntimeInferenceLanguage) :
    List (String × Nat) → List Pattern → Bool
  | [], [] => true
  | (_, depth) :: formals, argument :: arguments =>
      definition.argumentValidAt depth argument &&
        definition.argumentsValidAt formals arguments
  | _, _ => false

/-- Local replay under the closed-payload catalog profile. -/
def RuntimeInferenceLanguage.instantiateRule?
    (definition : RuntimeInferenceLanguage)
    (ruleInstance : RuleInstance) : Option (List Pattern × Pattern) :=
  match definition.lookupRule? ruleInstance.ruleId with
  | none => none
  | some rule =>
      if definition.argumentsValidAt
          rule.metavariables ruleInstance.arguments then do
        if InferenceChecker.RuleSchema.sideConditionsHold
            rule ruleInstance.arguments then do
          let premises ← instantiateSchemas? rule.metavariables
            ruleInstance.arguments rule.premises
          let conclusion ← instantiateSchema? rule.metavariables
            ruleInstance.arguments rule.conclusion
          some (premises, conclusion)
        else
          none
      else
        none

mutual

/-- Fuel-free closed-payload checker over the exact runtime projection. -/
def RuntimeInferenceLanguage.checkRaw (definition : RuntimeInferenceLanguage) :
    Pattern → RawProof → Bool
  | goal, .node ruleInstance children =>
      match definition.instantiateRule? ruleInstance with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) &&
            definition.checkRawChildren premises children
termination_by _ proof => sizeOf proof

def RuntimeInferenceLanguage.checkRawChildren
    (definition : RuntimeInferenceLanguage) :
    List Pattern → List RawProof → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      definition.checkRaw premise child &&
        definition.checkRawChildren premises children
  | _, _ => false
termination_by _ children => sizeOf children

end

@[simp] theorem RuntimeInferenceLanguage.ofDefinition_lookupRule?
    (definition : CalculusLanguageDef) (id : RuleId) :
    (RuntimeInferenceLanguage.ofDefinition definition).lookupRule? id =
      definition.lookupRule? id := by
  rfl

/-- The closed-payload runtime profile may reject additional articles, but
every argument it admits satisfies the generic checker's binder contract. -/
theorem RuntimeInferenceLanguage.argumentsValidAt_sound
    (definition : RuntimeInferenceLanguage) :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern),
      definition.argumentsValidAt formals arguments = true →
        InferenceChecker.argumentsValidAt formals arguments = true := by
  intro formals
  induction formals with
  | nil =>
      intro arguments hypothesis
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp [RuntimeInferenceLanguage.argumentsValidAt] at hypothesis
  | cons formal formals inductionHypothesis =>
      intro arguments hypothesis
      cases arguments with
      | nil =>
          simp [RuntimeInferenceLanguage.argumentsValidAt] at hypothesis
      | cons argument arguments =>
          simp only [RuntimeInferenceLanguage.argumentsValidAt,
            RuntimeInferenceLanguage.argumentValidAt,
            Bool.and_eq_true] at hypothesis
          simp only [InferenceChecker.argumentsValidAt, Bool.and_eq_true]
          exact ⟨hypothesis.1.1,
            inductionHypothesis arguments hypothesis.2⟩

/-- Successful local replay by the closed-payload runtime projection is a
successful application of the original validated definition. -/
theorem RuntimeInferenceLanguage.instantiateRule?_sound
    (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (hypothesis :
      (RuntimeInferenceLanguage.ofDefinition definition.1).instantiateRule?
          ruleInstance = some (premises, conclusion)) :
    InferenceChecker.instantiateRule? definition ruleInstance =
      some (premises, conclusion) := by
  simp only [RuntimeInferenceLanguage.instantiateRule?,
    RuntimeInferenceLanguage.ofDefinition_lookupRule?] at hypothesis
  cases lookup : definition.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at hypothesis
  | some rule =>
      rw [lookup] at hypothesis
      cases arguments :
          (RuntimeInferenceLanguage.ofDefinition definition.1).argumentsValidAt
            rule.metavariables ruleInstance.arguments with
      | false => simp [arguments] at hypothesis
      | true =>
          have genericArguments :
              InferenceChecker.argumentsValidAt
                  rule.metavariables ruleInstance.arguments = true :=
            RuntimeInferenceLanguage.argumentsValidAt_sound
              (RuntimeInferenceLanguage.ofDefinition definition.1)
              rule.metavariables ruleInstance.arguments arguments
          simpa [InferenceChecker.instantiateRule?, lookup, genericArguments,
            arguments] using hypothesis

mutual

/-- Acceptance by the closed-payload runtime checker refines acceptance by
the generic validated checker. -/
theorem RuntimeInferenceLanguage.checkRaw_sound
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) (proof : RawProof)
    (hypothesis :
      (RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw
        goal proof = true) :
    InferenceChecker.checkRaw definition goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [RuntimeInferenceLanguage.checkRaw] at hypothesis
      cases localResult :
          (RuntimeInferenceLanguage.ofDefinition definition.1).instantiateRule?
            ruleInstance with
      | none => simp [localResult] at hypothesis
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [localResult, Bool.and_eq_true, decide_eq_true_eq]
            at hypothesis
          have logicalResult := RuntimeInferenceLanguage.instantiateRule?_sound
            definition ruleInstance premises conclusion localResult
          simp only [InferenceChecker.checkRaw, logicalResult,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hypothesis.1,
            RuntimeInferenceLanguage.checkRawChildren_sound definition
              premises children hypothesis.2⟩
termination_by sizeOf proof

theorem RuntimeInferenceLanguage.checkRawChildren_sound
    (definition : ValidatedCalculusLanguageDef) (premises : List Pattern)
    (proofs : List RawProof)
    (hypothesis :
      (RuntimeInferenceLanguage.ofDefinition definition.1).checkRawChildren
        premises proofs = true) :
    InferenceChecker.checkRawChildren definition premises proofs = true := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => simp [InferenceChecker.checkRawChildren]
      | cons proof proofs =>
          simp [RuntimeInferenceLanguage.checkRawChildren] at hypothesis
  | cons premise premises =>
      cases proofs with
      | nil =>
          simp [RuntimeInferenceLanguage.checkRawChildren] at hypothesis
      | cons proof proofs =>
          simp only [RuntimeInferenceLanguage.checkRawChildren,
            Bool.and_eq_true] at hypothesis
          simp only [InferenceChecker.checkRawChildren, Bool.and_eq_true]
          exact ⟨RuntimeInferenceLanguage.checkRaw_sound definition premise proof
              hypothesis.1,
            RuntimeInferenceLanguage.checkRawChildren_sound definition
              premises proofs hypothesis.2⟩
termination_by sizeOf proofs

end

/-- Decode and replay one exact definition packet.  Malformed packets are
distinguished from rejected proof articles. -/
def checkEncodedLanguage (wire : WireTerm)
    (goal : Pattern) (proof : RawProof) : Option Bool := do
  let definition ← decodeRuntimeInferenceLanguage wire
  some (definition.checkRaw goal proof)

/-- Canonical definition transport preserves the complete closed-payload
checker result. -/
theorem checkEncodedLanguage_encodeRuntimeInferenceLanguage
    (definition : RuntimeInferenceLanguage)
    (goal : Pattern) (proof : RawProof) :
    checkEncodedLanguage (encodeRuntimeInferenceLanguage definition)
        goal proof =
      some (definition.checkRaw goal proof) := by
  simp [checkEncodedLanguage]

/-- The exact projection of an authored definition therefore has one
canonical checker result on the wire. -/
theorem checkEncodedLanguage_encodeDefinition
    (definition : CalculusLanguageDef) (goal : Pattern) (proof : RawProof) :
    checkEncodedLanguage (encodeDefinition definition) goal proof =
      some ((RuntimeInferenceLanguage.ofDefinition definition).checkRaw
        goal proof) := by
  simp [encodeDefinition, checkEncodedLanguage]

/-! ## Positive and negative canaries -/

private def guardedRule : RuleSchema :=
  { id := ⟨"guarded"⟩
    metavariables := [("body", 1), ("replacement", 0), ("result", 0)]
    premises := []
    conclusion :=
      .apply "Converts"
        [.subst (.fvar "body") (.fvar "replacement"), .fvar "result"]
    sideConditions := [.explicitSubstitution 0 0 1 2] }

private def unguardedRule : RuleSchema :=
  { guardedRule with sideConditions := [] }

/-- A guarded rule and its unsound unguarded erasure have distinct wire
identities. -/
theorem guarded_rule_not_unguarded_on_wire :
    encodeRule guardedRule ≠ encodeRule unguardedRule := by
  intro encodingEq
  have ruleEq : guardedRule = unguardedRule := encodeRule_inj encodingEq
  have sideConditionEq := congrArg RuleSchema.sideConditions ruleEq
  simp [guardedRule, unguardedRule] at sideConditionEq

/-- Omitting the side-condition field is not accepted as an older spelling of
the version-one rule carrier. -/
theorem missing_side_condition_field_rejects :
    decodeRule
      (.list [.symbol "WRule", .symbol "guarded",
        .list [], .list [], encodePattern guardedRule.conclusion]) = none := by
  rfl

/-- The version gate fails closed. -/
theorem wrong_language_version_rejects :
    decodeRuntimeInferenceLanguage
      (.list [.symbol "WInferenceLanguage", .natural 0,
        .list [], .list [], .list [], .symbol "WNoConversion"]) = none := by
  rfl

end Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
