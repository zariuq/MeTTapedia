import Mettapedia.GSLT.LanguageDef.ProofGSLTWireFormat

/-!
# Exact wire semantics for inference presentations

`ProofGSLTWireFormat` gives chronological proof articles a canonical symbolic
wire carrier.  This module gives the checker-facing projection of an admitted
inference presentation the same treatment.  The projection retains every
field consulted by generic replay: constructor arities, judgment arities,
ordered rules, exact metavariable occurrence depths, generic side conditions,
and the rooted conversion declaration.

The older executable `GPresentation/GRule` interface omitted the final two
items.  They are deliberately part of this versioned carrier so a guarded
presentation cannot serialize as its unguarded counterpart.
-/

namespace Mettapedia.GSLT.LanguageDef.InferencePresentationWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT

/-- The part of a term declaration consulted by the generic inference
checker.  Grammar categories and syntax remain authority-source data;
native replay needs the stable constructor head and exact arity. -/
structure ConstructorSignature where
  head : String
  arity : Nat
deriving Repr, DecidableEq

/-- Exact checker-facing projection of one inference presentation. -/
structure RuntimePresentation where
  constructors : List ConstructorSignature
  judgments : List JudgmentDecl
  rules : List RuleSchema
  conversion : Option ConversionDecl
deriving Repr, DecidableEq

def ConstructorSignature.ofGrammarRule
    (declaration : GrammarRule) : ConstructorSignature :=
  { head := declaration.label, arity := declaration.params.length }

def RuntimePresentation.ofPresentation
    (presentation : Presentation) : RuntimePresentation :=
  { constructors :=
      presentation.language.terms.map ConstructorSignature.ofGrammarRule
    judgments := presentation.judgments
    rules := presentation.rules
    conversion := presentation.conversion }

@[simp] theorem RuntimePresentation.ofPresentation_rules
    (presentation : Presentation) :
    (RuntimePresentation.ofPresentation presentation).rules =
      presentation.rules :=
  rfl

@[simp] theorem RuntimePresentation.ofPresentation_conversion
    (presentation : Presentation) :
    (RuntimePresentation.ofPresentation presentation).conversion =
      presentation.conversion :=
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

/-- Version one is the first presentation carrier that retains generic side
conditions and rooted conversion identity. -/
def presentationWireVersion : Nat := 1

def encodeRuntimePresentation (presentation : RuntimePresentation) : WireTerm :=
  .list [.symbol "WPresentation", .natural presentationWireVersion,
    .list (presentation.constructors.map encodeConstructor),
    .list (presentation.judgments.map encodeJudgment),
    .list (presentation.rules.map encodeRule),
    encodeConversion presentation.conversion]

def encodePresentation (presentation : Presentation) : WireTerm :=
  encodeRuntimePresentation (RuntimePresentation.ofPresentation presentation)

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

def decodeRuntimePresentation : WireTerm → Option RuntimePresentation
  | .list [.symbol "WPresentation", .natural version,
      .list constructors, .list judgments, .list rules, conversion] => do
      if version != presentationWireVersion then none
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

@[simp] theorem decodeRuntimePresentation_encodeRuntimePresentation
    (presentation : RuntimePresentation) :
    decodeRuntimePresentation (encodeRuntimePresentation presentation) =
      some presentation := by
  cases presentation
  simp [encodeRuntimePresentation, decodeRuntimePresentation,
    presentationWireVersion, decodeList_map_encode]

@[simp] theorem decodeRuntimePresentation_encodePresentation
    (presentation : Presentation) :
    decodeRuntimePresentation (encodePresentation presentation) =
      some (RuntimePresentation.ofPresentation presentation) := by
  simp [encodePresentation]

/-- Canonical wire identity is collision-free for checker projections. -/
theorem encodeRuntimePresentation_inj
    {left right : RuntimePresentation}
    (encodingEq :
      encodeRuntimePresentation left = encodeRuntimePresentation right) :
    left = right := by
  have decoded := decodeRuntimePresentation_encodeRuntimePresentation left
  rw [encodingEq, decodeRuntimePresentation_encodeRuntimePresentation right]
    at decoded
  exact Option.some.inj decoded.symm

/-- Rule wire identity is collision-free, including its side conditions. -/
theorem encodeRule_inj {left right : RuleSchema}
    (encodingEq : encodeRule left = encodeRule right) :
    left = right := by
  have decoded := decodeRule_encodeRule left
  rw [encodingEq, decodeRule_encodeRule right] at decoded
  exact Option.some.inj decoded.symm

theorem encodeRuntimePresentation_inj_iff
    (left right : RuntimePresentation) :
    encodeRuntimePresentation left = encodeRuntimePresentation right ↔
      left = right := by
  constructor
  · exact encodeRuntimePresentation_inj
  · intro equality
    rw [equality]

/-! ## Closed-payload runtime profile

The generic inference checker deliberately leaves metavariable payload
carriers open.  Native catalog replay uses a stricter, explicitly named
profile in which every structural application in a proof argument belongs to
the presentation's constructor signature.  An undeclared nullary application
remains open atom data, but a declared head is structural and must retain its
declared arity.  Authorities constrain open atoms through ordinary premises,
signatures, and environments.  Keeping this policy here prevents a physical
vocabulary check from being mistaken for universal NIK semantics.
-/

def RuntimePresentation.lookupRule? (presentation : RuntimePresentation)
    (id : RuleId) : Option RuleSchema :=
  presentation.rules.find? fun rule => decide (rule.id = id)

def RuntimePresentation.hasConstructorArity
    (presentation : RuntimePresentation) (head : String) (arity : Nat) : Bool :=
  match presentation.constructors.filter fun declaration =>
      declaration.head == head with
  | [declaration] => declaration.arity == arity
  | _ => false

/-- Classify one application relative to an admitted constructor signature.
An undeclared nullary head is opaque data.  A uniquely declared head must use
its declared arity, and duplicate declarations fail closed. -/
def RuntimePresentation.constructorApplicationValid
    (presentation : RuntimePresentation) (head : String) (arity : Nat) : Bool :=
  match presentation.constructors.filter fun declaration =>
      declaration.head == head with
  | [] => arity == 0
  | [declaration] => declaration.arity == arity
  | _ => false

mutual

/-- Closed structural-constructor validation for a ground proof argument. -/
def RuntimePresentation.fixedConstructorsValid
    (presentation : RuntimePresentation) : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply head arguments =>
      presentation.constructorApplicationValid head arguments.length &&
        presentation.fixedConstructorListsValid arguments
  | .lambda _ body => presentation.fixedConstructorsValid body
  | .multiLambda _ _ body => presentation.fixedConstructorsValid body
  | .subst body replacement =>
      presentation.fixedConstructorsValid body &&
        presentation.fixedConstructorsValid replacement
  | .collection _ elements _ =>
      presentation.fixedConstructorListsValid elements
termination_by pattern => sizeOf pattern

def RuntimePresentation.fixedConstructorListsValid
    (presentation : RuntimePresentation) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      presentation.fixedConstructorsValid pattern &&
        presentation.fixedConstructorListsValid patterns
termination_by patterns => sizeOf patterns

end

def RuntimePresentation.argumentValidAt
    (presentation : RuntimePresentation) (depth : Nat)
    (argument : Pattern) : Bool :=
  InferenceChecker.argumentValidAt depth argument &&
    presentation.fixedConstructorsValid argument

def RuntimePresentation.argumentsValidAt
    (presentation : RuntimePresentation) :
    List (String × Nat) → List Pattern → Bool
  | [], [] => true
  | (_, depth) :: formals, argument :: arguments =>
      presentation.argumentValidAt depth argument &&
        presentation.argumentsValidAt formals arguments
  | _, _ => false

/-- Local replay under the closed-payload catalog profile. -/
def RuntimePresentation.instantiateRule?
    (presentation : RuntimePresentation)
    (ruleInstance : RuleInstance) : Option (List Pattern × Pattern) :=
  match presentation.lookupRule? ruleInstance.ruleId with
  | none => none
  | some rule =>
      if presentation.argumentsValidAt
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
def RuntimePresentation.checkRaw (presentation : RuntimePresentation) :
    Pattern → RawProof → Bool
  | goal, .node ruleInstance children =>
      match presentation.instantiateRule? ruleInstance with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) &&
            presentation.checkRawChildren premises children
termination_by _ proof => sizeOf proof

def RuntimePresentation.checkRawChildren
    (presentation : RuntimePresentation) :
    List Pattern → List RawProof → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      presentation.checkRaw premise child &&
        presentation.checkRawChildren premises children
  | _, _ => false
termination_by _ children => sizeOf children

end

@[simp] theorem RuntimePresentation.ofPresentation_lookupRule?
    (presentation : Presentation) (id : RuleId) :
    (RuntimePresentation.ofPresentation presentation).lookupRule? id =
      presentation.lookupRule? id := by
  rfl

/-- The closed-payload runtime profile may reject additional articles, but
every argument it admits satisfies the generic checker's binder contract. -/
theorem RuntimePresentation.argumentsValidAt_sound
    (presentation : RuntimePresentation) :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern),
      presentation.argumentsValidAt formals arguments = true →
        InferenceChecker.argumentsValidAt formals arguments = true := by
  intro formals
  induction formals with
  | nil =>
      intro arguments hypothesis
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp [RuntimePresentation.argumentsValidAt] at hypothesis
  | cons formal formals inductionHypothesis =>
      intro arguments hypothesis
      cases arguments with
      | nil =>
          simp [RuntimePresentation.argumentsValidAt] at hypothesis
      | cons argument arguments =>
          simp only [RuntimePresentation.argumentsValidAt,
            RuntimePresentation.argumentValidAt,
            Bool.and_eq_true] at hypothesis
          simp only [InferenceChecker.argumentsValidAt, Bool.and_eq_true]
          exact ⟨hypothesis.1.1,
            inductionHypothesis arguments hypothesis.2⟩

/-- Successful local replay by the closed-payload runtime projection is a
successful application of the original validated presentation. -/
theorem RuntimePresentation.instantiateRule?_sound
    (presentation : ValidatedPresentation) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (hypothesis :
      (RuntimePresentation.ofPresentation presentation.1).instantiateRule?
          ruleInstance = some (premises, conclusion)) :
    InferenceChecker.instantiateRule? presentation ruleInstance =
      some (premises, conclusion) := by
  simp only [RuntimePresentation.instantiateRule?,
    RuntimePresentation.ofPresentation_lookupRule?] at hypothesis
  cases lookup : presentation.1.lookupRule? ruleInstance.ruleId with
  | none => simp [lookup] at hypothesis
  | some rule =>
      rw [lookup] at hypothesis
      cases arguments :
          (RuntimePresentation.ofPresentation presentation.1).argumentsValidAt
            rule.metavariables ruleInstance.arguments with
      | false => simp [arguments] at hypothesis
      | true =>
          have genericArguments :
              InferenceChecker.argumentsValidAt
                  rule.metavariables ruleInstance.arguments = true :=
            RuntimePresentation.argumentsValidAt_sound
              (RuntimePresentation.ofPresentation presentation.1)
              rule.metavariables ruleInstance.arguments arguments
          simpa [InferenceChecker.instantiateRule?, lookup, genericArguments,
            arguments] using hypothesis

mutual

/-- Acceptance by the closed-payload runtime checker refines acceptance by
the generic validated checker. -/
theorem RuntimePresentation.checkRaw_sound
    (presentation : ValidatedPresentation) (goal : Pattern) (proof : RawProof)
    (hypothesis :
      (RuntimePresentation.ofPresentation presentation.1).checkRaw
        goal proof = true) :
    InferenceChecker.checkRaw presentation goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [RuntimePresentation.checkRaw] at hypothesis
      cases localResult :
          (RuntimePresentation.ofPresentation presentation.1).instantiateRule?
            ruleInstance with
      | none => simp [localResult] at hypothesis
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [localResult, Bool.and_eq_true, decide_eq_true_eq]
            at hypothesis
          have logicalResult := RuntimePresentation.instantiateRule?_sound
            presentation ruleInstance premises conclusion localResult
          simp only [InferenceChecker.checkRaw, logicalResult,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hypothesis.1,
            RuntimePresentation.checkRawChildren_sound presentation
              premises children hypothesis.2⟩
termination_by sizeOf proof

theorem RuntimePresentation.checkRawChildren_sound
    (presentation : ValidatedPresentation) (premises : List Pattern)
    (proofs : List RawProof)
    (hypothesis :
      (RuntimePresentation.ofPresentation presentation.1).checkRawChildren
        premises proofs = true) :
    InferenceChecker.checkRawChildren presentation premises proofs = true := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => simp [InferenceChecker.checkRawChildren]
      | cons proof proofs =>
          simp [RuntimePresentation.checkRawChildren] at hypothesis
  | cons premise premises =>
      cases proofs with
      | nil =>
          simp [RuntimePresentation.checkRawChildren] at hypothesis
      | cons proof proofs =>
          simp only [RuntimePresentation.checkRawChildren,
            Bool.and_eq_true] at hypothesis
          simp only [InferenceChecker.checkRawChildren, Bool.and_eq_true]
          exact ⟨RuntimePresentation.checkRaw_sound presentation premise proof
              hypothesis.1,
            RuntimePresentation.checkRawChildren_sound presentation
              premises proofs hypothesis.2⟩
termination_by sizeOf proofs

end

/-- Decode and replay one exact presentation packet.  Malformed packets are
distinguished from rejected proof articles. -/
def checkEncodedPresentation (wire : WireTerm)
    (goal : Pattern) (proof : RawProof) : Option Bool := do
  let presentation ← decodeRuntimePresentation wire
  some (presentation.checkRaw goal proof)

/-- Canonical presentation transport preserves the complete closed-payload
checker result. -/
theorem checkEncodedPresentation_encodeRuntimePresentation
    (presentation : RuntimePresentation)
    (goal : Pattern) (proof : RawProof) :
    checkEncodedPresentation (encodeRuntimePresentation presentation)
        goal proof =
      some (presentation.checkRaw goal proof) := by
  simp [checkEncodedPresentation]

/-- The exact projection of an authored presentation therefore has one
canonical checker result on the wire. -/
theorem checkEncodedPresentation_encodePresentation
    (presentation : Presentation) (goal : Pattern) (proof : RawProof) :
    checkEncodedPresentation (encodePresentation presentation) goal proof =
      some ((RuntimePresentation.ofPresentation presentation).checkRaw
        goal proof) := by
  simp [encodePresentation, checkEncodedPresentation]

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
theorem wrong_presentation_version_rejects :
    decodeRuntimePresentation
      (.list [.symbol "WPresentation", .natural 0,
        .list [], .list [], .list [], .symbol "WNoConversion"]) = none := by
  rfl

end Mettapedia.GSLT.LanguageDef.InferencePresentationWire
