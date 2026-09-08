import Mettapedia.GSLT.LanguageDef.InferenceRuntimeAdequacy
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Exact CeTTa carrier for inference languages and articles

The generic inference checker already has a canonical symbolic `WireTerm`
carrier.  CeTTa consumes a distinct MeTTa-shaped carrier: quoted strings are
different from symbols, lists are encoded by `LNil`/`LCons`, and inference
packages use the `GInferenceLanguageV1` and `GProof` constructors.

This module instantiates the shared physical carrier with total canonical
encoders, fail-closed decoders, and round-trip theorems for inference data.
Both the logical `WInferenceLanguage` carrier and the CeTTa carrier decode to
the same `RuntimeInferenceLanguage`; the bridge theorem below therefore states
their exact semantic relationship without identifying their different
syntaxes.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceCettaWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

/-! ## Shared physical carrier and algebraic-list compatibility surface -/

abbrev CettaTerm := Mettapedia.GSLT.LanguageDef.CettaWire.Term

namespace CettaTerm

abbrev symbol := Mettapedia.GSLT.LanguageDef.CettaWire.Term.symbol
abbrev string := Mettapedia.GSLT.LanguageDef.CettaWire.Term.string
abbrev natural := Mettapedia.GSLT.LanguageDef.CettaWire.Term.natural
abbrev application := Mettapedia.GSLT.LanguageDef.CettaWire.Term.application
abbrev render := Mettapedia.GSLT.LanguageDef.CettaWire.Term.render

end CettaTerm

def encodeList (encode : α → CettaTerm) (values : List α) : CettaTerm :=
  Mettapedia.GSLT.LanguageDef.CettaWire.encodeList encode values

def decodeList (decode : CettaTerm → Option α)
    (term : CettaTerm) : Option (List α) :=
  Mettapedia.GSLT.LanguageDef.CettaWire.decodeList decode term

theorem decodeList_encodeList (decode : CettaTerm → Option α)
    (encode : α → CettaTerm)
    (roundTrip : ∀ value, decode (encode value) = some value)
    (values : List α) :
    decodeList decode (encodeList encode values) = some values :=
  Mettapedia.GSLT.LanguageDef.CettaWire.decodeList_encodeList
    decode encode roundTrip values

/-! ## Exact Pattern carrier -/

def encodeBinder : Option String → CettaTerm
  | none => .symbol "BNone"
  | some name => .application "BSome" [.string name]

def decodeBinder : CettaTerm → Option (Option String)
  | .symbol "BNone" => some none
  | .application "BSome" [.string name] => some (some name)
  | _ => none

def encodeRest : Option String → CettaTerm
  | none => .symbol "RNone"
  | some name => .application "RSome" [.string name]

def decodeRest : CettaTerm → Option (Option String)
  | .symbol "RNone" => some none
  | .application "RSome" [.string name] => some (some name)
  | _ => none

def encodeCollectionType : CollType → CettaTerm
  | .vec =>
      .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec"
  | .hashBag =>
      .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag"
  | .hashSet =>
      .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet"

def decodeCollectionType : CettaTerm → Option CollType
  | .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" => some .vec
  | .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" =>
      some .hashBag
  | .string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet" =>
      some .hashSet
  | _ => none

mutual

def encodePattern : Pattern → CettaTerm
  | .bvar index => .application "Var" [.natural index]
  | .fvar name => .application "FVar" [.string name]
  | .apply head arguments =>
      .application "PApp" [.string head, encodePatterns arguments]
  | .lambda binder body =>
      .application "PLam" [encodeBinder binder, encodePattern body]
  | .multiLambda arity binders body =>
      .application "PMultiLam"
        [.natural arity, encodeList CettaTerm.string binders,
          encodePattern body]
  | .subst body replacement =>
      .application "PSubst"
        [encodePattern body, encodePattern replacement]
  | .collection collectionType elements rest =>
      .application "PCollection"
        [encodeCollectionType collectionType, encodePatterns elements,
          encodeRest rest]
termination_by pattern => sizeOf pattern

def encodePatterns : List Pattern → CettaTerm
  | [] => .symbol "LNil"
  | pattern :: patterns =>
      .application "LCons" [encodePattern pattern, encodePatterns patterns]
termination_by patterns => sizeOf patterns

end

mutual

def decodePattern : CettaTerm → Option Pattern
  | .application "Var" [.natural index] => some (.bvar index)
  | .application "FVar" [.string name] => some (.fvar name)
  | .application "PApp" [.string head, arguments] => do
      let decodedArguments ← decodePatterns arguments
      some (.apply head decodedArguments)
  | .application "PLam" [binder, body] => do
      let decodedBinder ← decodeBinder binder
      let decodedBody ← decodePattern body
      some (.lambda decodedBinder decodedBody)
  | .application "PMultiLam" [.natural arity, binders, body] => do
      let decodedBinders ← decodeList
        (fun term => match term with
          | .string value => some value
          | _ => none) binders
      let decodedBody ← decodePattern body
      some (.multiLambda arity decodedBinders decodedBody)
  | .application "PSubst" [body, replacement] => do
      let decodedBody ← decodePattern body
      let decodedReplacement ← decodePattern replacement
      some (.subst decodedBody decodedReplacement)
  | .application "PCollection" [collectionType, elements, rest] => do
      let decodedType ← decodeCollectionType collectionType
      let decodedElements ← decodePatterns elements
      let decodedRest ← decodeRest rest
      some (.collection decodedType decodedElements decodedRest)
  | _ => none
termination_by term => sizeOf term

def decodePatterns : CettaTerm → Option (List Pattern)
  | .symbol "LNil" => some []
  | .application "LCons" [pattern, patterns] => do
      let decodedPattern ← decodePattern pattern
      let decodedPatterns ← decodePatterns patterns
      some (decodedPattern :: decodedPatterns)
  | _ => none
termination_by term => sizeOf term

end

@[simp] theorem decodeBinder_encodeBinder (binder : Option String) :
    decodeBinder (encodeBinder binder) = some binder := by
  cases binder <;> rfl

@[simp] theorem decodeRest_encodeRest (rest : Option String) :
    decodeRest (encodeRest rest) = some rest := by
  cases rest <;> rfl

@[simp] theorem decodeCollectionType_encodeCollectionType
    (collectionType : CollType) :
    decodeCollectionType (encodeCollectionType collectionType) =
      some collectionType := by
  cases collectionType <;> simp [encodeCollectionType, decodeCollectionType]

mutual

@[simp] theorem decodePattern_encodePattern (pattern : Pattern) :
    decodePattern (encodePattern pattern) = some pattern := by
  cases pattern with
  | bvar index => simp [encodePattern, decodePattern]
  | fvar name => simp [encodePattern, decodePattern]
  | apply head arguments =>
      simp [encodePattern, decodePattern,
        decodePatterns_encodePatterns arguments]
  | lambda binder body =>
      simp [encodePattern, decodePattern, decodePattern_encodePattern body]
  | multiLambda arity binders body =>
      simp [encodePattern, decodePattern, decodeList_encodeList,
        decodePattern_encodePattern body]
  | subst body replacement =>
      simp [encodePattern, decodePattern,
        decodePattern_encodePattern body,
        decodePattern_encodePattern replacement]
  | collection collectionType elements rest =>
      simp [encodePattern, decodePattern,
        decodePatterns_encodePatterns elements]

@[simp] theorem decodePatterns_encodePatterns (patterns : List Pattern) :
    decodePatterns (encodePatterns patterns) = some patterns := by
  cases patterns with
  | nil => simp [encodePatterns, decodePatterns]
  | cons pattern patterns =>
      simp [encodePatterns, decodePatterns, decodePattern_encodePattern,
        decodePatterns_encodePatterns]

end

/-- Canonical Pattern encoding is collision-free. -/
theorem encodePattern_injective : Function.Injective encodePattern := by
  intro left right equality
  have decoded := congrArg decodePattern equality
  simpa using decoded

/-- Canonical ordered Pattern-list encoding is collision-free. -/
theorem encodePatterns_injective : Function.Injective encodePatterns := by
  intro left right equality
  have decoded := congrArg decodePatterns equality
  simpa using decoded

/-! ## Exact definition carrier -/

def encodeConstructor (declaration : ConstructorSignature) : CettaTerm :=
  .application "CDecl"
    [.string declaration.head, .natural declaration.arity]

def decodeConstructor : CettaTerm → Option ConstructorSignature
  | .application "CDecl" [.string head, .natural arity] =>
      some ⟨head, arity⟩
  | _ => none

def encodeJudgment (declaration : JudgmentDecl) : CettaTerm :=
  .application "JDecl" [.string declaration.head, .natural declaration.arity]

def decodeJudgment : CettaTerm → Option JudgmentDecl
  | .application "JDecl" [.string head, .natural arity] =>
      some ⟨head, arity⟩
  | _ => none

def encodeFormal (formal : String × Nat) : CettaTerm :=
  .application "Formal" [.string formal.1, .natural formal.2]

def decodeFormal : CettaTerm → Option (String × Nat)
  | .application "Formal" [.string name, .natural depth] =>
      some (name, depth)
  | _ => none

def encodeSideCondition : RuleSideCondition → CettaTerm
  | .explicitSubstitution ambientDepth bodyArgument replacementArgument
      resultArgument =>
      .application "GExplicitSubstitution"
        [.natural ambientDepth, .natural bodyArgument,
          .natural replacementArgument, .natural resultArgument]
  | .unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      .application "GUnusedBinderElimination"
        [.natural ambientDepth, .natural bodyArgument,
          .natural resultArgument]

def decodeSideCondition : CettaTerm → Option RuleSideCondition
  | .application "GExplicitSubstitution"
      [.natural ambientDepth, .natural bodyArgument,
        .natural replacementArgument, .natural resultArgument] =>
      some (.explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument)
  | .application "GUnusedBinderElimination"
      [.natural ambientDepth, .natural bodyArgument,
        .natural resultArgument] =>
      some (.unusedBinderElimination ambientDepth bodyArgument resultArgument)
  | _ => none

def encodeRule (rule : RuleSchema) : CettaTerm :=
  .application "GRuleV1"
    [.string rule.id.value,
      encodeList encodeFormal rule.metavariables,
      encodePatterns rule.premises,
      encodePattern rule.conclusion,
      encodeList encodeSideCondition rule.sideConditions]

def decodeRule : CettaTerm → Option RuleSchema
  | .application "GRuleV1"
      [.string id, formals, premises, conclusion, sideConditions] => do
      let decodedFormals ← decodeList decodeFormal formals
      let decodedPremises ← decodePatterns premises
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

def encodeConversion : Option ConversionDecl → CettaTerm
  | none => .symbol "GNoConversion"
  | some declaration =>
      .application "GConversion"
        [.string declaration.judgmentHead, .string declaration.version]

def decodeConversion : CettaTerm → Option (Option ConversionDecl)
  | .symbol "GNoConversion" => some none
  | .application "GConversion"
      [.string judgmentHead, .string version] =>
      some (some ⟨judgmentHead, version⟩)
  | _ => none

def encodeRuntimeInferenceLanguage
    (definition : RuntimeInferenceLanguage) : CettaTerm :=
  .application "GInferenceLanguageV1"
    [.natural inferenceLanguageWireVersion,
      encodeList encodeConstructor definition.constructors,
      encodeList encodeJudgment definition.judgments,
      encodeList encodeRule definition.rules,
      encodeConversion definition.conversion]

def encodeDefinition (definition : CalculusLanguageDef) : CettaTerm :=
  encodeRuntimeInferenceLanguage (RuntimeInferenceLanguage.ofDefinition definition)

def decodeRuntimeInferenceLanguage : CettaTerm → Option RuntimeInferenceLanguage
  | .application "GInferenceLanguageV1"
      [.natural version, constructors, judgments, rules, conversion] => do
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
  simp [encodeRule, decodeRule, decodeList_encodeList]

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
    inferenceLanguageWireVersion, decodeList_encodeList]

@[simp] theorem decodeRuntimeInferenceLanguage_encodeDefinition
    (definition : CalculusLanguageDef) :
    decodeRuntimeInferenceLanguage (encodeDefinition definition) =
      some (RuntimeInferenceLanguage.ofDefinition definition) := by
  simp [encodeDefinition]

theorem encodeRuntimeInferenceLanguage_injective :
    Function.Injective encodeRuntimeInferenceLanguage := by
  intro left right equality
  have decoded := congrArg decodeRuntimeInferenceLanguage equality
  simpa using decoded

/-! ## Exact proof-tree carrier -/

def encodeRuleInstance (ruleInstance : RuleInstance) : CettaTerm :=
  .application "GRuleInst"
    [.string ruleInstance.ruleId.value,
      encodePatterns ruleInstance.arguments]

def decodeRuleInstance : CettaTerm → Option RuleInstance
  | .application "GRuleInst" [.string ruleId, arguments] => do
      let decodedArguments ← decodePatterns arguments
      some ⟨⟨ruleId⟩, decodedArguments⟩
  | _ => none

mutual

def encodeRawProof : RawProof → CettaTerm
  | .node ruleInstance children =>
      .application "GProof"
        [encodeRuleInstance ruleInstance, encodeProofs children]
termination_by proof => sizeOf proof

def encodeProofs : List RawProof → CettaTerm
  | [] => .symbol "PrNil"
  | proof :: proofs =>
      .application "PrCons" [encodeRawProof proof, encodeProofs proofs]
termination_by proofs => sizeOf proofs

end

mutual

def decodeRawProof : CettaTerm → Option RawProof
  | .application "GProof" [ruleInstance, children] => do
      let decodedInstance ← decodeRuleInstance ruleInstance
      let decodedChildren ← decodeProofs children
      some (.node decodedInstance decodedChildren)
  | _ => none
termination_by term => sizeOf term

def decodeProofs : CettaTerm → Option (List RawProof)
  | .symbol "PrNil" => some []
  | .application "PrCons" [proof, proofs] => do
      let decodedProof ← decodeRawProof proof
      let decodedProofs ← decodeProofs proofs
      some (decodedProof :: decodedProofs)
  | _ => none
termination_by term => sizeOf term

end


@[simp] theorem decodeRuleInstance_encodeRuleInstance
    (ruleInstance : RuleInstance) :
    decodeRuleInstance (encodeRuleInstance ruleInstance) =
      some ruleInstance := by
  cases ruleInstance
  simp [encodeRuleInstance, decodeRuleInstance]

mutual

@[simp] theorem decodeRawProof_encodeRawProof (proof : RawProof) :
    decodeRawProof (encodeRawProof proof) = some proof := by
  cases proof with
  | node ruleInstance children =>
      simp [encodeRawProof, decodeRawProof,
        decodeProofs_encodeProofs children]

@[simp] theorem decodeProofs_encodeProofs (proofs : List RawProof) :
    decodeProofs (encodeProofs proofs) = some proofs := by
  cases proofs with
  | nil => simp [encodeProofs, decodeProofs]
  | cons proof proofs =>
      simp [encodeProofs, decodeProofs, decodeRawProof_encodeRawProof,
        decodeProofs_encodeProofs]

end


theorem encodeRawProof_injective : Function.Injective encodeRawProof := by
  intro left right equality
  have decoded := congrArg decodeRawProof equality
  simpa using decoded

/-! ## Exact chronological CertificateGSLT article carrier -/

/-- Physical encoding of one ordered open-DAG edge.  Premise and node
references remain different constructors, even though closed NIK articles can
only discharge node references. -/
def encodeDAGReference : OpenDAGReference → CettaTerm
  | .premise index => .application "GRPremise" [.natural index]
  | .node id => .application "GRNode" [.natural id]

def decodeDAGReference : CettaTerm → Option OpenDAGReference
  | .application "GRPremise" [.natural index] => some (.premise index)
  | .application "GRNode" [.natural id] => some (.node id)
  | _ => none

def encodeDAGReferences (references : List OpenDAGReference) : CettaTerm :=
  encodeList encodeDAGReference references

def decodeDAGReferences (term : CettaTerm) :
    Option (List OpenDAGReference) :=
  decodeList decodeDAGReference term

/-- Physical chronological node.  The ordinary `GRuleInst` carrier is shared
with tree articles; only the child-edge carrier differs. -/
def encodeOpenDAGNode (node : OpenDAGNode) : CettaTerm :=
  .application "GDNode"
    [.natural node.id, encodeRuleInstance node.ruleInstance,
      encodeDAGReferences node.children]

def decodeOpenDAGNode : CettaTerm → Option OpenDAGNode
  | .application "GDNode" [.natural id, ruleInstance, children] => do
      let decodedRuleInstance ← decodeRuleInstance ruleInstance
      let decodedChildren ← decodeDAGReferences children
      some ⟨id, decodedRuleInstance, decodedChildren⟩
  | _ => none

def encodeOpenDAGNodes (nodes : List OpenDAGNode) : CettaTerm :=
  encodeList encodeOpenDAGNode nodes

def decodeOpenDAGNodes (term : CettaTerm) : Option (List OpenDAGNode) :=
  decodeList decodeOpenDAGNode term

/-- The physical CeTTa image of the logical `WireArticle`.  Version, selected
root, and target remain explicit and are rechecked by `checkWireArticle`. -/
def encodeWireArticle (article : WireArticle) : CettaTerm :=
  .application "GProofDAG"
    [.natural article.version, encodeOpenDAGNodes article.nodes,
      .natural article.rootId, encodePattern article.target]

def decodeWireArticle : CettaTerm → Option WireArticle
  | .application "GProofDAG" [.natural version, nodes, .natural rootId,
      target] => do
      let decodedNodes ← decodeOpenDAGNodes nodes
      let decodedTarget ← decodePattern target
      some ⟨version, decodedNodes, rootId, decodedTarget⟩
  | _ => none

@[simp] theorem decodeDAGReference_encodeDAGReference
    (reference : OpenDAGReference) :
    decodeDAGReference (encodeDAGReference reference) = some reference := by
  cases reference <;> rfl

@[simp] theorem decodeDAGReferences_encodeDAGReferences
    (references : List OpenDAGReference) :
    decodeDAGReferences (encodeDAGReferences references) = some references := by
  exact decodeList_encodeList decodeDAGReference encodeDAGReference
    decodeDAGReference_encodeDAGReference references

@[simp] theorem decodeOpenDAGNode_encodeOpenDAGNode (node : OpenDAGNode) :
    decodeOpenDAGNode (encodeOpenDAGNode node) = some node := by
  cases node
  simp [encodeOpenDAGNode, decodeOpenDAGNode]

@[simp] theorem decodeOpenDAGNodes_encodeOpenDAGNodes
    (nodes : List OpenDAGNode) :
    decodeOpenDAGNodes (encodeOpenDAGNodes nodes) = some nodes := by
  exact decodeList_encodeList decodeOpenDAGNode encodeOpenDAGNode
    decodeOpenDAGNode_encodeOpenDAGNode nodes

@[simp] theorem decodeWireArticle_encodeWireArticle (article : WireArticle) :
    decodeWireArticle (encodeWireArticle article) = some article := by
  cases article
  simp [encodeWireArticle, decodeWireArticle]

theorem encodeWireArticle_injective : Function.Injective encodeWireArticle := by
  intro left right equality
  have decoded := congrArg decodeWireArticle equality
  simpa using decoded

/-- Decode the physical article and invoke the exact logical CertificateGSLT
checker.  This function performs no proof search and preserves sharing. -/
def checkDAGPacket (definition : ValidatedCalculusLanguageDef)
    (articleTerm : CettaTerm) : Bool :=
  match decodeWireArticle articleTerm with
  | some article => checkWireArticle definition article
  | none => false

@[simp] theorem checkDAGPacket_encode (definition : ValidatedCalculusLanguageDef)
    (article : WireArticle) :
    checkDAGPacket definition (encodeWireArticle article) =
      checkWireArticle definition article := by
  simp [checkDAGPacket]

theorem checkDAGPacket_encode_sound (definition : ValidatedCalculusLanguageDef)
    (article : WireArticle)
    (accepted :
      checkDAGPacket definition (encodeWireArticle article) = true) :
    Nonempty (Derivation definition article.target) := by
  exact checkWireArticle_sound (by simpa using accepted)

/-! ## Checker and logical-wire refinement -/

/-- Decode all three CeTTa-facing inputs and replay the exact checker. -/
def checkPacket (languageTerm goalTerm proofTerm : CettaTerm) :
    Option Bool := do
  let definition ← decodeRuntimeInferenceLanguage languageTerm
  let goal ← decodePattern goalTerm
  let proof ← decodeRawProof proofTerm
  some (definition.checkRaw goal proof)

@[simp] theorem checkPacket_encode
    (definition : RuntimeInferenceLanguage) (goal : Pattern) (proof : RawProof) :
    checkPacket (encodeRuntimeInferenceLanguage definition)
        (encodePattern goal) (encodeRawProof proof) =
      some (definition.checkRaw goal proof) := by
  simp [checkPacket]

/-- An accepted canonical CeTTa packet denotes a typed derivation under the
authored validated definition, and that derivation erases to the identical
raw article.  The runtime profile is deliberately stricter about constructor
vocabulary, so no unrestricted converse is asserted. -/
theorem checkPacket_encode_acceptance_sound
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (proof : RawProof)
    (hypothesis :
      checkPacket
          (encodeRuntimeInferenceLanguage
            (RuntimeInferenceLanguage.ofDefinition definition.1))
          (encodePattern goal) (encodeRawProof proof) = some true) :
    ∃ derivation : Derivation definition goal,
      derivation.erase = proof := by
  have runtimeAccepted :
      (RuntimeInferenceLanguage.ofDefinition definition.1).checkRaw
          goal proof = true := by
    simpa using hypothesis
  have logicalAccepted := RuntimeInferenceLanguage.checkRaw_sound definition
    goal proof runtimeAccepted
  exact G2_checkRaw_iff_exists_derivation_erases_to.mp logicalAccepted

/-- For an article whose proof arguments are closed under the catalog's
constructor vocabulary, the canonical CeTTa packet is accepted exactly when
it denotes a typed derivation with the identical raw erasure. -/
theorem checkPacket_encode_adequate_of_payloadsValid
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (proof : RawProof)
    (payloadValid :
      (RuntimeInferenceLanguage.ofDefinition definition.1).proofPayloadsValid
        proof = true) :
    checkPacket
          (encodeRuntimeInferenceLanguage
            (RuntimeInferenceLanguage.ofDefinition definition.1))
          (encodePattern goal) (encodeRawProof proof) = some true ↔
      ∃ derivation : Derivation definition goal,
        derivation.erase = proof := by
  constructor
  · exact checkPacket_encode_acceptance_sound definition goal proof
  · rintro ⟨derivation, erases⟩
    have genericAccepted :
        InferenceChecker.checkRaw definition goal proof = true := by
      rw [← erases]
      exact checkRaw_erase derivation
    have runtimeAccepted :=
      RuntimeInferenceLanguage.checkRaw_complete
        definition goal proof genericAccepted payloadValid
    rw [checkPacket_encode]
    exact congrArg some runtimeAccepted

/-- Project a physical CeTTa definition to the canonical logical carrier.
Malformed physical packets have no logical interpretation. -/
def toLogicalLanguage? (term : CettaTerm) : Option WireTerm := do
  let definition ← decodeRuntimeInferenceLanguage term
  some (InferenceLanguageWire.encodeRuntimeInferenceLanguage definition)

@[simp] theorem toLogicalLanguage_encodeRuntimeInferenceLanguage
    (definition : RuntimeInferenceLanguage) :
    toLogicalLanguage? (encodeRuntimeInferenceLanguage definition) =
      some (InferenceLanguageWire.encodeRuntimeInferenceLanguage
        definition) := by
  simp [toLogicalLanguage?]

/-- Both exact carriers replay the same checker because they decode to the
same checker projection. -/
theorem physical_and_logical_check_agree
    (definition : RuntimeInferenceLanguage) (goal : Pattern) (proof : RawProof) :
    checkPacket (encodeRuntimeInferenceLanguage definition)
        (encodePattern goal) (encodeRawProof proof) =
      InferenceLanguageWire.checkEncodedLanguage
        (InferenceLanguageWire.encodeRuntimeInferenceLanguage definition)
        goal proof := by
  rw [checkPacket_encode,
    InferenceLanguageWire.checkEncodedLanguage_encodeRuntimeInferenceLanguage]

/-! ## Negative carrier canaries -/

theorem wrong_version_rejects :
    decodeRuntimeInferenceLanguage
      (.application "GInferenceLanguageV1"
        [.natural 0, .symbol "LNil", .symbol "LNil", .symbol "LNil",
          .symbol "GNoConversion"]) = none := by
  rfl

/-- A constructor name is a quoted string in the physical ABI, not a symbol. -/
theorem unquoted_constructor_rejects :
    decodeConstructor (.application "CDecl" [.symbol "C", .natural 0]) =
      none := by
  rfl

/-- Side conditions are mandatory fields of every version-one rule. -/
theorem missing_side_condition_field_rejects :
    decodeRule
      (.application "GRuleV1"
        [.string "r", .symbol "LNil", .symbol "LNil",
          .application "PApp" [.string "J", .symbol "LNil"]]) = none := by
  rfl

/-- A version not admitted by the logical article ABI remains rejected through
the physical CeTTa carrier. -/
theorem dag_wrong_version_rejects (definition : ValidatedCalculusLanguageDef)
    (article : WireArticle) (wrong : article.version ≠ wireArticleVersion) :
    checkDAGPacket definition (encodeWireArticle article) = false := by
  rw [checkDAGPacket_encode]
  exact checkWireArticle_version_gate wrong

/-- A node-reference constructor cannot be silently reinterpreted as a premise
reference. -/
theorem dag_reference_kinds_are_distinct (id : Nat) :
    decodeDAGReference (encodeDAGReference (.node id)) ≠
      some (.premise id) := by
  simp

end Mettapedia.GSLT.LanguageDef.InferenceCettaWire
