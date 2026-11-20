import Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
import Mettapedia.GSLT.LanguageDef.InferenceRuntimeAdequacy
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker
import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Exact CeTTa carrier for inference languages and articles

The generic inference checker already has a canonical symbolic `WireTerm`
carrier.  CeTTa consumes a distinct MeTTa-shaped carrier: quoted strings are
different from symbols, lists are encoded by `LNil`/`LCons`, and inference
packages use the `GInferenceLanguageV1` and `GProof` constructors.

Authored rule codecs also retain local dependency contexts, indexed occurrences,
all premise forms and contextual values. Their data round trips grant no
execution permissions.

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

/-- Canonical pattern rows use the shared ordered algebraic-list carrier. -/
theorem encodePatterns_eq_encodeList (patterns : List Pattern) :
    encodePatterns patterns =
      Mettapedia.GSLT.LanguageDef.CettaWire.encodeList encodePattern patterns := by
  induction patterns with
  | nil => simp [encodePatterns, Mettapedia.GSLT.LanguageDef.CettaWire.encodeList]
  | cons pattern patterns ih =>
      simp [encodePatterns, Mettapedia.GSLT.LanguageDef.CettaWire.encodeList, ih]

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
references remain different constructors, even though closed SemanticService articles can
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

/-! ## Open trees over the same physical certificate carrier -/

mutual
  /-- Local hypotheses add one occurrence constructor to the existing proof wire. -/
  def encodeOpenProof : RawOpenProof → CettaTerm
    | .premise index => .application "GOpenHyp" [.natural index]
    | .node ruleInstance children =>
        .application "GProof" [encodeRuleInstance ruleInstance, encodeOpenProofs children]
  termination_by proof => sizeOf proof

  def encodeOpenProofs : List RawOpenProof → CettaTerm
    | [] => .symbol "PrNil"
    | first :: rest => .application "PrCons" [encodeOpenProof first, encodeOpenProofs rest]
  termination_by proofs => sizeOf proofs
end

mutual
  def decodeOpenProof : CettaTerm → Option RawOpenProof
    | .application "GOpenHyp" [.natural index] => some (.premise index)
    | .application "GProof" [ruleInstance, children] => do
        let decoded ← decodeRuleInstance ruleInstance
        let premises ← decodeOpenProofs children
        pure (.node decoded premises)
    | _ => none
  termination_by wire => sizeOf wire

  def decodeOpenProofs : CettaTerm → Option (List RawOpenProof)
    | .symbol "PrNil" => some []
    | .application "PrCons" [first, rest] => do
        let proof ← decodeOpenProof first
        let proofs ← decodeOpenProofs rest
        pure (proof :: proofs)
    | _ => none
  termination_by wire => sizeOf wire
end

mutual
  @[simp] theorem decodeOpenProof_encodeOpenProof (proof : RawOpenProof) :
      decodeOpenProof (encodeOpenProof proof) = some proof := by
    cases proof with
    | premise index => simp [encodeOpenProof, decodeOpenProof]
    | node ruleInstance children =>
        simp [encodeOpenProof, decodeOpenProof, decodeOpenProofs_encodeOpenProofs children]
  termination_by sizeOf proof

  @[simp] theorem decodeOpenProofs_encodeOpenProofs (proofs : List RawOpenProof) :
      decodeOpenProofs (encodeOpenProofs proofs) = some proofs := by
    cases proofs with
    | nil => simp [encodeOpenProofs, decodeOpenProofs]
    | cons first rest =>
        simp [encodeOpenProofs, decodeOpenProofs, decodeOpenProof_encodeOpenProof first,
          decodeOpenProofs_encodeOpenProofs rest]
  termination_by sizeOf proofs
end

theorem open_hypothesis_requires_natural :
    decodeOpenProof (.application "GOpenHyp" [.string "0"]) = none := by
  simp [decodeOpenProof]

theorem open_hypothesis_is_not_a_rule :
    decodeRawProof (encodeOpenProof (.premise 0)) = none := by
  simp [decodeRawProof, encodeOpenProof]

open Mettapedia.OSLF.MeTTaIL.RuleBinding

/-! ## Exact authored rule and occurrence contexts

The executable first-order projection has five rewrite fields. Scoped rules
need the original sixth field as well: dependency contexts and every occurrence
substitution. This data boundary retains all premise forms and Pattern nodes;
decoding data grants no execution or rewriting permission.
-/

namespace AuthoredRule

/-- The quote scope of a presentation: `QuoteClosed`, or `QuoteReaching` with a
view `QuoteApply`, `QuoteFreeze` with its spelling, or `QuoteClosure` with its
context constructor. -/
def quoteScopeTerm : QuoteScope → CettaTerm
  | .closed => .symbol "QuoteClosed"
  | .reaching .apply => .application "QuoteReaching" [.symbol "QuoteApply"]
  | .reaching (.freeze frozen) =>
      .application "QuoteReaching" [.application "QuoteFreeze" [encodePattern frozen.spelling]]
  | .reaching (.closure context) =>
      .application "QuoteReaching" [.application "QuoteClosure" [.string context]]

def decodeQuoteScope? : CettaTerm → Option QuoteScope
  | .symbol "QuoteClosed" => some .closed
  | .application "QuoteReaching" [.symbol "QuoteApply"] => some (.reaching .apply)
  | .application "QuoteReaching" [.application "QuoteFreeze" [spelling]] =>
      match decodePattern spelling with
      | some pattern =>
          if ground : pattern.freeFvarNames = [] ∧ pattern.isWellScopedAt 0 = true then
            some (.reaching (.freeze ⟨pattern, ground⟩))
          else none
      | none => none
  | .application "QuoteReaching" [.application "QuoteClosure" [.string context]] =>
      some (.reaching (.closure context))
  | _ => none

@[simp] theorem decodeQuoteScope?_quoteScopeTerm (scope : QuoteScope) :
    decodeQuoteScope? (quoteScopeTerm scope) = some scope := by
  rcases scope with _ | (_ | ⟨spelling, ground⟩ | context)
  · simp [quoteScopeTerm, decodeQuoteScope?]
  · simp [quoteScopeTerm, decodeQuoteScope?]
  · simp [quoteScopeTerm, decodeQuoteScope?, decodePattern_encodePattern, ground]
  · simp [quoteScopeTerm, decodeQuoteScope?]

/-- Reflective presentation data retain every authored constructor and equation
name and the quote scope. This codec supplies data; it does not license a
binder operation. -/
def reflectivePresentationTerm (declaration : ReflectivePresentationDecl) : CettaTerm :=
  .application "ReflectivePresentation" [.string declaration.name, .string declaration.processSort,
    .string declaration.nameSort, .string declaration.quoteConstructor, .string declaration.dropConstructor,
    encodeCollectionType declaration.parallelCollection,
    .string declaration.parallelUnitConstructor, .string declaration.quoteDropEquation,
    quoteScopeTerm declaration.quoteScope]

def decodeReflectivePresentation? : CettaTerm → Option ReflectivePresentationDecl
  | .application "ReflectivePresentation" [.string name, .string processSort, .string nameSort,
      .string quoteConstructor, .string dropConstructor, parallelCollection,
      .string parallelUnitConstructor, .string quoteDropEquation, quoteScope] => do
      pure ⟨name, processSort, nameSort, quoteConstructor, dropConstructor,
        ← decodeCollectionType parallelCollection, parallelUnitConstructor, quoteDropEquation,
        ← decodeQuoteScope? quoteScope⟩
  | _ => none

@[simp] theorem decodeReflectivePresentation?_reflectivePresentationTerm
    (declaration : ReflectivePresentationDecl) :
    decodeReflectivePresentation? (reflectivePresentationTerm declaration) = some declaration := by
  cases declaration
  simp [reflectivePresentationTerm, decodeReflectivePresentation?]

theorem reflectivePresentationTerm_injective : Function.Injective reflectivePresentationTerm := by
  intro left right same
  have decoded := congrArg decodeReflectivePresentation? same
  simpa only [decodeReflectivePresentation?_reflectivePresentationTerm, Option.some.injEq] using decoded

example : decodeReflectivePresentation? (.application "ReflectivePresentation" []) = none := rfl

def typeTerm : TypeExpr → CettaTerm
  | .base name => .application "TBase" [.string name]
  | .arrow domain codomain => .application "TArrow" [typeTerm domain, typeTerm codomain]
  | .multiBinder body => .application "TMultiBinder" [typeTerm body]
  | .collection kind element =>
      .application "TCollection" [encodeCollectionType kind, typeTerm element]

def decodeType? : CettaTerm → Option TypeExpr
  | .application "TBase" [.string name] => some (.base name)
  | .application "TArrow" [domain, codomain] => do
      pure (.arrow (← decodeType? domain) (← decodeType? codomain))
  | .application "TMultiBinder" [body] => do
      pure (.multiBinder (← decodeType? body))
  | .application "TCollection" [kind, element] => do
      pure (.collection (← decodeCollectionType kind) (← decodeType? element))
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeType?_typeTerm (type : TypeExpr) :
    decodeType? (typeTerm type) = some type := by
  induction type with
  | base name => simp [typeTerm, decodeType?]
  | arrow domain codomain hd hc => simp [typeTerm, decodeType?, hd, hc]
  | multiBinder body ih => simp [typeTerm, decodeType?, ih]
  | collection kind element ih => simp [typeTerm, decodeType?, ih]


/-- Lossless constructor-parameter data. The simple case uses the established
first-order tag; binder cases retain authored display names and body names. -/
def parameterTerm : TermParam → CettaTerm
  | .simple name type => .application "TermSimple" [.string name, typeTerm type]
  | .abstractionNamed binder name type =>
      .application "TermAbstraction" [encodeBinder binder, .string name, typeTerm type]
  | .multiAbstractionNamed binders name type =>
      .application "TermMultiAbstraction" [encodeList .string binders, .string name, typeTerm type]

def decodeParameter? : CettaTerm → Option TermParam
  | .application "TermSimple" [.string name, type] => do
      pure (.simple name (← decodeType? type))
  | .application "TermAbstraction" [binder, .string name, type] => do
      pure (.abstractionNamed (← decodeBinder binder) name (← decodeType? type))
  | .application "TermMultiAbstraction" [binders, .string name, type] => do
      let names ← decodeList
        (fun term => match term with | .string name => some name | _ => none) binders
      pure (.multiAbstractionNamed names name (← decodeType? type))
  | _ => none

@[simp] theorem decodeParameter?_parameterTerm (parameter : TermParam) :
    decodeParameter? (parameterTerm parameter) = some parameter := by
  cases parameter with
  | simple name type => simp [parameterTerm, decodeParameter?]
  | abstractionNamed binder name type => simp [parameterTerm, decodeParameter?]
  | multiAbstractionNamed binders name type =>
      simp only [parameterTerm, decodeParameter?, decodeType?_typeTerm]
      have names : decodeList
          (fun term => match term with | .string name => some name | _ => none)
          (encodeList CettaTerm.string binders) = some binders :=
        decodeList_encodeList
          (fun term => match term with | .string name => some name | _ => none)
          CettaTerm.string (fun (name : String) => rfl) binders
      rw [names]
      rfl

theorem parameterTerm_injective : Function.Injective parameterTerm := by
  intro first second same
  have decoded := congrArg decodeParameter? same
  simpa only [decodeParameter?_parameterTerm, Option.some.injEq] using decoded

/-- The native typing view retains the collection representation. The
existing bare packet and the wrapped packet have distinct tags. -/
def typingDeclarationTerm (declaration : GrammarRule) : CettaTerm :=
  .application
    (match declaration.collectionRepresentation with
     | .bare => "GrammarTypingV1"
     | .wrapped => "GrammarTypingWrappedV1")
    [.string declaration.label, .string declaration.category, encodeList parameterTerm declaration.params]

def decodeTypingDeclaration? : CettaTerm → Option (String × String × List TermParam × CollectionRepresentation)
  | .application "GrammarTypingV1" [.string label, .string category, parameters] => do
      pure (label, category, ← decodeList decodeParameter? parameters, .bare)
  | .application "GrammarTypingWrappedV1" [.string label, .string category, parameters] => do
      pure (label, category, ← decodeList decodeParameter? parameters, .wrapped)
  | _ => none

@[simp] theorem decodeTypingDeclaration?_typingDeclarationTerm (declaration : GrammarRule) :
    decodeTypingDeclaration? (typingDeclarationTerm declaration) =
      some (declaration.label, declaration.category, declaration.params, declaration.collectionRepresentation) := by
  cases mode : declaration.collectionRepresentation <;>
    simp [typingDeclarationTerm, decodeTypingDeclaration?, decodeList_encodeList, mode]

/-- A change in representation cannot disappear in the native typing view. -/
theorem typing_representation_distinct (declaration : GrammarRule) :
    typingDeclarationTerm { declaration with collectionRepresentation := .bare } ≠
      typingDeclarationTerm { declaration with collectionRepresentation := .wrapped } := by
  simp [typingDeclarationTerm]

#print axioms decodeTypingDeclaration?_typingDeclarationTerm

namespace ParameterControls

theorem authored_names_retained :
    parameterTerm (.multiAbstractionNamed ["x", "y"] "body" (.base "Expr")) =
      .application "TermMultiAbstraction"
        [encodeList .string ["x", "y"], .string "body", .application "TBase" [.string "Expr"]] := rfl

theorem missing_binder_field_refused :
    decodeParameter? (.application "TermAbstraction"
      [.string "body", .application "TBase" [.string "Expr"]]) = none := rfl

theorem symbolic_binder_name_refused :
    decodeParameter? (.application "TermMultiAbstraction"
      [encodeList .symbol ["x"], .string "body", .application "TBase" [.string "Expr"]]) = none := by
  decide +kernel

end ParameterControls

#print axioms decodeParameter?_parameterTerm
#print axioms parameterTerm_injective
#print axioms ParameterControls.authored_names_retained
#print axioms ParameterControls.missing_binder_field_refused
#print axioms ParameterControls.symbolic_binder_name_refused

def siteTerm : RulePatternSite → CettaTerm
  | .left => .symbol "RuleLeft"
  | .right => .symbol "RuleRight"
  | .premise index quantifiers argument =>
      .application "RulePremise" [.natural index, .natural quantifiers, .natural argument]

def decodeSite? : CettaTerm → Option RulePatternSite
  | .symbol "RuleLeft" => some .left
  | .symbol "RuleRight" => some .right
  | .application "RulePremise" [.natural index, .natural quantifiers, .natural argument] =>
      some (.premise index quantifiers argument)
  | _ => none

@[simp] theorem decodeSite?_siteTerm (site : RulePatternSite) :
    decodeSite? (siteTerm site) = some site := by
  cases site <;> rfl

private def decodeNatural? : CettaTerm → Option Nat
  | .natural value => some value
  | _ => none

def occurrenceTerm (occurrence : MetavariableOccurrence) : CettaTerm :=
  .application "RuleOccurrence"
    [.string occurrence.name, siteTerm occurrence.site,
      encodeList .natural occurrence.path, encodePatterns occurrence.arguments]

def decodeOccurrence? : CettaTerm → Option MetavariableOccurrence
  | .application "RuleOccurrence" [.string name, site, path, arguments] => do
      pure ⟨name, ← decodeSite? site, ← decodeList decodeNatural? path,
        ← decodePatterns arguments⟩
  | _ => none

@[simp] theorem decodeOccurrence?_occurrenceTerm (occurrence : MetavariableOccurrence) :
    decodeOccurrence? (occurrenceTerm occurrence) = some occurrence := by
  rcases occurrence with ⟨name, site, path, arguments⟩
  have decodedPath : decodeList decodeNatural? (encodeList CettaTerm.natural path) = some path :=
    decodeList_encodeList decodeNatural? CettaTerm.natural (fun _ => rfl) path
  simp [occurrenceTerm, decodeOccurrence?, decodedPath]

def dependencyTerm (dependency : String × List TypeExpr) : CettaTerm :=
  .application "RuleDependency" [.string dependency.1, encodeList typeTerm dependency.2]

def decodeDependency? : CettaTerm → Option (String × List TypeExpr)
  | .application "RuleDependency" [.string name, sorts] => do
      pure (name, ← decodeList decodeType? sorts)
  | _ => none

@[simp] theorem decodeDependency?_dependencyTerm (dependency : String × List TypeExpr) :
    decodeDependency? (dependencyTerm dependency) = some dependency := by
  cases dependency
  simp [dependencyTerm, decodeDependency?, decodeList_encodeList]

def bindingSpecTerm (spec : RuleBindingSpec) : CettaTerm :=
  .application "RuleBindingSpec"
    [encodeList dependencyTerm spec.dependencies, encodeList occurrenceTerm spec.occurrences]

def decodeBindingSpec? : CettaTerm → Option RuleBindingSpec
  | .application "RuleBindingSpec" [dependencies, occurrences] => do
      pure ⟨← decodeList decodeDependency? dependencies,
        ← decodeList decodeOccurrence? occurrences⟩
  | _ => none

@[simp] theorem decodeBindingSpec?_bindingSpecTerm (spec : RuleBindingSpec) :
    decodeBindingSpec? (bindingSpecTerm spec) = some spec := by
  cases spec
  simp [bindingSpecTerm, decodeBindingSpec?, decodeList_encodeList]

def optionalBindingTerm : Option RuleBindingSpec → CettaTerm
  | none => .symbol "RuleBindingNone"
  | some spec => .application "RuleBindingSome" [bindingSpecTerm spec]

def decodeOptionalBinding? : CettaTerm → Option (Option RuleBindingSpec)
  | .symbol "RuleBindingNone" => some none
  | .application "RuleBindingSome" [spec] => do
      pure (some (← decodeBindingSpec? spec))
  | _ => none

@[simp] theorem decodeOptionalBinding?_optionalBindingTerm (spec : Option RuleBindingSpec) :
    decodeOptionalBinding? (optionalBindingTerm spec) = some spec := by
  cases spec <;> simp [optionalBindingTerm, decodeOptionalBinding?]

def typeBindingTerm (binding : String × TypeExpr) : CettaTerm :=
  .application "TypeBinding" [.string binding.1, typeTerm binding.2]

def decodeTypeBinding? : CettaTerm → Option (String × TypeExpr)
  | .application "TypeBinding" [.string name, sort] => do
      pure (name, ← decodeType? sort)
  | _ => none

@[simp] theorem decodeTypeBinding?_typeBindingTerm (binding : String × TypeExpr) :
    decodeTypeBinding? (typeBindingTerm binding) = some binding := by
  cases binding
  simp [typeBindingTerm, decodeTypeBinding?]

def premiseTerm : Premise → CettaTerm
  | .freshness condition =>
      .application "Freshness" [.string condition.varName, encodePattern condition.term]
  | .congruence source target =>
      .application "Congruence" [encodePattern source, encodePattern target]
  | .scopedStep step =>
      .application "ScopedStep" [encodeList typeTerm step.binders, typeTerm step.resultType,
        encodePattern step.source, encodePattern step.target]
  | .relationQuery relation arguments =>
      .application "RelationQuery" [.string relation, encodePatterns arguments]
  | .forAll collection parameter body =>
      .application "ForAll" [.string collection, .string parameter, premiseTerm body]

def decodePremise? : CettaTerm → Option Premise
  | .application "Freshness" [.string name, pattern] => do
      pure (.freshness ⟨name, ← decodePattern pattern⟩)
  | .application "Congruence" [source, target] => do
      pure (.congruence (← decodePattern source) (← decodePattern target))
  | .application "ScopedStep" [binders, sort, source, target] => do
      pure (.scopedStep ⟨← decodeList decodeType? binders, ← decodeType? sort,
        ← decodePattern source, ← decodePattern target⟩)
  | .application "RelationQuery" [.string relation, arguments] => do
      pure (.relationQuery relation (← decodePatterns arguments))
  | .application "ForAll" [.string collection, .string parameter, body] => do
      pure (.forAll collection parameter (← decodePremise? body))
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodePremise?_premiseTerm (premise : Premise) :
    decodePremise? (premiseTerm premise) = some premise := by
  induction premise with
  | freshness condition => cases condition; simp [premiseTerm, decodePremise?]
  | congruence source target => simp [premiseTerm, decodePremise?]
  | scopedStep step => cases step; simp [premiseTerm, decodePremise?, decodeList_encodeList]
  | relationQuery relation arguments => simp [premiseTerm, decodePremise?]
  | forAll collection parameter body ih => simp [premiseTerm, decodePremise?, ih]

def rewriteTerm (rule : RewriteRule) : CettaTerm :=
  .application "ScopedRewriteRuleV1" [.string rule.name,
    encodeList typeBindingTerm rule.typeContext, encodeList premiseTerm rule.premises,
    encodePattern rule.left, encodePattern rule.right, optionalBindingTerm rule.bindings]

def decodeRewrite? : CettaTerm → Option RewriteRule
  | .application "ScopedRewriteRuleV1" [.string name, context, premises, left, right, bindings] => do
      pure ⟨name, ← decodeList decodeTypeBinding? context, ← decodeList decodePremise? premises,
        ← decodePattern left, ← decodePattern right, ← decodeOptionalBinding? bindings⟩
  | _ => none

@[simp] theorem decodeRewrite?_rewriteTerm (rule : RewriteRule) :
    decodeRewrite? (rewriteTerm rule) = some rule := by
  cases rule
  simp [rewriteTerm, decodeRewrite?, decodeList_encodeList]

/-- The wire preserves the whole source rule, rather than just its matching shape. -/
theorem rewriteTerm_injective : Function.Injective rewriteTerm := by
  intro first second same
  have decoded := congrArg decodeRewrite? same
  simpa using decoded

theorem bindingSpecTerm_injective : Function.Injective bindingSpecTerm := by
  intro first second same
  have decoded := congrArg decodeBindingSpec? same
  simpa using decoded

theorem occurrenceTerm_injective : Function.Injective occurrenceTerm := by
  intro first second same
  have decoded := congrArg decodeOccurrence? same
  simpa using decoded

def contextualValueTerm (value : ContextualValue) : CettaTerm :=
  .application "ContextualValue"
    [encodeList typeTerm value.dependencies, .natural value.ambient, encodePattern value.body]

def decodeContextualValue? : CettaTerm → Option ContextualValue
  | .application "ContextualValue" [dependencies, .natural ambient, body] => do
      pure ⟨← decodeList decodeType? dependencies, ambient, ← decodePattern body⟩
  | _ => none

@[simp] theorem decodeContextualValue?_contextualValueTerm (value : ContextualValue) :
    decodeContextualValue? (contextualValueTerm value) = some value := by
  cases value
  simp [contextualValueTerm, decodeContextualValue?, decodeList_encodeList]

theorem contextualValueTerm_injective : Function.Injective contextualValueTerm := by
  intro first second same
  have decoded := congrArg decodeContextualValue? same
  simpa using decoded

namespace Controls

def annotatedRule : RewriteRule where
  name := "preserve-occurrence-contexts"
  typeContext := [("body", .arrow (.base "Name") (.base "Proc"))]
  premises := [.forAll "parts" "part" (.scopedStep
    ⟨[.base "Name"], .base "Proc", .fvar "body", .fvar "part"⟩)]
  left := .multiLambda 1 ["display"] (.fvar "body")
  right := .lambda "display" (.subst (.bvar 1) (.bvar 0))
  bindings := some
    ⟨[("body", [.base "Name"])],
      [⟨"body", .left, [0], [.bvar 0]⟩,
       ⟨"body", .premise 0 1 0, [], [.bvar 0]⟩]⟩

theorem annotated_round_trip : decodeRewrite? (rewriteTerm annotatedRule) = some annotatedRule :=
  decodeRewrite?_rewriteTerm annotatedRule

theorem omitted_binding_metadata_changes_wire :
    rewriteTerm annotatedRule ≠ rewriteTerm { annotatedRule with bindings := none } := by
  intro same
  have ruleSame := rewriteTerm_injective same
  have bindingSame := congrArg RewriteRule.bindings ruleSame
  cases bindingSame

theorem changed_occurrence_site_changes_wire :
    occurrenceTerm ⟨"body", .premise 0 1 0, [], [.bvar 0]⟩ ≠
      occurrenceTerm ⟨"body", .premise 0 0 0, [], [.bvar 0]⟩ := by
  intro same
  have occurrenceSame := occurrenceTerm_injective same
  have siteSame := congrArg MetavariableOccurrence.site occurrenceSame
  cases siteSame

theorem textual_occurrence_index_refused :
    decodeSite? (.application "RulePremise" [.string "0", .natural 1, .natural 0]) = none := by
  rfl

theorem five_field_rule_is_not_scoped_data :
    decodeRewrite? (.application "RewriteRule" [.string "name", .symbol "LNil", .symbol "LNil",
      encodePattern (.fvar "left"), encodePattern (.fvar "right")]) = none := by
  rfl

theorem improper_dependency_list_refused :
    decodeBindingSpec? (.application "RuleBindingSpec" [.symbol "Broken", .symbol "LNil"]) = none := by
  simp [decodeBindingSpec?, decodeList, Mettapedia.GSLT.LanguageDef.CettaWire.decodeList]

theorem contextual_ambient_is_not_dependency_count :
    contextualValueTerm ⟨[.base "Name"], 0, .bvar 0⟩ ≠
      contextualValueTerm ⟨[], 1, .bvar 0⟩ := by
  intro same
  have valueSame := contextualValueTerm_injective same
  have dependencySame := congrArg ContextualValue.dependencies valueSame
  cases dependencySame

end Controls

#print axioms decodeType?_typeTerm
#print axioms decodeSite?_siteTerm
#print axioms decodeOccurrence?_occurrenceTerm
#print axioms decodeBindingSpec?_bindingSpecTerm
#print axioms decodePremise?_premiseTerm
#print axioms decodeRewrite?_rewriteTerm
#print axioms rewriteTerm_injective
#print axioms contextualValueTerm_injective
#print axioms Controls.annotated_round_trip
#print axioms Controls.omitted_binding_metadata_changes_wire
#print axioms Controls.changed_occurrence_site_changes_wire
#print axioms Controls.textual_occurrence_index_refused
#print axioms Controls.five_field_rule_is_not_scoped_data
#print axioms Controls.improper_dependency_list_refused
#print axioms Controls.contextual_ambient_is_not_dependency_count

end AuthoredRule

end Mettapedia.GSLT.LanguageDef.InferenceCettaWire

namespace Mettapedia.GSLT.LanguageDef.InferenceCettaWire.ContextObservation

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites

def booleanTerm (value : Bool) : CettaTerm :=
  if value then .symbol "PermissionYes" else .symbol "PermissionNo"

def decodeBoolean? : CettaTerm → Option Bool
  | .symbol "PermissionYes" => some true
  | .symbol "PermissionNo" => some false
  | _ => none

@[simp] theorem decodeBoolean?_booleanTerm (value : Bool) :
    decodeBoolean? (booleanTerm value) = some value := by
  cases value <;> rfl

def slotTerm (slot : String × Nat) : CettaTerm :=
  .application "TermSlot" [.string slot.1, .natural slot.2]

def decodeSlot? : CettaTerm → Option (String × Nat)
  | .application "TermSlot" [.string constructor, .natural index] => some (constructor, index)
  | _ => none

@[simp] theorem decodeSlot?_slotTerm (slot : String × Nat) :
    decodeSlot? (slotTerm slot) = some slot := by
  cases slot
  rfl

/-- Explicit execution capabilities have their own lossless observation.
The authored rule does not manufacture this separately supplied authority. -/
def permissionsTerm (permissions : OperationalPermissions) : CettaTerm :=
  .application "OperationalPermissions"
    [booleanTerm permissions.enabled, booleanTerm permissions.allConstructorArguments,
      encodeList slotTerm permissions.constructorArguments,
      booleanTerm permissions.underLambda, booleanTerm permissions.underMultiLambda,
      encodeList encodeCollectionType permissions.collectionKinds]

def decodePermissions? : CettaTerm → Option OperationalPermissions
  | .application "OperationalPermissions" [enabled, all, slots, lam, multi, kinds] => do
      pure ⟨← decodeBoolean? enabled, ← decodeBoolean? all, ← decodeList decodeSlot? slots,
        ← decodeBoolean? lam, ← decodeBoolean? multi,
        ← decodeList decodeCollectionType kinds⟩
  | _ => none

@[simp] theorem decodePermissions?_permissionsTerm (permissions : OperationalPermissions) :
    decodePermissions? (permissionsTerm permissions) = some permissions := by
  cases permissions
  simp [permissionsTerm, decodePermissions?, decodeList_encodeList]

theorem permissionsTerm_injective : Function.Injective permissionsTerm := by
  intro left right same
  simpa using congrArg decodePermissions? same

/-- Encode the original structural zipper, including binder display metadata,
ordered siblings, collection rest metadata and explicit-substitution frames. -/
def contextTerm : OneHoleContext → CettaTerm
  | .hole => .symbol "ContextHole"
  | .apply constructor before inner after =>
      .application "ContextApp"
        [.string constructor, encodePatterns before, contextTerm inner, encodePatterns after]
  | .lambda binder inner => .application "ContextLam" [encodeBinder binder, contextTerm inner]
  | .multiLambda arity binders inner =>
      .application "ContextMultiLam" [.natural arity, encodeList CettaTerm.string binders, contextTerm inner]
  | .substBody inner replacement =>
      .application "ContextSubstBody" [contextTerm inner, encodePattern replacement]
  | .substReplacement body inner =>
      .application "ContextSubstReplacement" [encodePattern body, contextTerm inner]
  | .collection kind before inner after rest =>
      .application "ContextCollection"
        [encodeCollectionType kind, encodePatterns before, contextTerm inner, encodePatterns after, encodeRest rest]

def decodeContext? : CettaTerm → Option OneHoleContext
  | .symbol "ContextHole" => some .hole
  | .application "ContextApp" [.string constructor, before, inner, after] => do
      pure (.apply constructor (← decodePatterns before) (← decodeContext? inner) (← decodePatterns after))
  | .application "ContextLam" [binder, inner] => do
      pure (.lambda (← decodeBinder binder) (← decodeContext? inner))
  | .application "ContextMultiLam" [.natural arity, binders, inner] => do
      pure (.multiLambda arity (← decodeList (fun term => match term with
        | .string name => some name | _ => none) binders) (← decodeContext? inner))
  | .application "ContextSubstBody" [inner, replacement] => do
      pure (.substBody (← decodeContext? inner) (← decodePattern replacement))
  | .application "ContextSubstReplacement" [body, inner] => do
      pure (.substReplacement (← decodePattern body) (← decodeContext? inner))
  | .application "ContextCollection" [kind, before, inner, after, rest] => do
      pure (.collection (← decodeCollectionType kind) (← decodePatterns before)
        (← decodeContext? inner) (← decodePatterns after) (← decodeRest rest))
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeContext?_contextTerm (context : OneHoleContext) :
    decodeContext? (contextTerm context) = some context := by
  induction context <;> simp [contextTerm, decodeContext?, *, decodeList_encodeList]

theorem contextTerm_injective : Function.Injective contextTerm := by
  intro left right same
  simpa using congrArg decodeContext? same

/-- Public observation of an existing occurrence. Both rule positions and the
actual typed-site address remain distinct data; the rule uses the six-field
authored codec and the separately supplied permission is retained in full. -/
def focusObservationTerm (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) : CettaTerm :=
  .application "ScopedFocusObservation"
    [.natural ordinal, .natural declarationIndex, AuthoredRule.rewriteTerm rule,
      permissionsTerm permissions, encodeList CettaTerm.natural address, contextTerm context,
      encodePattern source, encodePattern target,
      encodePattern (context.fill source), encodePattern (context.fill target)]

def focusObservationOptionTerm (ordinal declarationIndex : Nat) (rule : RewriteRule)
    (permissions : OperationalPermissions) (address : List Nat)
    (context : OneHoleContext) (source target : Pattern) : CettaTerm :=
  if permissions.permitsContext context then
    .application "Some" [focusObservationTerm ordinal declarationIndex rule permissions address context source target]
  else .symbol "None"

theorem focusObservation_retains_origins
    {ordinal declarationIndex otherOrdinal otherDeclarationIndex : Nat}
    {rule otherRule : RewriteRule} {permissions otherPermissions : OperationalPermissions}
    {address otherAddress : List Nat} {context otherContext : OneHoleContext}
    {source target otherSource otherTarget : Pattern}
    (same : focusObservationTerm ordinal declarationIndex rule permissions address context source target =
      focusObservationTerm otherOrdinal otherDeclarationIndex otherRule otherPermissions
        otherAddress otherContext otherSource otherTarget) :
    ordinal = otherOrdinal ∧ declarationIndex = otherDeclarationIndex ∧ rule = otherRule ∧
      permissions = otherPermissions ∧ address = otherAddress ∧ context = otherContext ∧
      source = otherSource ∧ target = otherTarget := by
  have fields := (Mettapedia.GSLT.LanguageDef.CettaWire.Term.application.inj same).2
  have head := List.cons.inj fields
  have original := List.cons.inj head.2
  have authored := List.cons.inj original.2
  have capability := List.cons.inj authored.2
  have position := List.cons.inj capability.2
  have zipper := List.cons.inj position.2
  have before := List.cons.inj zipper.2
  have after := List.cons.inj before.2
  refine ⟨Mettapedia.GSLT.LanguageDef.CettaWire.Term.natural.inj head.1,
    Mettapedia.GSLT.LanguageDef.CettaWire.Term.natural.inj original.1,
    AuthoredRule.rewriteTerm_injective authored.1, permissionsTerm_injective capability.1,
    ?_, contextTerm_injective zipper.1,
    encodePattern_injective before.1, encodePattern_injective after.1⟩
  have decoded := congrArg (decodeList (fun term => match term with
    | .natural index => some index | _ => none)) position.1
  simpa [decodeList_encodeList] using decoded

namespace Controls

theorem malformed_permission_field_refused :
    decodePermissions? (.application "OperationalPermissions"
      [.symbol "True", booleanTerm false, .symbol "LNil", booleanTerm true, booleanTerm false, .symbol "LNil"]) = none := by
  rfl

theorem omitted_permission_field_refused :
    decodePermissions? (.application "OperationalPermissions"
      [booleanTerm true, booleanTerm false, .symbol "LNil", booleanTerm true, .symbol "LNil"]) = none := by
  rfl

theorem sibling_order_changes_context_wire :
    contextTerm (.apply "Pair" [.bvar 0, .bvar 1] .hole []) ≠
      contextTerm (.apply "Pair" [.bvar 1, .bvar 0] .hole []) := by
  intro same
  have recovered := contextTerm_injective same
  cases recovered

theorem compressed_binder_metadata_retained :
    decodeContext? (contextTerm (.apply "Binder" [] (.multiLambda 3 ["x", "y", "z"] .hole) [])) =
      some (.apply "Binder" [] (.multiLambda 3 ["x", "y", "z"] .hole) []) ∧
      contextTerm (.multiLambda 3 ["x", "y", "z"] .hole) ≠ contextTerm (.multiLambda 2 ["x", "y"] .hole) := by
  refine ⟨decodeContext?_contextTerm _, ?_⟩
  intro same
  have recovered := contextTerm_injective same
  cases recovered

end Controls

end Mettapedia.GSLT.LanguageDef.InferenceCettaWire.ContextObservation
