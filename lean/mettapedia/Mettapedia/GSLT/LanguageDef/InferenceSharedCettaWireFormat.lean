import Mettapedia.GSLT.LanguageDef.InferencePatternSharing
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Exact shared-Pattern carrier for NIK proof DAGs

Version 2 of the physical `GProofDAG` carrier factors repeated Pattern
subtrees into one chronological table.  Rule arguments and the submitted
target refer to that table; proof nodes retain the version-1 chronological
edge discipline.  Materialization is an untrusted transport step: the
ordinary admitted ProofGSLT checker still decides acceptance.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.GSLT.LanguageDef.InferencePatternSharing
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.ProofGSLT

def sharedArticleVersion : Nat := 2

def encodeNatList (values : List Nat) : CettaTerm :=
  encodeList CettaTerm.natural values

def decodeNat : CettaTerm → Option Nat
  | .natural value => some value
  | _ => none

def decodeNatList (term : CettaTerm) : Option (List Nat) :=
  decodeList decodeNat term

def encodePatternNodeKey : PatternNodeKey → CettaTerm
  | .bvar index => .application "GPKBVar" [.natural index]
  | .fvar name => .application "GPKFVar" [.string name]
  | .apply head children =>
      .application "GPKApply" [.string head, encodeNatList children]
  | .lambda binder body =>
      .application "GPKLambda" [encodeBinder binder, .natural body]
  | .multiLambda arity binders body =>
      .application "GPKMultiLambda"
        [.natural arity, encodeList CettaTerm.string binders, .natural body]
  | .subst body replacement =>
      .application "GPKSubst" [.natural body, .natural replacement]
  | .collection collectionType elements rest =>
      .application "GPKCollection"
        [encodeCollectionType collectionType, encodeNatList elements,
          encodeRest rest]

def decodePatternNodeKey : CettaTerm → Option PatternNodeKey
  | .application "GPKBVar" [.natural index] => some (.bvar index)
  | .application "GPKFVar" [.string name] => some (.fvar name)
  | .application "GPKApply" [.string head, children] => do
      let decodedChildren ← decodeNatList children
      some (.apply head decodedChildren)
  | .application "GPKLambda" [binder, .natural body] => do
      let decodedBinder ← decodeBinder binder
      some (.lambda decodedBinder body)
  | .application "GPKMultiLambda"
      [.natural arity, binders, .natural body] => do
      let decodedBinders ← decodeList
        (fun term => match term with
          | .string value => some value
          | _ => none) binders
      some (.multiLambda arity decodedBinders body)
  | .application "GPKSubst" [.natural body, .natural replacement] =>
      some (.subst body replacement)
  | .application "GPKCollection" [collectionType, elements, rest] => do
      let decodedType ← decodeCollectionType collectionType
      let decodedElements ← decodeNatList elements
      let decodedRest ← decodeRest rest
      some (.collection decodedType decodedElements decodedRest)
  | _ => none

def encodeSharedPatternNode (node : SharedPatternNode) : CettaTerm :=
  .application "GPatternNode" [.natural node.id, encodePatternNodeKey node.key]

def decodeSharedPatternNode : CettaTerm → Option SharedPatternNode
  | .application "GPatternNode" [.natural id, key] => do
      let decodedKey ← decodePatternNodeKey key
      some ⟨id, decodedKey⟩
  | _ => none

def encodeSharedPatternNodes (nodes : List SharedPatternNode) : CettaTerm :=
  encodeList encodeSharedPatternNode nodes

def decodeSharedPatternNodes (term : CettaTerm) :
    Option (List SharedPatternNode) :=
  decodeList decodeSharedPatternNode term

def encodeReferencedRuleInstance (node : ReferencedDAGNode) : CettaTerm :=
  .application "GRuleRefs"
    [.string node.ruleId.value, encodeNatList node.argumentIds]

def decodeReferencedRuleInstance : CettaTerm → Option (RuleId × List Nat)
  | .application "GRuleRefs" [.string ruleId, arguments] => do
      let decodedArguments ← decodeNatList arguments
      some (⟨ruleId⟩, decodedArguments)
  | _ => none

def encodeProofReferences (children : List Nat) : CettaTerm :=
  encodeList (fun id => CettaTerm.application "GRNode" [.natural id]) children

def decodeProofReference : CettaTerm → Option Nat
  | .application "GRNode" [.natural id] => some id
  | _ => none

def decodeProofReferences (term : CettaTerm) : Option (List Nat) :=
  decodeList decodeProofReference term

def encodeReferencedDAGNode (node : ReferencedDAGNode) : CettaTerm :=
  .application "GDNode"
    [.natural node.id, encodeReferencedRuleInstance node,
      encodeProofReferences node.children]

def decodeReferencedDAGNode : CettaTerm → Option ReferencedDAGNode
  | .application "GDNode" [.natural id, ruleInstance, children] => do
      let (ruleId, argumentIds) ← decodeReferencedRuleInstance ruleInstance
      let decodedChildren ← decodeProofReferences children
      some ⟨id, ruleId, argumentIds, decodedChildren⟩
  | _ => none

def encodeReferencedDAGNodes (nodes : List ReferencedDAGNode) : CettaTerm :=
  encodeList encodeReferencedDAGNode nodes

def decodeReferencedDAGNodes (term : CettaTerm) :
    Option (List ReferencedDAGNode) :=
  decodeList decodeReferencedDAGNode term

structure SharedWireArticle where
  version : Nat
  patterns : List SharedPatternNode
  nodes : List ReferencedDAGNode
  rootId : Nat
  targetId : Nat
deriving DecidableEq, Repr

def encodeSharedWireArticle (article : SharedWireArticle) : CettaTerm :=
  .application "GProofDAG"
    [.natural article.version, encodeSharedPatternNodes article.patterns,
      encodeReferencedDAGNodes article.nodes, .natural article.rootId,
      .natural article.targetId]

def decodeSharedWireArticle : CettaTerm → Option SharedWireArticle
  | .application "GProofDAG"
      [.natural version, patterns, nodes, .natural rootId,
        .natural targetId] => do
      let decodedPatterns ← decodeSharedPatternNodes patterns
      let decodedNodes ← decodeReferencedDAGNodes nodes
      some ⟨version, decodedPatterns, decodedNodes, rootId, targetId⟩
  | _ => none

@[simp] theorem decodeNatList_encodeNatList (values : List Nat) :
    decodeNatList (encodeNatList values) = some values := by
  exact decodeList_encodeList decodeNat CettaTerm.natural
    (fun _ => rfl) values

@[simp] theorem decodePatternNodeKey_encodePatternNodeKey
    (key : PatternNodeKey) :
    decodePatternNodeKey (encodePatternNodeKey key) = some key := by
  cases key <;>
    simp [encodePatternNodeKey, decodePatternNodeKey,
      decodeNatList_encodeNatList, decodeList_encodeList]

@[simp] theorem decodeSharedPatternNode_encodeSharedPatternNode
    (node : SharedPatternNode) :
    decodeSharedPatternNode (encodeSharedPatternNode node) = some node := by
  cases node
  simp [encodeSharedPatternNode, decodeSharedPatternNode]

@[simp] theorem decodeSharedPatternNodes_encodeSharedPatternNodes
    (nodes : List SharedPatternNode) :
    decodeSharedPatternNodes (encodeSharedPatternNodes nodes) = some nodes := by
  exact decodeList_encodeList decodeSharedPatternNode encodeSharedPatternNode
    decodeSharedPatternNode_encodeSharedPatternNode nodes

@[simp] theorem decodeReferencedRuleInstance_encodeReferencedRuleInstance
    (node : ReferencedDAGNode) :
    decodeReferencedRuleInstance (encodeReferencedRuleInstance node) =
      some (node.ruleId, node.argumentIds) := by
  cases node
  simp [encodeReferencedRuleInstance, decodeReferencedRuleInstance]

@[simp] theorem decodeProofReferences_encodeProofReferences
    (children : List Nat) :
    decodeProofReferences (encodeProofReferences children) = some children := by
  exact decodeList_encodeList decodeProofReference
    (fun id => CettaTerm.application "GRNode" [.natural id])
    (fun _ => rfl) children

@[simp] theorem decodeReferencedDAGNode_encodeReferencedDAGNode
    (node : ReferencedDAGNode) :
    decodeReferencedDAGNode (encodeReferencedDAGNode node) = some node := by
  cases node
  simp [encodeReferencedDAGNode, decodeReferencedDAGNode]

@[simp] theorem decodeReferencedDAGNodes_encodeReferencedDAGNodes
    (nodes : List ReferencedDAGNode) :
    decodeReferencedDAGNodes (encodeReferencedDAGNodes nodes) = some nodes := by
  exact decodeList_encodeList decodeReferencedDAGNode encodeReferencedDAGNode
    decodeReferencedDAGNode_encodeReferencedDAGNode nodes

@[simp] theorem decodeSharedWireArticle_encodeSharedWireArticle
    (article : SharedWireArticle) :
    decodeSharedWireArticle (encodeSharedWireArticle article) = some article := by
  cases article
  simp [encodeSharedWireArticle, decodeSharedWireArticle]

theorem encodeSharedWireArticle_injective :
    Function.Injective encodeSharedWireArticle := by
  intro left right equality
  have decoded := congrArg decodeSharedWireArticle equality
  simpa using decoded

def resolvePatternIds (patterns : Array Pattern) :
    List Nat → Option (List Pattern)
  | [] => some []
  | id :: ids => do
      let head ← patterns[id]?
      let tail ← resolvePatternIds patterns ids
      some (head :: tail)

def materializePatternNodeKey? (patterns : Array Pattern) :
    PatternNodeKey → Option Pattern
  | .bvar index => some (.bvar index)
  | .fvar name => some (.fvar name)
  | .apply head children => do
      let arguments ← resolvePatternIds patterns children
      some (.apply head arguments)
  | .lambda binder body => do
      let bodyPattern ← patterns[body]?
      some (.lambda binder bodyPattern)
  | .multiLambda arity binders body => do
      let bodyPattern ← patterns[body]?
      some (.multiLambda arity binders bodyPattern)
  | .subst body replacement => do
      let bodyPattern ← patterns[body]?
      let replacementPattern ← patterns[replacement]?
      some (.subst bodyPattern replacementPattern)
  | .collection collectionType elements rest => do
      let elementPatterns ← resolvePatternIds patterns elements
      some (.collection collectionType elementPatterns rest)

def materializePatternNodesLoop :
    List SharedPatternNode → Nat → Array Pattern → Option (Array Pattern)
  | [], _, patterns => some patterns
  | node :: nodes, nextId, patterns => do
      if node.id != nextId then none
      let pattern ← materializePatternNodeKey? patterns node.key
      materializePatternNodesLoop nodes (nextId + 1) (patterns.push pattern)

def materializePatternNodes (nodes : List SharedPatternNode) :
    Option (Array Pattern) :=
  materializePatternNodesLoop nodes 0 #[]

def materializeReferencedDAGNode? (patterns : Array Pattern)
    (node : ReferencedDAGNode) : Option OpenDAGNode := do
  let arguments ← resolvePatternIds patterns node.argumentIds
  some
    { id := node.id
      ruleInstance := { ruleId := node.ruleId, arguments }
      children := node.children.map OpenDAGReference.node }

def materializeReferencedDAGNodes? (patterns : Array Pattern) :
    List ReferencedDAGNode → Option (List OpenDAGNode)
  | [] => some []
  | node :: nodes => do
      let head ← materializeReferencedDAGNode? patterns node
      let tail ← materializeReferencedDAGNodes? patterns nodes
      some (head :: tail)

def materializeSharedArticle? (article : SharedWireArticle) :
    Option WireArticle := do
  if article.version != sharedArticleVersion then none
  let patterns ← materializePatternNodes article.patterns
  let target ← patterns[article.targetId]?
  let nodes ← materializeReferencedDAGNodes? patterns article.nodes
  some
    { version := wireArticleVersion
      nodes
      rootId := article.rootId
      target }

/-- Decode and materialize the physical article, then invoke the existing
admitted checker.  Sharing never becomes semantic authority. -/
def checkSharedPacket (presentation : ValidatedPresentation)
    (goal : Pattern) (term : CettaTerm) : Bool :=
  match decodeSharedWireArticle term with
  | none => false
  | some shared =>
      match materializeSharedArticle? shared with
      | none => false
      | some article =>
          if article.target = goal then checkWireArticle presentation article
          else false

theorem checkSharedPacket_sound (presentation : ValidatedPresentation)
    (goal : Pattern) (term : CettaTerm)
    (accepted : checkSharedPacket presentation goal term = true) :
    Nonempty (Derivation presentation goal) := by
  simp only [checkSharedPacket] at accepted
  split at accepted <;> rename_i decoded
  · contradiction
  · split at accepted <;> rename_i materialized
    · contradiction
    · split at accepted <;> rename_i target
      · subst goal
        exact checkWireArticle_sound accepted
      · contradiction

private def fixtureLeaf : Pattern := .apply "K" []
private def fixturePair : Pattern := .apply "Pair" [fixtureLeaf, fixtureLeaf]

private def fixturePatternNodes : List SharedPatternNode :=
  [⟨0, .apply "K" []⟩, ⟨1, .apply "Pair" [0, 0]⟩]

example : materializePatternNodes fixturePatternNodes =
    some #[fixtureLeaf, fixturePair] := by rfl

example : materializePatternNodes
    [⟨0, .apply "Pair" [1, 1]⟩] = none := by rfl

example (article : SharedWireArticle)
    (wrongVersion : article.version != sharedArticleVersion) :
    materializeSharedArticle? article = none := by
  simp [materializeSharedArticle?, wrongVersion]

end Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWire
