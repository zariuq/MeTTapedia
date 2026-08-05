import Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation

/-!
# Shared pattern transport for inference proof DAGs

Large first-order derivations often repeat the same ground pattern in many
rule instances.  This module hash-conses every pattern subtree and serializes
rule arguments as references to shared MeTTa definitions.  The definitions
expand to the ordinary `Pattern` syntax before the generic inference checker
sees a rule instance.  Sharing is therefore an untrusted transport
optimization: acceptance still depends on the existing source-indexed
checker, not on this compiler.
-/

namespace Mettapedia.GSLT.LanguageDef.InferencePatternSharing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation

/-- One pattern constructor after its recursive children have been interned. -/
inductive PatternNodeKey where
  | bvar (index : Nat)
  | fvar (name : String)
  | apply (head : String) (children : List Nat)
  | lambda (binder : Option String) (body : Nat)
  | multiLambda (arity : Nat) (binders : List String) (body : Nat)
  | subst (body replacement : Nat)
  | collection
      (collectionType : CollType) (elements : List Nat)
      (rest : Option String)
deriving DecidableEq, Hashable, Repr

/-- A chronological shared-pattern node.  Every referenced child has a
strictly smaller identifier. -/
structure SharedPatternNode where
  id : Nat
  key : PatternNodeKey
deriving DecidableEq, Repr

structure PatternSharingState where
  nextId : Nat := 0
  known : Std.HashMap PatternNodeKey Nat := {}
  nodesRev : List SharedPatternNode := []

mutual

/-- Intern one pattern bottom-up. -/
def internPattern : Pattern → StateM PatternSharingState Nat
  | .bvar index => internPatternKey (.bvar index)
  | .fvar name => internPatternKey (.fvar name)
  | .apply head arguments => do
      let children ← internPatterns arguments
      internPatternKey (.apply head children)
  | .lambda binder body => do
      let bodyId ← internPattern body
      internPatternKey (.lambda binder bodyId)
  | .multiLambda arity binders body => do
      let bodyId ← internPattern body
      internPatternKey (.multiLambda arity binders bodyId)
  | .subst body replacement => do
      let bodyId ← internPattern body
      let replacementId ← internPattern replacement
      internPatternKey (.subst bodyId replacementId)
  | .collection collectionType elements rest => do
      let elementIds ← internPatterns elements
      internPatternKey (.collection collectionType elementIds rest)
termination_by pattern => 2 * sizeOf pattern
decreasing_by all_goals simp_wf <;> omega

/-- Intern an ordered pattern vector. -/
def internPatterns : List Pattern → StateM PatternSharingState (List Nat)
  | [] => pure []
  | pattern :: patterns => do
      let id ← internPattern pattern
      let ids ← internPatterns patterns
      pure (id :: ids)
termination_by patterns => 2 * sizeOf patterns + 1

/-- Reuse an existing node or append one fresh chronological node. -/
def internPatternKey (key : PatternNodeKey) :
    StateM PatternSharingState Nat := do
  let state ← get
  match state.known.get? key with
  | some existingId => pure existingId
  | none =>
      let freshId := state.nextId
      set
        ({ nextId := freshId + 1
           known := state.known.insert key freshId
           nodesRev := { id := freshId, key } :: state.nodesRev } :
          PatternSharingState)
      pure freshId

end

/-- A proof-DAG node whose rule arguments are shared-pattern identifiers. -/
structure ReferencedDAGNode where
  id : Nat
  ruleId : RuleId
  argumentIds : List Nat
  children : List Nat
deriving DecidableEq, Repr

/-- One proof DAG after its argument patterns have been shared. -/
structure ReferencedProofDAG where
  rootId : Nat
  nodes : List ReferencedDAGNode
deriving DecidableEq, Repr

/-- One referenced proof node with its checked post-node release list. -/
structure ReferencedStreamingDAGNode where
  node : ReferencedDAGNode
  releases : List Nat
deriving DecidableEq, Repr

/-- A referenced proof DAG annotated with an untrusted liveness schedule. -/
structure ReferencedStreamingProofDAG where
  rootId : Nat
  nodes : List ReferencedStreamingDAGNode
deriving DecidableEq, Repr

/-- Two proof DAGs sharing one common pattern table. -/
structure SharedProofDAGPair where
  patterns : List SharedPatternNode
  left : ReferencedProofDAG
  right : ReferencedProofDAG
deriving DecidableEq, Repr

private def referenceDAGNode (node : DAGNode) :
    StateM PatternSharingState ReferencedDAGNode := do
  let argumentIds ← internPatterns node.ruleInstance.arguments
  pure
    { id := node.id
      ruleId := node.ruleInstance.ruleId
      argumentIds
      children := node.children }

private def referenceDAGNodes :
    List DAGNode → StateM PatternSharingState (List ReferencedDAGNode)
  | [] => pure []
  | node :: nodes => do
      let referenced ← referenceDAGNode node
      let rest ← referenceDAGNodes nodes
      pure (referenced :: rest)

private def referenceProofDAG (proof : CompiledProofDAG) :
    StateM PatternSharingState ReferencedProofDAG := do
  let nodes ← referenceDAGNodes proof.nodes
  pure { rootId := proof.rootId, nodes }

/-- Share every pattern subtree across two already-compiled proof DAGs. -/
def shareProofDAGPair
    (left right : CompiledProofDAG) : SharedProofDAGPair :=
  let ((leftReferenced, rightReferenced), state) :=
    (do
      let leftReferenced ← referenceProofDAG left
      let rightReferenced ← referenceProofDAG right
      pure (leftReferenced, rightReferenced)).run {}
  { patterns := state.nodesRev.reverse
    left := leftReferenced
    right := rightReferenced }

/-- Count every remaining chronological child use. -/
private def childUseCounts
    (nodes : List ReferencedDAGNode) : Std.HashMap Nat Nat :=
  nodes.foldl
    (fun counts node =>
      node.children.foldl
        (fun counts child =>
          let count := (counts.get? child).getD 0
          counts.insert child (count + 1))
        counts)
    {}

/-- Consume one child occurrence and emit its identifier exactly when that
occurrence is its final use. -/
private def consumeChildUse
    (state : Std.HashMap Nat Nat × List Nat) (child : Nat) :
    Std.HashMap Nat Nat × List Nat :=
  let (counts, releasesRev) := state
  match counts.get? child with
  | some 1 => (counts.erase child, child :: releasesRev)
  | some count => (counts.insert child (count - 1), releasesRev)
  | none => (counts, releasesRev)

private def annotateStreamingNodesLoop :
    List ReferencedDAGNode → Std.HashMap Nat Nat →
      List ReferencedStreamingDAGNode →
      List ReferencedStreamingDAGNode
  | [], _, annotatedRev => annotatedRev.reverse
  | node :: nodes, counts, annotatedRev =>
      let (remaining, releasesRev) :=
        node.children.foldl consumeChildUse (counts, [])
      annotateStreamingNodesLoop nodes remaining
        ({ node, releases := releasesRev.reverse } :: annotatedRev)

/-- Compute a final-use schedule for a referenced chronological proof DAG.
The schedule is an optimization hint only: the streaming checker validates
every release and rejects any later reference to an entry released too soon. -/
def annotateStreamingProofDAG
    (proof : ReferencedProofDAG) : ReferencedStreamingProofDAG :=
  { rootId := proof.rootId
    nodes :=
      annotateStreamingNodesLoop proof.nodes (childUseCounts proof.nodes) [] }

private def patternReference (stem : String) (id : Nat) : String :=
  s!"({stem}-{id})"

private def renderResolvedReferenceList
    (resolve : Nat → String) : List Nat → String
  | [] => "LNil"
  | id :: ids =>
      s!"(LCons {resolve id} {renderResolvedReferenceList resolve ids})"

private def renderReferenceList (stem : String) : List Nat → String :=
  renderResolvedReferenceList (patternReference stem)

private def renderOptionalBinder : Option String → String
  | none => "BNone"
  | some name => s!"(BSome {quote name})"

private def renderOptionalRest : Option String → String
  | none => "RNone"
  | some name => s!"(RSome {quote name})"

private def renderPatternNodeValueWith
    (resolve : Nat → String) : PatternNodeKey → String
  | .bvar index => s!"(Var {index})"
  | .fvar name => s!"(FVar {quote name})"
  | .apply head children =>
      s!"(PApp {quote head} {renderResolvedReferenceList resolve children})"
  | .lambda binder body =>
      s!"(PLam {renderOptionalBinder binder} {resolve body})"
  | .multiLambda arity binders body =>
      s!"(PMultiLam {arity} {renderList quote binders} " ++
        s!"{resolve body})"
  | .subst body replacement =>
      s!"(PSubst {resolve body} {resolve replacement})"
  | .collection collectionType elements rest =>
      s!"(PCollection {quote (reprStr collectionType)} " ++
        s!"{renderResolvedReferenceList resolve elements} " ++
        s!"{renderOptionalRest rest})"

private def renderPatternNodeValue
    (stem : String) (key : PatternNodeKey) : String :=
  renderPatternNodeValueWith (patternReference stem) key

/-- Expand a bounded number of pattern-DAG levels.  A missing identifier
renders an inert constructor that the ordinary inference checker rejects. -/
private def renderPatternAtDepth
    (table : Array SharedPatternNode) (stem : String) :
    Nat → Nat → String
  | 0, id => patternReference stem id
  | depth + 1, id =>
      match table[id]? with
      | some node =>
          renderPatternNodeValueWith
            (renderPatternAtDepth table stem depth) node.key
      | none => s!"(MissingSharedPattern {id})"

/-- Render one ordinary MeTTa definition for a shared pattern subtree. -/
def renderPatternDefinition
    (stem : String) (node : SharedPatternNode) : String :=
  s!"(= ({stem}-{node.id}) {renderPatternNodeValue stem node.key})"

/-- Render chronological shared-pattern definitions. -/
def renderPatternDefinitions
    (stem : String) (nodes : List SharedPatternNode) : String :=
  String.intercalate "\n" (nodes.map (renderPatternDefinition stem))

/-- Render definitions with bounded local expansion.  Depth one is the
ordinary shared representation.  Larger depths trade modest textual
duplication for a shallower evaluator call chain without changing the
expanded pattern supplied to the checker. -/
def renderPatternDefinitionsExpanded
    (expansionDepth : Nat) (stem : String)
    (nodes : List SharedPatternNode) : String :=
  let table := nodes.toArray
  let depth := max expansionDepth 1
  String.intercalate "\n" <|
    nodes.map fun node =>
      s!"(= ({stem}-{node.id}) " ++
        s!"{renderPatternAtDepth table stem depth node.id})"

private def renderReferencedRuleInstance
    (stem : String) (node : ReferencedDAGNode) : String :=
  s!"(GRuleInst {quote node.ruleId.value} " ++
    s!"{renderReferenceList stem node.argumentIds})"

/-- Serialize one proof-DAG node with shared-pattern rule arguments. -/
def renderReferencedDAGNode
    (stem : String) (node : ReferencedDAGNode) : String :=
  s!"(GDNode {node.id} {renderReferencedRuleInstance stem node} " ++
    s!"{renderChildIds node.children})"

def renderReferencedDAGNodes
    (stem : String) : List ReferencedDAGNode → String
  | [] => "DnNil"
  | node :: nodes =>
      s!"(DnCons {renderReferencedDAGNode stem node} " ++
        s!"{renderReferencedDAGNodes stem nodes})"

/-- Serialize bounded proof-DAG chunks whose arguments use shared patterns. -/
def renderReferencedDAGChunks
    (stem : String) : List (List ReferencedDAGNode) → String
  | [] => "DcNil"
  | nodes :: chunks =>
      s!"(DcCons {renderReferencedDAGNodes stem nodes} " ++
        s!"{renderReferencedDAGChunks stem chunks})"

/-- Serialize one referenced node with its post-admission release list. -/
def renderReferencedStreamingDAGNode
    (stem : String) (action : ReferencedStreamingDAGNode) : String :=
  s!"(GSLiveNode {renderReferencedDAGNode stem action.node} " ++
    s!"{renderChildIds action.releases})"

def renderReferencedStreamingDAGNodes
    (stem : String) : List ReferencedStreamingDAGNode → String
  | [] => "DsnNil"
  | action :: actions =>
      s!"(DsnCons {renderReferencedStreamingDAGNode stem action} " ++
        s!"{renderReferencedStreamingDAGNodes stem actions})"

private def chunkReference (stem : String) (index : Nat) : String :=
  s!"({stem}-chunk-{index})"

/-- Render each bounded proof block as its own MeTTa definition.  This keeps
both the inner node spine and the outer block spine shallow in the serialized
transport. -/
def renderReferencedDAGChunkDefinitions
    (chunkStem patternStem : String)
    (chunks : List (List ReferencedDAGNode)) : String :=
  String.intercalate "\n" <|
    chunks.zipIdx.map fun indexed =>
      s!"(= ({chunkStem}-chunk-{indexed.2}) " ++
        s!"{renderReferencedDAGNodes patternStem indexed.1})"

private def renderChunkReferences
    (stem : String) : List (List ReferencedDAGNode × Nat) → String
  | [] => "DcNil"
  | indexed :: rest =>
      s!"(DcCons {chunkReference stem indexed.2} " ++
        s!"{renderChunkReferences stem rest})"

/-- Serialize the outer block spine using separately defined proof blocks. -/
def renderReferencedDAGChunkReferences
    (stem : String) (chunks : List (List ReferencedDAGNode)) : String :=
  renderChunkReferences stem chunks.zipIdx

/-- Render bounded streaming blocks as separately named definitions. -/
def renderReferencedStreamingDAGChunkDefinitions
    (chunkStem patternStem : String)
    (chunks : List (List ReferencedStreamingDAGNode)) : String :=
  String.intercalate "\n" <|
    chunks.zipIdx.map fun indexed =>
      s!"(= ({chunkStem}-chunk-{indexed.2}) " ++
        s!"{renderReferencedStreamingDAGNodes patternStem indexed.1})"

private def renderStreamingChunkReferences
    (stem : String) :
    List (List ReferencedStreamingDAGNode × Nat) → String
  | [] => "DscNil"
  | indexed :: rest =>
      s!"(DscCons {chunkReference stem indexed.2} " ++
        s!"{renderStreamingChunkReferences stem rest})"

/-- Serialize the outer streaming-block spine through named blocks. -/
def renderReferencedStreamingDAGChunkReferences
    (stem : String) (chunks : List (List ReferencedStreamingDAGNode)) :
    String :=
  renderStreamingChunkReferences stem chunks.zipIdx

/-! ## Executable sharing boundaries -/

private def sharedLeaf : Pattern := .apply "Leaf" []
private def sharedPair : Pattern := .apply "Pair" [sharedLeaf, sharedLeaf]

private def sharedFixtureProof : RawProof :=
  .node
    { ruleId := ⟨"fixture"⟩
      arguments := [sharedPair, sharedPair] }
    []

/-- Repeated leaves and repeated whole arguments are represented once each. -/
def repeatedPatternSharingFixture : Bool :=
  let proof := compileRawProof sharedFixtureProof
  let shared := shareProofDAGPair proof proof
  shared.patterns.length == 2 &&
    shared.left.nodes.head?.map (fun node => node.argumentIds) ==
      some [1, 1] &&
    shared.right.nodes.head?.map (fun node => node.argumentIds) ==
      some [1, 1]

private def orderedFixtureProof : RawProof :=
  .node
    { ruleId := ⟨"fixture"⟩
      arguments :=
        [.apply "Pair" [.apply "A" [], .apply "B" []],
         .apply "Pair" [.apply "B" [], .apply "A" []]] }
    []

/-- Child order remains structural and produces distinct pattern roots. -/
def reorderedChildrenRemainDistinctFixture : Bool :=
  let proof := compileRawProof orderedFixtureProof
  let shared := shareProofDAGPair proof proof
  match shared.left.nodes.head? with
  | some node =>
      match node.argumentIds with
      | [left, right] => left != right
      | _ => false
  | none => false

/-- A shared leaf used twice is released once, after its second occurrence. -/
def finalUseAnnotationFixture : Bool :=
  let leaf : RawProof :=
    .node { ruleId := ⟨"stream-leaf"⟩, arguments := [sharedLeaf] } []
  let tree : RawProof :=
    .node
      { ruleId := ⟨"stream-pair"⟩
        arguments := [sharedPair, sharedPair] }
      [leaf, leaf]
  let proof := compileRawProof tree
  let shared := shareProofDAGPair proof proof
  let streamed := annotateStreamingProofDAG shared.left
  streamed.nodes.map (fun action => action.releases) == [[], [0]]

end Mettapedia.GSLT.LanguageDef.InferencePatternSharing
