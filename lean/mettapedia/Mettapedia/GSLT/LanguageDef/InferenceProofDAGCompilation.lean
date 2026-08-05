import Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# Hash-consed compilation of raw proof trees

The generic inference checker already supplies the trusted boundary:
`checkDAGBlocks_sound` proves that every accepted chronological proof DAG
expands to an ordinary accepted proof tree.  This file supplies an untrusted
artifact producer for that boundary.

Compilation is bottom-up.  A node key consists of its rule identifier, exact
ordered argument vector, and exact ordered child identifiers.  Structurally
equal subproofs therefore receive one identifier, while child order and rule
arguments remain visible to the checker.  A compiler defect can only produce
a DAG rejected by the existing checker; no theorem depends on compiler output
without rechecking it.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

deriving instance Hashable for RuleId
deriving instance Hashable for CollType
deriving instance Hashable for Pattern

/-- Canonical structural key for one proof node after its children have been
compiled. -/
structure ProofNodeKey where
  ruleId : RuleId
  arguments : List Pattern
  children : List Nat
deriving DecidableEq, Hashable, Repr

/-- Internal state of the bottom-up hash-consing compiler.  `nodesRev` stores
new nodes in reverse chronological order for constant-time insertion. -/
structure CompilationState where
  nextId : Nat := 0
  known : Std.HashMap ProofNodeKey Nat := {}
  nodesRev : List DAGNode := []

/-- Compact chronological representation of one raw proof. -/
structure CompiledProofDAG where
  rootId : Nat
  nodes : List DAGNode
deriving Repr

mutual

/-- Compile and intern one proof node. -/
def internProof : RawProof → StateM CompilationState Nat
  | .node ruleInstance children => do
      let childIds ← internProofs children
      let key : ProofNodeKey :=
        { ruleId := ruleInstance.ruleId
          arguments := ruleInstance.arguments
          children := childIds }
      let state ← get
      match state.known.get? key with
      | some existingId => pure existingId
      | none =>
          let freshId := state.nextId
          let node : DAGNode :=
            { id := freshId
              ruleInstance := ruleInstance
              children := childIds }
          set
            ({ nextId := freshId + 1
               known := state.known.insert key freshId
               nodesRev := node :: state.nodesRev } : CompilationState)
          pure freshId
termination_by proof => 2 * sizeOf proof
decreasing_by all_goals simp_wf; omega

/-- Compile an ordered child vector from left to right. -/
def internProofs : List RawProof → StateM CompilationState (List Nat)
  | [] => pure []
  | proof :: proofs => do
      let id ← internProof proof
      let ids ← internProofs proofs
      pure (id :: ids)
termination_by proofs => 2 * sizeOf proofs + 1

end

/-- Compile a proof tree from an empty interning environment. -/
def compileRawProof (proof : RawProof) : CompiledProofDAG :=
  let (rootId, state) := (internProof proof).run {}
  { rootId
    nodes := state.nodesRev.reverse }

/- Number of constructor occurrences in an unshared raw proof tree. -/
mutual

def rawProofNodeCount : RawProof → Nat
  | .node _ children => 1 + rawProofsNodeCount children
termination_by proof => 2 * sizeOf proof
decreasing_by all_goals simp_wf; omega

def rawProofsNodeCount : List RawProof → Nat
  | [] => 0
  | proof :: proofs =>
      rawProofNodeCount proof + rawProofsNodeCount proofs
termination_by proofs => 2 * sizeOf proofs + 1

end

/-- Serialize chronological child identifiers for the MeTTa DAG checker. -/
def renderChildIds : List Nat → String
  | [] => "DrNil"
  | id :: ids => s!"(DrCons {id} {renderChildIds ids})"

/-- Serialize one proof-DAG node. -/
def renderDAGNode (node : DAGNode) : String :=
  s!"(GDNode {node.id} {renderRuleInstance node.ruleInstance} " ++
    s!"{renderChildIds node.children})"

/-- Serialize a chronological proof-DAG node vector. -/
def renderDAGNodes : List DAGNode → String
  | [] => "DnNil"
  | node :: nodes =>
      s!"(DnCons {renderDAGNode node} {renderDAGNodes nodes})"

/-- Serialize bounded chronological node blocks.  The outer `DcCons` spine and
each inner `DnCons` spine remain independently bounded by the caller's chunk
size. -/
def renderDAGChunks : List (List DAGNode) → String
  | [] => "DcNil"
  | nodes :: chunks =>
      s!"(DcCons {renderDAGNodes nodes} {renderDAGChunks chunks})"

/-! ## Executable sharing boundary -/

private def fixturePattern : Pattern := .apply "Fixture" []

private def fixtureLeaf : RawProof :=
  .node { ruleId := ⟨"fixture-leaf"⟩, arguments := [fixturePattern] } []

private def fixtureDuplicatedTree : RawProof :=
  .node
    { ruleId := ⟨"fixture-pair"⟩
      arguments := [fixturePattern, fixturePattern] }
    [fixtureLeaf, fixtureLeaf]

/-- Distinct child arguments are not merged merely because their rules agree. -/
private def fixtureOtherLeaf : RawProof :=
  .node
    { ruleId := ⟨"fixture-leaf"⟩
      arguments := [.apply "Other" []] }
    []

private def fixtureDistinctTree : RawProof :=
  .node
    { ruleId := ⟨"fixture-pair"⟩
      arguments := [fixturePattern, .apply "Other" []] }
    [fixtureLeaf, fixtureOtherLeaf]

/-- Executable positive boundary: duplicated subproofs compile to two nodes,
and the parent retains two references to the same leaf. -/
def duplicatedSharingFixture : Bool :=
  let compiled := compileRawProof fixtureDuplicatedTree
  compiled.nodes.length == 2 &&
    compiled.nodes.getLast?.map (fun node => node.children) == some [0, 0]

/-- Executable negative boundary: changing a leaf argument prevents merging. -/
def distinctArgumentsFixture : Bool :=
  (compileRawProof fixtureDistinctTree).nodes.length == 3

end Mettapedia.GSLT.LanguageDef.InferenceProofDAGCompilation
