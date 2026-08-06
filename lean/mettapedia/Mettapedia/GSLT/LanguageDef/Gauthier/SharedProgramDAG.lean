/-
# Authenticated shared DAGs for Gauthier programs

Historical artifacts assign compact natural-number identifiers to shared
program nodes.  Those identifiers are transport data, not mathematical node
identity.  This module therefore separates two layers:

* `SharedProgramDAG` uses the canonical postfix encoding of a subtree as its
  structural identity.  Exact duplicate subtrees have exactly the same id.
* `WireProgramDAG` is the chronological numeric representation accepted at an
  artifact boundary.  Its checker rejects unknown operators, wrong arities,
  dangling references, and cycles before any node is unfolded.

Unfolding always delegates to the established Gauthier parser, so the DAG
layer introduces neither a second syntax nor a second well-formedness notion.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonTrace

namespace Mettapedia.GSLT.LanguageDef.GauthierProgramDAG

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace

universe u

mutual

/-- Executable structural equality for the nested `Prog` syntax. -/
def progDecEq : (left right : Prog) → Decidable (left = right)
  | .node leftOp leftChildren, .node rightOp rightChildren =>
      match decEq leftOp rightOp with
      | isFalse hop => isFalse (fun h => hop (Prog.node.inj h).1)
      | isTrue hop =>
          match progListDecEq leftChildren rightChildren with
          | isFalse hchildren =>
              isFalse (fun h => hchildren (Prog.node.inj h).2)
          | isTrue hchildren => isTrue (by simp [hop, hchildren])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

/-- Executable structural equality for vectors of nested programs. -/
def progListDecEq : (left right : List Prog) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | left :: lefts, right :: rights =>
      match progDecEq left right with
      | isFalse hhead => isFalse (fun h => hhead (List.cons.inj h).1)
      | isTrue hhead =>
          match progListDecEq lefts rights with
          | isFalse htail => isFalse (fun h => htail (List.cons.inj h).2)
          | isTrue htail => isTrue (by simp [hhead, htail])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

end

instance : DecidableEq Prog := progDecEq

/-- One structurally interned node.  `structuralId` is the canonical postfix
serialization of the complete subtree rooted at this node. -/
structure SharedNode where
  structuralId : List Tok
  opId : Nat
  childIds : List (List Tok)
  deriving DecidableEq, Repr

/-- The canonical node record of one program subtree. -/
def sharedNode : Prog → SharedNode
  | .node op children =>
      { structuralId := rpnTokens (.node op children)
        opId := op
        childIds := children.map rpnTokens }

/-- Postorder node occurrences before exact duplicate removal. -/
def occurrenceNodes : Prog → List SharedNode
  | program@(.node _ children) =>
      (children.map occurrenceNodes).flatten ++ [sharedNode program]

/-- Canonical exact structural interning. -/
def internedNodes (program : Prog) : Finset SharedNode :=
  (occurrenceNodes program).toFinset

/-- A finite shared program DAG with canonical structural identifiers. -/
structure SharedProgramDAG where
  rootId : List Tok
  nodes : Finset SharedNode

/-- Compress a ranked Gauthier tree by exact subtree identity. -/
def compress (program : Prog) : SharedProgramDAG :=
  { rootId := rpnTokens program
    nodes := internedNodes program }

/-- Unfold through the already-authenticated Gauthier parser. -/
def unfold? (sig : Signature σ) (dag : SharedProgramDAG) : Option Prog :=
  recognize sig dag.rootId

/-- Every successfully unfolded shared DAG is well-formed for the active
signature. -/
theorem unfold_wellFormed {sig : Signature σ} {dag : SharedProgramDAG}
    {program : Prog} (hunfold : unfold? sig dag = some program) :
    WellFormed sig program := by
  exact recognize_sound hunfold

/-- Canonical compression followed by parser-owned unfolding recovers the
original well-formed program exactly. -/
theorem unfold_compress {sig : Signature σ} {program : Prog}
    (hprogram : WellFormed sig program) :
    unfold? sig (compress program) = some program := by
  exact parse_emit_roundTrip hprogram

/-- Exact structural interning produces a duplicate-free node table. -/
theorem internedNodes_nodup (program : Prog) :
    (internedNodes program).val.Nodup := by
  exact (internedNodes program).nodup

@[simp] theorem sharedNode_structuralId (op : Nat) (children : List Prog) :
    (sharedNode (.node op children)).structuralId =
      (children.map rpnTokens).flatten ++ [op] := by
  simp [sharedNode, rpnTokens]

@[simp] theorem sharedNode_childIds (op : Nat) (children : List Prog) :
    (sharedNode (.node op children)).childIds = children.map rpnTokens := rfl

@[simp] theorem sharedNode_opId (op : Nat) (children : List Prog) :
    (sharedNode (.node op children)).opId = op := rfl

/-- The node's operator metadata is read from exactly the same signature row
as the authenticated role trace. -/
theorem sharedNode_roleRecord (sig : Signature σ) (op : Nat)
    (children : List Prog) :
    roleRecord sig (sharedNode (.node op children)).opId = roleRecord sig op := by
  rfl

/-- Before duplicate removal, mapping the DAG occurrences back to table-owned
role records gives exactly the established postfix role trace. -/
theorem occurrenceNodes_roleRecords (sig : Signature σ) (program : Prog) :
    (occurrenceNodes program).map (fun node => roleRecord sig node.opId) =
      roleRecords sig program := by
  fun_induction occurrenceNodes program
  simp only [roleRecords, List.map_append, List.map_singleton]
  congr 1
  rw [List.map_flatten]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  exact ‹∀ child ∈ _, _›

/-- Child argument coordinates are preserved exactly and in order. -/
theorem sharedNode_child_coordinate {op : Nat} {children : List Prog}
    {index : Nat} (hindex : index < children.length) :
    (sharedNode (.node op children)).childIds[index]'(by simpa [sharedNode] using hindex) =
      rpnTokens (children[index]'hindex) := by
  simp [sharedNode]

/-- The number of child structural references agrees with parser arity for a
well-formed node. -/
theorem sharedNode_arity {sig : Signature σ} {op : Nat}
    {children : List Prog} {entry : Entry σ}
    (hentry : entryAt sig op = some entry)
    (hprogram : WellFormed sig (.node op children)) :
    (sharedNode (.node op children)).childIds.length = entry.arity := by
  cases hprogram with
  | node hentry' hlength _ =>
      have : entry = _ := Option.some.inj (hentry.symm.trans hentry')
      subst entry
      simpa [sharedNode] using hlength

/-- Child roles and child structural references have identical coordinates. -/
theorem sharedNode_childRoles_length {sig : Signature σ} {op : Nat}
    {children : List Prog} {entry : Entry σ}
    (hentry : entryAt sig op = some entry)
    (hprogram : WellFormed sig (.node op children)) :
    (roleRecord sig op).childRoles.length =
      (sharedNode (.node op children)).childIds.length := by
  rw [roleRecord_of_entry hentry, childRoles_length]
  exact (sharedNode_arity hentry hprogram).symm

/-! ## Numeric artifact boundary -/

/-- One chronological wire node.  Its list position is its numeric id. -/
structure WireNode where
  opId : Nat
  children : List Nat
  deriving DecidableEq, Repr

/-- A compact numeric shared DAG as stored by experiment artifacts. -/
structure WireProgramDAG where
  root : Nat
  nodes : List WireNode
  deriving DecidableEq, Repr

/-- A wire node is admissible at position `index` exactly when its operator is
known, its arity is right, and every edge points strictly backward. -/
def wireNodeAccepted (sig : Signature σ) (index : Nat) (node : WireNode) : Bool :=
  match entryAt sig node.opId with
  | none => false
  | some entry =>
      node.children.length == entry.arity &&
        node.children.all (fun child => child < index)

/-- Executable boundary checker.  Strictly backward edges simultaneously rule
out dangling references and cycles. -/
def wireAccepted (sig : Signature σ) (dag : WireProgramDAG) : Bool :=
  dag.root < dag.nodes.length &&
    (dag.nodes.zipIdx.all fun (node, index) => wireNodeAccepted sig index node)

/-- Resolve one chronological wire node against programs already resolved. -/
def resolveWireNode (resolved : List Prog) (node : WireNode) : Option Prog := do
  let children ← node.children.mapM (listGet? resolved)
  pure (.node node.opId children)

/-- Resolve a chronological wire table from left to right. -/
def resolveWireNodes : List WireNode → List Prog → Option (List Prog)
  | [], resolved => some resolved
  | node :: rest, resolved => do
      let program ← resolveWireNode resolved node
      resolveWireNodes rest (resolved ++ [program])

/-- Unfold a checked numeric artifact.  The final parser replay is deliberate:
the wire layer does not become a second well-formedness authority. -/
def unfoldWire? (sig : Signature σ) (dag : WireProgramDAG) : Option Prog := do
  if wireAccepted sig dag then
    let programs ← resolveWireNodes dag.nodes []
    let root ← listGet? programs dag.root
    recognize sig (rpnTokens root)
  else
    none

/-- The parser remains the final authority for every accepted wire unfolding. -/
theorem unfoldWire_wellFormed {sig : Signature σ} {dag : WireProgramDAG}
    {program : Prog} (hunfold : unfoldWire? sig dag = some program) :
    WellFormed sig program := by
  unfold unfoldWire? at hunfold
  cases haccepted : wireAccepted sig dag with
  | false => simp [haccepted] at hunfold
  | true =>
      simp only [haccepted, if_true] at hunfold
      cases hresolved : resolveWireNodes dag.nodes [] with
      | none => simp [hresolved] at hunfold
      | some programs =>
          simp [hresolved] at hunfold
          cases hroot : listGet? programs dag.root with
          | none => simp [hroot] at hunfold
          | some root =>
              exact recognize_sound (by simpa [hroot] using hunfold)

/-! ## Concrete positive and rejection fixtures over `orgMemoSignature` -/

def sharedZeroAdd : WireProgramDAG :=
  { root := 1
    nodes :=
      [ { opId := 0, children := [] }
      , { opId := 3, children := [0, 0] }
      ] }

def unknownOperator : WireProgramDAG :=
  { root := 0, nodes := [{ opId := 99, children := [] }] }

def wrongArity : WireProgramDAG :=
  { root := 0, nodes := [{ opId := 3, children := [] }] }

def danglingEdge : WireProgramDAG :=
  { root := 1
    nodes :=
      [ { opId := 0, children := [] }
      , { opId := 3, children := [0, 7] }
      ] }

def cyclicEdge : WireProgramDAG :=
  { root := 1
    nodes :=
      [ { opId := 0, children := [] }
      , { opId := 3, children := [0, 1] }
      ] }

theorem sharedZeroAdd_accepted : wireAccepted orgMemoSignature sharedZeroAdd = true := by
  decide

theorem sharedZeroAdd_unfolds :
    unfoldWire? orgMemoSignature sharedZeroAdd =
      some (.node 3 [.node 0 [], .node 0 []]) := by
  simp [unfoldWire?, sharedZeroAdd, wireAccepted, wireNodeAccepted,
    resolveWireNodes, resolveWireNode, orgMemoSignature, rpnTokens,
    recognize, recognizeRaw, recognizeRawStack, recognizeRawStep,
    entryAt, entry, listGet?, popN,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps]

/-- Two references to node zero are one structural source in the wire table. -/
theorem sharedZeroAdd_one_source_two_occurrences :
    sharedZeroAdd.nodes.length = 2 ∧
      sharedZeroAdd.nodes[1].children = [0, 0] := by
  decide

theorem unknownOperator_rejected :
    wireAccepted orgMemoSignature unknownOperator = false := by decide

theorem wrongArity_rejected :
    wireAccepted orgMemoSignature wrongArity = false := by decide

theorem danglingEdge_rejected :
    wireAccepted orgMemoSignature danglingEdge = false := by decide

theorem cyclicEdge_rejected :
    wireAccepted orgMemoSignature cyclicEdge = false := by decide

#print axioms unfold_wellFormed
#print axioms unfold_compress
#print axioms occurrenceNodes_roleRecords
#print axioms sharedNode_child_coordinate
#print axioms sharedNode_childRoles_length
#print axioms unfoldWire_wellFormed
#print axioms sharedZeroAdd_accepted
#print axioms unknownOperator_rejected
#print axioms wrongArity_rejected
#print axioms danglingEdge_rejected
#print axioms cyclicEdge_rejected

end Mettapedia.GSLT.LanguageDef.GauthierProgramDAG
