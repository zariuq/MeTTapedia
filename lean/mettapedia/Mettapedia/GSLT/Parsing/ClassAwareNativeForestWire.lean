import Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract

/-!
# Canonical wire snapshot for a native packed forest

The native C parsers expose a backend-neutral binary packed forest.  This file
specifies the opt-in `CNF1` qualification snapshot independently of C struct
layout and decodes it into `ClassAwareNativeForestContract.ForestView`.

The snapshot carries disposable dense identities exactly.  Their semantic
meaning remains in a separate `IdentityTable`; decoding bytes cannot create
that authority.  Likewise, a decoded view must still satisfy `Represents`
before it inherits the exact ParserPack proof-fibre theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat

abbrev NativeTerminalValue :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract.TerminalValue
abbrev NativeNode :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract.Node
abbrev NativeNodeKind :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract.NodeKind
abbrev NativeChoice :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract.Choice
abbrev NativeForestView :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract.ForestView

/-- The distinguished absent-prefix value in the public C ABI. -/
def noneIndex : UInt32 := UInt32.ofNat 4294967295

/-- One physical native node before semantic decoding.  Every field is kept,
including fields which must be canonical for a particular node kind. -/
structure RawNode where
  kind : UInt32
  symbolId : UInt32
  productionIndex : UInt32
  dot : UInt32
  scalarStart : UInt32
  scalarStop : UInt32
  byteStart : UInt32
  byteStop : UInt32
  terminalIsEof : UInt32
  terminalScalar : UInt32
  terminalValueKind : UInt32
  terminalWitnessId : UInt32
  choiceBegin : UInt32
  choiceCount : UInt32
  deriving DecidableEq, Repr

/-- One physical binary packed choice. -/
structure RawChoice where
  parent : UInt32
  prefixNode : UInt32
  childNode : UInt32
  productionIndex : UInt32
  scalarPivot : UInt32
  bytePivot : UInt32
  deriving DecidableEq, Repr

/-- Complete `CNF1` payload, including diagnostic/resource receipts which do
not belong to the semantic `ForestView`. -/
structure Snapshot where
  outcome : UInt32
  nodes : List RawNode
  choices : List RawChoice
  roots : List UInt32
  expectedTerminalIds : List UInt32
  codepoints : List UInt32
  byteOffsets : List UInt32
  inputByteLen : UInt32
  farthestScalar : UInt32
  farthestByte : UInt32
  graphNodeCount : UInt32
  stackNodeCount : UInt32
  workItemCount : UInt32
  decodedByteLen : UInt32
  sourcePassCount : UInt32
  deriving DecidableEq, Repr

/-- Fixed fourteen-word header used by `CNF1`. -/
structure RawHeader where
  outcome : UInt32
  nodeCount : UInt32
  choiceCount : UInt32
  rootCount : UInt32
  expectedCount : UInt32
  scalarCount : UInt32
  inputByteLen : UInt32
  farthestScalar : UInt32
  farthestByte : UInt32
  graphNodeCount : UInt32
  stackNodeCount : UInt32
  workItemCount : UInt32
  decodedByteLen : UInt32
  sourcePassCount : UInt32
  deriving DecidableEq, Repr

def Snapshot.header (snapshot : Snapshot) : RawHeader := {
  outcome := snapshot.outcome
  nodeCount := UInt32.ofNat snapshot.nodes.length
  choiceCount := UInt32.ofNat snapshot.choices.length
  rootCount := UInt32.ofNat snapshot.roots.length
  expectedCount := UInt32.ofNat snapshot.expectedTerminalIds.length
  scalarCount := UInt32.ofNat snapshot.codepoints.length
  inputByteLen := snapshot.inputByteLen
  farthestScalar := snapshot.farthestScalar
  farthestByte := snapshot.farthestByte
  graphNodeCount := snapshot.graphNodeCount
  stackNodeCount := snapshot.stackNodeCount
  workItemCount := snapshot.workItemCount
  decodedByteLen := snapshot.decodedByteLen
  sourcePassCount := snapshot.sourcePassCount
}

def RawHeader.words (header : RawHeader) : List UInt32 :=
  [header.outcome, header.nodeCount, header.choiceCount, header.rootCount,
    header.expectedCount, header.scalarCount, header.inputByteLen,
    header.farthestScalar, header.farthestByte, header.graphNodeCount,
    header.stackNodeCount, header.workItemCount, header.decodedByteLen,
    header.sourcePassCount]

@[simp] theorem RawHeader.words_length (header : RawHeader) :
    header.words.length = 14 := by
  cases header
  rfl

def rawHeaderOfWords? : List UInt32 → Option RawHeader
  | [outcome, nodeCount, choiceCount, rootCount, expectedCount, scalarCount,
      inputByteLen, farthestScalar, farthestByte, graphNodeCount,
      stackNodeCount, workItemCount, decodedByteLen, sourcePassCount] =>
      some {
        outcome := outcome
        nodeCount := nodeCount
        choiceCount := choiceCount
        rootCount := rootCount
        expectedCount := expectedCount
        scalarCount := scalarCount
        inputByteLen := inputByteLen
        farthestScalar := farthestScalar
        farthestByte := farthestByte
        graphNodeCount := graphNodeCount
        stackNodeCount := stackNodeCount
        workItemCount := workItemCount
        decodedByteLen := decodedByteLen
        sourcePassCount := sourcePassCount
      }
  | _ => none

@[simp] theorem rawHeaderOfWords?_words (header : RawHeader) :
    rawHeaderOfWords? header.words = some header := by
  cases header
  rfl

def encodeRawHeader (header : RawHeader) : List UInt8 :=
  header.words.flatMap encodeUInt32LE

def readRawHeader : Reader RawHeader := fun input => do
  let (words, rest) <- readMany readUInt32LE 14 input
  let header <- rawHeaderOfWords? words
  some (header, rest)

@[simp] theorem readRawHeader_encodeRawHeader
    (header : RawHeader) (rest : List UInt8) :
    readRawHeader (encodeRawHeader header ++ rest) = some (header, rest) := by
  have wordsRead := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE header.words rest
  have wordsRead14 :
      readMany readUInt32LE 14
          (header.words.flatMap encodeUInt32LE ++ rest) =
        some (header.words, rest) := by
    simpa using wordsRead
  unfold encodeRawHeader readRawHeader
  rw [wordsRead14]
  simp

def RawNode.words (node : RawNode) : List UInt32 :=
  [node.kind, node.symbolId, node.productionIndex, node.dot,
    node.scalarStart, node.scalarStop, node.byteStart, node.byteStop,
    node.terminalIsEof, node.terminalScalar, node.terminalValueKind,
    node.terminalWitnessId, node.choiceBegin, node.choiceCount]

@[simp] theorem RawNode.words_length (node : RawNode) :
    node.words.length = 14 := by
  cases node
  rfl

def rawNodeOfWords? : List UInt32 → Option RawNode
  | [kind, symbolId, productionIndex, dot, scalarStart, scalarStop,
      byteStart, byteStop, terminalIsEof, terminalScalar, terminalValueKind,
      terminalWitnessId, choiceBegin, choiceCount] =>
      some {
        kind := kind
        symbolId := symbolId
        productionIndex := productionIndex
        dot := dot
        scalarStart := scalarStart
        scalarStop := scalarStop
        byteStart := byteStart
        byteStop := byteStop
        terminalIsEof := terminalIsEof
        terminalScalar := terminalScalar
        terminalValueKind := terminalValueKind
        terminalWitnessId := terminalWitnessId
        choiceBegin := choiceBegin
        choiceCount := choiceCount
      }
  | _ => none

@[simp] theorem rawNodeOfWords?_words (node : RawNode) :
    rawNodeOfWords? node.words = some node := by
  cases node
  rfl

def encodeRawNode (node : RawNode) : List UInt8 :=
  node.words.flatMap encodeUInt32LE

def readRawNode : Reader RawNode := fun input => do
  let (words, rest) <- readMany readUInt32LE 14 input
  let node <- rawNodeOfWords? words
  some (node, rest)

@[simp] theorem readRawNode_encodeRawNode
    (node : RawNode) (rest : List UInt8) :
    readRawNode (encodeRawNode node ++ rest) = some (node, rest) := by
  have wordsRead := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE node.words rest
  have wordsRead14 :
      readMany readUInt32LE 14
          (node.words.flatMap encodeUInt32LE ++ rest) =
        some (node.words, rest) := by
    simpa using wordsRead
  unfold encodeRawNode readRawNode
  rw [wordsRead14]
  simp

def RawChoice.words (choice : RawChoice) : List UInt32 :=
  [choice.parent, choice.prefixNode, choice.childNode,
    choice.productionIndex, choice.scalarPivot, choice.bytePivot]

@[simp] theorem RawChoice.words_length (choice : RawChoice) :
    choice.words.length = 6 := by
  cases choice
  rfl

def rawChoiceOfWords? : List UInt32 → Option RawChoice
  | [parent, prefixNode, childNode, productionIndex, scalarPivot, bytePivot] =>
      some {
        parent := parent
        prefixNode := prefixNode
        childNode := childNode
        productionIndex := productionIndex
        scalarPivot := scalarPivot
        bytePivot := bytePivot
      }
  | _ => none

@[simp] theorem rawChoiceOfWords?_words (choice : RawChoice) :
    rawChoiceOfWords? choice.words = some choice := by
  cases choice
  rfl

def encodeRawChoice (choice : RawChoice) : List UInt8 :=
  choice.words.flatMap encodeUInt32LE

def readRawChoice : Reader RawChoice := fun input => do
  let (words, rest) <- readMany readUInt32LE 6 input
  let choice <- rawChoiceOfWords? words
  some (choice, rest)

@[simp] theorem readRawChoice_encodeRawChoice
    (choice : RawChoice) (rest : List UInt8) :
    readRawChoice (encodeRawChoice choice ++ rest) = some (choice, rest) := by
  have wordsRead := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE choice.words rest
  have wordsRead6 :
      readMany readUInt32LE 6
          (choice.words.flatMap encodeUInt32LE ++ rest) =
        some (choice.words, rest) := by
    simpa using wordsRead
  unfold encodeRawChoice readRawChoice
  rw [wordsRead6]
  simp

theorem readMany_encodeRawNodes
    (nodes : List RawNode) (rest : List UInt8) :
    readMany readRawNode nodes.length
        (nodes.flatMap encodeRawNode ++ rest) = some (nodes, rest) :=
  readMany_encodeList readRawNode encodeRawNode
    readRawNode_encodeRawNode nodes rest

theorem readMany_encodeRawChoices
    (choices : List RawChoice) (rest : List UInt8) :
    readMany readRawChoice choices.length
        (choices.flatMap encodeRawChoice ++ rest) = some (choices, rest) :=
  readMany_encodeList readRawChoice encodeRawChoice
    readRawChoice_encodeRawChoice choices rest

def magic : List UInt8 := [67, 78, 70, 49]

def readMagic : Reader Unit
  | 67 :: 78 :: 70 :: 49 :: rest => some ((), rest)
  | _ => none

@[simp] theorem readMagic_magic (rest : List UInt8) :
    readMagic (magic ++ rest) = some ((), rest) := by rfl

/-- Physical representability of all implicit `UInt32` table counts. -/
def Snapshot.Encodable (snapshot : Snapshot) : Prop :=
  snapshot.nodes.length < UInt32.size ∧
  snapshot.choices.length < UInt32.size ∧
  snapshot.roots.length < UInt32.size ∧
  snapshot.expectedTerminalIds.length < UInt32.size ∧
  snapshot.codepoints.length < UInt32.size ∧
  snapshot.byteOffsets.length = snapshot.codepoints.length + 1

def encodeSnapshot (snapshot : Snapshot) : List UInt8 :=
  magic ++
  encodeRawHeader snapshot.header ++
  snapshot.nodes.flatMap encodeRawNode ++
  snapshot.choices.flatMap encodeRawChoice ++
  snapshot.roots.flatMap encodeUInt32LE ++
  snapshot.expectedTerminalIds.flatMap encodeUInt32LE ++
  snapshot.codepoints.flatMap encodeUInt32LE ++
  snapshot.byteOffsets.flatMap encodeUInt32LE

def readSnapshot : Reader Snapshot := fun input => do
  let (_, rest0) <- readMagic input
  let (header, rest1) <- readRawHeader rest0
  let (nodes, rest2) <- readMany readRawNode header.nodeCount.toNat rest1
  let (choices, rest16) <-
    readMany readRawChoice header.choiceCount.toNat rest2
  let (roots, rest17) <- readMany readUInt32LE header.rootCount.toNat rest16
  let (expectedTerminalIds, rest18) <-
    readMany readUInt32LE header.expectedCount.toNat rest17
  let (codepoints, rest19) <-
    readMany readUInt32LE header.scalarCount.toNat rest18
  let (byteOffsets, rest) <-
    readMany readUInt32LE (header.scalarCount.toNat + 1) rest19
  some (({
    outcome := header.outcome
    nodes := nodes
    choices := choices
    roots := roots
    expectedTerminalIds := expectedTerminalIds
    codepoints := codepoints
    byteOffsets := byteOffsets
    inputByteLen := header.inputByteLen
    farthestScalar := header.farthestScalar
    farthestByte := header.farthestByte
    graphNodeCount := header.graphNodeCount
    stackNodeCount := header.stackNodeCount
    workItemCount := header.workItemCount
    decodedByteLen := header.decodedByteLen
    sourcePassCount := header.sourcePassCount
  } : Snapshot), rest)

def decodeSnapshot? (bytes : List UInt8) : Option Snapshot :=
  match readSnapshot bytes with
  | some (snapshot, []) => some snapshot
  | _ => none

theorem readSnapshot_encodeSnapshot
    (snapshot : Snapshot) (rest : List UInt8)
    (encodable : snapshot.Encodable) :
    readSnapshot (encodeSnapshot snapshot ++ rest) = some (snapshot, rest) := by
  rcases encodable with
    ⟨nodesFit, choicesFit, rootsFit, expectedFit, codepointsFit,
      offsetsExact⟩
  have nodesExact :
      (UInt32.ofNat snapshot.nodes.length).toNat = snapshot.nodes.length := by
    simp [Nat.mod_eq_of_lt nodesFit]
  have choicesExact :
      (UInt32.ofNat snapshot.choices.length).toNat =
        snapshot.choices.length := by
    simp [Nat.mod_eq_of_lt choicesFit]
  have rootsExact :
      (UInt32.ofNat snapshot.roots.length).toNat = snapshot.roots.length := by
    simp [Nat.mod_eq_of_lt rootsFit]
  have expectedExact :
      (UInt32.ofNat snapshot.expectedTerminalIds.length).toNat =
        snapshot.expectedTerminalIds.length := by
    simp [Nat.mod_eq_of_lt expectedFit]
  have codepointsExact :
      (UInt32.ofNat snapshot.codepoints.length).toNat =
        snapshot.codepoints.length := by
    simp [Nat.mod_eq_of_lt codepointsFit]
  simp only [encodeSnapshot, List.append_assoc, readSnapshot]
  rw [readMagic_magic]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [readRawHeader_encodeRawHeader]
  dsimp only [Bind.bind, instMonadOption, Option.bind, Snapshot.header]
  rw [nodesExact, choicesExact, rootsExact, expectedExact, codepointsExact]
  rw [readMany_encodeRawNodes]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [readMany_encodeRawChoices]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [readMany_encodeList readUInt32LE encodeUInt32LE
    readUInt32LE_encodeUInt32LE]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [readMany_encodeList readUInt32LE encodeUInt32LE
    readUInt32LE_encodeUInt32LE]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [readMany_encodeList readUInt32LE encodeUInt32LE
    readUInt32LE_encodeUInt32LE]
  dsimp only [Bind.bind, instMonadOption, Option.bind]
  rw [← offsetsExact]
  rw [readMany_encodeList readUInt32LE encodeUInt32LE
    readUInt32LE_encodeUInt32LE]

@[simp] theorem decodeSnapshot?_encodeSnapshot
    (snapshot : Snapshot) (encodable : snapshot.Encodable) :
    decodeSnapshot? (encodeSnapshot snapshot) = some snapshot := by
  have exactRead :
      readSnapshot (encodeSnapshot snapshot) = some (snapshot, []) := by
    simpa using readSnapshot_encodeSnapshot snapshot [] encodable
  unfold decodeSnapshot?
  rw [exactRead]

/-! ## Semantic decoding of completed snapshots -/

def RawNode.terminalValue? (node : RawNode) : Option NativeTerminalValue :=
  match node.terminalValueKind.toNat with
  | 0 =>
      if node.terminalIsEof = 0 then
        some (.scalar node.terminalScalar.toNat)
      else none
  | 1 =>
      if node.terminalIsEof = 1 then some .eof else none
  | 2 =>
      if node.terminalIsEof = 0 then
        some (.witness node.terminalWitnessId.toNat)
      else none
  | _ => none

def RawNode.toNode? (node : RawNode) : Option NativeNode := do
  let kind : NativeNodeKind <- match node.kind.toNat with
    | 0 =>
        if node.productionIndex = noneIndex then
          match node.terminalValue? with
          | some value => some (.terminal node.symbolId.toNat value)
          | none => none
        else none
    | 1 =>
        if node.symbolId = noneIndex &&
            node.productionIndex = noneIndex &&
            node.scalarStart = node.scalarStop then
          some .epsilon
        else none
    | 2 =>
        if node.productionIndex = noneIndex then
          some (.symbol node.symbolId.toNat)
        else none
    | 3 =>
        if node.symbolId = noneIndex then
          some (.intermediate node.productionIndex.toNat node.dot.toNat)
        else none
    | _ => none
  some {
    kind
    scalarStart := node.scalarStart.toNat
    scalarStop := node.scalarStop.toNat
    byteStart := node.byteStart.toNat
    byteStop := node.byteStop.toNat
    choiceBegin := node.choiceBegin.toNat
    choiceCount := node.choiceCount.toNat
  }

def RawChoice.toChoice (choice : RawChoice) : NativeChoice := {
  parent := choice.parent.toNat
  prefixNode :=
    if choice.prefixNode = noneIndex then none else some choice.prefixNode.toNat
  childNode := choice.childNode.toNat
  productionIndex := choice.productionIndex.toNat
  scalarPivot := choice.scalarPivot.toNat
  bytePivot := choice.bytePivot.toNat
}

/-- Decode exactly the semantic arrays of a completed native snapshot.  The
receipt remains available on the enclosing `Snapshot`. -/
def Snapshot.completedView? (snapshot : Snapshot) : Option NativeForestView :=
  if snapshot.outcome ≠ 0 then none
  else do
    let nodes <- snapshot.nodes.mapM RawNode.toNode?
    if snapshot.byteOffsets.length ≠ snapshot.codepoints.length + 1 then none
    else some {
      nodes
      choices := snapshot.choices.map RawChoice.toChoice
      roots := snapshot.roots.map UInt32.toNat
      codepoints := snapshot.codepoints.map UInt32.toNat
      byteOffsets := snapshot.byteOffsets.map UInt32.toNat
    }

/-! ## Cross-runtime canaries and negative controls -/

private def canaryNodeSymbol : RawNode := {
  kind := 2
  symbolId := 3
  productionIndex := noneIndex
  dot := 0
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  terminalIsEof := 0
  terminalScalar := 0
  terminalValueKind := 0
  terminalWitnessId := 0
  choiceBegin := 0
  choiceCount := 1
}

private def canaryNodeTerminal : RawNode := {
  kind := 0
  symbolId := 10
  productionIndex := noneIndex
  dot := 0
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  terminalIsEof := 0
  terminalScalar := 65
  terminalValueKind := 0
  terminalWitnessId := 0
  choiceBegin := 1
  choiceCount := 0
}

private def canaryChoice : RawChoice := {
  parent := 0
  prefixNode := noneIndex
  childNode := 1
  productionIndex := 7
  scalarPivot := 0
  bytePivot := 0
}

private def canarySnapshot : Snapshot := {
  outcome := 0
  nodes := [canaryNodeSymbol, canaryNodeTerminal]
  choices := [canaryChoice]
  roots := [0]
  expectedTerminalIds := []
  codepoints := [65]
  byteOffsets := [0, 1]
  inputByteLen := 1
  farthestScalar := 1
  farthestByte := 1
  graphNodeCount := 2
  stackNodeCount := 0
  workItemCount := 3
  decodedByteLen := 1
  sourcePassCount := 1
}

theorem canarySnapshot_encodable : canarySnapshot.Encodable := by
  norm_num [Snapshot.Encodable, canarySnapshot, UInt32.size]

theorem canarySnapshot_roundTrip :
    decodeSnapshot? (encodeSnapshot canarySnapshot) = some canarySnapshot :=
  decodeSnapshot?_encodeSnapshot canarySnapshot canarySnapshot_encodable

private def canaryView : NativeForestView := {
  nodes := [
    { kind := .symbol 3
      scalarStart := 0
      scalarStop := 1
      byteStart := 0
      byteStop := 1
      choiceBegin := 0
      choiceCount := 1 },
    { kind := .terminal 10 (.scalar 65)
      scalarStart := 0
      scalarStop := 1
      byteStart := 0
      byteStop := 1
      choiceBegin := 1
      choiceCount := 0 }]
  choices := [{
    parent := 0
    prefixNode := none
    childNode := 1
    productionIndex := 7
    scalarPivot := 0
    bytePivot := 0
  }]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

theorem canarySnapshot_completedView :
    canarySnapshot.completedView? = some canaryView := by rfl

/-- A byte after the exact packet is rejected rather than silently ignored. -/
theorem trailing_byte_rejected :
    decodeSnapshot? (encodeSnapshot canarySnapshot ++ [0]) = none := by
  unfold decodeSnapshot?
  rw [readSnapshot_encodeSnapshot canarySnapshot [0]
    canarySnapshot_encodable]

/-- A magic-only truncated packet is rejected rather than manufacturing a
default header or empty forest. -/
theorem truncated_header_rejected :
    decodeSnapshot? magic = none := by rfl

/-- A malformed node-kind tag cannot cross the physical-to-semantic boundary. -/
theorem unknown_node_kind_rejected :
    Snapshot.completedView? {canarySnapshot with nodes :=
      [{canaryNodeSymbol with kind := 4}, canaryNodeTerminal]} = none := by
  rfl

private def canaryWitnessNode : NativeNode := {
  kind := .terminal 10 (.witness 37)
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 1
  choiceCount := 0
}

private def canaryRawWitnessNode : RawNode := {
  canaryNodeTerminal with
  terminalValueKind := 2
  terminalWitnessId := 37
}

/-- The decoder preserves an opaque witness identity, while the separate
class-aware semantic contract still refuses to interpret it as a JSON scalar. -/
theorem witness_identity_preserved :
    canaryRawWitnessNode.toNode? = some canaryWitnessNode := by rfl

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire
