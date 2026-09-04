import Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
import Mettapedia.Languages.Metamath.MM2CompressedIndexCanonicality
import Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerCanonicalHitBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Continuous compressed-proof public-boundary representation

This module defines the common representation boundary used between complete
source compressed-proof actions.  The target rows are reconstructed from the
source machine, its derivation-generated occurrence ledger, and the source
scanner boundary.  Additional verifier rows live in an explicit static frame;
that frame cannot contain dynamic compressed-machine state or verdicts.

Internal lookup, assertion, and scanner transitions may temporarily leave this
boundary.  A later action-simulation theorem must identify a nonempty finite
MM2 segment that returns to the same relation.  This module supplies the shared
induction invariant, not that simulation theorem.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Source-derived public rows -/

/-- Target-independent parameters fixed for one compressed theorem.  The
initial heap frontier is the length produced by header construction; each `Z`
save occupies the next position after that frontier. -/
structure BoundaryContext where
  scopeOwner : Atom
  proofOwner : Atom
  initialHeapLength : Nat

/-- The source scanner state at a public action boundary.  Raw bytes remain
bytes here; the MM2 list representation is produced only by `scannerRow`. -/
structure ScannerBoundary where
  wordPosition : Nat
  bytePosition : Nat
  remainingBytes : List UInt8
  phase : ScannerPhase
deriving DecidableEq

/-- Compact code carried by a terminal byte at one source scanner boundary. -/
def proofByteCode (before : ScannerBoundary)
    (occurrence : ByteOccurrence) : CompressedIndexCode :=
  { reversePrefixDigits := before.phase.reversePrefix
    terminalDigit := occurrence.byte.toNat - 65 }

/-- Scanner-prefix validity inherited from the authored U--Y byte grammar. -/
def scannerPrefixValid (boundary : ScannerBoundary) : Prop :=
  ∀ digit ∈ boundary.phase.reversePrefix, 1 ≤ digit ∧ digit ≤ 5

/-- One exact source-byte movement whose authored scanner result is a single
proof action.  The occurrence identity, head/tail split, and next scanner
frontier are all explicit; in particular the proof index is computed by
`authoredOutcome` rather than supplied independently to the verifier bridge. -/
structure ProofByteReceipt (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence)
    (index : Nat) : Prop where
  owner_eq : occurrence.owner = context.proofOwner
  occurrence_position_eq : occurrence.position = before.bytePosition
  consumes_head : before.remainingBytes = occurrence.byte :: after.remainingBytes
  word_position_eq : after.wordPosition = before.wordPosition
  byte_position_eq : after.bytePosition = before.bytePosition + 1
  phase_completed : after.phase = .completed
  code_valid : (proofByteCode before occurrence).Valid
  decoded : authoredOutcome before.phase occurrence.byte =
    .decoded [.step index] after.phase

/-- A proof-byte receipt reconstructs the actual authored scanner transition;
the target proof index is therefore tied to the byte that produced it. -/
theorem ProofByteReceipt.sourceStep
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    SourceStep (.request occurrence before.phase)
      (.outcome occurrence (.decoded [.step index] after.phase)) := by
  have step := SourceStep.run occurrence before.phase
  rw [receipt.decoded] at step
  exact step

/-- Canonical constructor for a terminal-byte proof receipt.  The index is
computed from the source scanner phase and byte, while validity is inherited
from the prefix grammar and the A--T byte range. -/
theorem proofByteReceipt_of_terminal
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) (remaining : List UInt8)
    (ownerEqual : occurrence.owner = context.proofOwner)
    (positionEqual : occurrence.position = before.bytePosition)
    (headExact : before.remainingBytes = occurrence.byte :: remaining)
    (prefixValid : scannerPrefixValid before)
    (terminal : 65 ≤ occurrence.byte.toNat ∧ occurrence.byte.toNat ≤ 84) :
    ProofByteReceipt context before
      { wordPosition := before.wordPosition
        bytePosition := before.bytePosition + 1
        remainingBytes := remaining
        phase := .completed }
      occurrence
      (compressedIndexValue before.phase.reversePrefix
        (occurrence.byte.toNat - 65)) := by
  refine
    { owner_eq := ownerEqual
      occurrence_position_eq := positionEqual
      consumes_head := headExact
      word_position_eq := rfl
      byte_position_eq := rfl
      phase_completed := rfl
      code_valid := ?_
      decoded := ?_ }
  · exact ⟨prefixValid, by
      dsimp only [proofByteCode]
      omega⟩
  · simp [authoredOutcome, terminal]

/-- The value of the scanner-carried compact code is exactly the proof index
named by the authored byte outcome. -/
theorem ProofByteReceipt.code_value
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    (proofByteCode before occurrence).value = index := by
  rcases before with ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  have decoded := receipt.decoded
  by_cases terminal :
      65 ≤ occurrence.byte.toNat ∧ occurrence.byte.toNat ≤ 84
  · simp [authoredOutcome, terminal] at decoded
    simpa [proofByteCode, CompressedIndexCode.value] using decoded.1
  · by_cases prefixCase :
        85 ≤ occurrence.byte.toNat ∧ occurrence.byte.toNat ≤ 89
    · simp [authoredOutcome, terminal, prefixCase] at decoded
    · by_cases save : occurrence.byte.toNat = 90
      · cases phase <;> simp [authoredOutcome, save] at decoded
      · by_cases question : occurrence.byte.toNat = 63
        · cases phase <;>
            simp [authoredOutcome, question] at decoded
        · simp [authoredOutcome, terminal, prefixCase, save, question] at decoded

/-- A valid scanner-built proof code is structurally the same code used by
the canonical natural-number lookup interface. -/
theorem ProofByteReceipt.code_eq_ofNat
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    proofByteCode before occurrence = CompressedIndexCode.ofNat index := by
  rw [← receipt.code_value]
  exact
    MM2CompressedIndexCanonicality.CompressedIndexCode.eq_ofNat_value
      (proofByteCode before occurrence) receipt.code_valid

/-- The raw scanner code and the canonical heap-lookup code have exactly the
same MM2 atom representation. -/
theorem ProofByteReceipt.code_atom_eq_ofNat
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index) :
    (proofByteCode before occurrence).atom =
      (CompressedIndexCode.ofNat index).atom := by
  rw [receipt.code_eq_ofNat]

/-- A fixed byte transition cannot decode to two distinct proof indices. -/
theorem ProofByteReceipt.index_eq
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {left right : Nat}
    (leftReceipt : ProofByteReceipt context before after occurrence left)
    (rightReceipt : ProofByteReceipt context before after occurrence right) :
    left = right := by
  have outcomeEqual :
      ScannerOutcome.decoded [.step left] after.phase =
        ScannerOutcome.decoded [.step right] after.phase :=
    leftReceipt.decoded.symm.trans rightReceipt.decoded
  injection outcomeEqual with actionsEqual
  injection actionsEqual with stepEqual
  exact CompressedAction.step.inj stepEqual

/-- Negative control: changing only the proof index invalidates an otherwise
identical scanner receipt. -/
theorem ProofByteReceipt.rejects_changed_index
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index changed : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    (different : changed ≠ index) :
    ¬ ProofByteReceipt context before after occurrence changed := by
  intro changedReceipt
  exact different (changedReceipt.index_eq receipt)

/-! ## Source-synchronised `Z` save -/

/-- One exact source-byte movement whose authored scanner result is `Z` save.
The source phase and successor phase are retained explicitly so the later MM2
segment cannot treat a save outside the completed-step boundary as valid. -/
structure SaveByteReceipt (context : BoundaryContext)
    (before after : ScannerBoundary) (occurrence : ByteOccurrence) : Prop where
  owner_eq : occurrence.owner = context.proofOwner
  occurrence_position_eq : occurrence.position = before.bytePosition
  consumes_head : before.remainingBytes = occurrence.byte :: after.remainingBytes
  word_position_eq : after.wordPosition = before.wordPosition
  byte_position_eq : after.bytePosition = before.bytePosition + 1
  phase_before : before.phase = .completed
  phase_after : after.phase = .between
  byte_is_z : occurrence.byte.toNat = 90
  decoded : authoredOutcome before.phase occurrence.byte =
    .decoded [.save] after.phase

/-- A save receipt reconstructs the actual authored scanner transition. -/
theorem SaveByteReceipt.sourceStep
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context before after occurrence) :
    SourceStep (.request occurrence before.phase)
      (.outcome occurrence (.decoded [.save] after.phase)) := by
  have step := SourceStep.run occurrence before.phase
  rw [receipt.decoded] at step
  exact step

/-- Canonical `Z` receipt.  The output boundary consumes exactly one byte and
returns to the between-step phase without manufacturing an action index. -/
theorem saveByteReceipt_of_z
    (context : BoundaryContext) (before : ScannerBoundary)
    (occurrence : ByteOccurrence) (remaining : List UInt8)
    (ownerEqual : occurrence.owner = context.proofOwner)
    (positionEqual : occurrence.position = before.bytePosition)
    (headExact : before.remainingBytes = occurrence.byte :: remaining)
    (phaseExact : before.phase = .completed)
    (byteExact : occurrence.byte.toNat = 90) :
    SaveByteReceipt context before
      { wordPosition := before.wordPosition
        bytePosition := before.bytePosition + 1
        remainingBytes := remaining
        phase := .between }
      occurrence := by
  refine
    { owner_eq := ownerEqual
      occurrence_position_eq := positionEqual
      consumes_head := headExact
      word_position_eq := rfl
      byte_position_eq := rfl
      phase_before := phaseExact
      phase_after := rfl
      byte_is_z := byteExact
      decoded := ?_ }
  rw [phaseExact]
  simp [authoredOutcome, byteExact]

/-- The same byte occurrence cannot be reinterpreted as `Z` from a different
source phase. -/
theorem SaveByteReceipt.rejects_changed_before_phase
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context before after occurrence)
    (changed : ScannerPhase) (different : changed ≠ before.phase) :
    ¬ SaveByteReceipt context { before with phase := changed } after
      occurrence := by
  intro changedReceipt
  have changedCompleted : changed = .completed := changedReceipt.phase_before
  have beforeCompleted : before.phase = .completed := receipt.phase_before
  exact different (changedCompleted.trans beforeCompleted.symm)

/-- Exact MM2 machine frontiers reconstructed from the source state. -/
def machineRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", context.scopeOwner, context.proofOwner,
      (CompressedIndexCode.ofNat state.heap.length).atom,
      (CompressedIndexCode.ofNat state.nodes.length).atom,
      (CompressedIndexCode.ofNat state.stack.length).atom]

/-- Exact public scanner row reconstructed from source bytes and phase. -/
def scannerRow (context : BoundaryContext)
    (boundary : ScannerBoundary) : Atom :=
  .expression
    [.symbol "mm-compressed-scan", context.scopeOwner, context.proofOwner,
      natAtom boundary.wordPosition,
      listAtom natAtom (boundary.remainingBytes.map UInt8.toNat),
      boundary.phase.atom,
      listAtom natAtom boundary.phase.reversePrefix]

/-- Locate an authored assertion by its globally unique source label.  Source
validity proves that a reachable assertion heap entry resolves to this
position; the total definition also gives a deterministic row for arbitrary
states. -/
def assertionPosition (source : SourcePrefix)
    (assertion : SourceAssertion) : Nat :=
  source.assertions.findIdx fun candidate =>
    decide (candidate.label = assertion.label)

/-- MM2 rows for assertion-valued heap entries, preserving every heterogeneous
heap position and the assertion's authored database position. -/
def assertionHeapRowsFrom
    {source : SourcePrefix} (proofOwner : Atom) :
    Nat -> List (SourceGSLTCompressedTheorem.HeapEntry source) -> List Atom
  | _, [] => []
  | heapPosition, .proof _ :: remaining =>
      assertionHeapRowsFrom proofOwner (heapPosition + 1) remaining
  | heapPosition, .assertion assertion :: remaining =>
      .expression
          [.symbol "mm-compressed-heap-assertion", proofOwner,
            (CompressedIndexCode.ofNat heapPosition).atom,
            natAtom (assertionPosition source assertion),
            stringAtom assertion.label] ::
        assertionHeapRowsFrom proofOwner (heapPosition + 1) remaining

def assertionHeapRows
    {source : SourcePrefix} (proofOwner : Atom)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) : List Atom :=
  assertionHeapRowsFrom proofOwner 0 heap

/-- Complete source-node table paired pointwise with its derivation-generated
occurrence ledger.  The ledger alignment law makes truncation unreachable. -/
def sourceNodeRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) :
    Nat -> List (ProofNode source target) -> List Atom -> List Atom
  | _, [], _ => []
  | _, _ :: _, [] => []
  | nodeId, node :: nodes, occurrence :: occurrences =>
      MM2CompressedProofHeapEncoding.nodeRow proofOwner
          (displayedProofOccurrence nodeId node occurrence) ::
        sourceNodeRowsFrom proofOwner (nodeId + 1) nodes occurrences

def sourceNodeRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : List Atom :=
  sourceNodeRowsFrom proofOwner 0 state.nodes ledger.occurrences

/-- Ordered compact and normal stack observations starting at an explicit
position. -/
def sourceStackRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : Nat -> List Nat -> List Atom
  | _, [] => []
  | stackPosition, nodeId :: remaining =>
      let rows :=
        match state.nodes[nodeId]?, ledger.occurrences[nodeId]? with
        | some node, some occurrence =>
            let item := displayedProofOccurrence nodeId node occurrence
            [compressedStackRow proofOwner stackPosition item,
              normalStackRow proofOwner stackPosition item]
        | _, _ => []
      rows ++ sourceStackRowsFrom proofOwner state ledger
        (stackPosition + 1) remaining

/-- Complete ordered stack view.  A dangling node identity emits no row;
source action reachability later rules that branch out. -/
def sourceStackRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : List Atom :=
  sourceStackRowsFrom proofOwner state ledger 0 state.stack

/-- Stack rows depend only on the node table and occurrence ledger, not on
the other machine-state fields. -/
theorem sourceStackRowsFrom_eq_of_nodes_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (leftState rightState : MachineState source target)
    (leftLedger : NodeOccurrenceLedger leftState)
    (rightLedger : NodeOccurrenceLedger rightState)
    (nodesExact : leftState.nodes = rightState.nodes)
    (occurrencesExact : leftLedger.occurrences = rightLedger.occurrences)
    (position : Nat) (stack : List Nat) :
    sourceStackRowsFrom proofOwner leftState leftLedger position stack =
      sourceStackRowsFrom proofOwner rightState rightLedger position stack := by
  induction stack generalizing position with
  | nil => rfl
  | cons nodeId remaining induction =>
      simp only [sourceStackRowsFrom]
      rw [nodesExact, occurrencesExact]
      split <;> rw [induction]

/-- Stack encoding respects concatenation while advancing the physical stack
position by the exact length of the encoded prefix. -/
theorem sourceStackRowsFrom_append
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat)
    (left right : List Nat) :
    sourceStackRowsFrom proofOwner state ledger position (left ++ right) =
      sourceStackRowsFrom proofOwner state ledger position left ++
        sourceStackRowsFrom proofOwner state ledger (position + left.length)
          right := by
  induction left generalizing position with
  | nil => simp [sourceStackRowsFrom]
  | cons nodeId remaining induction =>
      simp only [List.cons_append, sourceStackRowsFrom, List.length_cons]
      split
      · rw [induction]
        rw [List.append_assoc]
        have positionExact :
            position + 1 + remaining.length =
              position + (remaining.length + 1) := by
          omega
        rw [positionExact]
      · rw [induction]
        rw [List.append_assoc]
        have positionExact :
            position + 1 + remaining.length =
              position + (remaining.length + 1) := by
          omega
        rw [positionExact]

/-- Pushing one existing proof node appends exactly its compact and normal
stack observations; every prior stack row is retained in order. -/
theorem sourceStackRows_push
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (nodeId : Nat)
    (node : ProofNode source target) (sourceOccurrence : Atom)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (afterLedger : NodeOccurrenceLedger
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (occurrencesExact : afterLedger.occurrences = ledger.occurrences) :
    sourceStackRows proofOwner
        ({ state with stack := state.stack ++ [nodeId] } :
          MachineState source target)
        afterLedger =
      sourceStackRows proofOwner state ledger ++
        [compressedStackRow proofOwner state.stack.length
            (displayedProofOccurrence nodeId node sourceOccurrence),
          normalStackRow proofOwner state.stack.length
            (displayedProofOccurrence nodeId node sourceOccurrence)] := by
  have afterOccurrenceLookup :
      afterLedger.occurrences[nodeId]? = some sourceOccurrence := by
    rw [occurrencesExact]
    exact occurrenceLookup
  unfold sourceStackRows
  rw [sourceStackRowsFrom_append]
  rw [sourceStackRowsFrom_eq_of_nodes_occurrences proofOwner _ state afterLedger
    ledger rfl occurrencesExact]
  simp [sourceStackRowsFrom, nodeLookup, afterOccurrenceLookup]

theorem displayedHeap_eq_of_heap_nodes_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (left right : MachineState source target)
    (leftLedger : NodeOccurrenceLedger left)
    (rightLedger : NodeOccurrenceLedger right)
    (heapExact : left.heap = right.heap)
    (nodesExact : left.nodes = right.nodes)
    (occurrencesExact : leftLedger.occurrences = rightLedger.occurrences) :
    displayedHeap left leftLedger = displayedHeap right rightLedger := by
  unfold displayedHeap
  rw [heapExact]
  apply List.map_congr_left
  intro entry _member
  cases entry with
  | assertion assertion => rfl
  | proof nodeId =>
      simp only [displayedHeapEntry]
      rw [nodesExact, occurrencesExact]

theorem sourceNodeRows_eq_of_nodes_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (left right : MachineState source target)
    (leftLedger : NodeOccurrenceLedger left)
    (rightLedger : NodeOccurrenceLedger right)
    (nodesExact : left.nodes = right.nodes)
    (occurrencesExact : leftLedger.occurrences = rightLedger.occurrences) :
    sourceNodeRows proofOwner left leftLedger =
      sourceNodeRows proofOwner right rightLedger := by
  simp only [sourceNodeRows]
  rw [nodesExact, occurrencesExact]

/-- `Z` receipts starting at an explicit save occurrence. -/
def sourceSaveRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : Nat -> List Nat -> List Atom
  | _, [] => []
  | savePosition, nodeId :: remaining =>
      let rows :=
        match state.nodes[nodeId]?, ledger.occurrences[nodeId]? with
        | some node, some occurrence =>
            [saveReceiptRow context.proofOwner
              (context.initialHeapLength + savePosition)
              (displayedProofOccurrence nodeId node occurrence)]
        | _, _ => []
      rows ++ sourceSaveRowsFrom context state ledger
        (savePosition + 1) remaining

/-- Complete `Z` receipt view.  The receipt heap position is the header
frontier plus its save occurrence. -/
def sourceSaveRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : List Atom :=
  sourceSaveRowsFrom context state ledger 0 state.saves

theorem sourceSaveRowsFrom_eq_of_nodes_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (left right : MachineState source target)
    (leftLedger : NodeOccurrenceLedger left)
    (rightLedger : NodeOccurrenceLedger right)
    (nodesExact : left.nodes = right.nodes)
    (occurrencesExact : leftLedger.occurrences = rightLedger.occurrences)
    (position : Nat) (saves : List Nat) :
    sourceSaveRowsFrom context left leftLedger position saves =
      sourceSaveRowsFrom context right rightLedger position saves := by
  induction saves generalizing position with
  | nil => rfl
  | cons nodeId remaining induction =>
      simp only [sourceSaveRowsFrom]
      rw [nodesExact, occurrencesExact, induction]

/-- Source-derived rows that persist while scanner and machine control move
through one administrative target segment. -/
def canonicalPassiveRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) : List Atom :=
  heapProofRows context.proofOwner (displayedHeap state ledger) ++
    assertionHeapRows context.proofOwner state.heap ++
    sourceNodeRows context.proofOwner state ledger ++
    sourceStackRows context.proofOwner state ledger ++
    sourceSaveRows context state ledger

/-- A proof lookup changes only the stack display.  The complete passive row
set gains exactly the compact and normal observations at the old frontier. -/
theorem canonicalPassiveRows_push_mem_iff
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (nodeId : Nat)
    (node : ProofNode source target) (sourceOccurrence : Atom)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (afterLedger : NodeOccurrenceLedger
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (occurrencesExact : afterLedger.occurrences = ledger.occurrences)
    (row : Atom) :
    row ∈ canonicalPassiveRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          afterLedger ↔
      row ∈ canonicalPassiveRows context state ledger ∨
        row = compressedStackRow context.proofOwner state.stack.length
          (displayedProofOccurrence nodeId node sourceOccurrence) ∨
        row = normalStackRow context.proofOwner state.stack.length
          (displayedProofOccurrence nodeId node sourceOccurrence) := by
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  have heapExact : displayedHeap after afterLedger = displayedHeap state ledger :=
    displayedHeap_eq_of_heap_nodes_occurrences after state afterLedger ledger
      rfl rfl occurrencesExact
  have nodesExact : sourceNodeRows context.proofOwner after afterLedger =
      sourceNodeRows context.proofOwner state ledger :=
    sourceNodeRows_eq_of_nodes_occurrences context.proofOwner after state
      afterLedger ledger rfl occurrencesExact
  have stackExact : sourceStackRows context.proofOwner after afterLedger =
      sourceStackRows context.proofOwner state ledger ++
        [compressedStackRow context.proofOwner state.stack.length
            (displayedProofOccurrence nodeId node sourceOccurrence),
          normalStackRow context.proofOwner state.stack.length
            (displayedProofOccurrence nodeId node sourceOccurrence)] :=
    sourceStackRows_push context.proofOwner state ledger nodeId node
      sourceOccurrence nodeLookup occurrenceLookup afterLedger occurrencesExact
  have savesExact : sourceSaveRows context after afterLedger =
      sourceSaveRows context state ledger := by
    unfold sourceSaveRows
    exact sourceSaveRowsFrom_eq_of_nodes_occurrences context after state
      afterLedger ledger rfl occurrencesExact 0 state.saves
  change row ∈ canonicalPassiveRows context after afterLedger ↔ _
  simp only [canonicalPassiveRows, heapExact, nodesExact, stackExact,
    savesExact, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  aesop

/-- Every verifier-dynamic row present at a public action boundary, derived
from one source machine and its displayed occurrence ledger. -/
def canonicalBoundaryRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scanner : ScannerBoundary) : List Atom :=
  [machineRow context state, scannerRow context scanner] ++
    canonicalPassiveRows context state ledger

/-- Direct proof-handler context with every frontier reconstructed from the
source machine and scanner boundary.  Direct probing starts at heap cursor
zero; the requested compact index remains independent of that cursor. -/
def directContextAtBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) : DirectProofContext :=
  { scopeOwner := context.scopeOwner
    proofOwner := context.proofOwner
    wordPosition := natAtom scanner.wordPosition
    remainingBytes :=
      listAtom natAtom (scanner.remainingBytes.map UInt8.toNat)
    index := index
    cursor := 0
    heapNext := state.heap.length
    nodeNext := state.nodes.length
    stackPosition := state.stack.length
    nextStackPosition := state.stack.length + 1 }

@[simp] theorem directContextAtBoundary_frontiers
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) :
    (directContextAtBoundary context state scanner index).heapNext =
        state.heap.length ∧
      (directContextAtBoundary context state scanner index).nodeNext =
        state.nodes.length ∧
      (directContextAtBoundary context state scanner index).stackPosition =
        state.stack.length ∧
      (directContextAtBoundary context state scanner index).nextStackPosition =
        state.stack.length + 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The direct handler's advanced machine row is exactly the public machine
row of the source state after pushing one proof node. -/
theorem directContextAtBoundary_nextMachineRow_eq_machineRow_push
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index nodeId : Nat) :
    (directContextAtBoundary context state scanner index).nextMachineRow =
      machineRow context
        ({ state with stack := state.stack ++ [nodeId] } :
          MachineState source target) := by
  simp [directContextAtBoundary, DirectProofContext.nextMachineRow, machineRow,
    MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_succ]

/-- The scanner successor named by a proof-byte receipt is exactly the row
emitted by the direct proof handler after it consumes the corresponding
pending lookup. -/
theorem ProofByteReceipt.scannerRow_eq_resumedScanRow
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    (receipt : ProofByteReceipt context before after occurrence index)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) :
    scannerRow context after =
      (directContextAtBoundary context state after index).resumedScanRow := by
  simp [scannerRow, directContextAtBoundary,
    DirectProofContext.resumedScanRow, receipt.phase_completed,
    ScannerPhase.atom, ScannerPhase.reversePrefix]

/-- Source-derived frame rows not already present in the canonical direct-hit
slice.  MM2 spaces are set-valued, while the executable realization retains a
list carrier; filtering the two matched rows prevents representation-only
duplicates from changing concrete matcher enumeration. -/
def sourceProofAdditionalRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) : List Atom :=
  (canonicalPassiveRows context state ledger).filter fun row =>
    row != heapProofRow context.proofOwner index item &&
      row != MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item

/-- The source frame never duplicates the heap row already owned by the
canonical direct-hit slice. -/
@[simp] theorem heapProofRow_not_mem_sourceProofAdditionalRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) :
    heapProofRow context.proofOwner index item ∉
      sourceProofAdditionalRows context state ledger index item := by
  simp [sourceProofAdditionalRows]

/-- The source frame likewise never duplicates the matched node row. -/
@[simp] theorem nodeRow_not_mem_sourceProofAdditionalRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) :
    MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∉
      sourceProofAdditionalRows context state ledger index item := by
  simp [sourceProofAdditionalRows]

/-- Whole-state request space for one source-derived direct proof hit.  The
generated handler slice is extended by every other persistent row
reconstructed from the source state; no target row is accepted as an
occurrence witness. -/
def sourceProofRequestSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) : List Atom :=
  canonicalDirectProofSpace
      (directContextAtBoundary context state scanner index) item ++
    sourceProofAdditionalRows context state ledger index item

/-- The direct request merely separates its matched heap/node rows from the
remaining passive display; it never drops a source-derived passive row. -/
theorem canonicalPassiveRows_mem_sourceProofRequestSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {row : Atom}
    (member : row ∈ canonicalPassiveRows context state ledger) :
    row ∈ sourceProofRequestSpace context state ledger scanner index item := by
  by_cases heapExact : row = heapProofRow context.proofOwner index item
  · subst row
    simp [sourceProofRequestSpace, canonicalDirectProofSpace,
      directContextAtBoundary]
  by_cases nodeExact :
      row = MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item
  · subst row
    simp [sourceProofRequestSpace, canonicalDirectProofSpace,
      directContextAtBoundary]
  apply List.mem_append_right
  simp [sourceProofAdditionalRows, member, heapExact, nodeExact]

/-! ## Passive-row inversion -/

/-- The fixed constructor head of a source-derived dynamic row.  This small
projection lets later matcher proofs distinguish persistent source data without
decoding or reinterpreting its payload. -/
def compressedDynamicRowHead? : Atom → Option String
  | .expression (.symbol head :: _) => some head
  | _ => none

theorem compressedDynamicRowHead?_eq_some_iff
    (row : Atom) (head : String) :
    compressedDynamicRowHead? row = some head ↔
      ∃ tail, row = .expression (.symbol head :: tail) := by
  cases row with
  | grounded value => simp [compressedDynamicRowHead?]
  | symbol value => simp [compressedDynamicRowHead?]
  | «var» value => simp [compressedDynamicRowHead?]
  | expression atoms =>
      cases atoms with
      | nil => simp [compressedDynamicRowHead?]
      | cons atom tail =>
          cases atom with
          | grounded value => simp [compressedDynamicRowHead?]
          | symbol actual =>
              simp only [compressedDynamicRowHead?, Option.some.injEq]
              constructor
              · intro equal
                subst actual
                exact ⟨tail, rfl⟩
              · rintro ⟨candidateTail, equal⟩
                cases equal
                rfl
          | «var» value => simp [compressedDynamicRowHead?]
          | expression value => simp [compressedDynamicRowHead?]

/-- Invert an arbitrary proof-pointer row in an occurrence heap.  The physical
row recovers its exact heap position and the identity stored at that position;
the separately paired node row retains formula and source occurrence. -/
theorem heapProofRow_mem_heapProofRowsFrom_inverts
    {Other : Type} (proofOwner : Atom) (start : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other))
    (candidatePosition : Nat) (candidate : ProofOccurrence)
    (member : heapProofRow proofOwner candidatePosition candidate ∈
      heapProofRowsFrom proofOwner start heap) :
    ∃ index actual,
      heap[index]? = some (.occurrence actual) ∧
        candidatePosition = start + index ∧
        candidate.identity = actual.identity := by
  induction heap generalizing start candidatePosition with
  | nil => simp [heapProofRowsFrom] at member
  | cons entry remaining induction =>
      cases entry with
      | occurrence actual =>
          simp only [heapProofRowsFrom, List.mem_cons] at member
          rcases member with own | tail
          · have decoded :=
              (heapProofRow_eq_iff proofOwner candidatePosition start
                candidate actual).mp own
            exact ⟨0, actual, by simp, by simpa using decoded.1, decoded.2⟩
          · obtain ⟨index, found, lookup, positionEqual, identityEqual⟩ :=
              induction (start := start + 1)
                (candidatePosition := candidatePosition) tail
            refine ⟨index + 1, found, ?_, ?_, identityEqual⟩
            · simpa using lookup
            · omega
      | «opaque» value =>
          obtain ⟨index, found, lookup, positionEqual, identityEqual⟩ :=
            induction (start := start + 1)
              (candidatePosition := candidatePosition)
              (by simpa [heapProofRowsFrom] using member)
          refine ⟨index + 1, found, ?_, ?_, identityEqual⟩
          · simpa using lookup
          · omega

/-- Aligned source and occurrence lookups contribute their exact node row at
the corresponding shifted position. -/
theorem sourceNodeRow_mem_sourceNodeRowsFrom_of_getElem
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (start : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom)
    (index : Nat) (node : ProofNode source target) (occurrence : Atom)
    (nodeLookup : nodes[index]? = some node)
    (occurrenceLookup : occurrences[index]? = some occurrence) :
    MM2CompressedProofHeapEncoding.nodeRow proofOwner
        (displayedProofOccurrence (start + index) node occurrence) ∈
      sourceNodeRowsFrom proofOwner start nodes occurrences := by
  induction nodes generalizing start occurrences index with
  | nil => simp at nodeLookup
  | cons head nodes induction =>
      cases occurrences with
      | nil => simp at occurrenceLookup
      | cons headOccurrence occurrences =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq]
                at nodeLookup occurrenceLookup
              subst node
              subst occurrence
              simp [sourceNodeRowsFrom]
          | succ index =>
              simp only [List.getElem?_cons_succ]
                at nodeLookup occurrenceLookup
              have tail := induction (start := start + 1)
                (occurrences := occurrences) (index := index) nodeLookup
                occurrenceLookup
              have positionEqual :
                  start + Nat.succ index = start + 1 + index := by
                omega
              rw [positionEqual]
              exact List.mem_cons_of_mem _ tail

theorem sourceNodeRow_mem_sourceNodeRows_of_getElem
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (nodeId : Nat)
    (node : ProofNode source target) (occurrence : Atom)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some occurrence) :
    MM2CompressedProofHeapEncoding.nodeRow proofOwner
        (displayedProofOccurrence nodeId node occurrence) ∈
      sourceNodeRows proofOwner state ledger := by
  simpa [sourceNodeRows] using
    sourceNodeRow_mem_sourceNodeRowsFrom_of_getElem proofOwner 0 state.nodes
      ledger.occurrences nodeId node occurrence nodeLookup occurrenceLookup

/-- Invert an arbitrary node row in the pointwise source-node/occurrence
display.  The complete proof occurrence is reconstructed from the source
tables because the node-row encoder is injective. -/
theorem nodeRow_mem_sourceNodeRowsFrom_inverts
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (start : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom)
    (candidate : ProofOccurrence)
    (member : MM2CompressedProofHeapEncoding.nodeRow proofOwner candidate ∈
      sourceNodeRowsFrom proofOwner start nodes occurrences) :
    ∃ index node occurrence,
      nodes[index]? = some node ∧
        occurrences[index]? = some occurrence ∧
        candidate = displayedProofOccurrence (start + index) node occurrence := by
  induction nodes generalizing start occurrences with
  | nil => simp [sourceNodeRowsFrom] at member
  | cons node nodes induction =>
      cases occurrences with
      | nil => simp [sourceNodeRowsFrom] at member
      | cons occurrence occurrences =>
          simp only [sourceNodeRowsFrom, List.mem_cons] at member
          rcases member with own | tail
          · have exactOccurrence :=
              MM2CompressedProofHeapEncoding.nodeRow_injective proofOwner own
            exact ⟨0, node, occurrence, by simp, by simp,
              by simpa using exactOccurrence⟩
          · obtain ⟨index, foundNode, foundOccurrence, nodeLookup,
                occurrenceLookup, candidateExact⟩ :=
              induction (start := start + 1) (occurrences := occurrences) tail
            refine ⟨index + 1, foundNode, foundOccurrence, ?_, ?_, ?_⟩
            · simpa using nodeLookup
            · simpa using occurrenceLookup
            · have positionEqual : start + (index + 1) = start + 1 + index := by
                omega
              rw [positionEqual]
              exact candidateExact

theorem heapProofRowsFrom_head
    {Other : Type} (proofOwner : Atom) (position : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other)) :
    ∀ row, row ∈ heapProofRowsFrom proofOwner position heap →
      compressedDynamicRowHead? row = some "mm-compressed-heap-proof" := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | occurrence item =>
          intro row member
          simp only [heapProofRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · rfl
          · exact induction (position + 1) row tail
      | «opaque» value =>
          intro row member
          exact induction (position + 1) row
            (by simpa [heapProofRowsFrom] using member)

theorem assertionHeapRowsFrom_head
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    ∀ row, row ∈ assertionHeapRowsFrom proofOwner position heap →
      compressedDynamicRowHead? row =
        some "mm-compressed-heap-assertion" := by
  induction heap generalizing position with
  | nil => simp [assertionHeapRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | proof nodeId =>
          intro row member
          exact induction (position + 1) row
            (by simpa [assertionHeapRowsFrom] using member)
      | assertion assertion =>
          intro row member
          simp only [assertionHeapRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · rfl
          · exact induction (position + 1) row tail

theorem sourceNodeRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (position : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom) :
    ∀ row, row ∈ sourceNodeRowsFrom proofOwner position nodes occurrences →
      compressedDynamicRowHead? row = some "mm-compressed-node" := by
  induction nodes generalizing position occurrences with
  | nil => simp [sourceNodeRowsFrom]
  | cons node nodes induction =>
      cases occurrences with
      | nil => simp [sourceNodeRowsFrom]
      | cons occurrence occurrences =>
          intro row member
          simp only [sourceNodeRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · rfl
          · exact induction (position + 1) occurrences row tail

theorem sourceStackRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (stack : List Nat) :
    ∀ row, row ∈ sourceStackRowsFrom proofOwner state ledger position stack →
      compressedDynamicRowHead? row = some "mm-compressed-stack-cell" ∨
        compressedDynamicRowHead? row = some "mm-stack-cell" := by
  induction stack generalizing position with
  | nil => simp [sourceStackRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceStackRowsFrom] at member
      split at member
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at member
        rcases member with rfl | rfl | tail
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact induction (position + 1) row tail
      · exact induction (position + 1) row
          (by simpa only [List.nil_append] using member)

theorem sourceSaveRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (saves : List Nat) :
    ∀ row, row ∈ sourceSaveRowsFrom context state ledger position saves →
      compressedDynamicRowHead? row =
        some "mm-compressed-save-receipt" := by
  induction saves generalizing position with
  | nil => simp [sourceSaveRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceSaveRowsFrom] at member
      split at member
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at member
        rcases member with rfl | tail
        · rfl
        · exact induction (position + 1) row tail
      · exact induction (position + 1) row
          (by simpa only [List.nil_append] using member)

/-- Every persistent source row belongs to one of the seven data families
that may coexist at a public compressed-proof boundary. -/
theorem canonicalPassiveRows_head_cases
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) {row : Atom}
    (member : row ∈ canonicalPassiveRows context state ledger) :
    compressedDynamicRowHead? row = some "mm-compressed-heap-proof" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-assertion" ∨
      compressedDynamicRowHead? row = some "mm-compressed-node" ∨
      compressedDynamicRowHead? row = some "mm-compressed-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-compressed-save-receipt" := by
  simp only [canonicalPassiveRows, List.mem_append] at member
  rcases member with (((heap | assertion) | node) | stack) | save
  · exact Or.inl (heapProofRowsFrom_head context.proofOwner 0
      (displayedHeap state ledger) row (by simpa [heapProofRows] using heap))
  · exact Or.inr (Or.inl (assertionHeapRowsFrom_head context.proofOwner 0
      state.heap row (by simpa [assertionHeapRows] using assertion)))
  · exact Or.inr (Or.inr (Or.inl
      (sourceNodeRowsFrom_head context.proofOwner 0 state.nodes
        ledger.occurrences row (by simpa [sourceNodeRows] using node))))
  · rcases sourceStackRowsFrom_head context.proofOwner state ledger 0
        state.stack row (by simpa [sourceStackRows] using stack) with
      compact | normal
    · exact Or.inr (Or.inr (Or.inr (Or.inl compact)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl normal))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (sourceSaveRowsFrom_head context state ledger 0 state.saves row
        (by simpa [sourceSaveRows] using save))))))

/-- Filtering the two rows already owned by the direct-hit slice preserves
the same exhaustive head classification for the remaining source display. -/
theorem sourceProofAdditionalRows_head_cases
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) {row : Atom}
    (member : row ∈ sourceProofAdditionalRows context state ledger index item) :
    compressedDynamicRowHead? row = some "mm-compressed-heap-proof" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-assertion" ∨
      compressedDynamicRowHead? row = some "mm-compressed-node" ∨
      compressedDynamicRowHead? row = some "mm-compressed-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-compressed-save-receipt" := by
  exact canonicalPassiveRows_head_cases context state ledger
    (List.mem_filter.mp member).1

/-! ## Source boundary validity -/

/-- Structural facts needed for a source machine to inhabit a public boundary.
They are independent of target syntax: heap, stack, and saved proof identities
must name allocated nodes; assertion heap entries must come from the authored
source prefix; and every `Z` save advances the heap once. -/
structure SourceBoundaryWellFormed
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target) : Prop where
  heap_frontier :
    state.heap.length = context.initialHeapLength + state.saves.length
  heap_proof_nodes : forall nodeId,
    SourceGSLTCompressedTheorem.HeapEntry.proof nodeId ∈ state.heap ->
      nodeId < state.nodes.length
  heap_assertions_authored : forall assertion,
    SourceGSLTCompressedTheorem.HeapEntry.assertion assertion ∈ state.heap ->
      assertion ∈ source.assertions
  stack_nodes : forall nodeId, nodeId ∈ state.stack ->
    nodeId < state.nodes.length
  saved_nodes : forall nodeId, nodeId ∈ state.saves ->
    nodeId < state.nodes.length

/-- Every source proof action preserves the shared boundary invariant.  The
assertion case allocates exactly one fresh node; the save case advances heap
and save frontiers together without allocating a node. -/
theorem SourceBoundaryWellFormed.actionStep
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {action : CompressedAction}
    (wellFormed : SourceBoundaryWellFormed context before)
    (step : ActionStep before action after) :
    SourceBoundaryWellFormed context after := by
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      refine
        { heap_frontier := wellFormed.heap_frontier
          heap_proof_nodes := wellFormed.heap_proof_nodes
          heap_assertions_authored := wellFormed.heap_assertions_authored
          stack_nodes := ?_
          saved_nodes := wellFormed.saved_nodes }
      intro candidate member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact wellFormed.stack_nodes candidate old
      · exact (List.getElem?_eq_some_iff.mp nodeLookup).1
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      refine
        { heap_frontier := wellFormed.heap_frontier
          heap_proof_nodes := ?_
          heap_assertions_authored := wellFormed.heap_assertions_authored
          stack_nodes := ?_
          saved_nodes := ?_ }
      · intro nodeId heapMember
        have oldBound := wellFormed.heap_proof_nodes nodeId heapMember
        simpa using Nat.lt_succ_of_lt oldBound
      · intro nodeId stackMember
        simp only [List.mem_append, List.mem_singleton] at stackMember
        rcases stackMember with retainedMember | rfl
        · have beforeMember : nodeId ∈ before.stack := by
            rw [stack_eq]
            exact List.mem_append_left parents retainedMember
          have oldBound := wellFormed.stack_nodes nodeId beforeMember
          simpa using Nat.lt_succ_of_lt oldBound
        · simp
      · intro nodeId savedMember
        have oldBound := wellFormed.saved_nodes nodeId savedMember
        simpa using Nat.lt_succ_of_lt oldBound
  | save nodeId node stackTop nodeLookup =>
      refine
        { heap_frontier := ?_
          heap_proof_nodes := ?_
          heap_assertions_authored := ?_
          stack_nodes := wellFormed.stack_nodes
          saved_nodes := ?_ }
      · simp only [List.length_append, List.length_singleton]
        have frontier := wellFormed.heap_frontier
        omega
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | new
        · exact wellFormed.heap_proof_nodes candidate old
        · have candidate_eq : candidate = nodeId := by
            simpa using new
          subst candidate
          exact (List.getElem?_eq_some_iff.mp nodeLookup).1
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | impossible
        · exact wellFormed.heap_assertions_authored candidate old
        · cases impossible
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact wellFormed.saved_nodes candidate old
        · exact (List.getElem?_eq_some_iff.mp nodeLookup).1

/-- Arbitrary verified source execution preserves the same boundary facts.
This is the source-side induction spine later reused by target simulation. -/
theorem SourceBoundaryWellFormed.execute
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {actions : List CompressedAction}
    (wellFormed : SourceBoundaryWellFormed context before)
    (execution : Execute before actions after) :
    SourceBoundaryWellFormed context after := by
  induction execution with
  | nil => exact wellFormed
  | cons head tail induction =>
      exact induction (wellFormed.actionStep head)

/-- Scanner-synchronised source `Z` branch.  The byte decoder and semantic
machine perform the same save action, the shared boundary invariant is
preserved, the occurrence ledger is unchanged, and the heap receives the
existing stack-top node identity without allocating or copying a node. -/
theorem source_decoded_save_action_preserves_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) :
    SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.save] scannerAfter.phase)) ∧
      SourceBoundaryWellFormed context after ∧
      (ActionStep.occurrenceLedger step proofPosition ledger).occurrences =
        ledger.occurrences ∧
      ∃ nodeId node,
        before.stack.getLast? = some nodeId ∧
        before.nodes[nodeId]? = some node ∧
        after.nodes = before.nodes ∧
        after.heap = before.heap ++ [.proof nodeId] ∧
        after.saves = before.saves ++ [nodeId] := by
  refine ⟨receipt.sourceStep, wellFormed.actionStep step, ?_, ?_⟩
  · exact ActionStep.save_occurrenceLedger_unchanged step proofPosition ledger
  · exact ActionStep.save_reuses_identity step

/-- The displayed rich heap changes by exactly one proof occurrence under a
source save.  The occurrence is recovered from the derivation ledger at the
existing stack-top node; it is not supplied as target evidence. -/
theorem displayedHeap_save_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (step : ActionStep before .save after) :
    ∃ nodeId node sourceOccurrence,
      before.stack.getLast? = some nodeId ∧
      before.nodes[nodeId]? = some node ∧
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      displayedHeap after
          (ActionStep.occurrenceLedger step proofPosition ledger) =
        displayedHeap before ledger ++
          [.occurrence
            (displayedProofOccurrence nodeId node sourceOccurrence)] := by
  cases step with
  | save nodeId node stackTop nodeLookup =>
      have nodeBound := (List.getElem?_eq_some_iff.mp nodeLookup).1
      have occurrenceBound : nodeId < ledger.occurrences.length := by
        rw [ledger.aligned]
        exact nodeBound
      let sourceOccurrence := ledger.occurrences[nodeId]'occurrenceBound
      have occurrenceLookup :
          ledger.occurrences[nodeId]? = some sourceOccurrence := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨occurrenceBound, rfl⟩
      refine ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
        occurrenceLookup, ?_⟩
      simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms,
        displayedHeap, displayedHeapEntry, nodeLookup, occurrenceLookup]

/-! ## Exact dynamic ownership -/

/-- Heads reserved for compressed-verifier state, administrative work,
failures, and verdicts.  Structural successor tables and executable rules are
not dynamic rows and belong to the separately admitted verifier frame. -/
def dynamicRowHeads : List String :=
  ["mm-compressed-machine", "mm-compressed-scan",
   "mm-compressed-heap-proof", "mm-compressed-heap-assertion",
   "mm-compressed-node", "mm-compressed-stack-cell", "mm-stack-cell",
   "mm-compressed-save-receipt", "mm-compressed-control",
   "mm-compressed-header-control", "mm-compressed-step-pending",
   "mm-compressed-heap-lookup", "mm-compressed-assertion-context",
   "mm-compressed-assertion-resume", "mm-compressed-assertion-pc",
   "mm-compressed-assertion-done", "mm-normal-control",
   "mm-compressed-question-occurrence", "mm-proof-fault",
   "mm-compressed-proof-incomplete", "mm-accepted", "mm-rejected",
   "mm-source-theorem-admitted", "mm-source-theorem-rejected"]

def isDynamicRow : Atom -> Bool
  | .expression (.symbol head :: _) => dynamicRowHeads.contains head
  | _ => false

theorem heapProofRowsFrom_all_dynamic
    {Other : Type} (proofOwner : Atom) (position : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other)) :
    forall row, row ∈ heapProofRowsFrom proofOwner position heap ->
      isDynamicRow row = true := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | occurrence item =>
          intro row member
          simp only [heapProofRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [isDynamicRow, dynamicRowHeads, heapProofRow]
          · exact induction (position + 1) row tail
      | «opaque» value =>
          intro row member
          exact induction (position + 1) row
            (by simpa [heapProofRowsFrom] using member)

theorem assertionHeapRowsFrom_all_dynamic
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    forall row, row ∈ assertionHeapRowsFrom proofOwner position heap ->
      isDynamicRow row = true := by
  induction heap generalizing position with
  | nil => simp [assertionHeapRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | proof nodeId =>
          intro row member
          exact induction (position + 1) row
            (by simpa [assertionHeapRowsFrom] using member)
      | assertion assertion =>
          intro row member
          simp only [assertionHeapRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [isDynamicRow, dynamicRowHeads]
          · exact induction (position + 1) row tail

theorem sourceNodeRowsFrom_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (position : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom) :
    forall row,
      row ∈ sourceNodeRowsFrom proofOwner position nodes occurrences ->
        isDynamicRow row = true := by
  induction nodes generalizing position occurrences with
  | nil => simp [sourceNodeRowsFrom]
  | cons node nodes induction =>
      cases occurrences with
      | nil => simp [sourceNodeRowsFrom]
      | cons occurrence occurrences =>
          intro row member
          simp only [sourceNodeRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [isDynamicRow, dynamicRowHeads,
              MM2CompressedProofHeapEncoding.nodeRow]
          · exact induction (position + 1) occurrences row tail

theorem sourceStackRowsFrom_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat)
    (stack : List Nat) :
    forall row,
      row ∈ sourceStackRowsFrom proofOwner state ledger position stack ->
        isDynamicRow row = true := by
  induction stack generalizing position with
  | nil => simp [sourceStackRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceStackRowsFrom] at member
      split at member
      next node occurrence nodeLookup occurrenceLookup =>
        rw [List.mem_append] at member
        rcases member with ownRows | tail
        · simp only [List.mem_cons] at ownRows
          rcases ownRows with rfl | ownRows
          · simp [isDynamicRow, dynamicRowHeads, compressedStackRow]
          · rcases ownRows with rfl | impossible
            · simp [isDynamicRow, dynamicRowHeads, normalStackRow]
            · simp at impossible
        · exact induction (position + 1) row tail
      next => exact induction (position + 1) row (by simpa using member)

theorem sourceSaveRowsFrom_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat)
    (saves : List Nat) :
    forall row,
      row ∈ sourceSaveRowsFrom context state ledger position saves ->
        isDynamicRow row = true := by
  induction saves generalizing position with
  | nil => simp [sourceSaveRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceSaveRowsFrom] at member
      split at member
      next node occurrence nodeLookup occurrenceLookup =>
        rw [List.mem_append] at member
        rcases member with ownRows | tail
        · simp only [List.mem_singleton] at ownRows
          subst row
          simp [isDynamicRow, dynamicRowHeads, saveReceiptRow]
        · exact induction (position + 1) row tail
      next => exact induction (position + 1) row (by simpa using member)

/-- Every persistent row reconstructed from the source machine is dynamic;
none can be supplied by the static verifier frame. -/
theorem canonicalPassiveRows_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    forall row, row ∈ canonicalPassiveRows context state ledger ->
      isDynamicRow row = true := by
  intro row member
  simp only [canonicalPassiveRows] at member
  rcases List.mem_append.mp member with beforeSave | save
  · rcases List.mem_append.mp beforeSave with beforeStack | stack
    · rcases List.mem_append.mp beforeStack with beforeNode | node
      · rcases List.mem_append.mp beforeNode with heapProof | assertionHeap
        · exact heapProofRowsFrom_all_dynamic context.proofOwner 0
            (displayedHeap state ledger) row heapProof
        · exact assertionHeapRowsFrom_all_dynamic context.proofOwner 0
            state.heap row assertionHeap
      · exact sourceNodeRowsFrom_all_dynamic context.proofOwner 0
          state.nodes ledger.occurrences row node
    · exact sourceStackRowsFrom_all_dynamic context.proofOwner state ledger 0
        state.stack row stack
  · exact sourceSaveRowsFrom_all_dynamic context state ledger 0 state.saves
      row save

/-- Dynamic verifier rows are never executable scheduler shells. -/
theorem extractSupportedSourceExecFact_eq_none_of_dynamic
    (row : Atom) (dynamic : isDynamicRow row = true) :
    extractSupportedSourceExecFact row = none := by
  cases row with
  | grounded value => simp [isDynamicRow] at dynamic
  | symbol value => simp [isDynamicRow] at dynamic
  | «var» value => simp [isDynamicRow] at dynamic
  | expression atoms =>
      cases atoms with
      | nil => simp [isDynamicRow] at dynamic
      | cons head tail =>
          cases head with
          | grounded value => simp [isDynamicRow] at dynamic
          | «var» value => simp [isDynamicRow] at dynamic
          | expression value => simp [isDynamicRow] at dynamic
          | symbol name =>
              have notExec : name ≠ "exec" := by
                intro equal
                subst name
                simp [isDynamicRow, dynamicRowHeads] at dynamic
              simp [extractSupportedSourceExecFact, extractRawExecFact,
                notExec]

/-- Persistent source-machine rows contribute no executable rule and cannot
change scheduler inventory when attached to a generated handler slice. -/
theorem canonicalPassiveRows_no_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    cSupportedSourceExecFacts (canonicalPassiveRows context state ledger) = [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  exact extractSupportedSourceExecFact_eq_none_of_dynamic row
    (canonicalPassiveRows_all_dynamic context state ledger row member)

/-- Removing the two rows already supplied by the canonical matcher slice
does not introduce scheduler support into the remaining source frame. -/
theorem sourceProofAdditionalRows_no_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) :
    cSupportedSourceExecFacts
      (sourceProofAdditionalRows context state ledger index item) = [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  apply extractSupportedSourceExecFact_eq_none_of_dynamic row
  apply canonicalPassiveRows_all_dynamic context state ledger row
  exact (List.mem_filter.mp member).1

/-! ## Whole-state proof request -/

/-- Extending a direct proof request by scheduler-inert rows preserves its
exact scheduler inventory and positive matcher witness. -/
theorem DirectProofRequestFrame.append_scheduler_inert
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {state : SemanticState Other} {space extra : List Atom}
    (frame : DirectProofRequestFrame context item state space)
    (shell : speculativeDirectProofDirective.atom ∈ space)
    (inert : cSupportedSourceExecFacts extra = []) :
    DirectProofRequestFrame context item state (space ++ extra) := by
  have liveExact :
      directProofLive (space ++ extra) = directProofLive space ++ extra := by
    unfold directProofLive
    exact List.erase_append_left extra shell
  refine
    { control := frame.control
      found := frame.found
      heapRow := ?_
      nodeRow := ?_
      supported := ?_
      exactMatch := ?_ }
  · rw [liveExact]
    exact List.mem_append_left _ frame.heapRow
  · rw [liveExact]
    exact List.mem_append_left _ frame.nodeRow
  · unfold cSupportedSourceExecFacts at inert ⊢
    rw [List.filterMap_append, inert, List.append_nil]
    exact frame.supported
  · rcases frame.exactMatch with
      ⟨substitution, rowMember, pending, lookup, machine, nextMachine,
        compactStack, normalStack, resumedScan⟩
    refine ⟨substitution, ?_, pending, lookup, machine, nextMachine,
      compactStack, normalStack, resumedScan⟩
    have readIncluded : forall atom,
        atom ∈ speculativeDirectProofDirective.atom :: directProofLive space ->
          atom ∈ speculativeDirectProofDirective.atom ::
            directProofLive (space ++ extra) := by
      intro atom member
      simp only [List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (by
          rw [liveExact]
          exact List.mem_append_left _ member)
    unfold directProofMatcherRows at rowMember ⊢
    rw [List.mem_map] at rowMember ⊢
    obtain ⟨⟨matchedSubstitution, consumed⟩, matched, rfl⟩ := rowMember
    refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
    rw [speculative_direct_proof_input_exact] at matched ⊢
    exact Conformance.Computable.cmatchPattern_mono []
      (speculativeDirectProofDirective.atom :: directProofLive space)
      (speculativeDirectProofDirective.atom ::
        directProofLive (space ++ extra))
      _ readIncluded matchedSubstitution consumed matched

/-- An arbitrary source proof lookup constructs a whole-state target request
frame.  The proof occurrence comes only from the derivation ledger, while the
complete persistent machine display is scheduler-inert. -/
theorem source_proof_lookup_has_whole_state_request
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      DirectProofRequestFrame
        (directContextAtBoundary context state scanner index) item
        (displayedProofRequestState state ledger index)
        (sourceProofRequestSpace context state ledger scanner index item) := by
  obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof state ledger index nodeId node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let directContext := directContextAtBoundary context state scanner index
  apply DirectProofRequestFrame.append_scheduler_inert
    (canonical_direct_proof_request_frame directContext item
      (displayedProofRequestState state ledger index) (by rfl) (by
        simpa [directContext, directContextAtBoundary,
          displayedProofRequestState] using displayedLookup))
  · simp [canonicalDirectProofSpace]
  · exact sourceProofAdditionalRows_no_supported context state ledger index item

/-- The whole source-derived proof request performs the actual scheduled MM2
hit.  This is one concrete non-reflexive target step over the complete
persistent source display, not a fixture-local reconstruction. -/
theorem source_proof_lookup_whole_state_commutes
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      DirectProofHitCommutingSquare
        (directContextAtBoundary context state scanner index) item
        (displayedProofRequestState state ledger index)
        (sourceProofRequestSpace context state ledger scanner index item) := by
  obtain ⟨sourceOccurrence, occurrenceLookup, frame⟩ :=
    source_proof_lookup_has_whole_state_request context state ledger scanner
      index nodeId node heapLookup nodeLookup
  exact ⟨sourceOccurrence, occurrenceLookup,
    direct_proof_hit_commutes_of_exact_frame _ _ _ _ frame⟩

/-- The concrete scheduled step in a direct proof-hit square inhabits the
exact OSLF native target type generated from the executable reflective MM2
GSLT.  This is the same list-machine step stored by the square, not a second
reconstruction over a curated phase space. -/
theorem directProofHit_inhabits_exact_native_type
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (square : DirectProofHitCommutingSquare context item before space) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT .leaveInert)).satisfies space
        (reflectiveNativeListExactTargetNativeType .leaveInert
          (cFireReflectiveSourceExecFact
            space speculativeDirectProofDirective)).pred := by
  apply
    (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert space
      (cFireReflectiveSourceExecFact
        space speculativeDirectProofDirective)).2
  exact square.concreteStep

/-- Proof-action branch of the continuous simulation programme.  The source
step preserves boundary validity and allocates no occurrence, while the exact
source-derived whole-state request takes one actual scheduled MM2 step.  The
remaining scanner-resumption theorem must identify that concrete output with
the next public boundary. -/
theorem source_proof_action_has_whole_state_hit
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (wellFormed : SourceBoundaryWellFormed context state)
    (ledger : NodeOccurrenceLedger state) (proofPosition : Nat)
    (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    let after : MachineState source target :=
      { state with stack := state.stack ++ [nodeId] }
    ∃ sourceStep : ActionStep state (.step index) after,
      SourceBoundaryWellFormed context after ∧
        (ActionStep.occurrenceLedger sourceStep proofPosition ledger).occurrences =
          ledger.occurrences ∧
        ∃ sourceOccurrence,
          ledger.occurrences[nodeId]? = some sourceOccurrence ∧
          let item := displayedProofOccurrence nodeId node sourceOccurrence
          DirectProofHitCommutingSquare
            (directContextAtBoundary context state scanner index) item
            (displayedProofRequestState state ledger index)
            (sourceProofRequestSpace context state ledger scanner index item) := by
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  let sourceStep : ActionStep state (.step index) after :=
    .proof state index nodeId node heapLookup nodeLookup
  refine ⟨sourceStep, wellFormed.actionStep sourceStep, ?_, ?_⟩
  · simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms,
      heapOccurrenceKinds, heapLookup]
  · exact source_proof_lookup_whole_state_commutes context state ledger scanner
      index nodeId node heapLookup nodeLookup

/-- Scanner-synchronised proof branch.  One exact source byte occurrence
computes the proof index, the source machine performs that exact action, and
the corresponding whole-state MM2 request performs one nonempty scheduled
step inhabiting its exact OSLF target type.  The concrete output scanner row
is exactly the source scanner successor named by the receipt.

This theorem begins at the post-terminal pending request.  A later segment
theorem must prepend the concrete terminal-byte transition from the public
scanner boundary; no such transition is hidden here. -/
theorem source_decoded_proof_action_has_oslf_whole_state_hit
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (wellFormed : SourceBoundaryWellFormed context state)
    (ledger : NodeOccurrenceLedger state) (proofPosition : Nat)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      occurrence index)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    let after : MachineState source target :=
      { state with stack := state.stack ++ [nodeId] }
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let request :=
        sourceProofRequestSpace context state ledger scannerAfter index item
      let result := cFireReflectiveSourceExecFact request
        speculativeDirectProofDirective
      SourceStep (.request occurrence scannerBefore.phase)
          (.outcome occurrence (.decoded [.step index] scannerAfter.phase)) ∧
        ∃ sourceActionStep : ActionStep state (.step index) after,
          SourceBoundaryWellFormed context after ∧
          (ActionStep.occurrenceLedger sourceActionStep proofPosition
              ledger).occurrences = ledger.occurrences ∧
          DirectProofHitCommutingSquare
            (directContextAtBoundary context state scannerAfter index) item
            (displayedProofRequestState state ledger index) request ∧
          (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveNativeListExecGSLT .leaveInert)).satisfies request
              (reflectiveNativeListExactTargetNativeType .leaveInert result).pred ∧
          scannerRow context scannerAfter =
            (directContextAtBoundary context state scannerAfter index).resumedScanRow := by
  obtain ⟨sourceActionStep, afterWellFormed, ledgerEqual,
      sourceOccurrence, occurrenceLookup, square⟩ :=
    source_proof_action_has_whole_state_hit context state wellFormed ledger
      proofPosition scannerAfter index nodeId node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_, sourceActionStep,
    afterWellFormed, ledgerEqual, square, ?_, ?_⟩
  · exact receipt.sourceStep
  · exact directProofHit_inhabits_exact_native_type square
  · exact receipt.scannerRow_eq_resumedScanRow state

/-- A static verifier frame contains no source-machine state, administrative
cursor, proof result, failure, or verdict. -/
def StaticFrame (frame : List Atom) : Prop :=
  forall row, row ∈ frame -> isDynamicRow row = false

/-- Exact public-boundary relation.  Equality is extensional because an MM2
space is set-valued; occurrence multiplicity is retained inside row payloads. -/
structure RepresentsRunningBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (staticFrame space : List Atom) : Prop where
  source_wellFormed : SourceBoundaryWellFormed context state
  staticFrame_clean : StaticFrame staticFrame
  exact_rows : forall row,
    row ∈ space <->
      row ∈ canonicalBoundaryRows context state ledger scanner ++ staticFrame

/-- Physical refinement of the public-boundary relation used by actual MORK
execution.  The semantic relation identifies the rows; the permutation records
their multiplicity without imposing a fictitious storage order.  Ordinary and
compact-key duplicate freedom are retained separately because distinct atoms
can denote the same physical MORK support cell. -/
structure PhysicalRunningBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (staticFrame space : List Atom) : Prop where
  semantic : RepresentsRunningBoundary context state ledger scanner
    staticFrame space
  rows_perm : space.Perm
    (canonicalBoundaryRows context state ledger scanner ++ staticFrame)
  list_nodup : space.Nodup
  mork_nodup : MorkSupportNodup space

namespace PhysicalRunningBoundary

theorem canonical_with_frame_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    (canonicalBoundaryRows context state ledger scanner ++ staticFrame).Nodup :=
  represented.rows_perm.nodup_iff.mp represented.list_nodup

/-- The canonical presentation inherits compact-key duplicate freedom from
every physical permutation representing it. -/
theorem canonical_with_frame_mork_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    MorkSupportNodup
      (canonicalBoundaryRows context state ledger scanner ++ staticFrame) := by
  have physicalNodup : (space.map morkSupportKey).Nodup :=
    represented.mork_nodup
  unfold MorkSupportNodup
  exact (represented.rows_perm.map morkSupportKey).nodup_iff.mp
    physicalNodup

/-- Canonical source rows occur exactly once at a physical boundary. -/
theorem canonical_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    (canonicalBoundaryRows context state ledger scanner).Nodup :=
  represented.canonical_with_frame_nodup.of_append_left

/-- Static verifier rows occur exactly once at a physical boundary. -/
theorem staticFrame_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    staticFrame.Nodup :=
  represented.canonical_with_frame_nodup.of_append_right

/-- Source-derived rows and admitted static rows are disjoint.  This is a
multiplicity theorem, stronger than the dynamic/static membership argument. -/
theorem canonical_static_disjoint
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    List.Disjoint (canonicalBoundaryRows context state ledger scanner)
      staticFrame :=
  represented.canonical_with_frame_nodup.disjoint

/-- The physical relation retains the existing source-derived membership API. -/
theorem exact_rows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) (row : Atom) :
    row ∈ space ↔
      row ∈ canonicalBoundaryRows context state ledger scanner ++ staticFrame :=
  represented.rows_perm.mem_iff

/-- Executable-directive extraction respects the physical boundary
permutation. -/
theorem supportedFacts_perm
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    (cSupportedSourceExecFacts space).Perm
      (cSupportedSourceExecFacts
        (canonicalBoundaryRows context state ledger scanner ++ staticFrame)) := by
  exact represented.rows_perm.filterMap extractSupportedSourceExecFact

/-- Raw executable-shell extraction likewise respects physical row order. -/
theorem rawFacts_perm
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space) :
    (cRawExecFacts space).Perm
      (cRawExecFacts
        (canonicalBoundaryRows context state ledger scanner ++ staticFrame)) := by
  exact represented.rows_perm.filterMap extractRawExecFact

end PhysicalRunningBoundary

/-! ## Constructor, reflection, and negative controls -/

theorem canonical_represents_running_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (staticFrame : List Atom)
    (sourceWellFormed : SourceBoundaryWellFormed context state)
    (clean : StaticFrame staticFrame) :
    RepresentsRunningBoundary context state ledger scanner staticFrame
      (canonicalBoundaryRows context state ledger scanner ++ staticFrame) := by
  exact ⟨sourceWellFormed, clean, fun _ => Iff.rfl⟩

/-- Canonically ordered rows instantiate the physical boundary once both
ordinary and compact-key duplicate freedom have been established.  Those
premises are intentionally explicit: source well-formedness alone does not
rule out a representation collision. -/
theorem canonical_physical_running_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (staticFrame : List Atom)
    (sourceWellFormed : SourceBoundaryWellFormed context state)
    (clean : StaticFrame staticFrame)
    (listNodup :
      (canonicalBoundaryRows context state ledger scanner ++ staticFrame).Nodup)
    (morkNodup : MorkSupportNodup
      (canonicalBoundaryRows context state ledger scanner ++ staticFrame)) :
    PhysicalRunningBoundary context state ledger scanner staticFrame
      (canonicalBoundaryRows context state ledger scanner ++ staticFrame) := by
  exact
    { semantic := canonical_represents_running_boundary context state ledger
        scanner staticFrame sourceWellFormed clean
      rows_perm := .refl _
      list_nodup := listNodup
      mork_nodup := morkNodup }

/-- A rule-scoped MORK step preserves both duplicate-freedom obligations of a
physical boundary.  Re-establishing the source representation itself remains
the branch-specific semantic obligation. -/
theorem physical_boundary_ruleScoped_step_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space result : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      staticFrame space)
    (policy : UnsupportedExecPolicy)
    (moved : cRuleScopedSourceWorkQueueStep policy space = some result) :
    result.Nodup ∧ MorkSupportNodup result := by
  cases policy with
  | leaveInert =>
      unfold cRuleScopedSourceWorkQueueStep at moved
      cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => simp [selected] at moved
      | some directive =>
          simp only [selected, Option.some.injEq] at moved
          subst result
          exact
            ⟨cFireRuleScopedSourceExecFact_list_nodup space directive
                represented.list_nodup,
              cFireRuleScopedSourceExecFact_mork_nodup space directive
                represented.mork_nodup⟩
  | consume =>
      unfold cRuleScopedSourceWorkQueueStep at moved
      cases selected : selectNextScheduled (cRawExecFacts space) with
      | none => simp [selected] at moved
      | some raw =>
          simp only [selected] at moved
          cases decoded : decodeSupportedSourceExec raw with
          | none =>
              simp only [decoded, Option.some.injEq] at moved
              subst result
              exact
                ⟨morkEraseSupport_list_nodup space raw.atom
                    represented.list_nodup,
                  morkEraseSupport_nodup space raw.atom
                    represented.mork_nodup⟩
          | some directive =>
              simp only [decoded, Option.some.injEq] at moved
              subst result
              exact
                ⟨cFireRuleScopedSourceExecFact_list_nodup space directive
                    represented.list_nodup,
                  cFireRuleScopedSourceExecFact_mork_nodup space directive
                    represented.mork_nodup⟩

/-- Membership equivalence alone loses physical multiplicity: the duplicated
presentation and singleton presentation contain the same atoms but are not
permutations. -/
theorem duplicate_membership_is_not_physical (atom : Atom) :
    (∀ row, row ∈ [atom, atom] ↔ row ∈ [atom]) ∧
      ¬ [atom, atom].Perm [atom] := by
  constructor
  · intro row
    simp
  · intro perm
    have lengths := perm.length_eq
    simp at lengths

theorem machineRow_mem_canonicalBoundaryRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary) :
    machineRow context state ∈
      canonicalBoundaryRows context state ledger scanner := by
  simp [canonicalBoundaryRows]

theorem scannerRow_mem_canonicalBoundaryRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary) :
    scannerRow context scanner ∈
      canonicalBoundaryRows context state ledger scanner := by
  simp [canonicalBoundaryRows]

theorem represented_machineRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context state ledger scanner
      staticFrame space) :
    machineRow context state ∈ space := by
  apply (represented.exact_rows _).2
  exact List.mem_append_left _
    (machineRow_mem_canonicalBoundaryRows context state ledger scanner)

theorem represented_scannerRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context state ledger scanner
      staticFrame space) :
    scannerRow context scanner ∈ space := by
  apply (represented.exact_rows _).2
  exact List.mem_append_left _
    (scannerRow_mem_canonicalBoundaryRows context state ledger scanner)

/-- Every dynamic row in a represented space is reconstructed by the source
encoder.  No dynamic row can be justified merely by placing it in the frame. -/
theorem dynamic_row_source_derived
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context state ledger scanner
      staticFrame space)
    {row : Atom} (member : row ∈ space) (dynamic : isDynamicRow row = true) :
    row ∈ canonicalBoundaryRows context state ledger scanner := by
  have combined := (represented.exact_rows row).mp member
  rcases List.mem_append.mp combined with sourceRow | frameRow
  · exact sourceRow
  · have clean := represented.staticFrame_clean row frameRow
    rw [clean] at dynamic
    contradiction

@[simp] theorem machineRow_isDynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target) :
    isDynamicRow (machineRow context state) = true := by
  simp [isDynamicRow, dynamicRowHeads, machineRow]

@[simp] theorem scannerRow_isDynamic
    (context : BoundaryContext) (scanner : ScannerBoundary) :
    isDynamicRow (scannerRow context scanner) = true := by
  simp [isDynamicRow, dynamicRowHeads, scannerRow]

theorem machineRow_not_mem_staticFrame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    {frame : List Atom} (clean : StaticFrame frame) :
    machineRow context state ∉ frame := by
  intro member
  have := clean (machineRow context state) member
  simp at this

theorem scannerRow_not_mem_staticFrame
    (context : BoundaryContext) (scanner : ScannerBoundary)
    {frame : List Atom} (clean : StaticFrame frame) :
    scannerRow context scanner ∉ frame := by
  intro member
  have := clean (scannerRow context scanner) member
  simp at this

theorem represented_machineRow_source_derived
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context state ledger scanner
      staticFrame space)
    (member : machineRow context state ∈ space) :
    machineRow context state ∈
      canonicalBoundaryRows context state ledger scanner :=
  dynamic_row_source_derived represented member (machineRow_isDynamic _ _)

#print axioms canonical_represents_running_boundary
#print axioms PhysicalRunningBoundary.canonical_with_frame_nodup
#print axioms PhysicalRunningBoundary.canonical_with_frame_mork_nodup
#print axioms PhysicalRunningBoundary.canonical_nodup
#print axioms PhysicalRunningBoundary.staticFrame_nodup
#print axioms PhysicalRunningBoundary.canonical_static_disjoint
#print axioms PhysicalRunningBoundary.exact_rows
#print axioms PhysicalRunningBoundary.supportedFacts_perm
#print axioms PhysicalRunningBoundary.rawFacts_perm
#print axioms canonical_physical_running_boundary
#print axioms physical_boundary_ruleScoped_step_nodup
#print axioms duplicate_membership_is_not_physical
#print axioms ProofByteReceipt.sourceStep
#print axioms proofByteReceipt_of_terminal
#print axioms ProofByteReceipt.code_value
#print axioms ProofByteReceipt.code_eq_ofNat
#print axioms ProofByteReceipt.code_atom_eq_ofNat
#print axioms ProofByteReceipt.index_eq
#print axioms ProofByteReceipt.rejects_changed_index
#print axioms SaveByteReceipt.sourceStep
#print axioms saveByteReceipt_of_z
#print axioms SaveByteReceipt.rejects_changed_before_phase
#print axioms source_decoded_save_action_preserves_boundary
#print axioms displayedHeap_save_exact
#print axioms ProofByteReceipt.scannerRow_eq_resumedScanRow
#print axioms SourceBoundaryWellFormed.actionStep
#print axioms SourceBoundaryWellFormed.execute
#print axioms sourceStackRowsFrom_eq_of_nodes_occurrences
#print axioms sourceStackRowsFrom_append
#print axioms sourceStackRows_push
#print axioms displayedHeap_eq_of_heap_nodes_occurrences
#print axioms sourceNodeRows_eq_of_nodes_occurrences
#print axioms sourceSaveRowsFrom_eq_of_nodes_occurrences
#print axioms canonicalPassiveRows_push_mem_iff
#print axioms directContextAtBoundary_nextMachineRow_eq_machineRow_push
#print axioms canonicalPassiveRows_mem_sourceProofRequestSpace
#print axioms sourceNodeRow_mem_sourceNodeRowsFrom_of_getElem
#print axioms sourceNodeRow_mem_sourceNodeRows_of_getElem
#print axioms canonicalPassiveRows_all_dynamic
#print axioms canonicalPassiveRows_no_supported
#print axioms sourceProofAdditionalRows_no_supported
#print axioms heapProofRow_not_mem_sourceProofAdditionalRows
#print axioms nodeRow_not_mem_sourceProofAdditionalRows
#print axioms DirectProofRequestFrame.append_scheduler_inert
#print axioms source_proof_lookup_has_whole_state_request
#print axioms source_proof_lookup_whole_state_commutes
#print axioms directProofHit_inhabits_exact_native_type
#print axioms source_proof_action_has_whole_state_hit
#print axioms source_decoded_proof_action_has_oslf_whole_state_hit
#print axioms represented_machineRow
#print axioms represented_scannerRow
#print axioms dynamic_row_source_derived
#print axioms machineRow_isDynamic
#print axioms scannerRow_isDynamic
#print axioms machineRow_not_mem_staticFrame
#print axioms scannerRow_not_mem_staticFrame
#print axioms represented_machineRow_source_derived

end Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
