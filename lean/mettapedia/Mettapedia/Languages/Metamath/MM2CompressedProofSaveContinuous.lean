import Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd

/-!
# Continuous compressed-proof save square

This module lifts the bounded `Z` canary to an arbitrary source-derived
compressed-proof boundary.  The source byte scanner and semantic action
machine determine the saved occurrence.  An exact target matcher witness then
drives one real scheduled MM2 transition, classified through OSLF by both the
executable-list and authored support-valued native types.

The result proves two-sided correspondence for the complete dynamic successor
display: every canonical row is present, both obsolete controls are consumed,
and every dynamic output of every successful matcher assignment is recovered
from the source stack, node table, and occurrence ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Exact authored save surface -/

def saveScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position",
      .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
      .symbol "mm-compressed-just-completed-step", listAtom natAtom []]

def saveMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

def saveStackSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
      .var "stack-top", .var "stack-position"]

def saveStackCellTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof-owner",
      .var "stack-top", .var "node-id"]

def saveNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-id",
      .var "node-formula", .var "node-occurrence"]

def saveHeapSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-heap-owner", .var "proof-owner"],
      .var "heap-next", .var "next-heap-position"]

def afterSaveMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "next-heap-position", .var "node-next",
      .var "stack-position"]

def afterSaveScanTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-scan", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .symbol "mm-compressed-between-steps", listAtom natAtom []]

def savedHeapTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "heap-next", .var "node-id"]

def saveReceiptTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-save-receipt", .var "proof-owner",
      .var "heap-next", .var "node-id", .var "node-occurrence"]

def saveSelfTemplate : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "09", .symbol "mm-compressed-save"],
      .var "save-input", .var "save-output"]

def saveOwnedRuleTemplate (kind variableName : String) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol kind,
      .var variableName]

def savePatterns : List Atom :=
  [saveSelfTemplate, saveScanTemplate, saveMachineTemplate,
   saveStackSuccessorTemplate, saveStackCellTemplate, saveNodeTemplate,
   saveHeapSuccessorTemplate,
   saveOwnedRuleTemplate "prefix" "compressed-prefix-rule",
   saveOwnedRuleTemplate "terminal" "compressed-terminal-rule",
   saveOwnedRuleTemplate "proof" "compressed-proof-rule",
   saveOwnedRuleTemplate "invalid-byte" "compressed-invalid-byte-rule",
   saveOwnedRuleTemplate "question" "compressed-question-rule",
   saveOwnedRuleTemplate "question-open-fault"
     "compressed-question-open-fault-rule"]

def saveLive (space : List Atom) : List Atom :=
  space.erase compressedSaveDirective.atom

def saveMatcherRows (space : List Atom) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
    (compressedSaveDirective.atom :: saveLive space)
    compressedSaveDirective.rule.input).map Prod.fst

theorem compressedSaveDirective_sinks_exact :
    compressedSaveDirective.rule.tmpl.sinks =
      [.add
        (.expression
          [.symbol "exec",
            .expression [.symbol "09", .symbol "mm-compressed-save"],
            .var "save-input", .var "save-output"]),
       .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule"),
       .remove saveScanTemplate,
       .remove saveMachineTemplate,
       .add afterSaveMachineTemplate,
       .add afterSaveScanTemplate,
       .add savedHeapTemplate,
       .add saveReceiptTemplate] := by
  rfl

theorem compressedSaveDirective_input_exact :
    compressedSaveDirective.rule.input = .compat (mkPattern savePatterns) := by
  rfl

/-! ## Source-indexed request frame -/

/-- Exact consumed controls and successor instantiations for one matcher row
selected at a source-derived save boundary. -/
def ExactSaveMatch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary) (item : ProofOccurrence)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ saveMatcherRows space,
    instantiateTemplateAtom? substitution saveScanTemplate =
        some (scannerRow context scannerBefore) ∧
      instantiateTemplateAtom? substitution saveMachineTemplate =
        some (machineRow context before) ∧
      instantiateTemplateAtom? substitution afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateTemplateAtom? substitution afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateTemplateAtom? substitution savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateTemplateAtom? substitution saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item)

/-! ## Canonical symbolic matcher -/

/-- Pointwise node-table encoding: aligned source and ledger lookups place the
exact occurrence row at the same offset in the canonical MM2 node table. -/
theorem nodeRow_mem_sourceNodeRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (position : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom)
    (index : Nat) (node : ProofNode source target) (occurrence : Atom)
    (nodeLookup : nodes[index]? = some node)
    (occurrenceLookup : occurrences[index]? = some occurrence) :
    MM2CompressedProofHeapEncoding.nodeRow proofOwner
        (displayedProofOccurrence (position + index) node occurrence) ∈
      sourceNodeRowsFrom proofOwner position nodes occurrences := by
  induction nodes generalizing position occurrences index with
  | nil => simp at nodeLookup
  | cons head nodes induction =>
      cases occurrences with
      | nil => simp at occurrenceLookup
      | cons headOccurrence occurrences =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at nodeLookup occurrenceLookup
              subst node
              subst occurrence
              simp [sourceNodeRowsFrom]
          | succ index =>
              simp only [List.getElem?_cons_succ] at nodeLookup occurrenceLookup
              have tail := induction (position := position + 1)
                (occurrences := occurrences) (index := index) nodeLookup
                occurrenceLookup
              have positionEq :
                  position + Nat.succ index = position + 1 + index := by
                omega
              rw [positionEq]
              exact List.mem_cons_of_mem _ tail

/-- Pointwise stack encoding: a source stack lookup places both compact and
normal observations at the corresponding explicit MM2 stack position. -/
theorem compressedStackRow_mem_sourceStackRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat)
    (stack : List Nat) (index nodeId : Nat)
    (node : ProofNode source target) (occurrence : Atom)
    (stackLookup : stack[index]? = some nodeId)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some occurrence) :
    compressedStackRow proofOwner (position + index)
        (displayedProofOccurrence nodeId node occurrence) ∈
      sourceStackRowsFrom proofOwner state ledger position stack := by
  induction stack generalizing position index with
  | nil => simp at stackLookup
  | cons head stack induction =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at stackLookup
          subst head
          simp [sourceStackRowsFrom, nodeLookup, occurrenceLookup]
      | succ index =>
          simp only [List.getElem?_cons_succ] at stackLookup
          have tail := induction (position := position + 1) (index := index)
            stackLookup
          have positionEq :
              position + Nat.succ index = position + 1 + index := by
            omega
          rw [positionEq]
          simp only [sourceStackRowsFrom]
          split
          · exact List.mem_append_right _ tail
          · simpa only [List.nil_append] using tail

/-- The canonical complete node display contains the exact ledger occurrence
for every allocated source node. -/
theorem nodeRow_mem_sourceNodeRows
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
    nodeRow_mem_sourceNodeRowsFrom proofOwner 0 state.nodes ledger.occurrences
      nodeId node occurrence nodeLookup occurrenceLookup

/-- The canonical complete stack display contains the exact occurrence at any
source stack position. -/
theorem compressedStackRow_mem_sourceStackRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (stackPosition nodeId : Nat)
    (node : ProofNode source target) (occurrence : Atom)
    (stackLookup : state.stack[stackPosition]? = some nodeId)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some occurrence) :
    compressedStackRow proofOwner stackPosition
        (displayedProofOccurrence nodeId node occurrence) ∈
      sourceStackRows proofOwner state ledger := by
  simpa [sourceStackRows] using
    compressedStackRow_mem_sourceStackRowsFrom proofOwner state ledger 0
      state.stack stackPosition nodeId node occurrence stackLookup nodeLookup
      occurrenceLookup

/-- Equality of compact stack rows recovers the exact stack position and
proof-node identity.  Formula and source occurrence remain deliberately in
the separately matched node row. -/
theorem compressedStackRow_eq_iff (proofOwner : Atom)
    (leftPosition rightPosition : Nat) (left right : ProofOccurrence) :
    compressedStackRow proofOwner leftPosition left =
        compressedStackRow proofOwner rightPosition right ↔
      leftPosition = rightPosition ∧ left.identity = right.identity := by
  constructor
  · intro equal
    have atomsEqual := Atom.expression.inj equal
    have afterTag := (List.cons.inj atomsEqual).2
    have afterOwner := (List.cons.inj afterTag).2
    have positionEqual := (List.cons.inj afterOwner).1
    have identityEqual := (List.cons.inj (List.cons.inj afterOwner).2).1
    exact
      ⟨MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective
          (MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective
            positionEqual),
        identityEqual⟩
  · rintro ⟨rfl, identityEqual⟩
    simp only [compressedStackRow]
    rw [identityEqual]

/-- Inversion of an arbitrary compact stack row in the source-derived table.
The occurrence is reconstructed at the exact list position; no target packet
is accepted as evidence. -/
theorem compressedStackRow_mem_sourceStackRowsFrom_inverts
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (start : Nat) (stack : List Nat)
    (candidatePosition : Nat) (candidate : ProofOccurrence)
    (member : compressedStackRow proofOwner candidatePosition candidate ∈
      sourceStackRowsFrom proofOwner state ledger start stack) :
    ∃ index nodeId node occurrence,
      stack[index]? = some nodeId ∧
        state.nodes[nodeId]? = some node ∧
        ledger.occurrences[nodeId]? = some occurrence ∧
        candidatePosition = start + index ∧
        candidate.identity =
          (displayedProofOccurrence nodeId node occurrence).identity := by
  induction stack generalizing start with
  | nil => simp [sourceStackRowsFrom] at member
  | cons nodeId remaining induction =>
      simp only [sourceStackRowsFrom] at member
      split at member
      next node occurrence nodeLookup occurrenceLookup =>
        rw [List.mem_append] at member
        rcases member with own | tail
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at own
          rcases own with compact | normal
          · have decoded := (compressedStackRow_eq_iff proofOwner
                candidatePosition start candidate
                (displayedProofOccurrence nodeId node occurrence)).mp compact
            exact ⟨0, nodeId, node, occurrence, by simp, nodeLookup,
              occurrenceLookup, by simpa using decoded.1, decoded.2⟩
          · simp [compressedStackRow, normalStackRow] at normal
        · obtain ⟨index, foundId, foundNode, foundOccurrence, stackLookup,
              foundNodeLookup, foundOccurrenceLookup, positionEqual,
              identityEqual⟩ :=
              induction (start := start + 1) tail
          refine ⟨index + 1, foundId, foundNode, foundOccurrence, ?_,
            foundNodeLookup, foundOccurrenceLookup, ?_, identityEqual⟩
          · simpa using stackLookup
          · omega
      next =>
        obtain ⟨index, foundId, foundNode, foundOccurrence, stackLookup,
            foundNodeLookup, foundOccurrenceLookup, positionEqual,
            identityEqual⟩ :=
          induction (start := start + 1) (by simpa using member)
        refine ⟨index + 1, foundId, foundNode, foundOccurrence, ?_,
          foundNodeLookup, foundOccurrenceLookup, ?_, identityEqual⟩
        · simpa using stackLookup
        · omega

/-- Inversion of an arbitrary source-derived node row.  The complete proof
occurrence is recovered because the node encoder is injective. -/
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
            exact ⟨0, node, occurrence, by simp, by simp, by simpa using exactOccurrence⟩
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

def saveRuntimeCaptureRows : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     compressedQuestionOpenFaultRule]

/-- The six executable continuations carried through a compressed save.  A
verifier-presentation transformation may replace any field while preserving
the source save semantics and the surrounding matcher construction. -/
structure SaveRuntimeRuleBundle where
  prefixRule : Atom
  terminalRule : Atom
  proofRule : Atom
  invalidByteRule : Atom
  questionRule : Atom
  questionOpenFaultRule : Atom
deriving DecidableEq

/-- Presentation-relative authority for precisely the six executable values
republished by a save.  Resolution proves provenance; static classification
proves that republishing code cannot mint mutable proof state. -/
structure SaveRuntimeRuleAuthority
    (presentation : CompressedExecutablePresentation) where
  rules : SaveRuntimeRuleBundle
  prefixResolved : presentation.resolve .runtime "prefix" =
    some rules.prefixRule
  terminalResolved : presentation.resolve .runtime "terminal" =
    some rules.terminalRule
  proofResolved : presentation.resolve .runtime "proof" =
    some rules.proofRule
  invalidByteResolved : presentation.resolve .runtime "invalid-byte" =
    some rules.invalidByteRule
  questionResolved : presentation.resolve .runtime "question" =
    some rules.questionRule
  questionOpenFaultResolved : presentation.resolve .runtime
    "question-open-fault" = some rules.questionOpenFaultRule
  prefixStatic : isDynamicRow rules.prefixRule = false
  terminalStatic : isDynamicRow rules.terminalRule = false
  proofStatic : isDynamicRow rules.proofRule = false
  invalidByteStatic : isDynamicRow rules.invalidByteRule = false
  questionStatic : isDynamicRow rules.questionRule = false
  questionOpenFaultStatic : isDynamicRow rules.questionOpenFaultRule = false

def baseSaveRuntimeRuleBundle : SaveRuntimeRuleBundle where
  prefixRule := compressedPrefixRule
  terminalRule := compressedTerminalRule
  proofRule := compressedProofStepRule
  invalidByteRule := compressedInvalidByteRule
  questionRule := compressedQuestionRule
  questionOpenFaultRule := compressedQuestionOpenFaultRule

def baseSaveRuntimeRuleAuthority :
    SaveRuntimeRuleAuthority compressedBaseExecutablePresentation where
  rules := baseSaveRuntimeRuleBundle
  prefixResolved := rfl
  terminalResolved := rfl
  proofResolved := rfl
  invalidByteResolved := rfl
  questionResolved := rfl
  questionOpenFaultResolved := rfl
  prefixStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedPrefixRule]
  terminalStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedTerminalRule]
  proofStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedProofStepRule]
  invalidByteStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedInvalidByteRule]
  questionStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedQuestionRule]
  questionOpenFaultStatic := by
    simp [baseSaveRuntimeRuleBundle, isDynamicRow, dynamicRowHeads,
      compressedQuestionOpenFaultRule]

def SaveRuntimeRuleBundle.captureRows
    (rules : SaveRuntimeRuleBundle) : List Atom :=
  [compressedOwnedRuntimeRuleRow "prefix" rules.prefixRule,
   compressedOwnedRuntimeRuleRow "terminal" rules.terminalRule,
   compressedOwnedRuntimeRuleRow "proof" rules.proofRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" rules.invalidByteRule,
   compressedOwnedRuntimeRuleRow "question" rules.questionRule,
   compressedOwnedRuntimeRuleRow "question-open-fault"
     rules.questionOpenFaultRule]

/-- Runtime rules activated by a successful compressed save.  These are the
payloads protected by `captureRows`, in the exact authored sink order. -/
def SaveRuntimeRuleBundle.payloadRows
    (rules : SaveRuntimeRuleBundle) : List Atom :=
  [rules.prefixRule, rules.terminalRule, rules.proofRule,
   rules.invalidByteRule, rules.questionRule, rules.questionOpenFaultRule]

@[simp] theorem baseSaveRuntimeRuleBundle_captureRows :
    baseSaveRuntimeRuleBundle.captureRows = saveRuntimeCaptureRows := by
  rfl

/-- Minimal source-indexed surface on which the complete save input pattern
has a symbolic matcher row.  The successor spines remain verifier structure;
the scanner, machine, stack, and node observations are source-derived. -/
def canonicalSaveMatchSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore : ScannerBoundary) (stackTopPosition : Nat)
    (item : ProofOccurrence) : List Atom :=
  [compressedSaveDirective.atom, scannerRow context scannerBefore,
   machineRow context before,
   compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   compressedStackRow context.proofOwner stackTopPosition item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom] ++
    saveRuntimeCaptureRows

/-- Presentation-parametric canonical save surface.  Only the inert runtime
carrier payloads vary; source machine, scanner, stack, node, and frontier rows
remain unchanged. -/
def canonicalSaveMatchSpaceFor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target) (scannerBefore : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : List Atom :=
  [compressedSaveDirective.atom, scannerRow context scannerBefore,
   machineRow context before,
   compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   compressedStackRow context.proofOwner stackTopPosition item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom] ++
    rules.captureRows

@[simp] theorem canonicalSaveMatchSpaceFor_base
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore : ScannerBoundary) (stackTopPosition : Nat)
    (item : ProofOccurrence) :
    canonicalSaveMatchSpaceFor baseSaveRuntimeRuleBundle context before
        scannerBefore stackTopPosition item =
      canonicalSaveMatchSpace context before scannerBefore stackTopPosition
        item := by
  rfl

private def saveSelfInput : Atom :=
  match compressedSaveDirective.atom with
  | .expression [.symbol "exec", _location, input, _output] => input
  | _ => .symbol "mm-impossible-save-input"

private def saveSelfOutput : Atom :=
  match compressedSaveDirective.atom with
  | .expression [.symbol "exec", _location, _input, output] => output
  | _ => .symbol "mm-impossible-save-output"

private def saveSelfSubst : Subst :=
  [("save-output", saveSelfOutput), ("save-input", saveSelfInput)]

private def saveScanSubst (context : BoundaryContext)
    (before after : ScannerBoundary) : Subst :=
  [("remaining-bytes",
      listAtom natAtom (after.remainingBytes.map UInt8.toNat)),
   ("word-position", natAtom before.wordPosition),
   ("proof-owner", context.proofOwner),
   ("scope-owner", context.scopeOwner)] ++ saveSelfSubst

private def saveMachineSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary) : Subst :=
  [("stack-position", (CompressedIndexCode.ofNat before.stack.length).atom),
   ("node-next", (CompressedIndexCode.ofNat before.nodes.length).atom),
   ("heap-next", (CompressedIndexCode.ofNat before.heap.length).atom)] ++
    saveScanSubst context scannerBefore scannerAfter

private def saveStackSuccessorSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) : Subst :=
  [("stack-top", (CompressedIndexCode.ofNat stackTopPosition).atom)] ++
    saveMachineSubst context before scannerBefore scannerAfter

private def saveStackCellSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("node-id", item.identity)] ++
    saveStackSuccessorSubst context before scannerBefore scannerAfter
      stackTopPosition

private def saveNodeSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("node-occurrence", item.value.sourceOccurrence),
   ("node-formula", item.value.formula)] ++
    saveStackCellSubst context before scannerBefore scannerAfter
      stackTopPosition item

private def saveHeapSuccessorSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("next-heap-position",
      (CompressedIndexCode.ofNat (before.heap.length + 1)).atom)] ++
    saveNodeSubst context before scannerBefore scannerAfter stackTopPosition item

private def savePrefixSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-prefix-rule", compressedPrefixRule)] ++
    saveHeapSuccessorSubst context before scannerBefore scannerAfter
      stackTopPosition item

private def saveTerminalSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-terminal-rule", compressedTerminalRule)] ++
    savePrefixSubst context before scannerBefore scannerAfter stackTopPosition item

private def saveProofSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-proof-rule", compressedProofStepRule)] ++
    saveTerminalSubst context before scannerBefore scannerAfter stackTopPosition item

private def saveInvalidSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-invalid-byte-rule", compressedInvalidByteRule)] ++
    saveProofSubst context before scannerBefore scannerAfter stackTopPosition item

private def saveQuestionSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-question-rule", compressedQuestionRule)] ++
    saveInvalidSubst context before scannerBefore scannerAfter stackTopPosition item

private def saveFinalSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-question-open-fault-rule", compressedQuestionOpenFaultRule)] ++
    saveQuestionSubst context before scannerBefore scannerAfter stackTopPosition item

/-- First presentation-selected runtime binding, following the source-derived
heap-successor portion of the save matcher. -/
private def saveRuntimePrefixSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-prefix-rule", rules.prefixRule)] ++
    saveHeapSuccessorSubst context before scannerBefore scannerAfter
      stackTopPosition item

private def saveRuntimeTerminalSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-terminal-rule", rules.terminalRule)] ++
    saveRuntimePrefixSubst rules context before scannerBefore scannerAfter
      stackTopPosition item

private def saveRuntimeProofSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-proof-rule", rules.proofRule)] ++
    saveRuntimeTerminalSubst rules context before scannerBefore scannerAfter
      stackTopPosition item

private def saveRuntimeInvalidSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-invalid-byte-rule", rules.invalidByteRule)] ++
    saveRuntimeProofSubst rules context before scannerBefore scannerAfter
      stackTopPosition item

private def saveRuntimeQuestionSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-question-rule", rules.questionRule)] ++
    saveRuntimeInvalidSubst rules context before scannerBefore scannerAfter
      stackTopPosition item

/-- Final substitution produced after matching the six presentation-selected
runtime carriers.  Their bindings are kept separate from the source-derived
machine portion of the substitution. -/
private def saveRuntimeFinalSubst
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : Subst :=
  [("compressed-question-open-fault-rule", rules.questionOpenFaultRule)] ++
    saveRuntimeQuestionSubst rules context before scannerBefore scannerAfter
      stackTopPosition item

private theorem saveSelf_match :
    Conformance.Computable.cmatchAtom [] saveSelfTemplate
      compressedSaveDirective.atom = some saveSelfSubst := by
  decide +kernel

private theorem saveScan_match
    {context : BoundaryContext} {before after : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context before after occurrence) :
    Conformance.Computable.cmatchAtom saveSelfSubst saveScanTemplate
      (scannerRow context before) = some (saveScanSubst context before after) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases before with ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  rcases after with
    ⟨nextWordPosition, nextBytePosition, nextRemainingBytes, nextPhase⟩
  rcases occurrence with ⟨occurrenceOwner, occurrencePosition, byte⟩
  have headExact : remainingBytes = byte :: nextRemainingBytes :=
    receipt.consumes_head
  subst remainingBytes
  have wordExact : nextWordPosition = wordPosition :=
    by simpa using receipt.word_position_eq
  subst nextWordPosition
  have beforePhase : phase = .completed := receipt.phase_before
  subst phase
  have afterPhase : nextPhase = .between := receipt.phase_after
  subst nextPhase
  simp [saveScanSubst, saveSelfSubst, saveSelfInput, saveSelfOutput,
    saveScanTemplate, scannerRow, listAtom, consTag, natAtom,
    ScannerPhase.atom, ScannerPhase.reversePrefix, receipt.byte_is_z,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveMachine_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary) :
    Conformance.Computable.cmatchAtom
        (saveScanSubst context scannerBefore scannerAfter) saveMachineTemplate
        (machineRow context before) =
      some (saveMachineSubst context before scannerBefore scannerAfter) := by
  cases context
  cases before
  simp [saveMachineSubst, saveScanSubst, saveSelfSubst, saveSelfInput,
    saveSelfOutput, saveMachineTemplate, machineRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveStackSuccessor_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) :
    Conformance.Computable.cmatchAtom
        (saveMachineSubst context before scannerBefore scannerAfter)
        saveStackSuccessorTemplate
        (compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
          (CompressedIndexCode.ofNat stackTopPosition).atom
          (CompressedIndexCode.ofNat before.stack.length).atom) =
      some (saveStackSuccessorSubst context before scannerBefore scannerAfter
        stackTopPosition) := by
  cases context
  cases before
  simp [saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
    saveSelfSubst, saveSelfInput, saveSelfOutput,
    saveStackSuccessorTemplate, compressedIndexSuccessorRow,
    compressedStackOwner, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveStackCell_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom
        (saveStackSuccessorSubst context before scannerBefore scannerAfter
          stackTopPosition) saveStackCellTemplate
        (compressedStackRow context.proofOwner stackTopPosition item) =
      some (saveStackCellSubst context before scannerBefore scannerAfter
        stackTopPosition item) := by
  cases context
  cases before
  cases item
  simp [saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
    saveScanSubst, saveSelfSubst, saveSelfInput, saveSelfOutput,
    saveStackCellTemplate, compressedStackRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveNode_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom
        (saveStackCellSubst context before scannerBefore scannerAfter
          stackTopPosition item) saveNodeTemplate
        (MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item) =
      some (saveNodeSubst context before scannerBefore scannerAfter
        stackTopPosition item) := by
  cases context
  cases before
  rcases item with ⟨identity, value⟩
  cases value
  simp [saveNodeSubst, saveStackCellSubst, saveStackSuccessorSubst,
    saveMachineSubst, saveScanSubst, saveSelfSubst, saveSelfInput,
    saveSelfOutput, saveNodeTemplate, MM2CompressedProofHeapEncoding.nodeRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveHeapSuccessor_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    Conformance.Computable.cmatchAtom
        (saveNodeSubst context before scannerBefore scannerAfter
          stackTopPosition item) saveHeapSuccessorTemplate
        (compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat before.heap.length).atom
          (CompressedIndexCode.ofNat (before.heap.length + 1)).atom) =
      some (saveHeapSuccessorSubst context before scannerBefore scannerAfter
        stackTopPosition item) := by
  cases context
  cases before
  cases item
  simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
    saveStackSuccessorSubst, saveMachineSubst, saveScanSubst, saveSelfSubst,
    saveSelfInput, saveSelfOutput, saveHeapSuccessorTemplate,
    compressedIndexSuccessorRow, compressedHeapOwner,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem saveOwnedRule_match
    (before : Subst) (kind variableName : String) (rule : Atom)
    (fresh : Subst.lookup before variableName = none) :
    Conformance.Computable.cmatchAtom before
        (saveOwnedRuleTemplate kind variableName)
        (compressedOwnedRuntimeRuleRow kind rule) =
      some ((variableName, rule) :: before) := by
  simp [saveOwnedRuleTemplate, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, fresh]

private theorem cmatchPattern_go_cons_of_selected
    {space : List Atom} {pattern : Atom} {patterns : List Atom}
    {substitutionIn substitutionMid substitutionOut : Subst}
    {consumedIn consumedOut : List Atom} {concrete : Atom}
    (present : concrete ∈ space)
    (matched : Conformance.Computable.cmatchAtom substitutionIn pattern
      concrete = some substitutionMid)
    (continued : (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space patterns substitutionMid
        (concrete :: consumedIn)) :
    (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space (pattern :: patterns)
        substitutionIn consumedIn := by
  simp only [Conformance.Computable.cmatchPattern.go, List.mem_flatMap]
  refine ⟨(substitutionMid, concrete), ?_, continued⟩
  rw [List.mem_filterMap]
  exact ⟨concrete, present, by rw [matched]; rfl⟩

private def canonicalSaveConsumed
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scannerBefore : ScannerBoundary) (stackTopPosition : Nat)
    (item : ProofOccurrence) : List Atom :=
  [compressedOwnedRuntimeRuleRow "question-open-fault"
      compressedQuestionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "question" compressedQuestionRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" compressedInvalidByteRule,
   compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule,
   compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule,
   compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule,
   compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   compressedStackRow context.proofOwner stackTopPosition item,
   compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   machineRow context before, scannerRow context scannerBefore,
   compressedSaveDirective.atom]

private def canonicalSaveConsumedFor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (context : BoundaryContext)
    (before : MachineState source target) (scannerBefore : ScannerBoundary)
    (stackTopPosition : Nat) (item : ProofOccurrence) : List Atom :=
  [compressedOwnedRuntimeRuleRow "question-open-fault"
      rules.questionOpenFaultRule,
   compressedOwnedRuntimeRuleRow "question" rules.questionRule,
   compressedOwnedRuntimeRuleRow "invalid-byte" rules.invalidByteRule,
   compressedOwnedRuntimeRuleRow "proof" rules.proofRule,
   compressedOwnedRuntimeRuleRow "terminal" rules.terminalRule,
   compressedOwnedRuntimeRuleRow "prefix" rules.prefixRule,
   compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   compressedStackRow context.proofOwner stackTopPosition item,
   compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   machineRow context before, scannerRow context scannerBefore,
   compressedSaveDirective.atom]

/-- The canonical save surface has one genuine source-parameterized matcher
row; no closed fixture normalization is involved. -/
theorem canonicalSaveMatchSpace_has_match
    {context : BoundaryContext} {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (stackTopPosition : Nat)
    (item : ProofOccurrence) :
    (saveFinalSubst context before scannerBefore scannerAfter stackTopPosition
        item,
      canonicalSaveConsumed context before scannerBefore stackTopPosition item) ∈
      Conformance.Computable.cmatchInputSpec []
        (canonicalSaveMatchSpace context before scannerBefore stackTopPosition
          item) compressedSaveDirective.rule.input := by
  rw [compressedSaveDirective_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern]
  unfold savePatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedSaveDirective.atom)
  · simp [canonicalSaveMatchSpace]
  · exact saveSelf_match
  apply cmatchPattern_go_cons_of_selected
    (concrete := scannerRow context scannerBefore)
  · simp [canonicalSaveMatchSpace]
  · exact saveScan_match receipt
  apply cmatchPattern_go_cons_of_selected
    (concrete := machineRow context before)
  · simp [canonicalSaveMatchSpace]
  · exact saveMachine_match context before scannerBefore scannerAfter
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedIndexSuccessorRow
      (compressedStackOwner context.proofOwner)
      (CompressedIndexCode.ofNat stackTopPosition).atom
      (CompressedIndexCode.ofNat before.stack.length).atom)
  · simp [canonicalSaveMatchSpace]
  · exact saveStackSuccessor_match context before scannerBefore scannerAfter
      stackTopPosition
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedStackRow context.proofOwner stackTopPosition item)
  · simp [canonicalSaveMatchSpace]
  · exact saveStackCell_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := MM2CompressedProofHeapEncoding.nodeRow
      context.proofOwner item)
  · simp [canonicalSaveMatchSpace]
  · exact saveNode_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedIndexSuccessorRow
      (compressedHeapOwner context.proofOwner)
      (CompressedIndexCode.ofNat before.heap.length).atom
      (CompressedIndexCode.ofNat (before.heap.length + 1)).atom)
  · simp [canonicalSaveMatchSpace]
  · exact saveHeapSuccessor_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "prefix" compressedPrefixRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
      saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "terminal"
      compressedTerminalRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst,
      saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
      saveScanSubst, saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "proof" compressedProofStepRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst,
      saveMachineSubst, saveScanSubst, saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "invalid-byte"
      compressedInvalidByteRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
      saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question"
      compressedQuestionRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst,
      saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
      saveScanSubst, saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question-open-fault"
      compressedQuestionOpenFaultRule)
  · simp [canonicalSaveMatchSpace, saveRuntimeCaptureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst,
      saveMachineSubst, saveScanSubst, saveSelfSubst, Subst.lookup]
  simp [Conformance.Computable.cmatchPattern.go, canonicalSaveConsumed,
    saveFinalSubst, saveQuestionSubst, saveInvalidSubst, saveProofSubst,
    saveTerminalSubst, savePrefixSubst]

/-- The symbolic save matcher is uniform in all six executable continuation
payloads.  This is the reusable constructor needed by verifier-presentation
transformations: changing a runtime rule changes only the typed bundle and
its inert carrier row. -/
theorem canonicalSaveMatchSpaceFor_has_match
    {context : BoundaryContext} {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle) (before : MachineState source target)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
        stackTopPosition item,
      canonicalSaveConsumedFor rules context before scannerBefore
        stackTopPosition item) ∈
      Conformance.Computable.cmatchInputSpec []
        (canonicalSaveMatchSpaceFor rules context before scannerBefore
          stackTopPosition item) compressedSaveDirective.rule.input := by
  rw [compressedSaveDirective_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern]
  unfold savePatterns
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedSaveDirective.atom)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveSelf_match
  apply cmatchPattern_go_cons_of_selected
    (concrete := scannerRow context scannerBefore)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveScan_match receipt
  apply cmatchPattern_go_cons_of_selected
    (concrete := machineRow context before)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveMachine_match context before scannerBefore scannerAfter
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedIndexSuccessorRow
      (compressedStackOwner context.proofOwner)
      (CompressedIndexCode.ofNat stackTopPosition).atom
      (CompressedIndexCode.ofNat before.stack.length).atom)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveStackSuccessor_match context before scannerBefore scannerAfter
      stackTopPosition
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedStackRow context.proofOwner stackTopPosition item)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveStackCell_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := MM2CompressedProofHeapEncoding.nodeRow
      context.proofOwner item)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveNode_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedIndexSuccessorRow
      (compressedHeapOwner context.proofOwner)
      (CompressedIndexCode.ofNat before.heap.length).atom
      (CompressedIndexCode.ofNat (before.heap.length + 1)).atom)
  · simp [canonicalSaveMatchSpaceFor]
  · exact saveHeapSuccessor_match context before scannerBefore scannerAfter
      stackTopPosition item
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "prefix" rules.prefixRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
      saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "terminal" rules.terminalRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst,
      saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
      saveScanSubst, saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "proof" rules.proofRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
      saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "invalid-byte"
      rules.invalidByteRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst,
      saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
      saveScanSubst, saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question" rules.questionRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
      saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
      saveSelfSubst, Subst.lookup]
  apply cmatchPattern_go_cons_of_selected
    (concrete := compressedOwnedRuntimeRuleRow "question-open-fault"
      rules.questionOpenFaultRule)
  · simp [canonicalSaveMatchSpaceFor, SaveRuntimeRuleBundle.captureRows]
  · apply saveOwnedRule_match
    simp [saveHeapSuccessorSubst, saveNodeSubst,
      saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
      saveScanSubst, saveSelfSubst, Subst.lookup]
  simp [Conformance.Computable.cmatchPattern.go,
    canonicalSaveConsumedFor, saveRuntimeFinalSubst,
    saveRuntimeQuestionSubst, saveRuntimeInvalidSubst,
    saveRuntimeProofSubst, saveRuntimeTerminalSubst,
    saveRuntimePrefixSubst]

private theorem saveFinalSubst_instantiates_outputs
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {occurrence : ByteOccurrence}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) (stackTopPosition : Nat)
    (item : ProofOccurrence) :
    instantiateTemplateAtom?
        (saveFinalSubst context before scannerBefore scannerAfter
          stackTopPosition item) afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateTemplateAtom?
        (saveFinalSubst context before scannerBefore scannerAfter
          stackTopPosition item) afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateTemplateAtom?
        (saveFinalSubst context before scannerBefore scannerAfter
          stackTopPosition item) savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateTemplateAtom?
        (saveFinalSubst context before scannerBefore scannerAfter
          stackTopPosition item) saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases scannerBefore with
    ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  rcases scannerAfter with
    ⟨nextWordPosition, nextBytePosition, nextRemainingBytes, nextPhase⟩
  have wordExact : nextWordPosition = wordPosition :=
    by simpa using receipt.word_position_eq
  subst nextWordPosition
  have afterPhase : nextPhase = .between := receipt.phase_after
  subst nextPhase
  cases step
  simp [saveFinalSubst, saveQuestionSubst, saveInvalidSubst, saveProofSubst,
    saveTerminalSubst, savePrefixSubst, saveHeapSuccessorSubst, saveNodeSubst,
    saveStackCellSubst, saveStackSuccessorSubst, saveMachineSubst,
    saveScanSubst, saveSelfSubst, saveSelfInput, saveSelfOutput,
    afterSaveMachineTemplate, afterSaveScanTemplate, savedHeapTemplate,
    saveReceiptTemplate, machineRow, scannerRow, heapProofRow, saveReceiptRow,
    instantiateTemplateAtom?, applySubst, applySubst.applySubstList,
    templateCovered, templatesCovered, listAtom, ScannerPhase.atom,
    ScannerPhase.reversePrefix, Subst.lookup]

private theorem saveRuntimeFinalSubst_instantiates_outputs
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {occurrence : ByteOccurrence}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) (rules : SaveRuntimeRuleBundle)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases scannerBefore with
    ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  rcases scannerAfter with
    ⟨nextWordPosition, nextBytePosition, nextRemainingBytes, nextPhase⟩
  have wordExact : nextWordPosition = wordPosition :=
    by simpa using receipt.word_position_eq
  subst nextWordPosition
  have afterPhase : nextPhase = .between := receipt.phase_after
  subst nextPhase
  cases step
  simp [saveRuntimeFinalSubst, saveRuntimeQuestionSubst,
    saveRuntimeInvalidSubst, saveRuntimeProofSubst,
    saveRuntimeTerminalSubst, saveRuntimePrefixSubst,
    saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
    saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
    saveSelfSubst, saveSelfInput, saveSelfOutput, afterSaveMachineTemplate,
    afterSaveScanTemplate, savedHeapTemplate, saveReceiptTemplate,
    machineRow, scannerRow, heapProofRow, saveReceiptRow,
    instantiateTemplateAtom?, applySubst, applySubst.applySubstList,
    templateCovered, templatesCovered, listAtom, ScannerPhase.atom,
    ScannerPhase.reversePrefix, Subst.lookup]

private theorem saveRuntimeFinalSubst_instantiates_inputs
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {occurrence : ByteOccurrence}
    {context : BoundaryContext} {before : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (rules : SaveRuntimeRuleBundle) (stackTopPosition : Nat)
    (item : ProofOccurrence) :
    instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) saveScanTemplate =
        some (scannerRow context scannerBefore) ∧
      instantiateTemplateAtom?
        (saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
          stackTopPosition item) saveMachineTemplate =
        some (machineRow context before) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases scannerBefore with
    ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  rcases scannerAfter with
    ⟨nextWordPosition, nextBytePosition, nextRemainingBytes, nextPhase⟩
  have remainingExact :
      remainingBytes = occurrence.byte :: nextRemainingBytes := by
    simpa using receipt.consumes_head
  subst remainingBytes
  have phaseExact : phase = .completed := receipt.phase_before
  subst phase
  simp [saveRuntimeFinalSubst, saveRuntimeQuestionSubst,
    saveRuntimeInvalidSubst, saveRuntimeProofSubst,
    saveRuntimeTerminalSubst, saveRuntimePrefixSubst,
    saveHeapSuccessorSubst, saveNodeSubst, saveStackCellSubst,
    saveStackSuccessorSubst, saveMachineSubst, saveScanSubst,
    saveSelfSubst, saveSelfInput, saveSelfOutput, saveScanTemplate,
    saveMachineTemplate, machineRow, scannerRow, receipt.byte_is_z,
    instantiateTemplateAtom?, applySubst, applySubst.applySubstList,
    templateCovered, templatesCovered, listAtom, natAtom, ScannerPhase.atom,
    ScannerPhase.reversePrefix, Subst.lookup]

/-- Row-exact source save realization for an arbitrary presentation-selected
runtime bundle. -/
theorem canonicalSaveMatchSpaceFor_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) (rules : SaveRuntimeRuleBundle)
    (stackTopPosition : Nat) (item : ProofOccurrence) :
    ExactSaveMatch context before after scannerBefore scannerAfter item
      (canonicalSaveMatchSpaceFor rules context before scannerBefore
        stackTopPosition item) := by
  refine ⟨saveRuntimeFinalSubst rules context before scannerBefore scannerAfter
      stackTopPosition item, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold saveMatcherRows
    rw [List.mem_map]
    refine ⟨(_, canonicalSaveConsumedFor rules context before scannerBefore
      stackTopPosition item), ?_, rfl⟩
    have matched := canonicalSaveMatchSpaceFor_has_match receipt rules before
      stackTopPosition item
    simpa [saveLive, canonicalSaveMatchSpaceFor,
      saveRuntimeFinalSubst] using matched
  · exact (saveRuntimeFinalSubst_instantiates_inputs receipt rules
      stackTopPosition item).1
  · exact (saveRuntimeFinalSubst_instantiates_inputs receipt rules
      stackTopPosition item).2
  · exact (saveRuntimeFinalSubst_instantiates_outputs receipt step rules
      stackTopPosition item).1
  · exact (saveRuntimeFinalSubst_instantiates_outputs receipt step rules
      stackTopPosition item).2.1
  · exact (saveRuntimeFinalSubst_instantiates_outputs receipt step rules
      stackTopPosition item).2.2.1
  · exact (saveRuntimeFinalSubst_instantiates_outputs receipt step rules
      stackTopPosition item).2.2.2

/-- The symbolic canonical matcher is already sufficient for the row-exact
save conclusion required by the general continuous square. -/
theorem canonicalSaveMatchSpace_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) (stackTopPosition : Nat)
    (item : ProofOccurrence) :
    ExactSaveMatch context before after scannerBefore scannerAfter item
      (canonicalSaveMatchSpace context before scannerBefore stackTopPosition
        item) := by
  refine ⟨saveFinalSubst context before scannerBefore scannerAfter
      stackTopPosition item, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold saveMatcherRows
    rw [List.mem_map]
    refine ⟨(_, canonicalSaveConsumed context before scannerBefore
      stackTopPosition item), ?_, rfl⟩
    have matched := canonicalSaveMatchSpace_has_match receipt before
      stackTopPosition item
    simpa [saveLive, canonicalSaveMatchSpace, saveFinalSubst] using matched
  · exact (saveRuntimeFinalSubst_instantiates_inputs receipt
      baseSaveRuntimeRuleBundle stackTopPosition item).1
  · exact (saveRuntimeFinalSubst_instantiates_inputs receipt
      baseSaveRuntimeRuleBundle stackTopPosition item).2
  · exact (saveFinalSubst_instantiates_outputs receipt step
      stackTopPosition item).1
  · exact (saveFinalSubst_instantiates_outputs receipt step
      stackTopPosition item).2.1
  · exact (saveFinalSubst_instantiates_outputs receipt step
      stackTopPosition item).2.2.1
  · exact (saveFinalSubst_instantiates_outputs receipt step
      stackTopPosition item).2.2.2

/-- A save match remains valid in a larger scheduler read-space.  The premise
is stated on the actual `directive :: erase directive` carrier, so it neither
assumes list ordering nor mistakes duplicate executable shells for inert data. -/
theorem ExactSaveMatch.mono_read
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    {small large : List Atom}
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item small)
    (included : ∀ atom,
      atom ∈ compressedSaveDirective.atom :: saveLive small →
        atom ∈ compressedSaveDirective.atom :: saveLive large) :
    ExactSaveMatch context before after scannerBefore scannerAfter item large := by
  rcases matched with
    ⟨substitution, rowMember, scanBefore, machineBefore, machine, scanner,
      heap, receipt⟩
  refine ⟨substitution, ?_, scanBefore, machineBefore, machine, scanner, heap,
    receipt⟩
  unfold saveMatcherRows at rowMember ⊢
  rw [List.mem_map] at rowMember ⊢
  obtain ⟨⟨found, consumed⟩, foundMember, foundEq⟩ := rowMember
  change found = substitution at foundEq
  subst found
  refine ⟨(substitution, consumed), ?_, rfl⟩
  rw [compressedSaveDirective_input_exact] at foundMember ⊢
  simpa [Conformance.Computable.cmatchInputSpec, mkPattern,
    Conformance.Computable.cmatchPattern] using
      (Conformance.Computable.cmatchPattern_mono []
        (compressedSaveDirective.atom :: saveLive small)
        (compressedSaveDirective.atom :: saveLive large)
        (mkPattern savePatterns) included
        substitution consumed foundMember)

/-- A continuous represented boundary on which the ordinary scheduler selects
the authored save directive and the concrete matcher reconstructs exactly the
source-determined successor rows. -/
structure ContinuousSaveRequestFrame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (staticFrame space : List Atom) (item : ProofOccurrence) : Prop where
  represented : RepresentsRunningBoundary context before ledger scannerBefore
    staticFrame space
  invariant : ReflectiveWorkQueueInvariant space
  supported : cSupportedSourceExecFacts space = [compressedSaveDirective]
  exactMatch : ExactSaveMatch context before after scannerBefore scannerAfter
    item space

/-- Build the continuous save frame by embedding the canonical symbolic
matcher into the actual represented scheduler read-space. -/
theorem ContinuousSaveRequestFrame.of_canonical_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after) (stackTopPosition : Nat)
    (item : ProofOccurrence) {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (invariant : ReflectiveWorkQueueInvariant space)
    (supported : cSupportedSourceExecFacts space = [compressedSaveDirective])
    (included : ∀ atom,
      atom ∈ compressedSaveDirective.atom ::
          saveLive (canonicalSaveMatchSpace context before scannerBefore
            stackTopPosition item) →
        atom ∈ compressedSaveDirective.atom :: saveLive space) :
    ContinuousSaveRequestFrame context before after ledger scannerBefore
      scannerAfter staticFrame space item := by
  exact
    { represented := represented
      invariant := invariant
      supported := supported
      exactMatch :=
        (canonicalSaveMatchSpace_exact_match receipt step stackTopPosition item).mono_read
          included }

/-! ## Source-derived canonical-frame admission -/

/-- Presentation-parametric static verifier structure required by one source
save.  It separates fixed frontier rows from the six runtime carriers selected
by the executable presentation. -/
structure SaveStaticSupportFor
    (rules : SaveRuntimeRuleBundle)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) (staticFrame : List Atom) : Prop where
  directive : compressedSaveDirective.atom ∈ staticFrame
  stackSuccessor :
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        (CompressedIndexCode.ofNat stackTopPosition).atom
        (CompressedIndexCode.ofNat before.stack.length).atom ∈ staticFrame
  heapSuccessor :
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom
        (CompressedIndexCode.ofNat (before.heap.length + 1)).atom ∈ staticFrame
  captures : ∀ row ∈ rules.captureRows, row ∈ staticFrame

/-- Static verifier structure required by one source save.  These rows carry
only admitted code inventory and finite frontier structure; the saved node and
occurrence remain absent from this interface. -/
structure SaveStaticSupport
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) (staticFrame : List Atom) : Prop where
  directive : compressedSaveDirective.atom ∈ staticFrame
  stackSuccessor :
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        (CompressedIndexCode.ofNat stackTopPosition).atom
        (CompressedIndexCode.ofNat before.stack.length).atom ∈ staticFrame
  heapSuccessor :
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom
        (CompressedIndexCode.ofNat (before.heap.length + 1)).atom ∈ staticFrame
  captures : ∀ row ∈ saveRuntimeCaptureRows, row ∈ staticFrame

theorem SaveStaticSupport.asForBase
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {stackTopPosition : Nat} {staticFrame : List Atom}
    (support : SaveStaticSupport context before stackTopPosition staticFrame) :
    SaveStaticSupportFor baseSaveRuntimeRuleBundle context before
      stackTopPosition staticFrame := by
  exact
    { directive := support.directive
      stackSuccessor := support.stackSuccessor
      heapSuccessor := support.heapSuccessor
      captures := by
        intro row member
        exact support.captures row (by simpa using member) }

/-- Source-relative authority for the static part of a save boundary.  The
executable carriers are resolved by the admitted presentation, and the two
finite cursor edges are functional at the live source frontiers. -/
structure SaveStaticAuthority
    (presentation : CompressedExecutablePresentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) (staticFrame : List Atom) : Prop where
  support : SaveStaticSupport context before stackTopPosition staticFrame
  executable : CompressedExecutableCapabilities presentation staticFrame
  stackSuccessorFunctional : ∀ next,
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        (CompressedIndexCode.ofNat stackTopPosition).atom next ∈ staticFrame →
      next = (CompressedIndexCode.ofNat before.stack.length).atom
  stackPredecessorFunctional : ∀ previous,
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        previous (CompressedIndexCode.ofNat before.stack.length).atom ∈
          staticFrame →
      previous = (CompressedIndexCode.ofNat stackTopPosition).atom
  heapSuccessorFunctional : ∀ next,
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom next ∈ staticFrame →
      next = (CompressedIndexCode.ofNat (before.heap.length + 1)).atom

/-- Presentation-independent authority for both finite cursor edges consumed
by a save matcher.  Runtime continuation inventory is intentionally absent:
base and transformed presentations share these source-indexed frontiers. -/
structure SaveFrontierAuthority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) (staticFrame : List Atom) : Prop where
  directive : compressedSaveDirective.atom ∈ staticFrame
  stackSuccessor :
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        (CompressedIndexCode.ofNat stackTopPosition).atom
        (CompressedIndexCode.ofNat before.stack.length).atom ∈ staticFrame
  stackPredecessorFunctional : ∀ previous,
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        previous (CompressedIndexCode.ofNat before.stack.length).atom ∈
          staticFrame →
      previous = (CompressedIndexCode.ofNat stackTopPosition).atom
  heapSuccessor :
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom
        (CompressedIndexCode.ofNat (before.heap.length + 1)).atom ∈ staticFrame
  heapSuccessorFunctional : ∀ next,
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom next ∈ staticFrame →
      next = (CompressedIndexCode.ofNat (before.heap.length + 1)).atom

/-- Minimal presentation-independent authority needed to advance the heap
frontier.  Runtime continuation inventory is intentionally outside this
interface: base and transformed presentations may carry different rules while
sharing the same source-indexed frontier discipline. -/
structure SaveHeapFrontierAuthority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (staticFrame : List Atom) : Prop where
  directive : compressedSaveDirective.atom ∈ staticFrame
  successor :
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom
        (CompressedIndexCode.ofNat (before.heap.length + 1)).atom ∈ staticFrame
  functional : ∀ next,
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat before.heap.length).atom next ∈ staticFrame →
      next = (CompressedIndexCode.ofNat (before.heap.length + 1)).atom

theorem SaveStaticAuthority.heapFrontier
    {presentation : CompressedExecutablePresentation}
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {stackTopPosition : Nat} {staticFrame : List Atom}
    (authority : SaveStaticAuthority presentation context before
      stackTopPosition staticFrame) :
    SaveHeapFrontierAuthority context before staticFrame := by
  exact
    { directive := authority.support.directive
      successor := authority.support.heapSuccessor
      functional := authority.heapSuccessorFunctional }

theorem SaveStaticAuthority.frontier
    {presentation : CompressedExecutablePresentation}
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {stackTopPosition : Nat} {staticFrame : List Atom}
    (authority : SaveStaticAuthority presentation context before
      stackTopPosition staticFrame) :
    SaveFrontierAuthority context before stackTopPosition staticFrame := by
  exact
    { directive := authority.support.directive
      stackSuccessor := authority.support.stackSuccessor
      stackPredecessorFunctional := authority.stackPredecessorFunctional
      heapSuccessor := authority.support.heapSuccessor
      heapSuccessorFunctional := authority.heapSuccessorFunctional }

theorem SaveFrontierAuthority.heapFrontier
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {stackTopPosition : Nat} {staticFrame : List Atom}
    (authority : SaveFrontierAuthority context before stackTopPosition
      staticFrame) :
    SaveHeapFrontierAuthority context before staticFrame := by
  exact
    { directive := authority.directive
      successor := authority.heapSuccessor
      functional := authority.heapSuccessorFunctional }

/-- Minimal source-indexed static frame for one base-presentation save step. -/
def canonicalSaveStaticFrame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) : List Atom :=
  [compressedSaveDirective.atom,
   compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
     (CompressedIndexCode.ofNat stackTopPosition).atom
     (CompressedIndexCode.ofNat before.stack.length).atom,
   compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
     (CompressedIndexCode.ofNat before.heap.length).atom
     (CompressedIndexCode.ofNat (before.heap.length + 1)).atom] ++
    compressedBaseExecutableCaptureRows

theorem canonicalSaveStaticFrame_clean
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    StaticFrame (canonicalSaveStaticFrame context before stackTopPosition) := by
  intro row member
  simp only [canonicalSaveStaticFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with fixed | capture
  · rcases fixed with rfl | rfl | rfl
    all_goals
      simp [isDynamicRow, dynamicRowHeads, compressedSaveDirective,
        compressedSaveRule, compressedIndexSuccessorRow,
        compressedStackOwner, compressedHeapOwner]
  · rw [compressedBaseExecutableCaptureRows, List.mem_map] at capture
    obtain ⟨captured, _capturedMember, rfl⟩ := capture
    exact encodeCompressedExecutableCapture_isDynamic_false captured

theorem canonicalSaveStaticFrame_authority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    SaveStaticAuthority compressedBaseExecutablePresentation context before
      stackTopPosition
      (canonicalSaveStaticFrame context before stackTopPosition) := by
  have capturesWithin :
      CompressedExecutableCapabilities compressedBaseExecutablePresentation
        compressedBaseExecutableCaptureRows :=
    compressedBaseExecutableCaptureRows_authorized
  refine
    { support := ?_
      executable := ?_
      stackSuccessorFunctional := ?_
      stackPredecessorFunctional := ?_
      heapSuccessorFunctional := ?_ }
  · refine
      { directive := by simp [canonicalSaveStaticFrame]
        stackSuccessor := by simp [canonicalSaveStaticFrame]
        heapSuccessor := by simp [canonicalSaveStaticFrame]
        captures := ?_ }
    intro row member
    apply List.mem_append_right
    rw [compressedBaseExecutableCaptureRows_eq_existing]
    apply List.mem_append_left
    simp only [saveRuntimeCaptureRows, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [compressedScannerRuleCaptureRows]
  · intro row member
    simp only [canonicalSaveStaticFrame, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with fixed | capture
    · rcases fixed with rfl | rfl | rfl
      all_goals
        simp [CompressedExecutableCarrierAuthorized,
          decodeCompressedExecutableCapture, compressedSaveDirective,
          compressedSaveRule, compressedIndexSuccessorRow,
          compressedStackOwner, compressedHeapOwner]
    · exact capturesWithin row capture
  · intro next member
    simp [canonicalSaveStaticFrame, compressedIndexSuccessorRow,
      compressedStackOwner, compressedHeapOwner,
      compressedBaseExecutableCaptureRows,
      compressedBaseExecutableCaptures, encodeCompressedExecutableCapture] at member
    rcases member with impossible | exactNext
    · have rawEqual := congrArg extractRawExecFact impossible
      simp [compressedSaveDirective, compressedSaveRule,
        extractRawExecFact] at rawEqual
    · exact exactNext
  · intro previous member
    simp [canonicalSaveStaticFrame, compressedIndexSuccessorRow,
      compressedStackOwner, compressedHeapOwner,
      compressedBaseExecutableCaptureRows,
      compressedBaseExecutableCaptures, encodeCompressedExecutableCapture] at member
    rcases member with impossible | exactPrevious
    · have rawEqual := congrArg extractRawExecFact impossible
      simp [compressedSaveDirective, compressedSaveRule,
        extractRawExecFact] at rawEqual
    · exact exactPrevious
  · intro next member
    simp [canonicalSaveStaticFrame, compressedIndexSuccessorRow,
      compressedStackOwner, compressedHeapOwner,
      compressedBaseExecutableCaptureRows,
      compressedBaseExecutableCaptures, encodeCompressedExecutableCapture] at member
    rcases member with impossible | exactNext
    · have rawEqual := congrArg extractRawExecFact impossible
      simp [compressedSaveDirective, compressedSaveRule,
        extractRawExecFact] at rawEqual
    · change next = (CompressedIndexCode.ofNat before.heap.length).next.atom
      exact exactNext

private def forgedSavePrefixCarrier : Atom :=
  compressedOwnedRuntimeRuleRow "prefix" compressedTerminalRule

/-- Negative frame control: appending a genuine executable rule under the
wrong continuation kind makes the source-relative save authority impossible. -/
theorem forged_save_prefix_capture_rejected
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (stackTopPosition : Nat) :
    ¬ SaveStaticAuthority compressedBaseExecutablePresentation context before
      stackTopPosition
      (forgedSavePrefixCarrier ::
        canonicalSaveStaticFrame context before stackTopPosition) := by
  intro authority
  have forgedAuthorized := authority.executable forgedSavePrefixCarrier
    (by simp)
  exact swapped_prefix_terminal_capture_rejected forgedAuthorized

private theorem canonicalBoundaryRows_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary) :
    ∀ row, row ∈ canonicalBoundaryRows context state ledger scanner →
      isDynamicRow row = true := by
  intro row member
  simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with control | passive
  · rcases control with rfl | rfl
    · exact machineRow_isDynamic context state
    · exact scannerRow_isDynamic context scanner
  · exact canonicalPassiveRows_all_dynamic context state ledger row passive

private theorem saveOwnedRule_match_decodes
    (before : Subst) (kind variableName : String)
    {result : Subst} {atom : Atom}
    (matched : Conformance.Computable.cmatchAtom before
      (saveOwnedRuleTemplate kind variableName) atom = some result) :
    ∃ payload,
      atom = compressedOwnedRuntimeRuleRow kind payload ∧
        Subst.lookup result variableName = some payload := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons kindMatched tail2 =>
          cases kindMatched
          cases tail2 with
          | expr_cons payloadMatched finished =>
              cases finished
              cases payloadMatched with
              | var_fresh lookup =>
                  exact ⟨_, rfl, by simp [Subst.lookup]⟩
              | var_bound lookup => exact ⟨_, rfl, lookup⟩

private theorem save_cmatchAtom_filterMap_witness
    {space : List Atom} {before after : Subst} {pattern atom : Atom}
    (member : (after, atom) ∈ space.filterMap fun candidate =>
      (Conformance.Computable.cmatchAtom before pattern candidate).map
        (·, candidate)) :
    atom ∈ space ∧
      Conformance.Computable.cmatchAtom before pattern atom = some after := by
  rw [List.mem_filterMap] at member
  obtain ⟨candidate, candidateMember, mapped⟩ := member
  simp only [Option.map_eq_some_iff] at mapped
  obtain ⟨substitution, matched, equal⟩ := mapped
  cases equal
  exact ⟨candidateMember, matched⟩

private theorem saveReadCandidate_mem_space
    {context : BoundaryContext}
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before : MachineState source target} {ledger : NodeOccurrenceLedger before}
    {scanner : ScannerBoundary} {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {candidate : Atom}
    (member : candidate ∈ compressedSaveDirective.atom :: saveLive space) :
    candidate ∈ space := by
  rcases List.mem_cons.mp member with rfl | live
  · apply (represented.exact_rows _).2
    exact List.mem_append_right _ directivePresent
  · exact List.mem_of_mem_erase live

private theorem save_matchAtomList_variable_lookup
    (prefixPatterns prefixAtoms suffixPatterns suffixAtoms : List Atom)
    (initial final : Subst) (variableName : String) (value : Atom)
    (prefixLength : prefixPatterns.length = prefixAtoms.length)
    (matched :
      matchAtom.matchAtomList initial
          (prefixPatterns ++ .var variableName :: suffixPatterns)
          (prefixAtoms ++ value :: suffixAtoms) = some final) :
    final.lookup variableName = some value := by
  induction prefixPatterns generalizing prefixAtoms initial with
  | nil =>
      cases prefixAtoms with
      | nil =>
          simp only [List.nil_append, matchAtom.matchAtomList] at matched
          cases variableMatched : matchAtom initial (.var variableName) value with
          | none => simp [variableMatched] at matched
          | some afterVariable =>
              simp only [variableMatched] at matched
              have bound : afterVariable.lookup variableName = some value := by
                have relation := matchAtom_sound variableMatched
                cases relation with
                | var_fresh _ => simp [Subst.lookup]
                | var_bound lookup => exact lookup
              exact
                (matchAtom_lookupExtends.matchAtomList_lookupExtends matched)
                  variableName value bound
      | cons atom atoms => simp at prefixLength
  | cons pattern patterns induction =>
      cases prefixAtoms with
      | nil => simp at prefixLength
      | cons atom atoms =>
          simp only [List.length_cons, Nat.succ.injEq] at prefixLength
          simp only [List.cons_append, matchAtom.matchAtomList] at matched
          cases headMatched : matchAtom initial pattern atom with
          | none => simp [headMatched] at matched
          | some afterHead =>
              simp only [headMatched] at matched
              exact induction atoms afterHead prefixLength matched

private theorem saveMachine_match_has_head
    {initial final : Subst} {candidate : Atom}
    (matched : Conformance.Computable.cmatchAtom initial saveMachineTemplate
      candidate = some final) :
    ∃ tail, candidate =
      .expression (.symbol "mm-compressed-machine" :: tail) := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tailMatched =>
      cases headMatched
      exact ⟨_, rfl⟩

private theorem saveScan_match_has_head
    {initial final : Subst} {candidate : Atom}
    (matched : Conformance.Computable.cmatchAtom initial saveScanTemplate
      candidate = some final) :
    ∃ tail, candidate =
      .expression (.symbol "mm-compressed-scan" :: tail) := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tailMatched =>
      cases headMatched
      exact ⟨_, rfl⟩

private theorem saveScan_candidate_eq
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (passiveScannerFree : ∀ tail,
      .expression (.symbol "mm-compressed-scan" :: tail) ∉
        canonicalPassiveRows context before ledger)
    {initial final : Subst} {candidate : Atom}
    (candidateMember : candidate ∈
      compressedSaveDirective.atom :: saveLive space)
    (matched : Conformance.Computable.cmatchAtom initial saveScanTemplate
      candidate = some final) :
    candidate = scannerRow context scanner := by
  obtain ⟨tail, shape⟩ := saveScan_match_has_head matched
  have present : candidate ∈ space :=
    saveReadCandidate_mem_space represented directivePresent candidateMember
  have combined := (represented.exact_rows candidate).1 present
  rcases List.mem_append.mp combined with sourceRow | staticRow
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at sourceRow
    rcases sourceRow with (machineEq | rfl) | passive
    · exfalso
      rw [machineEq] at shape
      simp [machineRow] at shape
    · rfl
    · exact False.elim (passiveScannerFree tail (shape ▸ passive))
  · have clean := represented.staticFrame_clean candidate staticRow
    rw [shape] at clean
    simp [isDynamicRow, dynamicRowHeads] at clean

private theorem saveScan_match_remaining_lookup
    (initial final : Subst) (context : BoundaryContext)
    (scanner : ScannerBoundary)
    (matched : Conformance.Computable.cmatchAtom initial saveScanTemplate
      (scannerRow context scanner) = some final) :
    final.lookup "remaining-bytes" =
      some (listAtom natAtom (scanner.remainingBytes.tail.map UInt8.toNat)) := by
  rcases scanner with ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  cases remainingBytes with
  | nil =>
      rw [Conformance.cmatchAtom_eq_matchAtom] at matched
      have relational := matchAtom_sound matched
      cases relational with
      | expr_cons _ tail1 =>
          cases tail1 with
          | expr_cons _ tail2 =>
              cases tail2 with
              | expr_cons _ tail3 =>
                  cases tail3 with
                  | expr_cons _ tail4 =>
                      cases tail4 with
                      | expr_cons bytesMatched _ =>
                          cases bytesMatched with
                          | expr_cons _ impossible => cases impossible
  | cons byte remainingBytes =>
    change final.lookup "remaining-bytes" =
      some (listAtom natAtom (remainingBytes.map UInt8.toNat))
    rw [Conformance.cmatchAtom_eq_matchAtom] at matched
    have relational := matchAtom_sound matched
    cases relational with
    | expr_cons _ tail1 =>
        cases tail1 with
        | expr_cons _ tail2 =>
            cases tail2 with
            | expr_cons _ tail3 =>
                cases tail3 with
                | expr_cons _ tail4 =>
                    cases tail4 with
                    | expr_cons bytesMatched tail5 =>
                        cases bytesMatched with
                        | expr_cons _ bytesTail1 =>
                            cases bytesTail1 with
                            | expr_cons _ bytesTail2 =>
                                cases bytesTail2 with
                                | expr_cons remainingMatched bytesFinished =>
                                    cases bytesFinished
                                    cases remainingMatched with
                                    | var_fresh _ =>
                                        apply (matchAtom_lookupExtends
                                          (matchAtom_complete tail5))
                                        simp [Subst.lookup]
                                    | var_bound lookup =>
                                        exact (matchAtom_lookupExtends
                                          (matchAtom_complete tail5)) _ _ lookup

private theorem saveMachine_candidate_eq
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (passiveMachineFree : ∀ tail,
      .expression (.symbol "mm-compressed-machine" :: tail) ∉
        canonicalPassiveRows context before ledger)
    {initial final : Subst} {candidate : Atom}
    (candidateMember : candidate ∈
      compressedSaveDirective.atom :: saveLive space)
    (matched : Conformance.Computable.cmatchAtom initial saveMachineTemplate
      candidate = some final) :
    candidate = machineRow context before := by
  obtain ⟨tail, shape⟩ := saveMachine_match_has_head matched
  have present : candidate ∈ space :=
    saveReadCandidate_mem_space represented directivePresent candidateMember
  have combined := (represented.exact_rows candidate).1 present
  rcases List.mem_append.mp combined with sourceRow | staticRow
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at sourceRow
    rcases sourceRow with (rfl | scannerEq) | passive
    · rfl
    · exfalso
      rw [scannerEq] at shape
      simp [scannerRow] at shape
    · exact False.elim (passiveMachineFree tail (shape ▸ passive))
  · have clean := represented.staticFrame_clean candidate staticRow
    rw [shape] at clean
    simp [isDynamicRow, dynamicRowHeads] at clean

private theorem saveHeapSuccessor_match_decodes
    (context : BoundaryContext)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target)
    {initial final : Subst} {candidate : Atom}
    (proofOwnerLookup : initial.lookup "proof-owner" =
      some context.proofOwner)
    (heapLookup : initial.lookup "heap-next" =
      some (CompressedIndexCode.ofNat before.heap.length).atom)
    (matched : Conformance.Computable.cmatchAtom initial
      saveHeapSuccessorTemplate candidate = some final) :
    ∃ next,
      candidate = compressedIndexSuccessorRow
          (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat before.heap.length).atom next ∧
        final.lookup "next-heap-position" = some next := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons ownerMatched tail2 =>
          cases ownerMatched with
          | expr_cons ownerHeadMatched ownerTail =>
              cases ownerHeadMatched
              cases ownerTail with
              | expr_cons proofMatched ownerFinished =>
                  cases ownerFinished
                  cases proofMatched with
                  | var_fresh lookup => simp [proofOwnerLookup] at lookup
                  | var_bound lookup =>
                      have proofEqual := Option.some.inj
                        (lookup.symm.trans proofOwnerLookup)
                      subst proofEqual
                      cases tail2 with
                      | expr_cons heapMatched tail3 =>
                          cases heapMatched with
                          | var_fresh lookup => simp [heapLookup] at lookup
                          | var_bound lookup =>
                              have heapEqual := Option.some.inj
                                (lookup.symm.trans heapLookup)
                              subst heapEqual
                              cases tail3 with
                              | expr_cons nextMatched finished =>
                                  cases finished
                                  cases nextMatched with
                                  | var_fresh lookup =>
                                      exact ⟨_, rfl, by simp [Subst.lookup]⟩
                                  | var_bound lookup =>
                                      exact ⟨_, rfl, lookup⟩

private theorem matchAtom_lookup_of_var
    {initial final : Subst} {variableName : String} {candidate : Atom}
    (matched : MatchAtomRel initial (.var variableName) candidate final) :
    final.lookup variableName = some candidate := by
  cases matched with
  | var_fresh _ => simp [Subst.lookup]
  | var_bound lookup => exact lookup

private theorem saveStackSuccessor_match_decodes
    (context : BoundaryContext)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target)
    {initial final : Subst} {candidate : Atom}
    (proofOwnerLookup : initial.lookup "proof-owner" =
      some context.proofOwner)
    (stackLookup : initial.lookup "stack-position" =
      some (CompressedIndexCode.ofNat before.stack.length).atom)
    (matched : Conformance.Computable.cmatchAtom initial
      saveStackSuccessorTemplate candidate = some final) :
    ∃ previous,
      candidate = compressedIndexSuccessorRow
          (compressedStackOwner context.proofOwner) previous
          (CompressedIndexCode.ofNat before.stack.length).atom ∧
        final.lookup "stack-top" = some previous := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons ownerMatched tail2 =>
          cases ownerMatched with
          | expr_cons ownerHeadMatched ownerTail =>
              cases ownerHeadMatched
              cases ownerTail with
              | expr_cons proofMatched ownerFinished =>
                  cases ownerFinished
                  cases proofMatched with
                  | var_fresh lookup => simp [proofOwnerLookup] at lookup
                  | var_bound lookup =>
                      have proofEqual := Option.some.inj
                        (lookup.symm.trans proofOwnerLookup)
                      subst proofEqual
                      cases tail2 with
                      | expr_cons previousMatched tail3 =>
                          cases tail3 with
                          | expr_cons stackMatched finished =>
                              cases finished
                              have stackLookupAfterPrevious :=
                                (matchAtom_lookupExtends
                                  (matchAtom_complete previousMatched)) _ _
                                    stackLookup
                              cases stackMatched with
                              | var_fresh lookup =>
                                  simp [stackLookupAfterPrevious] at lookup
                              | var_bound lookup =>
                                  have stackEqual := Option.some.inj
                                    (lookup.symm.trans stackLookupAfterPrevious)
                                  subst stackEqual
                                  cases previousMatched with
                                  | var_fresh previousFresh =>
                                      exact ⟨_, rfl, by simp [Subst.lookup]⟩
                                  | var_bound previousLookup =>
                                      exact ⟨_, rfl, previousLookup⟩

private theorem saveStackCell_match_decodes
    (context : BoundaryContext) (stackTop : Atom)
    {initial final later : Subst} {candidate : Atom}
    (extendsToLater : later.lookupExtends final)
    (proofOwnerLookup : later.lookup "proof-owner" =
      some context.proofOwner)
    (stackTopLookup : later.lookup "stack-top" = some stackTop)
    (matched : Conformance.Computable.cmatchAtom initial saveStackCellTemplate
      candidate = some final) :
    ∃ nodeIdentity,
      candidate = .expression
          [.symbol "mm-compressed-stack-cell", context.proofOwner,
            stackTop, nodeIdentity] ∧
        later.lookup "node-id" = some nodeIdentity := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons proofMatched tail2 =>
          have proofFinal :=
            (matchAtom_lookupExtends (matchAtom_complete tail2)) _ _
              (matchAtom_lookup_of_var proofMatched)
          have proofEqual := Option.some.inj
            ((extendsToLater _ _ proofFinal).symm.trans proofOwnerLookup)
          subst proofEqual
          cases tail2 with
          | expr_cons stackMatched tail3 =>
              have stackFinal :=
                (matchAtom_lookupExtends (matchAtom_complete tail3)) _ _
                  (matchAtom_lookup_of_var stackMatched)
              have stackEqual := Option.some.inj
                ((extendsToLater _ _ stackFinal).symm.trans stackTopLookup)
              subst stackEqual
              cases tail3 with
              | expr_cons nodeMatched finished =>
                  cases finished
                  exact ⟨_, rfl, extendsToLater _ _
                    (matchAtom_lookup_of_var nodeMatched)⟩

private theorem saveNode_match_decodes
    (context : BoundaryContext) (nodeIdentity : Atom)
    {initial final later : Subst} {candidate : Atom}
    (extendsToLater : later.lookupExtends final)
    (proofOwnerLookup : later.lookup "proof-owner" =
      some context.proofOwner)
    (nodeLookup : later.lookup "node-id" = some nodeIdentity)
    (matched : Conformance.Computable.cmatchAtom initial saveNodeTemplate
      candidate = some final) :
    ∃ formula sourceOccurrence,
      candidate = MM2CompressedProofHeapEncoding.nodeRow context.proofOwner
          ⟨nodeIdentity, ⟨formula, sourceOccurrence⟩⟩ ∧
        later.lookup "node-formula" = some formula ∧
        later.lookup "node-occurrence" = some sourceOccurrence := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons proofMatched tail2 =>
          have proofFinal :=
            (matchAtom_lookupExtends (matchAtom_complete tail2)) _ _
              (matchAtom_lookup_of_var proofMatched)
          have proofEqual := Option.some.inj
            ((extendsToLater _ _ proofFinal).symm.trans proofOwnerLookup)
          subst proofEqual
          cases tail2 with
          | expr_cons nodeMatched tail3 =>
              have nodeFinal :=
                (matchAtom_lookupExtends (matchAtom_complete tail3)) _ _
                  (matchAtom_lookup_of_var nodeMatched)
              have nodeEqual := Option.some.inj
                ((extendsToLater _ _ nodeFinal).symm.trans nodeLookup)
              subst nodeEqual
              cases tail3 with
              | expr_cons formulaMatched tail4 =>
                  cases tail4 with
                  | expr_cons occurrenceMatched finished =>
                      cases finished
                      have formulaIntermediate :=
                        matchAtom_lookup_of_var formulaMatched
                      have formulaLookup :=
                        extendsToLater _ _ ((matchAtom_lookupExtends
                          (matchAtom_complete occurrenceMatched))
                          "node-formula" _ formulaIntermediate)
                      exact ⟨_, _, rfl, formulaLookup,
                        extendsToLater _ _
                          (matchAtom_lookup_of_var occurrenceMatched)⟩

/-- A matched runtime carrier can only contain the rule assigned to that
family/kind by the admitted base presentation. -/
theorem saveOwnedRuntimeRule_candidate_eq
    (presentation : CompressedExecutablePresentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    (substitution : Subst) (kind variableName : String) (expected : Atom)
    (expectedResolved : presentation.resolve
      .runtime kind = some expected)
    {candidate : Atom} {result : Subst}
    (candidateMember : candidate ∈
      compressedSaveDirective.atom :: saveLive space)
    (matched : Conformance.Computable.cmatchAtom substitution
      (saveOwnedRuleTemplate kind variableName) candidate = some result) :
    candidate = compressedOwnedRuntimeRuleRow kind expected := by
  obtain ⟨payload, candidateEq, _lookup⟩ :=
    saveOwnedRule_match_decodes substitution kind variableName matched
  subst candidate
  have present : compressedOwnedRuntimeRuleRow kind payload ∈ space :=
    saveReadCandidate_mem_space represented directivePresent candidateMember
  have combined := (represented.exact_rows _).1 present
  rcases List.mem_append.mp combined with sourceRow | staticRow
  · have dynamic := canonicalBoundaryRows_all_dynamic context before ledger scanner
      (compressedOwnedRuntimeRuleRow kind payload) sourceRow
    simp [isDynamicRow, dynamicRowHeads, compressedOwnedRuntimeRuleRow] at dynamic
  · have authorized := capabilities _ staticRow
    simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture, compressedOwnedRuntimeRuleRow] at authorized
    have payloadEq := presentation.capture_exact
      expectedResolved authorized
    subst payload
    rfl

/-- Every matcher row of an authorized save boundary carries the six exact
scanner continuations selected by the admitted presentation.  The statement
does not assume that the matcher chose the canonical row; it reconstructs the
payloads from the actual thirteen-premise match and the frame authority. -/
theorem saveMatcherRow_runtime_rules_exact_of_resolved
    (presentation : CompressedExecutablePresentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    (prefixRule terminalRule proofRule invalidByteRule questionRule
      questionOpenFaultRule : Atom)
    (prefixResolved : presentation.resolve .runtime "prefix" =
      some prefixRule)
    (terminalResolved : presentation.resolve .runtime "terminal" =
      some terminalRule)
    (proofResolved : presentation.resolve .runtime "proof" =
      some proofRule)
    (invalidByteResolved : presentation.resolve .runtime "invalid-byte" =
      some invalidByteRule)
    (questionResolved : presentation.resolve .runtime "question" =
      some questionRule)
    (questionOpenFaultResolved : presentation.resolve .runtime
      "question-open-fault" = some questionOpenFaultRule)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    Subst.lookup substitution "compressed-prefix-rule" =
        some prefixRule ∧
      Subst.lookup substitution "compressed-terminal-rule" =
        some terminalRule ∧
      Subst.lookup substitution "compressed-proof-rule" =
        some proofRule ∧
      Subst.lookup substitution "compressed-invalid-byte-rule" =
        some invalidByteRule ∧
      Subst.lookup substitution "compressed-question-rule" =
        some questionRule ∧
      Subst.lookup substitution "compressed-question-open-fault-rule" =
        some questionOpenFaultRule := by
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  change matchedSubst = substitution at substEq
  subst matchedSubst
  rw [compressedSaveDirective_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold savePatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, r9⟩ := r8
  obtain ⟨⟨s10, a10⟩, f10, r10⟩ := r9
  obtain ⟨⟨s11, a11⟩, f11, r11⟩ := r10
  obtain ⟨⟨s12, a12⟩, f12, r12⟩ := r11
  obtain ⟨⟨s13, a13⟩, f13, finished⟩ := r12
  have runtimeLookup : ∀
      (beforeMatch afterMatch : Subst) (candidate : Atom)
      (kind variableName : String) (expected : Atom),
      (afterMatch, candidate) ∈
          (compressedSaveDirective.atom :: saveLive space).filterMap
            (fun atom =>
              (Conformance.Computable.cmatchAtom beforeMatch
                (saveOwnedRuleTemplate kind variableName) atom).map
                  (·, atom)) →
      presentation.resolve .runtime kind = some expected →
      Subst.lookup afterMatch variableName = some expected ∧
        afterMatch.lookupExtends beforeMatch := by
    intro beforeMatch afterMatch candidate kind variableName expected
      filtered resolved
    obtain ⟨candidateMember, candidateMatch⟩ :=
      save_cmatchAtom_filterMap_witness filtered
    have candidateEq := saveOwnedRuntimeRule_candidate_eq
      presentation represented directivePresent capabilities
      beforeMatch kind variableName expected resolved candidateMember
      candidateMatch
    obtain ⟨payload, decodedEq, lookup⟩ :=
      saveOwnedRule_match_decodes beforeMatch kind variableName candidateMatch
    rw [candidateEq] at decodedEq
    have payloadEq : payload = expected := by
      symm
      simpa [compressedOwnedRuntimeRuleRow] using decodedEq
    refine ⟨by simpa only [payloadEq] using lookup, ?_⟩
    rw [Conformance.cmatchAtom_eq_matchAtom] at candidateMatch
    exact matchAtom_lookupExtends candidateMatch
  obtain ⟨prefixAt8, _extends8⟩ := runtimeLookup s7 s8 a8 "prefix"
    "compressed-prefix-rule" prefixRule f8 prefixResolved
  obtain ⟨terminalAt9, extends9⟩ := runtimeLookup s8 s9 a9 "terminal"
    "compressed-terminal-rule" terminalRule f9 terminalResolved
  obtain ⟨proofAt10, extends10⟩ := runtimeLookup s9 s10 a10 "proof"
    "compressed-proof-rule" proofRule f10 proofResolved
  obtain ⟨invalidAt11, extends11⟩ := runtimeLookup s10 s11 a11
    "invalid-byte" "compressed-invalid-byte-rule" invalidByteRule
    f11 invalidByteResolved
  obtain ⟨questionAt12, extends12⟩ := runtimeLookup s11 s12 a12 "question"
    "compressed-question-rule" questionRule f12 questionResolved
  obtain ⟨questionFaultAt13, extends13⟩ := runtimeLookup s12 s13 a13
    "question-open-fault" "compressed-question-open-fault-rule"
    questionOpenFaultRule f13 questionOpenFaultResolved
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  have finalEq : substitution = s13 := finished.1
  subst substitution
  exact
    ⟨extends13 _ _ (extends12 _ _ (extends11 _ _
        (extends10 _ _ (extends9 _ _ prefixAt8)))),
      extends13 _ _ (extends12 _ _ (extends11 _ _
        (extends10 _ _ terminalAt9))),
      extends13 _ _ (extends12 _ _ (extends11 _ _ proofAt10)),
      extends13 _ _ (extends12 _ _ invalidAt11),
      extends13 _ _ questionAt12,
      questionFaultAt13⟩

/-- Base-presentation specialization of the presentation-parametric runtime
origin theorem. -/
theorem saveMatcherRow_runtime_rules_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom} {stackTopPosition : Nat}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveStaticAuthority compressedBaseExecutablePresentation
      context before stackTopPosition staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    Subst.lookup substitution "compressed-prefix-rule" =
        some compressedPrefixRule ∧
      Subst.lookup substitution "compressed-terminal-rule" =
        some compressedTerminalRule ∧
      Subst.lookup substitution "compressed-proof-rule" =
        some compressedProofStepRule ∧
      Subst.lookup substitution "compressed-invalid-byte-rule" =
        some compressedInvalidByteRule ∧
      Subst.lookup substitution "compressed-question-rule" =
        some compressedQuestionRule ∧
      Subst.lookup substitution "compressed-question-open-fault-rule" =
        some compressedQuestionOpenFaultRule := by
  exact saveMatcherRow_runtime_rules_exact_of_resolved
    compressedBaseExecutablePresentation represented authority.support.directive
    authority.executable
    compressedPrefixRule compressedTerminalRule compressedProofStepRule
    compressedInvalidByteRule compressedQuestionRule
    compressedQuestionOpenFaultRule rfl rfl rfl rfl rfl rfl rowMember

/-- Every actual matcher row obtains its stack-top cursor from the unique
source-indexed predecessor edge.  This is the static half of recovering the
saved proof occurrence from the source stack/node join. -/
theorem saveMatcherRow_stack_top_exact_of_passive_machine_free
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom} {stackTopPosition : Nat}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveFrontierAuthority context before
      stackTopPosition staticFrame)
    (passiveMachineFree : ∀ tail,
      .expression (.symbol "mm-compressed-machine" :: tail) ∉
        canonicalPassiveRows context before ledger)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    substitution.lookup "stack-top" =
      some (CompressedIndexCode.ofNat stackTopPosition).atom := by
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  change matchedSubst = substitution at substEq
  subst matchedSubst
  rw [compressedSaveDirective_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold savePatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, r9⟩ := r8
  obtain ⟨⟨s10, a10⟩, f10, r10⟩ := r9
  obtain ⟨⟨s11, a11⟩, f11, r11⟩ := r10
  obtain ⟨⟨s12, a12⟩, f12, r12⟩ := r11
  obtain ⟨⟨s13, a13⟩, f13, finished⟩ := r12
  obtain ⟨a3Member, m3⟩ := save_cmatchAtom_filterMap_witness f3
  have a3Eq := saveMachine_candidate_eq represented
    authority.directive passiveMachineFree a3Member m3
  subst a3
  rw [Conformance.cmatchAtom_eq_matchAtom] at m3
  have machineListMatched :
      matchAtom.matchAtomList s2
          [.symbol "mm-compressed-machine", .var "scope-owner",
            .var "proof-owner", .var "heap-next", .var "node-next",
            .var "stack-position"]
          [.symbol "mm-compressed-machine", context.scopeOwner,
            context.proofOwner,
            (CompressedIndexCode.ofNat before.heap.length).atom,
            (CompressedIndexCode.ofNat before.nodes.length).atom,
            (CompressedIndexCode.ofNat before.stack.length).atom] = some s3 := by
    simpa only [saveMachineTemplate, machineRow, matchAtom] using m3
  have proofAt3 : s3.lookup "proof-owner" = some context.proofOwner :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner"]
      [.symbol "mm-compressed-machine", context.scopeOwner]
      [.var "heap-next", .var "node-next", .var "stack-position"]
      [(CompressedIndexCode.ofNat before.heap.length).atom,
        (CompressedIndexCode.ofNat before.nodes.length).atom,
        (CompressedIndexCode.ofNat before.stack.length).atom]
      s2 s3 "proof-owner" context.proofOwner (by rfl) machineListMatched
  have stackAt3 : s3.lookup "stack-position" =
      some (CompressedIndexCode.ofNat before.stack.length).atom :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner",
        .var "proof-owner", .var "heap-next", .var "node-next"]
      [.symbol "mm-compressed-machine", context.scopeOwner,
        context.proofOwner,
        (CompressedIndexCode.ofNat before.heap.length).atom,
        (CompressedIndexCode.ofNat before.nodes.length).atom]
      [] [] s2 s3 "stack-position"
      (CompressedIndexCode.ofNat before.stack.length).atom (by rfl)
      machineListMatched
  obtain ⟨a4Member, m4⟩ := save_cmatchAtom_filterMap_witness f4
  obtain ⟨previous, a4Eq, previousAt4⟩ :=
    saveStackSuccessor_match_decodes context before proofAt3 stackAt3 m4
  subst a4
  have a4Present :
      compressedIndexSuccessorRow
          (compressedStackOwner context.proofOwner) previous
          (CompressedIndexCode.ofNat before.stack.length).atom ∈ space :=
    saveReadCandidate_mem_space represented authority.directive a4Member
  have a4Combined := (represented.exact_rows _).1 a4Present
  have a4Static :
      compressedIndexSuccessorRow
          (compressedStackOwner context.proofOwner) previous
          (CompressedIndexCode.ofNat before.stack.length).atom ∈ staticFrame := by
    rcases List.mem_append.mp a4Combined with sourceRow | staticRow
    · have dynamic := canonicalBoundaryRows_all_dynamic context before ledger
        scanner _ sourceRow
      simp [isDynamicRow, dynamicRowHeads, compressedIndexSuccessorRow,
        compressedStackOwner] at dynamic
    · exact staticRow
  have previousEq := authority.stackPredecessorFunctional previous a4Static
  subst previous
  obtain ⟨_a5Member, m5⟩ := save_cmatchAtom_filterMap_witness f5
  obtain ⟨_a6Member, m6⟩ := save_cmatchAtom_filterMap_witness f6
  obtain ⟨_a7Member, m7⟩ := save_cmatchAtom_filterMap_witness f7
  obtain ⟨_a8Member, m8⟩ := save_cmatchAtom_filterMap_witness f8
  obtain ⟨_a9Member, m9⟩ := save_cmatchAtom_filterMap_witness f9
  obtain ⟨_a10Member, m10⟩ := save_cmatchAtom_filterMap_witness f10
  obtain ⟨_a11Member, m11⟩ := save_cmatchAtom_filterMap_witness f11
  obtain ⟨_a12Member, m12⟩ := save_cmatchAtom_filterMap_witness f12
  obtain ⟨_a13Member, m13⟩ := save_cmatchAtom_filterMap_witness f13
  rw [Conformance.cmatchAtom_eq_matchAtom] at m5 m6 m7 m8 m9 m10 m11 m12 m13
  have finalLookup := (matchAtom_lookupExtends m13) _ _
    ((matchAtom_lookupExtends m12) _ _
      ((matchAtom_lookupExtends m11) _ _
        ((matchAtom_lookupExtends m10) _ _
          ((matchAtom_lookupExtends m9) _ _
            ((matchAtom_lookupExtends m8) _ _
              ((matchAtom_lookupExtends m7) _ _
                ((matchAtom_lookupExtends m6) _ _
                  ((matchAtom_lookupExtends m5) _ _ previousAt4))))))))
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  have finalEq : substitution = s13 := finished.1
  subst substitution
  exact finalLookup

/-- Every actual matcher row at an authorized represented save boundary gets
its next heap frontier from the unique source-indexed successor edge.  This is
the load-bearing freshness theorem for consuming the old machine control. -/
theorem saveMatcherRow_next_heap_position_exact_of_passive_machine_free
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    (passiveMachineFree : ∀ tail,
      .expression (.symbol "mm-compressed-machine" :: tail) ∉
        canonicalPassiveRows context before ledger)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    Subst.lookup substitution "next-heap-position" =
      some (CompressedIndexCode.ofNat (before.heap.length + 1)).atom := by
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  change matchedSubst = substitution at substEq
  subst matchedSubst
  rw [compressedSaveDirective_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold savePatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, r9⟩ := r8
  obtain ⟨⟨s10, a10⟩, f10, r10⟩ := r9
  obtain ⟨⟨s11, a11⟩, f11, r11⟩ := r10
  obtain ⟨⟨s12, a12⟩, f12, r12⟩ := r11
  obtain ⟨⟨s13, a13⟩, f13, finished⟩ := r12
  obtain ⟨a3Member, m3⟩ := save_cmatchAtom_filterMap_witness f3
  have a3Eq := saveMachine_candidate_eq represented
    authority.directive passiveMachineFree a3Member m3
  subst a3
  rw [Conformance.cmatchAtom_eq_matchAtom] at m3
  have machineListMatched :
      matchAtom.matchAtomList s2
          [.symbol "mm-compressed-machine", .var "scope-owner",
            .var "proof-owner", .var "heap-next", .var "node-next",
            .var "stack-position"]
          [.symbol "mm-compressed-machine", context.scopeOwner,
            context.proofOwner,
            (CompressedIndexCode.ofNat before.heap.length).atom,
            (CompressedIndexCode.ofNat before.nodes.length).atom,
            (CompressedIndexCode.ofNat before.stack.length).atom] = some s3 := by
    simpa only [saveMachineTemplate, machineRow, matchAtom] using m3
  have proofOwnerAt3 : s3.lookup "proof-owner" = some context.proofOwner :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner"]
      [.symbol "mm-compressed-machine", context.scopeOwner]
      [.var "heap-next", .var "node-next", .var "stack-position"]
      [(CompressedIndexCode.ofNat before.heap.length).atom,
       (CompressedIndexCode.ofNat before.nodes.length).atom,
       (CompressedIndexCode.ofNat before.stack.length).atom]
      s2 s3 "proof-owner" context.proofOwner (by rfl) machineListMatched
  have heapAt3 : s3.lookup "heap-next" =
      some (CompressedIndexCode.ofNat before.heap.length).atom :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner",
        .var "proof-owner"]
      [.symbol "mm-compressed-machine", context.scopeOwner,
        context.proofOwner]
      [.var "node-next", .var "stack-position"]
      [(CompressedIndexCode.ofNat before.nodes.length).atom,
       (CompressedIndexCode.ofNat before.stack.length).atom]
      s2 s3 "heap-next"
      (CompressedIndexCode.ofNat before.heap.length).atom (by rfl)
      machineListMatched
  obtain ⟨a4Member, m4⟩ := save_cmatchAtom_filterMap_witness f4
  obtain ⟨a5Member, m5⟩ := save_cmatchAtom_filterMap_witness f5
  obtain ⟨a6Member, m6⟩ := save_cmatchAtom_filterMap_witness f6
  have proofOwnerAt6 : s6.lookup "proof-owner" = some context.proofOwner := by
    rw [Conformance.cmatchAtom_eq_matchAtom] at m4 m5 m6
    exact (matchAtom_lookupExtends m6) _ _
      ((matchAtom_lookupExtends m5) _ _
        ((matchAtom_lookupExtends m4) _ _ proofOwnerAt3))
  have heapAt6 : s6.lookup "heap-next" =
      some (CompressedIndexCode.ofNat before.heap.length).atom := by
    rw [Conformance.cmatchAtom_eq_matchAtom] at m4 m5 m6
    exact (matchAtom_lookupExtends m6) _ _
      ((matchAtom_lookupExtends m5) _ _
        ((matchAtom_lookupExtends m4) _ _ heapAt3))
  obtain ⟨a7Member, m7⟩ := save_cmatchAtom_filterMap_witness f7
  obtain ⟨next, a7Eq, nextAt7⟩ :=
    saveHeapSuccessor_match_decodes context before proofOwnerAt6 heapAt6 m7
  subst a7
  have a7Present :
      compressedIndexSuccessorRow
          (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat before.heap.length).atom next ∈ space :=
    saveReadCandidate_mem_space represented authority.directive a7Member
  have a7Combined := (represented.exact_rows _).1 a7Present
  have a7Static :
      compressedIndexSuccessorRow
          (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat before.heap.length).atom next ∈
        staticFrame := by
    rcases List.mem_append.mp a7Combined with sourceRow | staticRow
    · have dynamic := canonicalBoundaryRows_all_dynamic context before ledger
        scanner _ sourceRow
      simp [isDynamicRow, dynamicRowHeads, compressedIndexSuccessorRow,
        compressedHeapOwner] at dynamic
    · exact staticRow
  have nextEq : next =
      (CompressedIndexCode.ofNat (before.heap.length + 1)).atom :=
    authority.functional next a7Static
  subst next
  obtain ⟨_a8Member, m8⟩ := save_cmatchAtom_filterMap_witness f8
  obtain ⟨_a9Member, m9⟩ := save_cmatchAtom_filterMap_witness f9
  obtain ⟨_a10Member, m10⟩ := save_cmatchAtom_filterMap_witness f10
  obtain ⟨_a11Member, m11⟩ := save_cmatchAtom_filterMap_witness f11
  obtain ⟨_a12Member, m12⟩ := save_cmatchAtom_filterMap_witness f12
  obtain ⟨_a13Member, m13⟩ := save_cmatchAtom_filterMap_witness f13
  rw [Conformance.cmatchAtom_eq_matchAtom] at m8 m9 m10 m11 m12 m13
  have nextAt13 := (matchAtom_lookupExtends m13) _ _
    ((matchAtom_lookupExtends m12) _ _
      ((matchAtom_lookupExtends m11) _ _
        ((matchAtom_lookupExtends m10) _ _
          ((matchAtom_lookupExtends m9) _ _
            ((matchAtom_lookupExtends m8) _ _ nextAt7)))))
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  have finalEq : substitution = s13 := finished.1
  subst substitution
  exact nextAt13

private theorem mem_saveLive_of_mem_of_inert
    {space : List Atom} {row : Atom}
    (inert : extractSupportedSourceExecFact row = none)
    (present : row ∈ space) :
    row ∈ saveLive space := by
  unfold saveLive
  apply (List.mem_erase_of_ne ?_).2 present
  intro equal
  subst row
  have extracted :
      extractSupportedSourceExecFact compressedSaveDirective.atom =
        some compressedSaveDirective := by
    rfl
  rw [extracted] at inert
  contradiction

/-- Every row of the presentation-parametric canonical save read is present
in the represented read-space when the static frame supplies the two finite
successors and that presentation's six runtime carriers. -/
theorem source_save_canonical_read_included_for
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (rules : SaveRuntimeRuleBundle)
    {context : BoundaryContext} {before : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore : ScannerBoundary} {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (staticSupport : SaveStaticSupportFor rules context before
      (before.stack.length - 1) staticFrame) :
    ∀ atom,
      atom ∈ compressedSaveDirective.atom ::
          saveLive (canonicalSaveMatchSpaceFor rules context before
            scannerBefore (before.stack.length - 1)
            (displayedProofOccurrence nodeId node sourceOccurrence)) →
        atom ∈ compressedSaveDirective.atom :: saveLive space := by
  have stackLookup :
      before.stack[before.stack.length - 1]? = some nodeId := by
    simpa only [List.getLast?_eq_getElem?] using stackTop
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  have stackSource :
      compressedStackRow context.proofOwner (before.stack.length - 1) item ∈
        sourceStackRows context.proofOwner before ledger :=
    compressedStackRow_mem_sourceStackRows context.proofOwner before ledger
      (before.stack.length - 1) nodeId node sourceOccurrence stackLookup
      nodeLookup occurrenceLookup
  have nodeSource :
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
        sourceNodeRows context.proofOwner before ledger :=
    nodeRow_mem_sourceNodeRows context.proofOwner before ledger nodeId node
      sourceOccurrence nodeLookup occurrenceLookup
  have stackPresent :
      compressedStackRow context.proofOwner (before.stack.length - 1) item ∈
        space := by
    apply (represented.exact_rows _).2
    apply List.mem_append_left
    simp [canonicalBoundaryRows, canonicalPassiveRows, stackSource]
  have nodePresent :
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈ space := by
    apply (represented.exact_rows _).2
    apply List.mem_append_left
    simp [canonicalBoundaryRows, canonicalPassiveRows, nodeSource]
  have staticPresent : ∀ row ∈ staticFrame, row ∈ space := by
    intro row member
    apply (represented.exact_rows row).2
    exact List.mem_append_right _ member
  intro atom member
  have liveEq :
      saveLive (canonicalSaveMatchSpaceFor rules context before scannerBefore
        (before.stack.length - 1) item) =
        [scannerRow context scannerBefore, machineRow context before,
         compressedIndexSuccessorRow
           (compressedStackOwner context.proofOwner)
           (CompressedIndexCode.ofNat (before.stack.length - 1)).atom
           (CompressedIndexCode.ofNat before.stack.length).atom,
         compressedStackRow context.proofOwner (before.stack.length - 1) item,
         MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
         compressedIndexSuccessorRow
           (compressedHeapOwner context.proofOwner)
           (CompressedIndexCode.ofNat before.heap.length).atom
           (CompressedIndexCode.ofNat (before.heap.length + 1)).atom] ++
          rules.captureRows := by
    simp [saveLive, canonicalSaveMatchSpaceFor]
  rw [liveEq] at member
  rcases List.mem_cons.mp member with self | liveMember
  · subst atom
    exact List.mem_cons_self
  · rcases List.mem_append.mp liveMember with canonical | captures
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at canonical
      rcases canonical with scan | machine | stackSuccessor | stackCell |
        nodeRow | heapSuccessor
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · exact extractSupportedSourceExecFact_eq_none_of_dynamic _
            (scannerRow_isDynamic context scannerBefore)
        · exact represented_scannerRow represented
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · exact extractSupportedSourceExecFact_eq_none_of_dynamic _
            (machineRow_isDynamic context before)
        · exact represented_machineRow represented
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · simp [compressedIndexSuccessorRow, compressedStackOwner,
            extractSupportedSourceExecFact, extractRawExecFact]
        · exact staticPresent _ staticSupport.stackSuccessor
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · simp [compressedStackRow, extractSupportedSourceExecFact,
            extractRawExecFact]
        · exact stackPresent
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · simp [MM2CompressedProofHeapEncoding.nodeRow,
            extractSupportedSourceExecFact, extractRawExecFact]
        · exact nodePresent
      · subst atom
        apply List.mem_cons_of_mem
        apply mem_saveLive_of_mem_of_inert
        · simp [compressedIndexSuccessorRow, compressedHeapOwner,
            extractSupportedSourceExecFact, extractRawExecFact]
        · exact staticPresent _ staticSupport.heapSuccessor
    · apply List.mem_cons_of_mem
      apply mem_saveLive_of_mem_of_inert
      · have captureMember := captures
        simp [SaveRuntimeRuleBundle.captureRows] at captureMember
        rcases captureMember with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp [compressedOwnedRuntimeRuleRow,
            extractSupportedSourceExecFact, extractRawExecFact]
      · exact staticPresent atom (staticSupport.captures atom captures)

/-- Base-presentation corollary of the reusable canonical-read inclusion. -/
theorem source_save_canonical_read_included
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore : ScannerBoundary} {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (staticSupport : SaveStaticSupport context before
      (before.stack.length - 1) staticFrame) :
    ∀ atom,
      atom ∈ compressedSaveDirective.atom ::
          saveLive (canonicalSaveMatchSpace context before scannerBefore
            (before.stack.length - 1)
            (displayedProofOccurrence nodeId node sourceOccurrence)) →
        atom ∈ compressedSaveDirective.atom :: saveLive space := by
  simpa using source_save_canonical_read_included_for
    baseSaveRuntimeRuleBundle ledger represented stackTop nodeLookup
      occurrenceLookup staticSupport.asForBase

/-- Complete canonical represented space at a base-presentation save
boundary.  Dynamic rows come only from the source machine and ledger; the
static suffix is the admitted save frame above. -/
def canonicalSaveBoundarySpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat) : List Atom :=
  canonicalBoundaryRows context state ledger scanner ++
    canonicalSaveStaticFrame context state stackTopPosition

theorem canonicalSaveBoundarySpace_represents
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (stackTopPosition : Nat)
    (wellFormed : SourceBoundaryWellFormed context state) :
    RepresentsRunningBoundary context state ledger scanner
      (canonicalSaveStaticFrame context state stackTopPosition)
      (canonicalSaveBoundarySpace context state ledger scanner
        stackTopPosition) := by
  exact canonical_represents_running_boundary context state ledger scanner
    (canonicalSaveStaticFrame context state stackTopPosition) wellFormed
    (canonicalSaveStaticFrame_clean context state stackTopPosition)

/-- On the canonical source-derived frame, the exact save matcher witness no
longer requires a caller-supplied target-space packet. -/
theorem source_save_canonical_space_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    ExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence)
      (canonicalSaveBoundarySpace context before ledger scannerBefore
        (before.stack.length - 1)) := by
  let staticFrame := canonicalSaveStaticFrame context before
    (before.stack.length - 1)
  let space := canonicalSaveBoundarySpace context before ledger scannerBefore
    (before.stack.length - 1)
  have represented : RepresentsRunningBoundary context before ledger
      scannerBefore staticFrame space :=
    canonicalSaveBoundarySpace_represents context before ledger scannerBefore
      (before.stack.length - 1) wellFormed
  have included := source_save_canonical_read_included ledger represented
    stackTop nodeLookup occurrenceLookup
    (canonicalSaveStaticFrame_authority context before
      (before.stack.length - 1)).support
  exact (canonicalSaveMatchSpace_exact_match receipt step
    (before.stack.length - 1)
      (displayedProofOccurrence nodeId node sourceOccurrence)).mono_read included

/-- The exact matcher component of a continuous save request is constructed
from the represented source boundary and admitted static verifier structure;
the caller supplies only the independent scheduler invariant and exact support
inventory needed by the ordinary work queue. -/
theorem ContinuousSaveRequestFrame.of_source_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (staticAuthority : SaveStaticAuthority compressedBaseExecutablePresentation
      context before (before.stack.length - 1) staticFrame)
    (invariant : ReflectiveWorkQueueInvariant space)
    (supported : cSupportedSourceExecFacts space = [compressedSaveDirective]) :
    ContinuousSaveRequestFrame context before after ledger scannerBefore
      scannerAfter staticFrame space
      (displayedProofOccurrence nodeId node sourceOccurrence) := by
  apply ContinuousSaveRequestFrame.of_canonical_match receipt step
    (before.stack.length - 1)
      (displayedProofOccurrence nodeId node sourceOccurrence) represented
      invariant supported
  exact source_save_canonical_read_included ledger represented stackTop
    nodeLookup occurrenceLookup staticAuthority.support

/-! ## Concrete row theorem -/

/-- Appending a proof-valued source heap cell contributes no assertion row.
This is the assertion-valued half of the heterogeneous save delta. -/
theorem assertionHeapRowsFrom_append_proof
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (nodeId : Nat) :
    assertionHeapRowsFrom proofOwner position
        (heap ++ [.proof nodeId]) =
      assertionHeapRowsFrom proofOwner position heap := by
  induction heap generalizing position with
  | nil => simp [assertionHeapRowsFrom]
  | cons entry remaining induction =>
      cases entry <;> simp [assertionHeapRowsFrom, induction]

/-- Appending one saved node appends exactly its source-derived receipt.  The
position is the authored save occurrence, not a target-supplied heap index. -/
theorem sourceSaveRowsFrom_append_singleton
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (savePosition : Nat)
    (saved : List Nat) (nodeId : Nat) (node : ProofNode source target)
    (sourceOccurrence : Atom)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    sourceSaveRowsFrom context state ledger savePosition
        (saved ++ [nodeId]) =
      sourceSaveRowsFrom context state ledger savePosition saved ++
        [saveReceiptRow context.proofOwner
          (context.initialHeapLength + savePosition + saved.length)
          (displayedProofOccurrence nodeId node sourceOccurrence)] := by
  induction saved generalizing savePosition with
  | nil =>
      simp [sourceSaveRowsFrom, nodeLookup, occurrenceLookup]
  | cons head remaining induction =>
      simp only [List.cons_append, sourceSaveRowsFrom, List.length_cons]
      split
      all_goals
        have positionEqual :
            context.initialHeapLength + (savePosition + 1) +
                remaining.length =
              context.initialHeapLength + savePosition +
                (remaining.length + 1) := by
          omega
        rw [induction (savePosition + 1), positionEqual]
        simp only [List.append_assoc, List.nil_append]

/-- Receipt generation depends only on the node table and occurrence ledger;
heap and stack changes cannot alter an already-authored save display. -/
theorem sourceSaveRowsFrom_congr
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext)
    (left right : MachineState source target)
    (leftLedger : NodeOccurrenceLedger left)
    (rightLedger : NodeOccurrenceLedger right)
    (nodesEqual : left.nodes = right.nodes)
    (occurrencesEqual : leftLedger.occurrences = rightLedger.occurrences)
    (savePosition : Nat) (saved : List Nat) :
    sourceSaveRowsFrom context left leftLedger savePosition saved =
      sourceSaveRowsFrom context right rightLedger savePosition saved := by
  induction saved generalizing savePosition with
  | nil => rfl
  | cons nodeId remaining induction =>
      simp only [sourceSaveRowsFrom]
      rw [nodesEqual, occurrencesEqual]
      rw [induction (savePosition + 1)]

/-- Stack-row generation likewise ignores heap and save frontiers once the
node table and occurrence ledger are fixed. -/
theorem sourceStackRowsFrom_congr
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom)
    (left right : MachineState source target)
    (leftLedger : NodeOccurrenceLedger left)
    (rightLedger : NodeOccurrenceLedger right)
    (nodesEqual : left.nodes = right.nodes)
    (occurrencesEqual : leftLedger.occurrences = rightLedger.occurrences)
    (stackPosition : Nat) (stack : List Nat) :
    sourceStackRowsFrom proofOwner left leftLedger stackPosition stack =
      sourceStackRowsFrom proofOwner right rightLedger stackPosition stack := by
  induction stack generalizing stackPosition with
  | nil => rfl
  | cons nodeId remaining induction =>
      simp only [sourceStackRowsFrom]
      rw [nodesEqual, occurrencesEqual, induction (stackPosition + 1)]

/-- A semantic `Z` save changes the complete passive MM2 display by exactly
one proof-heap row and one receipt row, extensionally.  Nodes and stack rows
are unchanged, and the heterogeneous assertion view ignores the new proof
cell. -/
theorem canonicalPassiveRows_save_iff
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (step : ActionStep before .save after)
    (nodeId : Nat) (node : ProofNode source target)
    (sourceOccurrence : Atom)
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (row : Atom) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    row ∈ canonicalPassiveRows context after ledgerAfter ↔
      row ∈ canonicalPassiveRows context before ledger ∨
        row = heapProofRow context.proofOwner before.heap.length item ∨
        row = saveReceiptRow context.proofOwner before.heap.length item := by
  dsimp only
  cases step with
  | save actualNodeId actualNode actualTop actualLookup =>
      have nodeIdEq : nodeId = actualNodeId := by
        rw [actualTop] at stackTop
        exact Option.some.inj stackTop.symm
      subst nodeId
      have nodeEq : node = actualNode := by
        rw [actualLookup] at nodeLookup
        exact Option.some.inj nodeLookup.symm
      subst node
      have ledgerOccurrences :
          (ActionStep.occurrenceLedger
            (ActionStep.save before actualNodeId actualNode actualTop
              actualLookup) proofPosition ledger).occurrences =
            ledger.occurrences :=
        ActionStep.save_occurrenceLedger_unchanged
          (ActionStep.save before actualNodeId actualNode actualTop actualLookup)
          proofPosition ledger
      have heapDisplay :
          displayedHeap
              { before with
                heap := before.heap ++ [.proof actualNodeId]
                saves := before.saves ++ [actualNodeId] }
              (ActionStep.occurrenceLedger
                (ActionStep.save before actualNodeId actualNode actualTop
                  actualLookup) proofPosition ledger) =
            displayedHeap before ledger ++
              [.occurrence
                (displayedProofOccurrence actualNodeId actualNode
                  sourceOccurrence)] := by
        simp [displayedHeap, displayedHeapEntry, actualLookup,
          occurrenceLookup, ledgerOccurrences]
      have assertionRows :
          assertionHeapRows context.proofOwner
              (before.heap ++ [.proof actualNodeId]) =
            assertionHeapRows context.proofOwner before.heap := by
        simpa [assertionHeapRows] using
          assertionHeapRowsFrom_append_proof context.proofOwner 0 before.heap
            actualNodeId
      have saveRows :
          sourceSaveRows context
              { before with
                heap := before.heap ++ [.proof actualNodeId]
                saves := before.saves ++ [actualNodeId] }
              (ActionStep.occurrenceLedger
                (ActionStep.save before actualNodeId actualNode actualTop
                  actualLookup) proofPosition ledger) =
            sourceSaveRows context before ledger ++
              [saveReceiptRow context.proofOwner before.heap.length
                (displayedProofOccurrence actualNodeId actualNode
                  sourceOccurrence)] := by
        have appended := sourceSaveRowsFrom_append_singleton context before
          ledger 0 before.saves actualNodeId actualNode sourceOccurrence
          actualLookup occurrenceLookup
        have transported := sourceSaveRowsFrom_congr context
          { before with
            heap := before.heap ++ [.proof actualNodeId]
            saves := before.saves ++ [actualNodeId] }
          before
          (ActionStep.occurrenceLedger
            (ActionStep.save before actualNodeId actualNode actualTop
              actualLookup) proofPosition ledger)
          ledger rfl ledgerOccurrences 0 (before.saves ++ [actualNodeId])
        unfold sourceSaveRows
        rw [transported, appended, wellFormed.heap_frontier]
        simp only [Nat.add_zero]
      have nodeRows :
          sourceNodeRows context.proofOwner
              { before with
                heap := before.heap ++ [.proof actualNodeId]
                saves := before.saves ++ [actualNodeId] }
              (ActionStep.occurrenceLedger
                (ActionStep.save before actualNodeId actualNode actualTop
                  actualLookup) proofPosition ledger) =
            sourceNodeRows context.proofOwner before ledger := by
        unfold sourceNodeRows
        rw [ledgerOccurrences]
      have stackRows :
          sourceStackRows context.proofOwner
              { before with
                heap := before.heap ++ [.proof actualNodeId]
                saves := before.saves ++ [actualNodeId] }
              (ActionStep.occurrenceLedger
                (ActionStep.save before actualNodeId actualNode actualTop
                  actualLookup) proofPosition ledger) =
            sourceStackRows context.proofOwner before ledger := by
        unfold sourceStackRows
        exact sourceStackRowsFrom_congr context.proofOwner
          { before with
            heap := before.heap ++ [.proof actualNodeId]
            saves := before.saves ++ [actualNodeId] }
          before
          (ActionStep.occurrenceLedger
            (ActionStep.save before actualNodeId actualNode actualTop
              actualLookup) proofPosition ledger)
          ledger rfl ledgerOccurrences 0 before.stack
      rw [canonicalPassiveRows, heapDisplay,
        heapProofRows_append_singleton, assertionRows,
        nodeRows, stackRows, canonicalPassiveRows, saveRows]
      simp only [List.mem_append, List.mem_singleton]
      rw [displayedHeap_length]
      tauto

/-! ## Passive-frame preservation -/

/-- Rows that cannot be one of the two moving save controls.  The property is
deliberately structural: it is independent of a particular substitution. -/
def avoidsSaveControlHeads : Atom -> Bool
  | .expression (.symbol head :: _) =>
      head != "mm-compressed-scan" && head != "mm-compressed-machine"
  | _ => false

private def saveRowHead? : Atom → Option String
  | .expression (.symbol head :: _) => some head
  | _ => none

private theorem heapProofRowsFrom_head
    {Other : Type} (proofOwner : Atom) (position : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other)) :
    ∀ row, row ∈ heapProofRowsFrom proofOwner position heap →
      saveRowHead? row = some "mm-compressed-heap-proof" := by
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

private theorem assertionHeapRowsFrom_head
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    ∀ row, row ∈ assertionHeapRowsFrom proofOwner position heap →
      saveRowHead? row = some "mm-compressed-heap-assertion" := by
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

private theorem sourceNodeRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (position : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom) :
    ∀ row, row ∈ sourceNodeRowsFrom proofOwner position nodes occurrences →
      saveRowHead? row = some "mm-compressed-node" := by
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

private theorem sourceStackRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (stack : List Nat) :
    ∀ row, row ∈ sourceStackRowsFrom proofOwner state ledger position stack →
      saveRowHead? row = some "mm-compressed-stack-cell" ∨
        saveRowHead? row = some "mm-stack-cell" := by
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

private theorem sourceSaveRowsFrom_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat) (saves : List Nat) :
    ∀ row, row ∈ sourceSaveRowsFrom context state ledger position saves →
      saveRowHead? row = some "mm-compressed-save-receipt" := by
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

theorem heapProofRowsFrom_avoid_save_controls
    {Other : Type} (proofOwner : Atom) (position : Nat)
    (heap : List (MM2CompressedProofHeapEncoding.HeapEntry Other)) :
    ∀ row, row ∈ heapProofRowsFrom proofOwner position heap ->
      avoidsSaveControlHeads row = true := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | occurrence item =>
          intro row member
          simp only [heapProofRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [avoidsSaveControlHeads, heapProofRow]
          · exact induction (position + 1) row tail
      | «opaque» value =>
          intro row member
          exact induction (position + 1) row
            (by simpa [heapProofRowsFrom] using member)

theorem assertionHeapRowsFrom_avoid_save_controls
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    ∀ row, row ∈ assertionHeapRowsFrom proofOwner position heap ->
      avoidsSaveControlHeads row = true := by
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
          · simp [avoidsSaveControlHeads]
          · exact induction (position + 1) row tail

theorem sourceNodeRowsFrom_avoid_save_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (nodeId : Nat)
    (nodes : List (ProofNode source target)) (occurrences : List Atom) :
    ∀ row, row ∈ sourceNodeRowsFrom proofOwner nodeId nodes occurrences ->
      avoidsSaveControlHeads row = true := by
  induction nodes generalizing nodeId occurrences with
  | nil => simp [sourceNodeRowsFrom]
  | cons node nodes induction =>
      cases occurrences with
      | nil => simp [sourceNodeRowsFrom]
      | cons occurrence occurrences =>
          intro row member
          simp only [sourceNodeRowsFrom, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [avoidsSaveControlHeads,
              MM2CompressedProofHeapEncoding.nodeRow]
          · exact induction (nodeId + 1) occurrences row tail

theorem sourceStackRowsFrom_avoid_save_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (stackPosition : Nat)
    (stack : List Nat) :
    ∀ row, row ∈ sourceStackRowsFrom proofOwner state ledger stackPosition stack ->
      avoidsSaveControlHeads row = true := by
  induction stack generalizing stackPosition with
  | nil => simp [sourceStackRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceStackRowsFrom] at member
      split at member
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at member
        rcases member with rfl | rfl | tail
        · simp [avoidsSaveControlHeads, compressedStackRow]
        · change
            ("mm-stack-cell" != "mm-compressed-scan" &&
              "mm-stack-cell" != "mm-compressed-machine") = true
          decide
        · exact induction (stackPosition + 1) row tail
      · exact induction (stackPosition + 1) row
          (by simpa only [List.nil_append] using member)

theorem sourceSaveRowsFrom_avoid_save_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (savePosition : Nat)
    (saved : List Nat) :
    ∀ row, row ∈ sourceSaveRowsFrom context state ledger savePosition saved ->
      avoidsSaveControlHeads row = true := by
  induction saved generalizing savePosition with
  | nil => simp [sourceSaveRowsFrom]
  | cons nodeId remaining induction =>
      intro row member
      simp only [sourceSaveRowsFrom] at member
      split at member
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at member
        rcases member with rfl | tail
        · simp [avoidsSaveControlHeads, saveReceiptRow]
        · exact induction (savePosition + 1) row tail
      · exact induction (savePosition + 1) row
          (by simpa only [List.nil_append] using member)

/-- Every source-derived passive row is structurally disjoint from the scan
and machine controls removed by a save. -/
theorem canonicalPassiveRows_avoid_save_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    ∀ row, row ∈ canonicalPassiveRows context state ledger ->
      avoidsSaveControlHeads row = true := by
  intro row member
  simp only [canonicalPassiveRows, List.mem_append] at member
  rcases member with (((heap | assertion) | node) | stack) | save
  · exact heapProofRowsFrom_avoid_save_controls context.proofOwner 0
      (displayedHeap state ledger) row (by simpa [heapProofRows] using heap)
  · exact assertionHeapRowsFrom_avoid_save_controls context.proofOwner 0
      state.heap row (by simpa [assertionHeapRows] using assertion)
  · exact sourceNodeRowsFrom_avoid_save_controls context.proofOwner 0
      state.nodes ledger.occurrences row
      (by simpa [sourceNodeRows] using node)
  · exact sourceStackRowsFrom_avoid_save_controls context.proofOwner state
      ledger 0 state.stack row (by simpa [sourceStackRows] using stack)
  · exact sourceSaveRowsFrom_avoid_save_controls context state ledger 0
      state.saves row (by simpa [sourceSaveRows] using save)

private theorem canonicalPassiveRows_machine_free
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    ∀ tail, .expression (.symbol "mm-compressed-machine" :: tail) ∉
      canonicalPassiveRows context state ledger := by
  intro tail member
  have avoids := canonicalPassiveRows_avoid_save_controls context state ledger
    (.expression (.symbol "mm-compressed-machine" :: tail)) member
  simp [avoidsSaveControlHeads] at avoids

private theorem canonicalPassiveRows_scanner_free
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    ∀ tail, .expression (.symbol "mm-compressed-scan" :: tail) ∉
      canonicalPassiveRows context state ledger := by
  intro tail member
  have avoids := canonicalPassiveRows_avoid_save_controls context state ledger
    (.expression (.symbol "mm-compressed-scan" :: tail)) member
  simp [avoidsSaveControlHeads] at avoids

private theorem represented_saveStackCell_mem_sourceStackRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {candidate : Atom} (candidateMember : candidate ∈
      compressedSaveDirective.atom :: saveLive space)
    {stackTop nodeIdentity : Atom}
    (shape : candidate = .expression
      [.symbol "mm-compressed-stack-cell", context.proofOwner,
        stackTop, nodeIdentity]) :
    candidate ∈ sourceStackRows context.proofOwner before ledger := by
  have present : candidate ∈ space :=
    saveReadCandidate_mem_space represented directivePresent candidateMember
  have combined := (represented.exact_rows candidate).1 present
  rcases List.mem_append.mp combined with sourceRow | staticRow
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at sourceRow
    rcases sourceRow with (machineEq | scannerEq) | passive
    · rw [machineEq] at shape
      simp [machineRow] at shape
    · rw [scannerEq] at shape
      simp [scannerRow] at shape
    · simp only [canonicalPassiveRows, List.mem_append] at passive
      rcases passive with (((heap | assertion) | node) | stack) | save
      · have head := heapProofRowsFrom_head context.proofOwner 0
          (displayedHeap before ledger) candidate
          (by simpa [heapProofRows] using heap)
        rw [shape] at head
        simp [saveRowHead?] at head
      · have head := assertionHeapRowsFrom_head context.proofOwner 0
          before.heap candidate (by simpa [assertionHeapRows] using assertion)
        rw [shape] at head
        simp [saveRowHead?] at head
      · have head := sourceNodeRowsFrom_head context.proofOwner 0
          before.nodes ledger.occurrences candidate
          (by simpa [sourceNodeRows] using node)
        rw [shape] at head
        simp [saveRowHead?] at head
      · exact stack
      · have head := sourceSaveRowsFrom_head context before ledger 0
          before.saves candidate (by simpa [sourceSaveRows] using save)
        rw [shape] at head
        simp [saveRowHead?] at head
  · have clean := represented.staticFrame_clean candidate staticRow
    rw [shape] at clean
    simp [isDynamicRow, dynamicRowHeads] at clean

private theorem represented_saveNode_mem_sourceNodeRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {candidate : Atom} (candidateMember : candidate ∈
      compressedSaveDirective.atom :: saveLive space)
    {item : ProofOccurrence}
    (shape : candidate =
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item) :
    candidate ∈ sourceNodeRows context.proofOwner before ledger := by
  have present : candidate ∈ space :=
    saveReadCandidate_mem_space represented directivePresent candidateMember
  have combined := (represented.exact_rows candidate).1 present
  rcases List.mem_append.mp combined with sourceRow | staticRow
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at sourceRow
    rcases sourceRow with (machineEq | scannerEq) | passive
    · rw [machineEq] at shape
      simp [machineRow, MM2CompressedProofHeapEncoding.nodeRow] at shape
    · rw [scannerEq] at shape
      simp [scannerRow, MM2CompressedProofHeapEncoding.nodeRow] at shape
    · simp only [canonicalPassiveRows, List.mem_append] at passive
      rcases passive with (((heap | assertion) | node) | stack) | save
      · have head := heapProofRowsFrom_head context.proofOwner 0
          (displayedHeap before ledger) candidate
          (by simpa [heapProofRows] using heap)
        rw [shape] at head
        simp [saveRowHead?, MM2CompressedProofHeapEncoding.nodeRow] at head
      · have head := assertionHeapRowsFrom_head context.proofOwner 0
          before.heap candidate (by simpa [assertionHeapRows] using assertion)
        rw [shape] at head
        simp [saveRowHead?, MM2CompressedProofHeapEncoding.nodeRow] at head
      · exact node
      · have head := sourceStackRowsFrom_head context.proofOwner before
          ledger 0 before.stack candidate (by simpa [sourceStackRows] using stack)
        rw [shape] at head
        simp [saveRowHead?, MM2CompressedProofHeapEncoding.nodeRow] at head
      · have head := sourceSaveRowsFrom_head context before ledger 0
          before.saves candidate (by simpa [sourceSaveRows] using save)
        rw [shape] at head
        simp [saveRowHead?, MM2CompressedProofHeapEncoding.nodeRow] at head
  · have clean := represented.staticFrame_clean candidate staticRow
    rw [shape] at clean
    simp [isDynamicRow, dynamicRowHeads,
      MM2CompressedProofHeapEncoding.nodeRow] at clean

/-- Source-derived passive rows discharge the structural side condition of
the presentation-parametric stack-frontier inversion theorem. -/
theorem saveMatcherRow_stack_top_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom} {stackTopPosition : Nat}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveFrontierAuthority context before
      stackTopPosition staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    substitution.lookup "stack-top" =
      some (CompressedIndexCode.ofNat stackTopPosition).atom := by
  exact saveMatcherRow_stack_top_exact_of_passive_machine_free represented authority
      (canonicalPassiveRows_machine_free context before ledger) rowMember

/-- Every actual matcher row at an authorized represented save boundary gets
the unique source-indexed next heap frontier. -/
theorem saveMatcherRow_next_heap_position_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    Subst.lookup substitution "next-heap-position" =
      some (CompressedIndexCode.ofNat (before.heap.length + 1)).atom := by
  exact saveMatcherRow_next_heap_position_exact_of_passive_machine_free
    represented authority
      (canonicalPassiveRows_machine_free context before ledger) rowMember

/-- Every complete save matcher replays the two predecessor controls exactly.
This is the removal-side counterpart of the successor-control theorem: a
physical remove may consume only the represented scanner and machine rows,
never an unrelated row selected through a noncanonical assignment. -/
theorem saveMatcherRow_predecessor_controls_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (directivePresent : compressedSaveDirective.atom ∈ staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    instantiateTemplateAtom? substitution saveScanTemplate =
        some (scannerRow context scanner) ∧
      instantiateTemplateAtom? substitution saveMachineTemplate =
        some (machineRow context before) := by
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, substitutionExact⟩ :=
    rowMember
  change matchedSubstitution = substitution at substitutionExact
  subst matchedSubstitution
  rw [compressedSaveDirective_input_exact] at matched
  have matcherMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (compressedSaveDirective.atom :: saveLive space)
        (.compat (mkPattern savePatterns))).map Prod.fst :=
    List.mem_map_of_mem matched
  have scanOrigin : ∃ beforeFactor afterFactor carrier,
      carrier ∈ compressedSaveDirective.atom :: saveLive space ∧
        Conformance.Computable.cmatchAtom beforeFactor saveScanTemplate
            carrier = some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution saveScanTemplate = carrier :=
    Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
      (compressedSaveDirective.atom :: saveLive space)
      (mkPattern savePatterns) saveScanTemplate
      (by simp [savePatterns, mkPattern]) matcherMember
  obtain ⟨scanBefore, scanAfter, scanCarrier, scanMember, scanMatched,
      scanExtends, scanReplay⟩ := scanOrigin
  have scanExact : scanCarrier = scannerRow context scanner :=
    saveScan_candidate_eq represented directivePresent
      (canonicalPassiveRows_scanner_free context before ledger)
      scanMember scanMatched
  have scanCoveredAtMatch :
      templateCovered scanAfter saveScanTemplate = true :=
    Conformance.Computable.cmatchAtom_templateCovered scanBefore
      saveScanTemplate scanCarrier scanAfter scanMatched
  have scanCovered : templateCovered substitution saveScanTemplate = true :=
    Conformance.Computable.templateCovered_of_lookupExtends scanExtends
      saveScanTemplate scanCoveredAtMatch
  have scanInstantiated :=
    instantiateTemplateAtom_of_covered substitution saveScanTemplate scanCovered
  have machineOrigin : ∃ beforeFactor afterFactor carrier,
      carrier ∈ compressedSaveDirective.atom :: saveLive space ∧
        Conformance.Computable.cmatchAtom beforeFactor saveMachineTemplate
            carrier = some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution saveMachineTemplate = carrier :=
    Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
      (compressedSaveDirective.atom :: saveLive space)
      (mkPattern savePatterns) saveMachineTemplate
      (by simp [savePatterns, mkPattern]) matcherMember
  obtain ⟨machineBefore, machineAfter, machineCarrier, machineMember,
      machineMatched, machineExtends, machineReplay⟩ := machineOrigin
  have machineExact : machineCarrier = machineRow context before :=
    saveMachine_candidate_eq represented directivePresent
      (canonicalPassiveRows_machine_free context before ledger)
      machineMember machineMatched
  have machineCoveredAtMatch :
      templateCovered machineAfter saveMachineTemplate = true :=
    Conformance.Computable.cmatchAtom_templateCovered machineBefore
      saveMachineTemplate machineCarrier machineAfter machineMatched
  have machineCovered :
      templateCovered substitution saveMachineTemplate = true :=
    Conformance.Computable.templateCovered_of_lookupExtends machineExtends
      saveMachineTemplate machineCoveredAtMatch
  have machineInstantiated :=
    instantiateTemplateAtom_of_covered substitution saveMachineTemplate
      machineCovered
  constructor
  · calc
      instantiateTemplateAtom? substitution saveScanTemplate =
          some (applySubst substitution saveScanTemplate) := scanInstantiated
      _ = some scanCarrier := congrArg some scanReplay
      _ = some (scannerRow context scanner) := congrArg some scanExact
  · calc
      instantiateTemplateAtom? substitution saveMachineTemplate =
          some (applySubst substitution saveMachineTemplate) :=
        machineInstantiated
      _ = some machineCarrier := congrArg some machineReplay
      _ = some (machineRow context before) := congrArg some machineExact

/-- Every actual matcher row reconstructs the exact two moving successor
controls.  The proof ranges over the complete thirteen-premise matcher, not
only the canonical positive witness: owner and frontiers come from the unique
represented controls, the scanner tail comes from the consumed source byte,
and the heap successor comes from source-relative frontier authority. -/
theorem saveMatcherRow_successor_controls_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    instantiateTemplateAtom? substitution afterSaveMachineTemplate =
        some (machineRow context after) ∧
      instantiateTemplateAtom? substitution afterSaveScanTemplate =
        some (scannerRow context scannerAfter) ∧
      substitution.lookup "proof-owner" = some context.proofOwner ∧
      substitution.lookup "heap-next" =
        some (CompressedIndexCode.ofNat before.heap.length).atom := by
  have originalRowMember := rowMember
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  change matchedSubst = substitution at substEq
  subst matchedSubst
  rw [compressedSaveDirective_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold savePatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, r9⟩ := r8
  obtain ⟨⟨s10, a10⟩, f10, r10⟩ := r9
  obtain ⟨⟨s11, a11⟩, f11, r11⟩ := r10
  obtain ⟨⟨s12, a12⟩, f12, r12⟩ := r11
  obtain ⟨⟨s13, a13⟩, f13, finished⟩ := r12
  obtain ⟨a2Member, m2⟩ := save_cmatchAtom_filterMap_witness f2
  have a2Eq := saveScan_candidate_eq represented authority.directive
    (canonicalPassiveRows_scanner_free context before ledger) a2Member m2
  subst a2
  rw [Conformance.cmatchAtom_eq_matchAtom] at m2
  have scannerListMatched :
      matchAtom.matchAtomList s1
          [.symbol "mm-compressed-scan", .var "scope-owner",
            .var "proof-owner", .var "word-position",
            .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
            .symbol "mm-compressed-just-completed-step", listAtom natAtom []]
          [.symbol "mm-compressed-scan", context.scopeOwner,
            context.proofOwner, natAtom scannerBefore.wordPosition,
            listAtom natAtom (scannerBefore.remainingBytes.map UInt8.toNat),
            scannerBefore.phase.atom,
            listAtom natAtom scannerBefore.phase.reversePrefix] = some s2 := by
    simpa only [saveScanTemplate, scannerRow, matchAtom] using m2
  have scopeAt2 : s2.lookup "scope-owner" = some context.scopeOwner :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-scan"] [.symbol "mm-compressed-scan"]
      [.var "proof-owner", .var "word-position",
        .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
        .symbol "mm-compressed-just-completed-step", listAtom natAtom []]
      [context.proofOwner, natAtom scannerBefore.wordPosition,
        listAtom natAtom (scannerBefore.remainingBytes.map UInt8.toNat),
        scannerBefore.phase.atom,
        listAtom natAtom scannerBefore.phase.reversePrefix]
      s1 s2 "scope-owner" context.scopeOwner (by rfl) scannerListMatched
  have proofAt2 : s2.lookup "proof-owner" = some context.proofOwner :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-scan", .var "scope-owner"]
      [.symbol "mm-compressed-scan", context.scopeOwner]
      [.var "word-position",
        .expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
        .symbol "mm-compressed-just-completed-step", listAtom natAtom []]
      [natAtom scannerBefore.wordPosition,
        listAtom natAtom (scannerBefore.remainingBytes.map UInt8.toNat),
        scannerBefore.phase.atom,
        listAtom natAtom scannerBefore.phase.reversePrefix]
      s1 s2 "proof-owner" context.proofOwner (by rfl) scannerListMatched
  have wordAt2 : s2.lookup "word-position" =
      some (natAtom scannerBefore.wordPosition) :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-scan", .var "scope-owner", .var "proof-owner"]
      [.symbol "mm-compressed-scan", context.scopeOwner, context.proofOwner]
      [.expression [.symbol consTag, natAtom 90, .var "remaining-bytes"],
        .symbol "mm-compressed-just-completed-step", listAtom natAtom []]
      [listAtom natAtom (scannerBefore.remainingBytes.map UInt8.toNat),
        scannerBefore.phase.atom,
        listAtom natAtom scannerBefore.phase.reversePrefix]
      s1 s2 "word-position" (natAtom scannerBefore.wordPosition) (by rfl)
      scannerListMatched
  have remainingAt2 : s2.lookup "remaining-bytes" =
      some (listAtom natAtom (scannerAfter.remainingBytes.map UInt8.toNat)) := by
    have decoded := saveScan_match_remaining_lookup s1 s2 context scannerBefore
      (by simpa only [Conformance.cmatchAtom_eq_matchAtom] using m2)
    have tails : scannerBefore.remainingBytes.tail =
        scannerAfter.remainingBytes := by
      rw [receipt.consumes_head]
      rfl
    simpa [tails] using decoded
  obtain ⟨a3Member, m3⟩ := save_cmatchAtom_filterMap_witness f3
  have a3Eq := saveMachine_candidate_eq represented authority.directive
    (canonicalPassiveRows_machine_free context before ledger) a3Member m3
  subst a3
  rw [Conformance.cmatchAtom_eq_matchAtom] at m3
  have machineListMatched :
      matchAtom.matchAtomList s2
          [.symbol "mm-compressed-machine", .var "scope-owner",
            .var "proof-owner", .var "heap-next", .var "node-next",
            .var "stack-position"]
          [.symbol "mm-compressed-machine", context.scopeOwner,
            context.proofOwner,
            (CompressedIndexCode.ofNat before.heap.length).atom,
            (CompressedIndexCode.ofNat before.nodes.length).atom,
            (CompressedIndexCode.ofNat before.stack.length).atom] = some s3 := by
    simpa only [saveMachineTemplate, machineRow, matchAtom] using m3
  have nodeAt3 : s3.lookup "node-next" =
      some (CompressedIndexCode.ofNat before.nodes.length).atom :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner",
        .var "proof-owner", .var "heap-next"]
      [.symbol "mm-compressed-machine", context.scopeOwner,
        context.proofOwner,
        (CompressedIndexCode.ofNat before.heap.length).atom]
      [.var "stack-position"]
      [(CompressedIndexCode.ofNat before.stack.length).atom]
      s2 s3 "node-next" (CompressedIndexCode.ofNat before.nodes.length).atom
      (by rfl) machineListMatched
  have heapAt3 : s3.lookup "heap-next" =
      some (CompressedIndexCode.ofNat before.heap.length).atom :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner",
        .var "proof-owner"]
      [.symbol "mm-compressed-machine", context.scopeOwner,
        context.proofOwner]
      [.var "node-next", .var "stack-position"]
      [(CompressedIndexCode.ofNat before.nodes.length).atom,
        (CompressedIndexCode.ofNat before.stack.length).atom]
      s2 s3 "heap-next" (CompressedIndexCode.ofNat before.heap.length).atom
      (by rfl) machineListMatched
  have stackAt3 : s3.lookup "stack-position" =
      some (CompressedIndexCode.ofNat before.stack.length).atom :=
    save_matchAtomList_variable_lookup
      [.symbol "mm-compressed-machine", .var "scope-owner",
        .var "proof-owner", .var "heap-next", .var "node-next"]
      [.symbol "mm-compressed-machine", context.scopeOwner,
        context.proofOwner,
        (CompressedIndexCode.ofNat before.heap.length).atom,
        (CompressedIndexCode.ofNat before.nodes.length).atom]
      [] [] s2 s3 "stack-position"
      (CompressedIndexCode.ofNat before.stack.length).atom (by rfl)
      machineListMatched
  obtain ⟨_a4Member, m4⟩ := save_cmatchAtom_filterMap_witness f4
  obtain ⟨_a5Member, m5⟩ := save_cmatchAtom_filterMap_witness f5
  obtain ⟨_a6Member, m6⟩ := save_cmatchAtom_filterMap_witness f6
  obtain ⟨_a7Member, m7⟩ := save_cmatchAtom_filterMap_witness f7
  obtain ⟨_a8Member, m8⟩ := save_cmatchAtom_filterMap_witness f8
  obtain ⟨_a9Member, m9⟩ := save_cmatchAtom_filterMap_witness f9
  obtain ⟨_a10Member, m10⟩ := save_cmatchAtom_filterMap_witness f10
  obtain ⟨_a11Member, m11⟩ := save_cmatchAtom_filterMap_witness f11
  obtain ⟨_a12Member, m12⟩ := save_cmatchAtom_filterMap_witness f12
  obtain ⟨_a13Member, m13⟩ := save_cmatchAtom_filterMap_witness f13
  rw [Conformance.cmatchAtom_eq_matchAtom] at m4
  rw [Conformance.cmatchAtom_eq_matchAtom] at m5
  rw [Conformance.cmatchAtom_eq_matchAtom] at m6
  rw [Conformance.cmatchAtom_eq_matchAtom] at m7
  rw [Conformance.cmatchAtom_eq_matchAtom] at m8
  rw [Conformance.cmatchAtom_eq_matchAtom] at m9
  rw [Conformance.cmatchAtom_eq_matchAtom] at m10
  rw [Conformance.cmatchAtom_eq_matchAtom] at m11
  rw [Conformance.cmatchAtom_eq_matchAtom] at m12
  rw [Conformance.cmatchAtom_eq_matchAtom] at m13
  have extends3to13 : s13.lookupExtends s3 := by
    intro name value lookup
    exact (matchAtom_lookupExtends m13) _ _
      ((matchAtom_lookupExtends m12) _ _
        ((matchAtom_lookupExtends m11) _ _
          ((matchAtom_lookupExtends m10) _ _
            ((matchAtom_lookupExtends m9) _ _
              ((matchAtom_lookupExtends m8) _ _
                ((matchAtom_lookupExtends m7) _ _
                  ((matchAtom_lookupExtends m6) _ _
                    ((matchAtom_lookupExtends m5) _ _
                      ((matchAtom_lookupExtends m4) _ _ lookup)))))))))
  have extends2to13 : s13.lookupExtends s2 := by
    intro name value lookup
    exact extends3to13 name value
      ((matchAtom_lookupExtends m3) name value lookup)
  have scopeFinal := extends2to13 _ _ scopeAt2
  have proofFinal := extends2to13 _ _ proofAt2
  have wordFinal := extends2to13 _ _ wordAt2
  have remainingFinal := extends2to13 _ _ remainingAt2
  have nodeFinal := extends3to13 _ _ nodeAt3
  have heapFinal := extends3to13 _ _ heapAt3
  have stackFinal := extends3to13 _ _ stackAt3
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  have finalEq : substitution = s13 := finished.1
  subst substitution
  have nextFinal := saveMatcherRow_next_heap_position_exact represented authority
    (substitution := s13) originalRowMember
  refine ⟨?_, ?_, proofFinal, heapFinal⟩
  · cases step
    simp [afterSaveMachineTemplate, machineRow, instantiateTemplateAtom?,
      templateCovered, templatesCovered, applySubst,
      applySubst.applySubstList, scopeFinal, proofFinal, nextFinal, nodeFinal,
      stackFinal]
  · have wordEqual : scannerAfter.wordPosition = scannerBefore.wordPosition :=
      receipt.word_position_eq
    have phaseEqual : scannerAfter.phase = .between := receipt.phase_after
    simp [afterSaveScanTemplate, scannerRow, instantiateTemplateAtom?,
      templateCovered, templatesCovered, applySubst,
      applySubst.applySubstList, scopeFinal, proofFinal, wordFinal,
      remainingFinal, wordEqual, phaseEqual, ScannerPhase.atom,
      ScannerPhase.reversePrefix, listAtom, nilTag]

/-- Every complete save matcher reconstructs the exact source stack-top
occurrence.  The matched compact stack and node rows are inverted through the
source-derived tables; neither node identity, formula, nor occurrence is
accepted from a target-side witness. -/
theorem saveMatcherRow_saved_item_bindings_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (authority : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    substitution.lookup "node-id" = some item.identity ∧
      substitution.lookup "node-formula" = some item.value.formula ∧
      substitution.lookup "node-occurrence" =
        some item.value.sourceOccurrence ∧
      substitution.lookup "heap-next" =
        some (CompressedIndexCode.ofNat before.heap.length).atom := by
  dsimp only
  have originalRowMember := rowMember
  unfold saveMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubst, consumed⟩, matched, substEq⟩ := rowMember
  change matchedSubst = substitution at substEq
  subst matchedSubst
  rw [compressedSaveDirective_input_exact] at matched
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern] at matched
  unfold savePatterns at matched
  simp only [Conformance.Computable.cmatchPattern.go,
    List.mem_flatMap] at matched
  obtain ⟨⟨s1, a1⟩, f1, r1⟩ := matched
  obtain ⟨⟨s2, a2⟩, f2, r2⟩ := r1
  obtain ⟨⟨s3, a3⟩, f3, r3⟩ := r2
  obtain ⟨⟨s4, a4⟩, f4, r4⟩ := r3
  obtain ⟨⟨s5, a5⟩, f5, r5⟩ := r4
  obtain ⟨⟨s6, a6⟩, f6, r6⟩ := r5
  obtain ⟨⟨s7, a7⟩, f7, r7⟩ := r6
  obtain ⟨⟨s8, a8⟩, f8, r8⟩ := r7
  obtain ⟨⟨s9, a9⟩, f9, r9⟩ := r8
  obtain ⟨⟨s10, a10⟩, f10, r10⟩ := r9
  obtain ⟨⟨s11, a11⟩, f11, r11⟩ := r10
  obtain ⟨⟨s12, a12⟩, f12, r12⟩ := r11
  obtain ⟨⟨s13, a13⟩, f13, finished⟩ := r12
  obtain ⟨_a1Member, m1⟩ := save_cmatchAtom_filterMap_witness f1
  obtain ⟨_a2Member, m2⟩ := save_cmatchAtom_filterMap_witness f2
  obtain ⟨_a3Member, m3⟩ := save_cmatchAtom_filterMap_witness f3
  obtain ⟨_a4Member, m4⟩ := save_cmatchAtom_filterMap_witness f4
  obtain ⟨a5Member, m5⟩ := save_cmatchAtom_filterMap_witness f5
  obtain ⟨a6Member, m6⟩ := save_cmatchAtom_filterMap_witness f6
  obtain ⟨_a7Member, m7⟩ := save_cmatchAtom_filterMap_witness f7
  obtain ⟨_a8Member, m8⟩ := save_cmatchAtom_filterMap_witness f8
  obtain ⟨_a9Member, m9⟩ := save_cmatchAtom_filterMap_witness f9
  obtain ⟨_a10Member, m10⟩ := save_cmatchAtom_filterMap_witness f10
  obtain ⟨_a11Member, m11⟩ := save_cmatchAtom_filterMap_witness f11
  obtain ⟨_a12Member, m12⟩ := save_cmatchAtom_filterMap_witness f12
  obtain ⟨_a13Member, m13⟩ := save_cmatchAtom_filterMap_witness f13
  have cm5 := m5
  have cm6 := m6
  rw [Conformance.cmatchAtom_eq_matchAtom] at m6 m7 m8 m9 m10 m11 m12 m13
  have extends6to13 : s13.lookupExtends s6 := by
    intro name value lookup
    exact (matchAtom_lookupExtends m13) _ _
      ((matchAtom_lookupExtends m12) _ _
        ((matchAtom_lookupExtends m11) _ _
          ((matchAtom_lookupExtends m10) _ _
            ((matchAtom_lookupExtends m9) _ _
              ((matchAtom_lookupExtends m8) _ _
                ((matchAtom_lookupExtends m7) _ _ lookup))))))
  have extends5to13 : s13.lookupExtends s5 := by
    intro name value lookup
    exact extends6to13 name value ((matchAtom_lookupExtends m6) _ _ lookup)
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  have finalEq : substitution = s13 := finished.1
  subst substitution
  have controls := saveMatcherRow_successor_controls_exact receipt step
    represented authority.heapFrontier originalRowMember
  have proofOwnerFinal := controls.2.2.1
  have heapFinal := controls.2.2.2
  have stackTopFinal := saveMatcherRow_stack_top_exact represented authority
    originalRowMember
  obtain ⟨matchedIdentity, stackShape, identityFinal⟩ :=
    saveStackCell_match_decodes context
      (CompressedIndexCode.ofNat (before.stack.length - 1)).atom
      extends5to13 proofOwnerFinal stackTopFinal cm5
  have stackSource := represented_saveStackCell_mem_sourceStackRows represented
    authority.directive a5Member stackShape
  let stackItem : ProofOccurrence :=
    ⟨matchedIdentity,
      ⟨.symbol "mm-save-stack-formula", .symbol "mm-save-stack-occurrence"⟩⟩
  have stackShape' : a5 = compressedStackRow context.proofOwner
      (before.stack.length - 1) stackItem := by
    simpa [compressedStackRow, stackItem] using stackShape
  have stackSourceFrom : compressedStackRow context.proofOwner
      (before.stack.length - 1) stackItem ∈
        sourceStackRowsFrom context.proofOwner before ledger 0 before.stack := by
    rw [← stackShape']
    simpa [sourceStackRows] using stackSource
  obtain ⟨stackIndex, foundNodeId, foundNode, foundOccurrence,
      stackLookup, foundNodeLookup, foundOccurrenceLookup, positionExact,
      identityExact⟩ :=
    compressedStackRow_mem_sourceStackRowsFrom_inverts context.proofOwner before
      ledger 0 before.stack (before.stack.length - 1) stackItem stackSourceFrom
  have stackIndexExact : stackIndex = before.stack.length - 1 := by
    omega
  subst stackIndex
  have topLookup : before.stack[before.stack.length - 1]? = some nodeId := by
    simpa only [List.getLast?_eq_getElem?] using stackTop
  have foundNodeIdExact : foundNodeId = nodeId :=
    Option.some.inj (stackLookup.symm.trans topLookup)
  subst foundNodeId
  have foundNodeExact : foundNode = node :=
    Option.some.inj (foundNodeLookup.symm.trans nodeLookup)
  subst foundNode
  have foundOccurrenceExact : foundOccurrence = sourceOccurrence :=
    Option.some.inj (foundOccurrenceLookup.symm.trans occurrenceLookup)
  subst foundOccurrence
  have matchedIdentityExact : matchedIdentity =
      (displayedProofOccurrence nodeId node sourceOccurrence).identity := by
    simpa [stackItem] using identityExact
  obtain ⟨matchedFormula, matchedOccurrence, nodeShape, formulaFinal,
      occurrenceFinal⟩ :=
    saveNode_match_decodes context matchedIdentity extends6to13
      proofOwnerFinal identityFinal cm6
  let matchedItem : ProofOccurrence :=
    ⟨matchedIdentity, ⟨matchedFormula, matchedOccurrence⟩⟩
  have nodeShape' : a6 =
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner matchedItem := by
    simpa [matchedItem] using nodeShape
  have nodeSource := represented_saveNode_mem_sourceNodeRows represented
    authority.directive a6Member nodeShape'
  have nodeSourceFrom :
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner matchedItem ∈
        sourceNodeRowsFrom context.proofOwner 0 before.nodes
          ledger.occurrences := by
    rw [nodeShape'] at nodeSource
    simpa [sourceNodeRows] using nodeSource
  obtain ⟨nodeIndex, foundNode, foundOccurrence, foundNodeLookup,
      foundOccurrenceLookup, matchedItemExact⟩ :=
    nodeRow_mem_sourceNodeRowsFrom_inverts context.proofOwner 0 before.nodes
      ledger.occurrences matchedItem nodeSourceFrom
  have identityAtIndex := congrArg
    (fun item : ProofOccurrence => item.identity) matchedItemExact
  have nodeIndexExact : nodeIndex = nodeId := by
    change matchedIdentity =
      (displayedProofOccurrence (0 + nodeIndex) foundNode
        foundOccurrence).identity at identityAtIndex
    rw [matchedIdentityExact] at identityAtIndex
    apply MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective
    apply MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective
    simpa [matchedItem, displayedProofOccurrence] using identityAtIndex.symm
  subst nodeIndex
  have foundNodeExact : foundNode = node :=
    Option.some.inj (foundNodeLookup.symm.trans nodeLookup)
  subst foundNode
  have foundOccurrenceExact : foundOccurrence = sourceOccurrence :=
    Option.some.inj (foundOccurrenceLookup.symm.trans occurrenceLookup)
  subst foundOccurrence
  have matchedFormulaExact : matchedFormula =
      (displayedProofOccurrence nodeId node sourceOccurrence).value.formula := by
    have exactValue := congrArg
      (fun item : ProofOccurrence => item.value.formula) matchedItemExact
    simpa [matchedItem] using exactValue
  have matchedOccurrenceExact : matchedOccurrence =
      (displayedProofOccurrence nodeId node sourceOccurrence).value.sourceOccurrence := by
    have exactValue := congrArg
      (fun item : ProofOccurrence => item.value.sourceOccurrence) matchedItemExact
    simpa [matchedItem] using exactValue
  rw [matchedIdentityExact] at identityFinal
  rw [matchedFormulaExact] at formulaFinal
  rw [matchedOccurrenceExact] at occurrenceFinal
  exact ⟨identityFinal, formulaFinal, occurrenceFinal, heapFinal⟩

/-- The two data-producing save sinks are exact for every successful matcher
row in a represented boundary.  This is the output-reflection counterpart of
the canonical positive matcher: no alternative stack or node occurrence can
be published by another satisfying assignment. -/
theorem saveMatcherRow_saved_outputs_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (authority : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    instantiateTemplateAtom? substitution savedHeapTemplate =
        some (heapProofRow context.proofOwner before.heap.length item) ∧
      instantiateTemplateAtom? substitution saveReceiptTemplate =
        some (saveReceiptRow context.proofOwner before.heap.length item) := by
  dsimp only
  have bindings := saveMatcherRow_saved_item_bindings_exact receipt step
    stackTop nodeLookup occurrenceLookup represented authority rowMember
  have controls := saveMatcherRow_successor_controls_exact receipt step
    represented authority.heapFrontier rowMember
  have proofOwner := controls.2.2.1
  refine ⟨?_, ?_⟩
  · simp [savedHeapTemplate, heapProofRow, instantiateTemplateAtom?,
      templateCovered, templatesCovered, applySubst,
      applySubst.applySubstList, proofOwner, bindings.2.2.2, bindings.1]
  · simp [saveReceiptTemplate, saveReceiptRow, instantiateTemplateAtom?,
      templateCovered, templatesCovered, applySubst,
      applySubst.applySubstList, proofOwner, bindings.2.2.2, bindings.1,
      bindings.2.2.1]

/-- Every dynamic atom introduced by the complete save sink batch is one of
the four source-determined successor rows.  The self-rule and six executable
continuations are admitted code with non-dynamic heads; remove sinks introduce
nothing. -/
theorem save_added_dynamic_atom_exact
    (presentation : CompressedExecutablePresentation)
    (runtimeAuthority : SaveRuntimeRuleAuthority presentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (frontierAuthority : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    {atom : Atom}
    (added : ReflectiveAddedAtom (saveMatcherRows space)
      compressedSaveDirective.rule.tmpl.sinks atom)
    (dynamic : isDynamicRow atom = true) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    atom = machineRow context after ∨
      atom = scannerRow context scannerAfter ∨
      atom = heapProofRow context.proofOwner before.heap.length item ∨
      atom = saveReceiptRow context.proofOwner before.heap.length item := by
  dsimp only
  rcases added with ⟨sink, sinkMember, authored, sinkEq, substitution,
    rowMember, instantiated⟩
  have controls := saveMatcherRow_successor_controls_exact receipt step
    represented frontierAuthority.heapFrontier rowMember
  have outputs := saveMatcherRow_saved_outputs_exact receipt step stackTop
    nodeLookup occurrenceLookup represented frontierAuthority rowMember
  have runtime := saveMatcherRow_runtime_rules_exact_of_resolved presentation
    represented frontierAuthority.directive capabilities
    runtimeAuthority.rules.prefixRule runtimeAuthority.rules.terminalRule
    runtimeAuthority.rules.proofRule runtimeAuthority.rules.invalidByteRule
    runtimeAuthority.rules.questionRule
    runtimeAuthority.rules.questionOpenFaultRule
    runtimeAuthority.prefixResolved runtimeAuthority.terminalResolved
    runtimeAuthority.proofResolved runtimeAuthority.invalidByteResolved
    runtimeAuthority.questionResolved runtimeAuthority.questionOpenFaultResolved
    rowMember
  rw [compressedSaveDirective_sinks_exact] at sinkMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    unfold instantiateTemplateAtom? at instantiated
    split at instantiated
    next covered =>
      have atomExact := Option.some.inj instantiated
      subst atom
      simp [applySubst, applySubst.applySubstList,
        isDynamicRow, dynamicRowHeads] at dynamic
    next => simp at instantiated
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-prefix-rule" runtimeAuthority.rules.prefixRule).2 runtime.1
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.prefixStatic] at dynamic
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-terminal-rule" runtimeAuthority.rules.terminalRule).2
          runtime.2.1
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.terminalStatic] at dynamic
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-proof-rule" runtimeAuthority.rules.proofRule).2 runtime.2.2.1
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.proofStatic] at dynamic
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-invalid-byte-rule"
        runtimeAuthority.rules.invalidByteRule).2 runtime.2.2.2.1
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.invalidByteStatic] at dynamic
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-question-rule" runtimeAuthority.rules.questionRule).2
          runtime.2.2.2.2.1
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.questionStatic] at dynamic
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    have exactInstantiation :=
      (instantiateTemplateAtom?_var_eq_some_iff substitution
        "compressed-question-open-fault-rule"
        runtimeAuthority.rules.questionOpenFaultRule).2 runtime.2.2.2.2.2
    have atomExact := Option.some.inj (instantiated.symm.trans exactInstantiation)
    subst atom
    simp [runtimeAuthority.questionOpenFaultStatic] at dynamic
  · rw [h] at sinkEq
    cases sinkEq
  · rw [h] at sinkEq
    cases sinkEq
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    exact Or.inl (Option.some.inj (instantiated.symm.trans controls.1))
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    exact Or.inr (Or.inl
      (Option.some.inj (instantiated.symm.trans controls.2.1)))
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    exact Or.inr (Or.inr (Or.inl
      (Option.some.inj (instantiated.symm.trans outputs.1))))
  · rw [h] at sinkEq
    injection sinkEq with authoredEq
    subst authored
    exact Or.inr (Or.inr (Or.inr
      (Option.some.inj (instantiated.symm.trans outputs.2))))

private theorem instantiate_afterSaveMachineTemplate_ne_old_of_next
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (substitution : Subst)
    (nextExact : substitution.lookup "next-heap-position" =
      some (CompressedIndexCode.ofNat (before.heap.length + 1)).atom) :
    instantiateTemplateAtom? substitution afterSaveMachineTemplate ≠
      some (machineRow context before) := by
  have frontierDifferent :
      (CompressedIndexCode.ofNat (before.heap.length + 1)).atom ≠
        (CompressedIndexCode.ofNat before.heap.length).atom := by
    intro equal
    have decoded := congrArg CompressedIndexCode.decodeCompressedIndexAtom equal
    simp only [CompressedIndexCode.decodeCompressedIndexAtom_ofNat_atom,
      Option.some.injEq] at decoded
    omega
  have nextDifferent :
      (CompressedIndexCode.ofNat before.heap.length).next.atom ≠
        (CompressedIndexCode.ofNat before.heap.length).atom := by
    simpa only [MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_succ] using
      frontierDifferent
  unfold instantiateTemplateAtom?
  split
  · simp [afterSaveMachineTemplate, machineRow, applySubst,
      applySubst.applySubstList, nextExact, nextDifferent]
  · simp

/-- Authorized matcher rows cannot recreate the old machine frontier. -/
theorem saveMatcherRow_after_machine_fresh
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    {substitution : Subst} (rowMember : substitution ∈ saveMatcherRows space) :
    instantiateTemplateAtom? substitution afterSaveMachineTemplate ≠
      some (machineRow context before) := by
  exact instantiate_afterSaveMachineTemplate_ne_old_of_next context before
    substitution
      (saveMatcherRow_next_heap_position_exact represented authority rowMember)

theorem instantiate_saveScanTemplate_ne_of_avoids
    (substitution : Subst) (row : Atom)
    (avoids : avoidsSaveControlHeads row = true) :
    instantiateTemplateAtom? substitution saveScanTemplate ≠ some row := by
  cases row with
  | symbol value => simp [avoidsSaveControlHeads] at avoids
  | var name => simp [avoidsSaveControlHeads] at avoids
  | grounded value => simp [avoidsSaveControlHeads] at avoids
  | expression atoms =>
      cases atoms with
      | nil => simp [avoidsSaveControlHeads] at avoids
      | cons head tail =>
          cases head with
          | symbol candidateHead =>
              simp only [avoidsSaveControlHeads, Bool.and_eq_true,
                bne_iff_ne] at avoids
              exact instantiateTemplateAtom?_expression_symbol_head_ne
                substitution "mm-compressed-scan" candidateHead
                [Atom.var "scope-owner", Atom.var "proof-owner",
                  Atom.var "word-position",
                  Atom.expression
                    [Atom.symbol consTag, natAtom 90,
                      Atom.var "remaining-bytes"],
                  Atom.symbol "mm-compressed-just-completed-step",
                  listAtom natAtom []]
                tail avoids.1.symm
          | var name => simp [avoidsSaveControlHeads] at avoids
          | grounded value => simp [avoidsSaveControlHeads] at avoids
          | expression nested => simp [avoidsSaveControlHeads] at avoids

theorem instantiate_saveMachineTemplate_ne_of_avoids
    (substitution : Subst) (row : Atom)
    (avoids : avoidsSaveControlHeads row = true) :
    instantiateTemplateAtom? substitution saveMachineTemplate ≠ some row := by
  cases row with
  | symbol value => simp [avoidsSaveControlHeads] at avoids
  | var name => simp [avoidsSaveControlHeads] at avoids
  | grounded value => simp [avoidsSaveControlHeads] at avoids
  | expression atoms =>
      cases atoms with
      | nil => simp [avoidsSaveControlHeads] at avoids
      | cons head tail =>
          cases head with
          | symbol candidateHead =>
              simp only [avoidsSaveControlHeads, Bool.and_eq_true,
                bne_iff_ne] at avoids
              exact instantiateTemplateAtom?_expression_symbol_head_ne
                substitution "mm-compressed-machine" candidateHead
                [Atom.var "scope-owner", Atom.var "proof-owner",
                  Atom.var "heap-next", Atom.var "node-next",
                  Atom.var "stack-position"]
                tail avoids.2.symm
          | var name => simp [avoidsSaveControlHeads] at avoids
          | grounded value => simp [avoidsSaveControlHeads] at avoids
          | expression nested => simp [avoidsSaveControlHeads] at avoids

/-- Every passive row in the represented source boundary survives the complete
save sink batch.  The theorem quantifies over all actual matcher rows. -/
theorem canonicalPassiveRow_mem_save_fire
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scanner
      staticFrame space) (row : Atom)
    (member : row ∈ canonicalPassiveRows context before ledger) :
    row ∈ cFireReflectiveSourceExecFact space compressedSaveDirective := by
  have avoids := canonicalPassiveRows_avoid_save_controls context before ledger
    row member
  have present : row ∈ saveLive space := by
    apply mem_saveLive_of_mem_of_inert
    · exact extractSupportedSourceExecFact_eq_none_of_dynamic row
        (canonicalPassiveRows_all_dynamic context before ledger row member)
    · apply (represented.exact_rows row).2
      exact List.mem_append_left _
        (List.mem_append_right _ member)
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedSaveDirective_sinks_exact]
  apply mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
      (saveMatcherRows space) (present := present)
  intro sink sinkMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  all_goals first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨_, rfl, fun substitution _ =>
        instantiate_saveScanTemplate_ne_of_avoids substitution row avoids⟩
    | exact Or.inr ⟨_, rfl, fun substitution _ =>
        instantiate_saveMachineTemplate_ne_of_avoids substitution row avoids⟩

private theorem instantiate_afterSaveScanTemplate_ne_completed_scanner
    (context : BoundaryContext) (scanner : ScannerBoundary)
    (completed : scanner.phase = .completed) (substitution : Subst) :
    instantiateTemplateAtom? substitution afterSaveScanTemplate ≠
      some (scannerRow context scanner) := by
  rcases context with ⟨scopeOwner, proofOwner, initialHeapLength⟩
  rcases scanner with
    ⟨wordPosition, bytePosition, remainingBytes, phase⟩
  change phase = .completed at completed
  subst phase
  simp [afterSaveScanTemplate, scannerRow, instantiateTemplateAtom?,
    templateCovered, templatesCovered, applySubst,
    applySubst.applySubstList, listAtom, natAtom, ScannerPhase.atom,
    ScannerPhase.reversePrefix, Subst.lookup]

/-- The concrete save transition consumes the completed-step scanner control.
No matcher row can recreate it: the only scanner output has the authored
between-step phase. -/
theorem save_fire_consumes_old_scanner
    {context : BoundaryContext} {scannerBefore : ScannerBoundary}
    (completed : scannerBefore.phase = .completed) (space : List Atom)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item space) :
    scannerRow context scannerBefore ∉
      cFireReflectiveSourceExecFact space compressedSaveDirective := by
  rcases matched with
    ⟨substitution, rowMember, scanBefore, _machineBefore, _machineAfter,
      _scanAfter, _heap, _receipt⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedSaveDirective_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    (saveMatcherRows space) (saveLive space)
    [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-proof-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule")]
    saveScanTemplate (scannerRow context scannerBefore)
    [.remove saveMachineTemplate, .add afterSaveMachineTemplate,
     .add afterSaveScanTemplate, .add savedHeapTemplate,
     .add saveReceiptTemplate]
    substitution rowMember scanBefore
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨saveMachineTemplate, rfl⟩
  · exact Or.inr ⟨afterSaveMachineTemplate, rfl, fun later _ => by
      unfold afterSaveMachineTemplate scannerRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨afterSaveScanTemplate, rfl, fun later _ =>
      instantiate_afterSaveScanTemplate_ne_completed_scanner context
        scannerBefore completed later⟩
  · exact Or.inr ⟨savedHeapTemplate, rfl, fun later _ => by
      unfold savedHeapTemplate scannerRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨saveReceiptTemplate, rfl, fun later _ => by
      unfold saveReceiptTemplate scannerRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩

/-- Factored removal lemma: heap-frontier freshness is supplied separately so
the sink-batch argument remains independent of matcher inversion. -/
theorem save_fire_consumes_old_machine_of_fresh
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    (space : List Atom)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item space)
    (fresh : ∀ substitution ∈ saveMatcherRows space,
      instantiateTemplateAtom? substitution afterSaveMachineTemplate ≠
        some (machineRow context before)) :
    machineRow context before ∉
      cFireReflectiveSourceExecFact space compressedSaveDirective := by
  rcases matched with
    ⟨substitution, rowMember, _scanBefore, machineBefore, _machineAfter,
      _scanAfter, _heap, _receipt⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedSaveDirective_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    (saveMatcherRows space) (saveLive space)
    [.add saveSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-proof-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule"),
     .remove saveScanTemplate]
    saveMachineTemplate (machineRow context before)
    [.add afterSaveMachineTemplate, .add afterSaveScanTemplate,
     .add savedHeapTemplate, .add saveReceiptTemplate]
    substitution rowMember machineBefore
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inr ⟨afterSaveMachineTemplate, rfl, fresh⟩
  · exact Or.inr ⟨afterSaveScanTemplate, rfl, fun later _ => by
      unfold afterSaveScanTemplate machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨savedHeapTemplate, rfl, fun later _ => by
      unfold savedHeapTemplate machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨saveReceiptTemplate, rfl, fun later _ => by
      unfold saveReceiptTemplate machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩

/-- Source-relative static authority discharges the freshness premise, so a
represented save firing unconditionally consumes its old machine control. -/
theorem save_fire_consumes_old_machine
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item space) :
    machineRow context before ∉
      cFireReflectiveSourceExecFact space compressedSaveDirective := by
  exact save_fire_consumes_old_machine_of_fresh space matched
    (fun substitution rowMember =>
      saveMatcherRow_after_machine_fresh represented authority rowMember)

/-- A represented source-authorized save consumes both obsolete controls. -/
theorem save_fire_consumes_old_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary} {item : ProofOccurrence}
    {staticFrame space : List Atom}
    (completed : scannerBefore.phase = .completed)
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (authority : SaveHeapFrontierAuthority context before staticFrame)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item space) :
    machineRow context before ∉
        cFireReflectiveSourceExecFact space compressedSaveDirective ∧
      scannerRow context scannerBefore ∉
        cFireReflectiveSourceExecFact space compressedSaveDirective := by
  exact ⟨save_fire_consumes_old_machine represented authority matched,
    save_fire_consumes_old_scanner completed space matched⟩

theorem save_fire_adds_source_rows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary) (item : ProofOccurrence)
    (space : List Atom)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      item space) :
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    machineRow context after ∈ result ∧
      scannerRow context scannerAfter ∈ result ∧
      heapProofRow context.proofOwner before.heap.length item ∈ result ∧
      saveReceiptRow context.proofOwner before.heap.length item ∈ result := by
  dsimp only
  rcases matched with
    ⟨substitution, rowMember, _scanBefore, _machineBefore, machine, scanner,
      heap, receipt⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [compressedSaveDirective_sinks_exact]
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (saveMatcherRows space) (saveLive space)
      [.add
        (.expression
          [.symbol "exec",
            .expression [.symbol "09", .symbol "mm-compressed-save"],
            .var "save-input", .var "save-output"]),
       .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule"),
       .remove saveScanTemplate, .remove saveMachineTemplate]
      afterSaveMachineTemplate (machineRow context after)
      [.add afterSaveScanTemplate, .add savedHeapTemplate,
        .add saveReceiptTemplate]
      substitution rowMember machine (by
        intro sink member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · constructor
    · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
        (saveMatcherRows space) (saveLive space)
        [.add
          (.expression
            [.symbol "exec",
              .expression [.symbol "09", .symbol "mm-compressed-save"],
              .var "save-input", .var "save-output"]),
         .add (.var "compressed-prefix-rule"),
         .add (.var "compressed-terminal-rule"),
         .add (.var "compressed-proof-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .remove saveScanTemplate, .remove saveMachineTemplate,
         .add afterSaveMachineTemplate]
        afterSaveScanTemplate (scannerRow context scannerAfter)
        [.add savedHeapTemplate, .add saveReceiptTemplate]
        substitution rowMember scanner (by
          intro sink member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact ⟨_, rfl⟩)
    · constructor
      · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
          (saveMatcherRows space) (saveLive space)
          [.add
            (.expression
              [.symbol "exec",
                .expression [.symbol "09", .symbol "mm-compressed-save"],
                .var "save-input", .var "save-output"]),
           .add (.var "compressed-prefix-rule"),
           .add (.var "compressed-terminal-rule"),
           .add (.var "compressed-proof-rule"),
           .add (.var "compressed-invalid-byte-rule"),
           .add (.var "compressed-question-rule"),
           .add (.var "compressed-question-open-fault-rule"),
           .remove saveScanTemplate, .remove saveMachineTemplate,
           .add afterSaveMachineTemplate, .add afterSaveScanTemplate]
          savedHeapTemplate
          (heapProofRow context.proofOwner before.heap.length item)
          [.add saveReceiptTemplate] substitution rowMember heap (by
            intro sink member
            simp only [List.mem_singleton] at member
            subst sink
            exact ⟨_, rfl⟩)
      · exact mem_cApplyReflectiveSinkBatch_append_add_of_row
          (saveMatcherRows space) (saveLive space)
          [.add
            (.expression
              [.symbol "exec",
                .expression [.symbol "09", .symbol "mm-compressed-save"],
                .var "save-input", .var "save-output"]),
           .add (.var "compressed-prefix-rule"),
           .add (.var "compressed-terminal-rule"),
           .add (.var "compressed-proof-rule"),
           .add (.var "compressed-invalid-byte-rule"),
           .add (.var "compressed-question-rule"),
           .add (.var "compressed-question-open-fault-rule"),
           .remove saveScanTemplate, .remove saveMachineTemplate,
           .add afterSaveMachineTemplate, .add afterSaveScanTemplate,
           .add savedHeapTemplate]
          saveReceiptTemplate
          (saveReceiptRow context.proofOwner before.heap.length item)
          substitution rowMember receipt

/-- Every row in the canonical semantic successor boundary is present after
the concrete save firing.  This strengthens four distinguished observations
to the complete source-derived dynamic display, while remaining independent
of the surrounding verifier presentation. -/
theorem save_fire_contains_canonical_successor_rows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence) space) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    ∀ row, row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ->
      row ∈ cFireReflectiveSourceExecFact space compressedSaveDirective := by
  dsimp only
  have added := save_fire_adds_source_rows context before after scannerBefore
    scannerAfter
    (displayedProofOccurrence nodeId node sourceOccurrence) space matched
  intro row member
  simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | passive
  · exact added.1
  · exact added.2.1
  · have delta := (canonicalPassiveRows_save_iff wellFormed ledger
      proofPosition step nodeId node sourceOccurrence stackTop nodeLookup
      occurrenceLookup row).1 passive
    rcases delta with old | rfl | rfl
    · exact canonicalPassiveRow_mem_save_fire represented row old
    · exact added.2.2.1
    · exact added.2.2.2

/-- Exact dynamic-state reflection for one source-derived save.  Membership
in the concrete result is equivalent to membership in the canonical semantic
successor display once verifier code is excluded by its static authority.
This closes both directions: every canonical row survives or is added, and no
other dynamic row can be introduced by a noncanonical matcher assignment. -/
theorem save_fire_dynamic_rows_iff_canonical_successor
    (presentation : CompressedExecutablePresentation)
    (runtimeAuthority : SaveRuntimeRuleAuthority presentation)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter byteOccurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {staticFrame space : List Atom}
    (represented : RepresentsRunningBoundary context before ledger scannerBefore
      staticFrame space)
    (frontierAuthority : SaveFrontierAuthority context before
      (before.stack.length - 1) staticFrame)
    (capabilities : CompressedExecutableCapabilities presentation staticFrame)
    (matched : ExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence) space)
    (row : Atom) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    row ∈ cFireReflectiveSourceExecFact space compressedSaveDirective ∧
        isDynamicRow row = true ↔
      row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter := by
  dsimp only
  constructor
  · rintro ⟨resultMember, dynamic⟩
    have oldAbsent := save_fire_consumes_old_controls receipt.phase_before
      represented frontierAuthority.heapFrontier matched
    have fired : row ∈ cApplyReflectiveTemplate (saveLive space)
        (saveMatcherRows space) compressedSaveDirective.rule.tmpl := by
      simpa [cFireReflectiveSourceExecFact, saveLive, saveMatcherRows] using
        resultMember
    have supported : ReflectiveSupportSetTemplate
        compressedSaveDirective.rule.tmpl := by
      intro sink sinkMember
      rw [compressedSaveDirective_sinks_exact] at sinkMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
      rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> trivial
    rcases mem_cApplyReflectiveTemplate_of_supportSet (saveLive space)
        (saveMatcherRows space) compressedSaveDirective.rule.tmpl supported
        fired with prior | added
    · have present : row ∈ space := by
        exact List.mem_of_mem_erase prior
      have representedRow := (represented.exact_rows row).1 present
      rcases List.mem_append.mp representedRow with sourceRow | staticRow
      · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at sourceRow
        rcases sourceRow with (rfl | rfl) | passive
        · exact False.elim (oldAbsent.1 resultMember)
        · exact False.elim (oldAbsent.2 resultMember)
        · have passiveAfter :=
            (canonicalPassiveRows_save_iff represented.source_wellFormed ledger
              proofPosition step nodeId node sourceOccurrence stackTop
              nodeLookup occurrenceLookup row).2 (Or.inl passive)
          simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false]
          exact Or.inr passiveAfter
      · have clean := represented.staticFrame_clean row staticRow
        rw [dynamic] at clean
        contradiction
    · have exactAdded := save_added_dynamic_atom_exact presentation
        runtimeAuthority receipt step stackTop nodeLookup occurrenceLookup
        represented frontierAuthority capabilities added dynamic
      rcases exactAdded with rfl | rfl | heapExact | receiptExact
      · simp [canonicalBoundaryRows]
      · simp [canonicalBoundaryRows]
      · have passiveAfter :=
          (canonicalPassiveRows_save_iff represented.source_wellFormed ledger
            proofPosition step nodeId node sourceOccurrence stackTop nodeLookup
            occurrenceLookup _).2 (Or.inr (Or.inl heapExact))
        simp [canonicalBoundaryRows, passiveAfter]
      · have passiveAfter :=
          (canonicalPassiveRows_save_iff represented.source_wellFormed ledger
            proofPosition step nodeId node sourceOccurrence stackTop nodeLookup
            occurrenceLookup _).2 (Or.inr (Or.inr receiptExact))
        simp [canonicalBoundaryRows, passiveAfter]
  · intro canonical
    exact ⟨save_fire_contains_canonical_successor_rows
        represented.source_wellFormed ledger proofPosition step stackTop
          nodeLookup occurrenceLookup represented matched row canonical,
      canonicalBoundaryRows_all_dynamic context after
        (ActionStep.occurrenceLedger step proofPosition ledger) scannerAfter
        row canonical⟩

/-! ## Continuous scheduled square -/

structure ContinuousSaveCommutingSquare
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence)
    (sourceActionStep : ActionStep before .save after)
    (savedNodeId : Nat) (savedNode : ProofNode source target)
    (sourceOccurrence : Atom)
    (space result : List Atom) : Prop where
  sourceScannerStep : SourceStep (.request occurrence scannerBefore.phase)
    (.outcome occurrence (.decoded [.save] scannerAfter.phase))
  sourceAfterWellFormed : SourceBoundaryWellFormed context after
  ledgerUnchanged :
    (ActionStep.occurrenceLedger sourceActionStep proofPosition ledger).occurrences =
      ledger.occurrences
  stackTop : before.stack.getLast? = some savedNodeId
  nodeLookup : before.nodes[savedNodeId]? = some savedNode
  occurrenceLookup : ledger.occurrences[savedNodeId]? = some sourceOccurrence
  nodesUnchanged : after.nodes = before.nodes
  heapExact : after.heap = before.heap ++ [.proof savedNodeId]
  savesExact : after.saves = before.saves ++ [savedNodeId]
  concreteStep :
    cReflectiveSourceWorkQueueStep .leaveInert space = some result
  executableNative :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies space
      (reflectiveNativeListExactTargetNativeType .leaveInert result).pred
  supportNative :
    Nonempty
      (ReflectiveSupportNativeTypeTrace .leaveInert space.toFinset
        result.toFinset)
  machineExact : machineRow context after ∈ result
  scannerExact : scannerRow context scannerAfter ∈ result
  heapRowExact :
    heapProofRow context.proofOwner before.heap.length
      (displayedProofOccurrence savedNodeId savedNode sourceOccurrence) ∈ result
  receiptExact :
    saveReceiptRow context.proofOwner before.heap.length
      (displayedProofOccurrence savedNodeId savedNode sourceOccurrence) ∈ result

/-- General continuous `Z` square.  The saved occurrence is reconstructed
from the source action and occurrence ledger; the concrete frame supplies only
the matcher realization of those source-determined rows. -/
def source_save_commutes_of_continuous_frame
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (wellFormed : SourceBoundaryWellFormed context before)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    (space staticFrame : List Atom)
    (frame : ∀ nodeId node sourceOccurrence,
      before.stack.getLast? = some nodeId →
      before.nodes[nodeId]? = some node →
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      ContinuousSaveRequestFrame context before after ledger scannerBefore
        scannerAfter staticFrame space
        (displayedProofOccurrence nodeId node sourceOccurrence)) :
    let result := cFireReflectiveSourceExecFact space compressedSaveDirective
    ∃ nodeId node sourceOccurrence,
      ContinuousSaveCommutingSquare context before after ledger proofPosition
        scannerBefore scannerAfter occurrence step nodeId node
        sourceOccurrence space result := by
  dsimp only
  obtain ⟨scannerStep, afterWellFormed, ledgerEqual,
      nodeId, node, stackTop, nodeLookup, nodesEqual, heapEqual, savesEqual⟩ :=
    source_decoded_save_action_preserves_boundary wellFormed ledger
      proofPosition receipt step
  have nodeBound := (List.getElem?_eq_some_iff.mp nodeLookup).1
  have occurrenceBound : nodeId < ledger.occurrences.length := by
    rw [ledger.aligned]
    exact nodeBound
  let sourceOccurrence := ledger.occurrences[nodeId]'occurrenceBound
  have occurrenceLookup :
      ledger.occurrences[nodeId]? = some sourceOccurrence := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨occurrenceBound, rfl⟩
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  have requestFrame := frame nodeId node sourceOccurrence stackTop nodeLookup
    occurrenceLookup
  let result := cFireReflectiveSourceExecFact space compressedSaveDirective
  have moved : cReflectiveSourceWorkQueueStep .leaveInert space = some result := by
    unfold cReflectiveSourceWorkQueueStep
    rw [requestFrame.supported]
    rfl
  have rows := save_fire_adds_source_rows context before after scannerBefore
    scannerAfter item space requestFrame.exactMatch
  let adequate : CReflectiveAdequateTrace .leaveInert 1 space result :=
    .step requestFrame.invariant moved (.refl)
  refine ⟨nodeId, node, sourceOccurrence, ?_⟩
  exact
    { sourceScannerStep := scannerStep
      sourceAfterWellFormed := afterWellFormed
      ledgerUnchanged := ledgerEqual
      stackTop := stackTop
      nodeLookup := nodeLookup
      occurrenceLookup := occurrenceLookup
      nodesUnchanged := nodesEqual
      heapExact := heapEqual
      savesExact := savesEqual
      concreteStep := moved
      executableNative :=
        (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
          .leaveInert space result).2 moved
      supportNative := ⟨adequate.toSupportNativeTypeTrace⟩
      machineExact := rows.1
      scannerExact := rows.2.1
      heapRowExact := rows.2.2.1
      receiptExact := rows.2.2.2 }

section AxiomAudit

#print axioms compressedSaveDirective_sinks_exact
#print axioms compressedSaveDirective_input_exact
#print axioms nodeRow_mem_sourceNodeRows
#print axioms compressedStackRow_mem_sourceStackRows
#print axioms compressedStackRow_mem_sourceStackRowsFrom_inverts
#print axioms nodeRow_mem_sourceNodeRowsFrom_inverts
#print axioms canonicalSaveMatchSpace_has_match
#print axioms canonicalSaveMatchSpace_exact_match
#print axioms canonicalSaveMatchSpaceFor_has_match
#print axioms canonicalSaveMatchSpaceFor_exact_match
#print axioms ExactSaveMatch.mono_read
#print axioms ContinuousSaveRequestFrame.of_canonical_match
#print axioms canonicalSaveStaticFrame_clean
#print axioms canonicalSaveStaticFrame_authority
#print axioms SaveStaticAuthority.heapFrontier
#print axioms SaveStaticAuthority.frontier
#print axioms forged_save_prefix_capture_rejected
#print axioms saveOwnedRuntimeRule_candidate_eq
#print axioms saveMatcherRow_runtime_rules_exact_of_resolved
#print axioms saveMatcherRow_runtime_rules_exact
#print axioms SaveStaticSupport.asForBase
#print axioms source_save_canonical_read_included_for
#print axioms source_save_canonical_read_included
#print axioms canonicalSaveBoundarySpace_represents
#print axioms source_save_canonical_space_exact_match
#print axioms ContinuousSaveRequestFrame.of_source_boundary
#print axioms assertionHeapRowsFrom_append_proof
#print axioms sourceSaveRowsFrom_append_singleton
#print axioms sourceSaveRowsFrom_congr
#print axioms sourceStackRowsFrom_congr
#print axioms canonicalPassiveRows_save_iff
#print axioms canonicalPassiveRows_avoid_save_controls
#print axioms saveMatcherRow_stack_top_exact
#print axioms saveMatcherRow_next_heap_position_exact
#print axioms saveMatcherRow_predecessor_controls_exact
#print axioms saveMatcherRow_successor_controls_exact
#print axioms saveMatcherRow_saved_item_bindings_exact
#print axioms saveMatcherRow_saved_outputs_exact
#print axioms save_added_dynamic_atom_exact
#print axioms saveMatcherRow_after_machine_fresh
#print axioms instantiate_saveScanTemplate_ne_of_avoids
#print axioms instantiate_saveMachineTemplate_ne_of_avoids
#print axioms canonicalPassiveRow_mem_save_fire
#print axioms save_fire_consumes_old_scanner
#print axioms save_fire_consumes_old_machine_of_fresh
#print axioms save_fire_consumes_old_machine
#print axioms save_fire_consumes_old_controls
#print axioms save_fire_adds_source_rows
#print axioms save_fire_contains_canonical_successor_rows
#print axioms save_fire_dynamic_rows_iff_canonical_successor
#print axioms source_save_commutes_of_continuous_frame

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
