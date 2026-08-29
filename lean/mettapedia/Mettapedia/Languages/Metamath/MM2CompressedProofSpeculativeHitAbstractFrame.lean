import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Symbolic frame for a generated speculative proof hit

This module separates the reusable commuting argument from the bounded hit
fixture.  It is parameterized by the owner, cursor, machine frontier, stack
position, semantic heap, and concrete live frame.  The exact matcher witness
is explicit: a downstream source-to-MM2 realization must derive it from its
canonical rows rather than assume that arbitrary target data is authorized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Target-owned context threaded through one direct proof lookup.  Natural
frontiers use the canonical compact-index encoding; source bytes remain
opaque atoms because the proof-hit rule only transports them. -/
structure DirectProofContext where
  scopeOwner : Atom
  proofOwner : Atom
  wordPosition : Atom
  remainingBytes : Atom
  index : Nat
  cursor : Nat
  heapNext : Nat
  nodeNext : Nat
  stackPosition : Nat
  nextStackPosition : Nat

namespace DirectProofContext

def pendingRow (context : DirectProofContext) : Atom :=
  .expression
    [.symbol "mm-compressed-step-pending", context.scopeOwner,
      context.proofOwner, context.wordPosition, context.remainingBytes,
      (CompressedIndexCode.ofNat context.index).atom]

def lookupRow (context : DirectProofContext) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", context.scopeOwner,
      context.proofOwner, context.wordPosition, context.remainingBytes,
      (CompressedIndexCode.ofNat context.index).atom,
      (CompressedIndexCode.ofNat context.cursor).atom]

def machineRow (context : DirectProofContext) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", context.scopeOwner, context.proofOwner,
      (CompressedIndexCode.ofNat context.heapNext).atom,
      (CompressedIndexCode.ofNat context.nodeNext).atom,
      (CompressedIndexCode.ofNat context.stackPosition).atom]

def stackSuccessorRow (context : DirectProofContext) : Atom :=
  compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
    (CompressedIndexCode.ofNat context.stackPosition).atom
    (CompressedIndexCode.ofNat context.nextStackPosition).atom

def nextMachineRow (context : DirectProofContext) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", context.scopeOwner, context.proofOwner,
      (CompressedIndexCode.ofNat context.heapNext).atom,
      (CompressedIndexCode.ofNat context.nodeNext).atom,
      (CompressedIndexCode.ofNat context.nextStackPosition).atom]

def resumedScanRow (context : DirectProofContext) : Atom :=
  .expression
    [.symbol "mm-compressed-scan", context.scopeOwner, context.proofOwner,
      context.wordPosition, context.remainingBytes,
      .symbol "mm-compressed-just-completed-step", listAtom natAtom []]

end DirectProofContext

/-- The actual data frame seen by the selected directive after its unique
scheduler shell has been removed from the assembled MM2 space. -/
def directProofLive (space : List Atom) : List Atom :=
  space.erase speculativeDirectProofDirective.atom

/-- Matcher rows used by the actual generated direct proof directive after
its unique scheduler shell has been removed from the assembled space. -/
def directProofMatcherRows (space : List Atom) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (speculativeDirectProofDirective.atom :: directProofLive space)
      speculativeDirectProofDirective.rule.input).map Prod.fst

/-- Exact data-flow witness for one direct proof match.  It ties the consumed
request and machine rows to the emitted stack occurrence and continuation. -/
def ExactDirectProofMatch (context : DirectProofContext)
    (item : ProofOccurrence) (space : List Atom) : Prop :=
  ∃ substitution ∈ directProofMatcherRows space,
    instantiateTemplateAtom? substitution directPendingTemplate =
        some context.pendingRow ∧
      instantiateTemplateAtom? substitution directLookupTemplate =
        some context.lookupRow ∧
      instantiateTemplateAtom? substitution directMachineTemplate =
        some context.machineRow ∧
      instantiateTemplateAtom? substitution directNextMachineTemplate =
        some context.nextMachineRow ∧
      instantiateTemplateAtom? substitution directStackCellTemplate =
        some (compressedStackRow context.proofOwner context.stackPosition item) ∧
      instantiateTemplateAtom? substitution directNormalStackCellTemplate =
        some (normalStackRow context.proofOwner context.stackPosition item) ∧
      instantiateTemplateAtom? substitution directResumedScanTemplate =
        some context.resumedScanRow

/-- Displayed subspace on which the generated direct proof handler is
scheduled and semantically related to one generic heap request. -/
structure DirectProofRequestFrame {Other : Type}
    (context : DirectProofContext) (item : ProofOccurrence)
    (state : SemanticState Other) (space : List Atom) : Prop where
  control : state.control =
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request context.index
  found : state.heap[context.index]? = some (.occurrence item)
  heapRow : heapProofRow context.proofOwner context.index item ∈ directProofLive space
  nodeRow : MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
    directProofLive space
  supported :
    cSupportedSourceExecFacts space =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectProofDirective, speculativeDirectAssertionDirective]
  exactMatch : ExactDirectProofMatch context item space

/-- Semantic successor for the generic hit; only the lookup control changes. -/
def semanticHitAfter {Other : Type} (context : DirectProofContext)
    (item : ProofOccurrence) (state : SemanticState Other) : SemanticState Other :=
  ⟨state.heap, state.reserve,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.finished context.index
      (.found context.index (.occurrence item))⟩

private theorem directProofSinks_preserve_expression_head
    (rows : List Subst) (candidateHead : String) (candidateTail : List Atom)
    (notPending : "mm-compressed-step-pending" ≠ candidateHead)
    (notLookup : "mm-compressed-heap-lookup" ≠ candidateHead)
    (notMachine : "mm-compressed-machine" ≠ candidateHead) :
    ∀ sink ∈ directProofSinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows,
            instantiateTemplateAtom? substitution authored ≠
              some (.expression (.symbol candidateHead :: candidateTail)) := by
  intro sink member
  simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨directPendingTemplate, rfl, fun substitution _ => by
      unfold directPendingTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notPending⟩
  · exact Or.inr ⟨directLookupTemplate, rfl, fun substitution _ => by
      unfold directLookupTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notLookup⟩
  · exact Or.inr ⟨directMachineTemplate, rfl, fun substitution _ => by
      unfold directMachineTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notMachine⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

private theorem directProofSinks_compact_split :
    directProofSinks =
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate] ++
      .add directStackCellTemplate ::
        [.add directNormalStackCellTemplate, .add directResumedScanTemplate] := by
  rfl

private theorem directProofSinks_normal_split :
    directProofSinks =
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate] ++
      .add directNormalStackCellTemplate :: [.add directResumedScanTemplate] := by
  rfl

theorem direct_fire_retains_heap_row
    (context : DirectProofContext) (item : ProofOccurrence) (space : List Atom)
    (present : heapProofRow context.proofOwner context.index item ∈
      directProofLive space) :
    heapProofRow context.proofOwner context.index item ∈
      cFireReflectiveSourceExecFact
        space speculativeDirectProofDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    (directProofMatcherRows space)
    (directProofSinks_preserve_expression_head
      (directProofMatcherRows space) "mm-compressed-heap-proof"
      [context.proofOwner, (CompressedIndexCode.ofNat context.index).atom,
        item.identity]
      (by decide) (by decide) (by decide)) present

theorem direct_fire_retains_node_row
    (context : DirectProofContext) (item : ProofOccurrence) (space : List Atom)
    (present : MM2CompressedProofHeapEncoding.nodeRow
      context.proofOwner item ∈ directProofLive space) :
    MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
      cFireReflectiveSourceExecFact
        space speculativeDirectProofDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    (directProofMatcherRows space)
    (directProofSinks_preserve_expression_head
      (directProofMatcherRows space) "mm-compressed-node"
      [context.proofOwner, item.identity, item.value.formula,
        item.value.sourceOccurrence]
      (by decide) (by decide) (by decide)) present

theorem direct_fire_adds_stack_rows
    (context : DirectProofContext) (item : ProofOccurrence) (space : List Atom)
    (matched : ExactDirectProofMatch context item space) :
    compressedStackRow context.proofOwner context.stackPosition item ∈
        cFireReflectiveSourceExecFact
          space speculativeDirectProofDirective ∧
      normalStackRow context.proofOwner context.stackPosition item ∈
        cFireReflectiveSourceExecFact
          space speculativeDirectProofDirective := by
  rcases matched with
    ⟨substitution, rowMember, _pending, _lookup, _machine, _nextMachine,
      compactStack, normalStack, _scan⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  constructor
  · rw [directProofSinks_compact_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (directProofMatcherRows space) (directProofLive space) _
      directStackCellTemplate _
      _ substitution rowMember compactStack (by
        intro sink member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [directProofSinks_normal_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row
      (directProofMatcherRows space) (directProofLive space) _
      directNormalStackCellTemplate _
      _ substitution rowMember normalStack (by
        intro sink member
        simp only [List.mem_singleton] at member
        subst sink
        exact ⟨_, rfl⟩)

/-- Symbolic commuting theorem for every semantic proof occurrence and every
well-framed concrete space.  No fixture-sized reduction appears in the proof. -/
structure DirectProofHitCommutingSquare {Other : Type}
    (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other) (space : List Atom) : Prop where
  semanticStep :
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step before
      (semanticHitAfter context item before)
  concreteStep :
    cReflectiveSourceWorkQueueStep .leaveInert
        space =
      some
        (cFireReflectiveSourceExecFact
          space speculativeDirectProofDirective)
  outputRepresentation :
    RepresentsProofHit context.proofOwner context.stackPosition
      (semanticHitAfter context item before)
      (cFireReflectiveSourceExecFact
        space speculativeDirectProofDirective)

theorem direct_proof_hit_commutes_of_exact_frame
    {Other : Type} (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other) (space : List Atom)
    (frame : DirectProofRequestFrame context item before space) :
    DirectProofHitCommutingSquare context item before space := by
  have retainedHeap :=
    direct_fire_retains_heap_row context item space frame.heapRow
  have retainedNode :=
    direct_fire_retains_node_row context item space frame.nodeRow
  obtain ⟨compactStack, normalStack⟩ :=
    direct_fire_adds_stack_rows context item space frame.exactMatch
  refine ⟨?_, ?_, ?_⟩
  · cases before with
    | mk heap reserve control =>
        have controlEq := frame.control
        dsimp only at controlEq
        subst control
        exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
          heap reserve context.index (.occurrence item) frame.found
  · unfold cReflectiveSourceWorkQueueStep
    rw [select_direct_proof_of_supported_exact frame.supported]
  · exact ⟨context.index, item, rfl, frame.found, retainedHeap, retainedNode,
      compactStack, normalStack⟩

#print axioms direct_fire_retains_heap_row
#print axioms direct_fire_retains_node_row
#print axioms direct_fire_adds_stack_rows
#print axioms direct_proof_hit_commutes_of_exact_frame

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
