import Mettapedia.Languages.Metamath.MM2CompressedProofDataSpineAgreement
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness

/-!
# Reserved physical frame for repeated compressed saves

The source-data transformation emits finite heap, node, and stack successor
spines before execution.  This module places those reservations in the
compiler-selected verifier frame and proves that a source save consumes an
already-authorized edge.  The save rule never manufactures an unbounded
successor capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofReservedSaveFrame

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofData
open Mettapedia.Languages.Metamath.MM2CompressedProofDataSpineAgreement
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Finite allocation infrastructure shared by compressed proof, assertion,
and save transitions.  Its size is linear in the source proof data. -/
def reservedIndexRows (proofOwner : Atom)
    (heapCapacity nodeCapacity stackCapacity : Nat) : List Atom :=
  compressedIndexSuccessorRows (compressedHeapOwner proofOwner) heapCapacity ++
    compressedIndexSuccessorRows (compressedNodeOwner proofOwner) nodeCapacity ++
    compressedIndexSuccessorRows (compressedStackOwner proofOwner) stackCapacity ++
    compressedNormalStackSuccessorRows proofOwner stackCapacity

/-- Save activation over the finite source-derived reservation and the
compiler-selected persistent verifier presentation. -/
def reservedSaveStaticFrame (context : BoundaryContext)
    (heapCapacity nodeCapacity stackCapacity : Nat) : List Atom :=
  compressedSaveDirective.atom ::
    (reservedIndexRows context.proofOwner heapCapacity nodeCapacity
      stackCapacity ++ baseCompiledPresentation.targetStaticRows)

private def hasExecHead : Atom → Bool
  | .expression (.symbol "exec" :: _) => true
  | _ => false

private def speculativeTargetStaticNoExecHeadCheck : Bool :=
  baseCompiledPresentation.targetStaticRows.all fun row => !hasExecHead row

private theorem speculativeTargetStaticNoExecHeadCheck_eq_true :
    speculativeTargetStaticNoExecHeadCheck = true := by
  decide +kernel

private theorem speculativeTargetStaticRows_no_exec_head
    (row : Atom) (member : row ∈ baseCompiledPresentation.targetStaticRows) :
    hasExecHead row = false := by
  have checked := (List.all_eq_true.mp
    speculativeTargetStaticNoExecHeadCheck_eq_true) row member
  cases exact : hasExecHead row <;> simp_all

private theorem reservedIndexRows_no_exec_head
    (proofOwner : Atom) (heapCapacity nodeCapacity stackCapacity : Nat)
    (row : Atom)
    (member : row ∈ reservedIndexRows proofOwner heapCapacity nodeCapacity
      stackCapacity) :
    hasExecHead row = false := by
  simp only [reservedIndexRows, List.mem_append] at member
  rcases member with ((heap | node) | stack) | normalStack
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedHeapOwner proofOwner) _ heapCapacity).1 heap
    rfl
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedNodeOwner proofOwner) _ nodeCapacity).1 node
    rfl
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedStackOwner proofOwner) _ stackCapacity).1 stack
    rfl
  · rw [compressedNormalStackSuccessorRows, List.mem_map] at normalStack
    obtain ⟨position, _bound, rfl⟩ := normalStack
    rfl

/-- Within the finite reserved frame, the only row with the save
directive's top-level executable shape is the directive itself. -/
private theorem reservedSaveStaticFrame_exec_head_exact
    (context : BoundaryContext)
    (heapCapacity nodeCapacity stackCapacity : Nat) (row : Atom)
    (member : row ∈ reservedSaveStaticFrame context heapCapacity nodeCapacity
      stackCapacity)
    (execHead : hasExecHead row = true) :
    row = compressedSaveDirective.atom := by
  simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append] at member
  rcases member with rfl | reserved | target
  · rfl
  · have noExec := reservedIndexRows_no_exec_head context.proofOwner
      heapCapacity nodeCapacity stackCapacity row reserved
    exact False.elim (Bool.false_ne_true (noExec.symm.trans execHead))
  · have noExec := speculativeTargetStaticRows_no_exec_head row target
    exact False.elim (Bool.false_ne_true (noExec.symm.trans execHead))

theorem current_heap_successor_mem_reservedIndexRows
    (context : BoundaryContext) (heapCapacity nodeCapacity stackCapacity
      position : Nat) (available : position < heapCapacity) :
    compressedIndexSuccessorRow (compressedHeapOwner context.proofOwner)
        (CompressedIndexCode.ofNat position).atom
        (CompressedIndexCode.ofNat (position + 1)).atom ∈
      reservedIndexRows context.proofOwner heapCapacity nodeCapacity
        stackCapacity := by
  simp only [reservedIndexRows, List.mem_append]
  exact Or.inl (Or.inl (Or.inl
    (compressedIndexSuccessorRow_mem _ heapCapacity position available)))

theorem current_stack_successor_mem_reservedIndexRows
    (context : BoundaryContext) (heapCapacity nodeCapacity stackCapacity
      position : Nat) (available : position < stackCapacity) :
    compressedIndexSuccessorRow (compressedStackOwner context.proofOwner)
        (CompressedIndexCode.ofNat position).atom
        (CompressedIndexCode.ofNat (position + 1)).atom ∈
      reservedIndexRows context.proofOwner heapCapacity nodeCapacity
        stackCapacity := by
  simp only [reservedIndexRows, List.mem_append]
  exact Or.inl (Or.inr
    (compressedIndexSuccessorRow_mem _ stackCapacity position available))

/-- A finite compact successor spine has one destination at each represented
source position. -/
theorem compressedIndexSuccessorRows_current_functional
    (owner : Atom) (count position : Nat) (next : Atom)
    (member :
      compressedIndexSuccessorRow owner
          (CompressedIndexCode.ofNat position).atom next ∈
        compressedIndexSuccessorRows owner count) :
    next = (CompressedIndexCode.ofNat (position + 1)).atom := by
  obtain ⟨other, _bound, equal⟩ :=
    (mem_compressedIndexSuccessorRows_iff owner _ count).1 member
  have atomsEqual := Atom.expression.inj equal
  have currentEqual :
      (CompressedIndexCode.ofNat position).atom =
        (CompressedIndexCode.ofNat other).atom :=
    (List.cons.inj (List.cons.inj (List.cons.inj atomsEqual).2).2).1
  have positionEqual : position = other :=
    CanonicalIndexCode.ofNat_injective
      (CanonicalIndexCode.atom_injective currentEqual)
  have nextEqual :
      next = (CompressedIndexCode.ofNat (other + 1)).atom :=
    (List.cons.inj
      (List.cons.inj (List.cons.inj (List.cons.inj atomsEqual).2).2).2).1
  simpa only [positionEqual] using nextEqual

/-- Dually, a finite compact successor spine has one predecessor at each
represented nonzero destination. -/
theorem compressedIndexSuccessorRows_predecessor_functional
    (owner : Atom) (count position : Nat) (previous : Atom)
    (member :
      compressedIndexSuccessorRow owner previous
          (CompressedIndexCode.ofNat (position + 1)).atom ∈
        compressedIndexSuccessorRows owner count) :
    previous = (CompressedIndexCode.ofNat position).atom := by
  obtain ⟨other, _bound, equal⟩ :=
    (mem_compressedIndexSuccessorRows_iff owner _ count).1 member
  have atomsEqual := Atom.expression.inj equal
  have nextEqual :
      (CompressedIndexCode.ofNat (position + 1)).atom =
        (CompressedIndexCode.ofNat (other + 1)).atom :=
    (List.cons.inj
      (List.cons.inj (List.cons.inj (List.cons.inj atomsEqual).2).2).2).1
  have positionEqual : position = other := by
    have codeEqual := CanonicalIndexCode.atom_injective nextEqual
    have natEqual := CanonicalIndexCode.ofNat_injective codeEqual
    omega
  have previousEqual :
      previous = (CompressedIndexCode.ofNat other).atom :=
    (List.cons.inj (List.cons.inj (List.cons.inj atomsEqual).2).2).1
  simpa only [positionEqual] using previousEqual

/-- The complete reserved inventory remains functional at every compact heap
cursor despite carrying independent node, stack, and normal-stack spines. -/
theorem reservedIndexRows_heap_current_functional
    (proofOwner : Atom) (heapCapacity nodeCapacity stackCapacity position : Nat)
    (next : Atom)
    (member :
      compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat position).atom next ∈
        reservedIndexRows proofOwner heapCapacity nodeCapacity stackCapacity) :
    next = (CompressedIndexCode.ofNat (position + 1)).atom := by
  simp only [reservedIndexRows, List.mem_append] at member
  rcases member with ((heap | node) | stack) | normalStack
  · exact compressedIndexSuccessorRows_current_functional
      (compressedHeapOwner proofOwner) heapCapacity position next heap
  · obtain ⟨other, _bound, equal⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedNodeOwner proofOwner) _ nodeCapacity).1 node
    simp [compressedIndexSuccessorRow, compressedHeapOwner,
      compressedNodeOwner] at equal
  · obtain ⟨other, _bound, equal⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedStackOwner proofOwner) _ stackCapacity).1 stack
    simp [compressedIndexSuccessorRow, compressedHeapOwner,
      compressedStackOwner] at equal
  · rw [compressedNormalStackSuccessorRows, List.mem_map] at normalStack
    obtain ⟨other, _bound, equal⟩ := normalStack
    simp [compressedIndexSuccessorRow] at equal

/-- The stack portion of the complete reservation has one predecessor at a
source-identified destination. -/
theorem reservedIndexRows_stack_predecessor_functional
    (proofOwner : Atom) (heapCapacity nodeCapacity stackCapacity position : Nat)
    (previous : Atom)
    (member :
      compressedIndexSuccessorRow (compressedStackOwner proofOwner) previous
          (CompressedIndexCode.ofNat (position + 1)).atom ∈
        reservedIndexRows proofOwner heapCapacity nodeCapacity stackCapacity) :
    previous = (CompressedIndexCode.ofNat position).atom := by
  simp only [reservedIndexRows, List.mem_append] at member
  rcases member with ((heap | node) | stack) | normalStack
  · obtain ⟨other, _bound, equal⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedHeapOwner proofOwner) _ heapCapacity).1 heap
    simp [compressedIndexSuccessorRow, compressedHeapOwner,
      compressedStackOwner] at equal
  · obtain ⟨other, _bound, equal⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedNodeOwner proofOwner) _ nodeCapacity).1 node
    simp [compressedIndexSuccessorRow, compressedNodeOwner,
      compressedStackOwner] at equal
  · exact compressedIndexSuccessorRows_predecessor_functional
      (compressedStackOwner proofOwner) stackCapacity position previous stack
  · rw [compressedNormalStackSuccessorRows, List.mem_map] at normalStack
    obtain ⟨other, _bound, equal⟩ := normalStack
    simp [compressedIndexSuccessorRow, compressedStackOwner] at equal

/-- A live save frontier is admitted precisely by unused finite source
capacity.  No successor is generated by the transition itself. -/
theorem reservedSaveStaticFrame_supportFor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (heapCapacity nodeCapacity stackCapacity stackTopPosition : Nat)
    (heapAvailable : before.heap.length < heapCapacity)
    (stackTopNext : stackTopPosition + 1 = before.stack.length)
    (stackAvailable : stackTopPosition < stackCapacity) :
    SaveStaticSupportFor speculativeSaveRuntimeRuleBundle context before
      stackTopPosition
      (reservedSaveStaticFrame context heapCapacity nodeCapacity
        stackCapacity) := by
  refine
    { directive := by simp [reservedSaveStaticFrame]
      stackSuccessor := ?_
      heapSuccessor := ?_
      captures := ?_ }
  · have member := current_stack_successor_mem_reservedIndexRows context
      heapCapacity nodeCapacity stackCapacity stackTopPosition stackAvailable
    rw [stackTopNext] at member
    simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl member)
  · simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl
      (current_heap_successor_mem_reservedIndexRows context heapCapacity
        nodeCapacity stackCapacity before.heap.length heapAvailable))
  · intro row member
    simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr
      (speculativeSaveRuntimeCaptureRows_mem_target row member))

/-- The finite reservation supplies unique live heap and stack edges.  Adding
future source-reserved edges therefore does not make the current save
ambiguous. -/
theorem reservedSaveStaticFrame_frontierAuthority
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (heapCapacity nodeCapacity stackCapacity stackTopPosition : Nat)
    (heapAvailable : before.heap.length < heapCapacity)
    (stackTopNext : stackTopPosition + 1 = before.stack.length)
    (stackAvailable : stackTopPosition < stackCapacity) :
    SaveFrontierAuthority context before stackTopPosition
      (reservedSaveStaticFrame context heapCapacity nodeCapacity
        stackCapacity) := by
  have support := reservedSaveStaticFrame_supportFor context before heapCapacity
    nodeCapacity stackCapacity stackTopPosition heapAvailable stackTopNext
    stackAvailable
  refine
    { directive := support.directive
      stackSuccessor := support.stackSuccessor
      stackPredecessorFunctional := ?_
      heapSuccessor := support.heapSuccessor
      heapSuccessorFunctional := ?_ }
  · intro previous member
    simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append] at member
    rcases member with save | reserved | transformed
    · have rawEqual := congrArg extractRawExecFact save
      simp [compressedSaveDirective, compressedSaveRule,
        compressedIndexSuccessorRow, extractRawExecFact] at rawEqual
    · rw [← stackTopNext] at reserved
      exact reservedIndexRows_stack_predecessor_functional context.proofOwner
        heapCapacity nodeCapacity stackCapacity stackTopPosition previous reserved
    · exact False.elim
        (speculativeTargetStaticRows_no_index_successor _ transformed
          (compressedStackOwner context.proofOwner) previous
          (CompressedIndexCode.ofNat before.stack.length).atom rfl)
  · intro next member
    simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append] at member
    rcases member with save | reserved | transformed
    · have rawEqual := congrArg extractRawExecFact save
      simp [compressedSaveDirective, compressedSaveRule,
        compressedIndexSuccessorRow, extractRawExecFact] at rawEqual
    · exact reservedIndexRows_heap_current_functional context.proofOwner
        heapCapacity nodeCapacity stackCapacity before.heap.length next reserved
    · exact False.elim
        (speculativeTargetStaticRows_no_index_successor _ transformed
          (compressedHeapOwner context.proofOwner)
          (CompressedIndexCode.ofNat before.heap.length).atom next rfl)

/-- Reserved index rows are data, not scheduled executable directives. -/
theorem reservedIndexRows_no_supported
    (proofOwner : Atom) (heapCapacity nodeCapacity stackCapacity : Nat) :
    cSupportedSourceExecFacts
      (reservedIndexRows proofOwner heapCapacity nodeCapacity stackCapacity) =
        [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  simp only [reservedIndexRows, List.mem_append] at member
  rcases member with ((heap | node) | stack) | normalStack
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedHeapOwner proofOwner) row heapCapacity).1 heap
    rfl
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedNodeOwner proofOwner) row nodeCapacity).1 node
    rfl
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedStackOwner proofOwner) row stackCapacity).1 stack
    rfl
  · rw [compressedNormalStackSuccessorRows, List.mem_map] at normalStack
    obtain ⟨position, _bound, rfl⟩ := normalStack
    rfl

/-- Reservation rows cannot carry executable payloads under any presentation;
their authority is limited to finite cursor movement. -/
theorem reservedIndexRows_capabilities
    (presentation : CompressedExecutablePresentation) (proofOwner : Atom)
    (heapCapacity nodeCapacity stackCapacity : Nat) :
    CompressedExecutableCapabilities presentation
      (reservedIndexRows proofOwner heapCapacity nodeCapacity stackCapacity) := by
  intro row member
  simp only [reservedIndexRows, List.mem_append] at member
  rcases member with ((heap | node) | stack) | normalStack
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedHeapOwner proofOwner) row heapCapacity).1 heap
    simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture, compressedIndexSuccessorRow,
      compressedHeapOwner]
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedNodeOwner proofOwner) row nodeCapacity).1 node
    simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture, compressedIndexSuccessorRow,
      compressedNodeOwner]
  · obtain ⟨position, _bound, rfl⟩ :=
      (mem_compressedIndexSuccessorRows_iff
        (compressedStackOwner proofOwner) row stackCapacity).1 stack
    simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture, compressedIndexSuccessorRow,
      compressedStackOwner]
  · rw [compressedNormalStackSuccessorRows, List.mem_map] at normalStack
    obtain ⟨position, _bound, rfl⟩ := normalStack
    simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture]

/-- The complete reserved frame inherits executable authority solely from the
compiler-selected persistent presentation. -/
theorem reservedSaveStaticFrame_capabilities
    (context : BoundaryContext)
    (heapCapacity nodeCapacity stackCapacity : Nat) :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      (reservedSaveStaticFrame context heapCapacity nodeCapacity
        stackCapacity) := by
  intro row member
  simp only [reservedSaveStaticFrame, List.mem_cons, List.mem_append] at member
  rcases member with rfl | reserved | persistent
  · simp [CompressedExecutableCarrierAuthorized,
      decodeCompressedExecutableCapture, compressedSaveDirective,
      compressedSaveRule]
  · exact reservedIndexRows_capabilities speculativeBaseExecutablePresentation
      context.proofOwner heapCapacity nodeCapacity stackCapacity row reserved
  · exact speculative_target_static_rows_authorized row persistent

/-- Exactly the save directive is scheduled at the reserved save boundary;
all finite index rows and persistent compiler rows remain inert. -/
theorem reservedSaveStaticFrame_supported
    (context : BoundaryContext)
    (heapCapacity nodeCapacity stackCapacity : Nat) :
    cSupportedSourceExecFacts
      (reservedSaveStaticFrame context heapCapacity nodeCapacity
        stackCapacity) = [compressedSaveDirective] := by
  unfold reservedSaveStaticFrame cSupportedSourceExecFacts
  simp only [List.filterMap_cons]
  rw [List.filterMap_append]
  have reserved :
      List.filterMap extractSupportedSourceExecFact
          (reservedIndexRows context.proofOwner heapCapacity nodeCapacity
            stackCapacity) = [] := by
    simpa [cSupportedSourceExecFacts] using
      reservedIndexRows_no_supported context.proofOwner heapCapacity
        nodeCapacity stackCapacity
  have persistent :
      List.filterMap extractSupportedSourceExecFact
          baseCompiledPresentation.targetStaticRows = [] := by
    simpa [cSupportedSourceExecFacts] using
      speculativeTargetStaticRows_no_supported
  rw [reserved, persistent]
  rfl

/-- Every physical permutation of the reserved boundary schedules the same
source-derived save rule. -/
theorem physical_reserved_save_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {heapCapacity nodeCapacity stackCapacity : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    cSupportedSourceExecFacts space = [compressedSaveDirective] := by
  have perm := represented.supportedFacts_perm
  have canonical :
      cSupportedSourceExecFacts
          (canonicalBoundaryRows context state ledger scanner ++
            reservedSaveStaticFrame context heapCapacity nodeCapacity
              stackCapacity) = [compressedSaveDirective] := by
    unfold cSupportedSourceExecFacts
    rw [List.filterMap_append]
    have dynamicRows :
        List.filterMap extractSupportedSourceExecFact
            (canonicalBoundaryRows context state ledger scanner) = [] := by
      simpa [cSupportedSourceExecFacts] using
        canonicalBoundaryRows_no_supported context state ledger scanner
    have staticRows :
        List.filterMap extractSupportedSourceExecFact
            (reservedSaveStaticFrame context heapCapacity nodeCapacity
              stackCapacity) = [compressedSaveDirective] := by
      simpa [cSupportedSourceExecFacts] using
        reservedSaveStaticFrame_supported context heapCapacity nodeCapacity
          stackCapacity
    rw [dynamicRows, staticRows]
    rfl
  rw [canonical] at perm
  simpa using perm

/-- Every matcher row selected from a physical permutation of the reserved
save boundary replays the exact admitted save directive.  Dynamic source rows
cannot have an executable head, and the finite static reservation contains no
other such row. -/
theorem physical_reserved_save_matcher_self_replay
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {heapCapacity nodeCapacity stackCapacity : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space)
    (substitution : Subst)
    (member : substitution ∈ physicalSaveMatcherRows space) :
    applySubst substitution saveSelfTemplate = compressedSaveDirective.atom := by
  have reflectiveMember :=
    physicalSaveMatcherRows_subset_saveMatcherRows_of_frame represented
      (by simp [reservedSaveStaticFrame]) member
  unfold saveMatcherRows at reflectiveMember
  rw [compressedSaveDirective_input_exact] at reflectiveMember
  obtain ⟨carrier, carrierMember, replay⟩ :=
    Conformance.Computable.cmatchInputSpec_compat_factor_replay_origin
      (compressedSaveDirective.atom :: saveLive space)
      (mkPattern savePatterns) saveSelfTemplate
      (by simp [mkPattern, savePatterns]) reflectiveMember
  rcases List.mem_cons.mp carrierMember with rfl | liveMember
  · exact replay
  · have carrierSpace : carrier ∈ space := List.mem_of_mem_erase liveMember
    have representedMember := (represented.exact_rows carrier).1 carrierSpace
    rcases List.mem_append.mp representedMember with canonical | static
    · have dynamic := canonicalBoundaryRows_all_dynamic context state ledger
        scanner carrier canonical
      have nondynamic : isDynamicRow carrier = false := by
        rw [← replay]
        simp [saveSelfTemplate, isDynamicRow, dynamicRowHeads, applySubst,
          applySubst.applySubstList]
      exact False.elim (Bool.false_ne_true (nondynamic.symm.trans dynamic))
    · have execHead : hasExecHead carrier = true := by
        rw [← replay]
        simp [saveSelfTemplate, hasExecHead, applySubst,
          applySubst.applySubstList]
      exact replay.trans
        (reservedSaveStaticFrame_exec_head_exact context heapCapacity
          nodeCapacity stackCapacity carrier static execHead)

/-- Any old represented row distinct from the directive and two moving
controls survives the reserved physical save.  Compact-key separation is
derived from the predecessor boundary's own duplicate-freedom, so no global
injectivity of variable-bearing MORK syntax is assumed. -/
theorem physical_reserved_save_preserves_old_row
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {scanner : ScannerBoundary}
    {heapCapacity nodeCapacity stackCapacity : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scanner
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space)
    (row : Atom)
    (referenceMember : row ∈
      canonicalBoundaryRows context before ledger scanner ++
        reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
    (notDirective : row ≠ compressedSaveDirective.atom)
    (notScanner : row ≠ scannerRow context scanner)
    (notMachine : row ≠ machineRow context before) :
    row ∈ cFireRuleScopedSourceExecFact space compressedSaveDirective := by
  let reference := canonicalBoundaryRows context before ledger scanner ++
    reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity
  have referenceMorkNodup : MorkSupportNodup reference := by
    simpa [reference] using represented.canonical_with_frame_mork_nodup
  have rowMember : row ∈ space :=
    (represented.exact_rows row).2 referenceMember
  have scannerReference : scannerRow context scanner ∈ reference := by
    simp [reference, canonicalBoundaryRows]
  have machineReference : machineRow context before ∈ reference := by
    simp [reference, canonicalBoundaryRows]
  have notScannerKey :
      morkSupportKey row ≠ morkSupportKey (scannerRow context scanner) := by
    intro keysEqual
    exact notScanner
      (morkSupportKey_injective_on referenceMorkNodup referenceMember
        scannerReference keysEqual)
  have notMachineKey :
      morkSupportKey row ≠ morkSupportKey (machineRow context before) := by
    intro keysEqual
    exact notMachine
      (morkSupportKey_injective_on referenceMorkNodup referenceMember
        machineReference keysEqual)
  exact physical_save_preserves_input_row_of_frame represented
    (by simp [reservedSaveStaticFrame]) row rowMember notDirective
    notScannerKey notMachineKey

/-- The rule-scoped MORK matcher reconstructs the exact semantic save from a
finite reserved frame. -/
theorem physical_reserved_source_save_exact_match
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
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    PhysicalExactSaveMatch context before after scannerBefore scannerAfter
      (displayedProofOccurrence nodeId node sourceOccurrence) space := by
  obtain ⟨stackPrefix, stackEq⟩ := List.getLast?_eq_some_iff.mp stackTop
  have stackPositive : 0 < before.stack.length := by
    rw [stackEq]
    simp
  exact physical_source_save_exact_match_of_support ledger receipt step
    stackTop nodeLookup occurrenceLookup represented
    (reservedSaveStaticFrame_supportFor context before heapCapacity nodeCapacity
      stackCapacity (before.stack.length - 1) heapAvailable (by omega)
      (by omega))

/-- The consumed save directive is reactivated by its authored self add and
remains present through the rest of the physical sink batch. -/
theorem physical_reserved_save_self_support_present
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
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    morkSupportContains
      (cFireRuleScopedSourceExecFact space compressedSaveDirective)
      compressedSaveDirective.atom = true := by
  obtain ⟨stackPrefix, stackEq⟩ := List.getLast?_eq_some_iff.mp stackTop
  have stackPositive : 0 < before.stack.length := by
    rw [stackEq]
    simp
  have support := reservedSaveStaticFrame_supportFor context before heapCapacity
    nodeCapacity stackCapacity (before.stack.length - 1) heapAvailable
    (by omega) (by omega)
  have matched := physical_source_save_exact_match_of_support ledger receipt
    step stackTop nodeLookup occurrenceLookup represented support
  rcases matched with ⟨witness, witnessMember, _⟩
  let rows := physicalSaveMatcherRows space
  have witnessMember' : witness ∈ rows := by simpa [rows] using witnessMember
  have selfReplay := physical_reserved_save_matcher_self_replay represented
    witness witnessMember'
  have selfExact := physical_save_matcher_self_instantiation_exact_of_frame
    represented (by simp [reservedSaveStaticFrame]) witnessMember' selfReplay
  let reference := canonicalBoundaryRows context before ledger scannerBefore ++
    reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity
  have referenceMorkNodup : MorkSupportNodup reference := by
    simpa [reference] using represented.canonical_with_frame_mork_nodup
  have directiveReference : compressedSaveDirective.atom ∈ reference := by
    simp [reference, reservedSaveStaticFrame]
  have scannerReference : scannerRow context scannerBefore ∈ reference := by
    simp [reference, canonicalBoundaryRows]
  have machineReference : machineRow context before ∈ reference := by
    simp [reference, canonicalBoundaryRows]
  have directiveNotScanner :
      compressedSaveDirective.atom ≠ scannerRow context scannerBefore := by
    simp [compressedSaveDirective, compressedSaveRule, scannerRow]
  have directiveNotMachine :
      compressedSaveDirective.atom ≠ machineRow context before := by
    simp [compressedSaveDirective, compressedSaveRule, machineRow]
  have keyNotScanner : morkSupportKey compressedSaveDirective.atom ≠
      morkSupportKey (scannerRow context scannerBefore) := by
    intro keysEqual
    exact directiveNotScanner
      (morkSupportKey_injective_on referenceMorkNodup directiveReference
        scannerReference keysEqual)
  have keyNotMachine : morkSupportKey compressedSaveDirective.atom ≠
      morkSupportKey (machineRow context before) := by
    intro keysEqual
    exact directiveNotMachine
      (morkSupportKey_injective_on referenceMorkNodup directiveReference
        machineReference keysEqual)
  have restSafe : ∀ sink ∈
      ([.add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-proof-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule"),
       .remove saveScanTemplate, .remove saveMachineTemplate,
       .add afterSaveMachineTemplate, .add afterSaveScanTemplate,
       .add savedHeapTemplate, .add saveReceiptTemplate] : List Sink),
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows, ∀ removed,
            instantiateRuleTemplateAtom? compressedSaveDirective.rule.input
                substitution authored = some removed →
              morkSupportKey compressedSaveDirective.atom ≠
                morkSupportKey removed := by
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨saveScanTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented (by simp [reservedSaveStaticFrame]) substitutionMember
          have removedExact : removed = scannerRow context scannerBefore :=
            Option.some.inj (instantiated.symm.trans exact.1)
          simpa [removedExact] using keyNotScanner⟩
      | exact Or.inr ⟨saveMachineTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_save_matcher_predecessor_controls_exact_of_frame
            represented (by simp [reservedSaveStaticFrame]) substitutionMember
          have removedExact : removed = machineRow context before :=
            Option.some.inj (instantiated.symm.trans exact.2)
          simpa [removedExact] using keyNotMachine⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change morkSupportContains
      (cApplyRuleScopedSinkBatch compressedSaveDirective.rule.input rows
        (morkEraseSupport space compressedSaveDirective.atom)
        compressedSaveDirective.rule.tmpl.sinks)
      compressedSaveDirective.atom = true
  rw [compressedSaveDirective_sinks_exact]
  exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
    compressedSaveDirective.rule.input rows
    (morkEraseSupport space compressedSaveDirective.atom) [] saveSelfTemplate
    compressedSaveDirective.atom _ witness witnessMember' selfExact restSafe

/-- The actual rule-scoped MORK result over the finite reservation contains
all four source-determined dynamic save outputs by physical support identity. -/
theorem physical_reserved_save_successor_support_present
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
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    morkSupportContains result (machineRow context after) = true ∧
      morkSupportContains result (scannerRow context scannerAfter) = true ∧
      morkSupportContains result
        (heapProofRow context.proofOwner before.heap.length item) = true ∧
      morkSupportContains result
        (saveReceiptRow context.proofOwner before.heap.length item) = true := by
  obtain ⟨stackPrefix, stackEq⟩ := List.getLast?_eq_some_iff.mp stackTop
  have stackPositive : 0 < before.stack.length := by
    rw [stackEq]
    simp
  exact physical_save_successor_support_present_of_frame ledger receipt step
    stackTop nodeLookup occurrenceLookup represented
    (reservedSaveStaticFrame_supportFor context before heapCapacity nodeCapacity
      stackCapacity (before.stack.length - 1) heapAvailable (by omega)
      (by omega))
    (reservedSaveStaticFrame_frontierAuthority context before heapCapacity
      nodeCapacity stackCapacity (before.stack.length - 1) heapAvailable
      (by omega) (by omega))

/-- Every row of the complete source-derived successor presentation is
present in the physical MORK result.  Old passive and static rows survive;
the two obsolete controls do not; the directive and six runtime rules are
reactivated by authored adds; and the four dynamic outputs come from the
source save step. -/
theorem physical_reserved_save_successor_support_complete
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let successorStatic :=
      reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
        speculativeSaveRuntimeRuleBundle.payloadRows
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    ∀ row, row ∈
        canonicalBoundaryRows context after ledgerAfter scannerAfter ++
          successorStatic →
      morkSupportContains result row = true := by
  dsimp only
  obtain ⟨stackPrefix, stackEq⟩ := List.getLast?_eq_some_iff.mp stackTop
  have stackPositive : 0 < before.stack.length := by
    rw [stackEq]
    simp
  have support := reservedSaveStaticFrame_supportFor context before heapCapacity
    nodeCapacity stackCapacity (before.stack.length - 1) heapAvailable
    (by omega) (by omega)
  have dynamicPresent := physical_reserved_save_successor_support_present
    ledger receipt step stackTop nodeLookup occurrenceLookup heapAvailable
    stackFits represented
  have selfPresent := physical_reserved_save_self_support_present ledger
    receipt step stackTop nodeLookup occurrenceLookup heapAvailable stackFits
    represented
  intro row member
  rcases List.mem_append.mp member with canonical | static
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at canonical
    rcases canonical with (rfl | rfl) | passive
    · exact dynamicPresent.1
    · exact dynamicPresent.2.1
    · have delta :=
        (canonicalPassiveRows_save_iff represented.semantic.source_wellFormed
          ledger proofPosition step nodeId node sourceOccurrence stackTop
          nodeLookup occurrenceLookup row).1 passive
      rcases delta with old | rfl | rfl
      · have avoids := canonicalPassiveRows_avoid_save_controls context before
          ledger row old
        have notDirective : row ≠ compressedSaveDirective.atom := by
          intro equal
          subst row
          have dynamic := canonicalPassiveRows_all_dynamic context before ledger
            compressedSaveDirective.atom old
          have clean := represented.semantic.staticFrame_clean
            compressedSaveDirective.atom (by simp [reservedSaveStaticFrame])
          rw [clean] at dynamic
          contradiction
        have notScanner : row ≠ scannerRow context scannerBefore := by
          intro equal
          subst row
          simp [avoidsSaveControlHeads, scannerRow] at avoids
        have notMachine : row ≠ machineRow context before := by
          intro equal
          subst row
          simp [avoidsSaveControlHeads, machineRow] at avoids
        apply morkSupportContains_eq_true_of_mem
        apply physical_reserved_save_preserves_old_row represented row
        · apply List.mem_append_left
          simp [canonicalBoundaryRows, old]
        · exact notDirective
        · exact notScanner
        · exact notMachine
      · exact dynamicPresent.2.2.1
      · exact dynamicPresent.2.2.2
  · rcases List.mem_append.mp static with oldStatic | payload
    · by_cases directiveExact : row = compressedSaveDirective.atom
      · subst row
        exact selfPresent
      · have clean := represented.semantic.staticFrame_clean row oldStatic
        have notScanner : row ≠ scannerRow context scannerBefore := by
          intro equal
          subst row
          rw [scannerRow_isDynamic context scannerBefore] at clean
          contradiction
        have notMachine : row ≠ machineRow context before := by
          intro equal
          subst row
          rw [machineRow_isDynamic context before] at clean
          contradiction
        apply morkSupportContains_eq_true_of_mem
        apply physical_reserved_save_preserves_old_row represented row
        · exact List.mem_append_right _ oldStatic
        · exact directiveExact
        · exact notScanner
        · exact notMachine
    · exact physical_save_runtime_payload_support_present_of_frame ledger
        receipt step stackTop nodeLookup occurrenceLookup represented support
        (reservedSaveStaticFrame_capabilities context heapCapacity nodeCapacity
          stackCapacity) row payload

/-- No exact representative outside the complete successor presentation can
survive or be introduced by the reserved physical save. -/
theorem physical_reserved_save_result_rows_within_successor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (step : ActionStep before .save after)
    {nodeId : Nat} {node : ProofNode source target} {sourceOccurrence : Atom}
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    let ledgerAfter := ActionStep.occurrenceLedger step proofPosition ledger
    let successorStatic :=
      reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
        speculativeSaveRuntimeRuleBundle.payloadRows
    ∀ row, row ∈ cFireRuleScopedSourceExecFact space compressedSaveDirective →
      row ∈ canonicalBoundaryRows context after ledgerAfter scannerAfter ++
        successorStatic := by
  dsimp only
  obtain ⟨stackPrefix, stackEq⟩ := List.getLast?_eq_some_iff.mp stackTop
  have stackPositive : 0 < before.stack.length := by
    rw [stackEq]
    simp
  exact physical_save_result_rows_within_successor_of_frame ledger proofPosition
    receipt step stackTop nodeLookup occurrenceLookup represented
    (reservedSaveStaticFrame_supportFor context before heapCapacity nodeCapacity
      stackCapacity (before.stack.length - 1) heapAvailable (by omega)
      (by omega))
    (reservedSaveStaticFrame_frontierAuthority context before heapCapacity
      nodeCapacity stackCapacity (before.stack.length - 1) heapAvailable
      (by omega) (by omega))
    (reservedSaveStaticFrame_capabilities context heapCapacity nodeCapacity
      stackCapacity)
    (physical_reserved_save_matcher_self_replay represented)

/-- Under the explicit successor duplicate-freedom obligations, one reserved
save returns to the same physical representation relation with the updated
source state, occurrence ledger, scanner, and activated runtime frame. -/
theorem physical_reserved_save_returns_to_boundary_of_successor_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (sourceStep : ActionStep before .save after)
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space)
    (successorListNodup :
      (canonicalBoundaryRows context after
          (ActionStep.occurrenceLedger sourceStep proofPosition ledger)
          scannerAfter ++
        (reservedSaveStaticFrame context heapCapacity nodeCapacity
          stackCapacity ++ speculativeSaveRuntimeRuleBundle.payloadRows)).Nodup)
    (successorMorkNodup : MorkSupportNodup
      (canonicalBoundaryRows context after
          (ActionStep.occurrenceLedger sourceStep proofPosition ledger)
          scannerAfter ++
        (reservedSaveStaticFrame context heapCapacity nodeCapacity
          stackCapacity ++ speculativeSaveRuntimeRuleBundle.payloadRows))) :
    PhysicalRunningBoundary context after
      (ActionStep.occurrenceLedger sourceStep proofPosition ledger) scannerAfter
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
        speculativeSaveRuntimeRuleBundle.payloadRows)
      (cFireRuleScopedSourceExecFact space compressedSaveDirective) := by
  obtain ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
      occurrenceLookup, _heapExact⟩ :=
    displayedHeap_save_exact ledger proofPosition sourceStep
  let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
  let successor := canonicalBoundaryRows context after
      (ActionStep.occurrenceLedger sourceStep proofPosition ledger) scannerAfter ++
    (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
      speculativeSaveRuntimeRuleBundle.payloadRows)
  have within : ∀ row ∈ result, row ∈ successor := by
    intro row member
    simpa [result, successor] using
      physical_reserved_save_result_rows_within_successor ledger proofPosition
        receipt sourceStep stackTop nodeLookup occurrenceLookup heapAvailable
        stackFits represented row (by simpa [result] using member)
  have covered : ∀ row ∈ successor,
      morkSupportContains result row = true := by
    intro row member
    simpa [result, successor] using
      physical_reserved_save_successor_support_complete ledger proofPosition
        receipt sourceStep stackTop nodeLookup occurrenceLookup heapAvailable
        stackFits represented row (by simpa [successor] using member)
  have exactRows : ∀ row, row ∈ result ↔ row ∈ successor := by
    intro row
    constructor
    · exact within row
    · intro member
      exact mem_of_morkSupportContains_of_reference successorMorkNodup member
        within (covered row member)
  have resultListNodup : result.Nodup := by
    exact cFireRuleScopedSourceExecFact_list_nodup space
      compressedSaveDirective represented.list_nodup
  have resultMorkNodup : MorkSupportNodup result := by
    exact cFireRuleScopedSourceExecFact_mork_nodup space
      compressedSaveDirective represented.mork_nodup
  have rowsPerm : result.Perm successor :=
    (List.perm_ext_iff_of_nodup resultListNodup successorListNodup).2 exactRows
  have successorClean : StaticFrame
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
        speculativeSaveRuntimeRuleBundle.payloadRows) := by
    intro row member
    rcases List.mem_append.mp member with old | payload
    · exact represented.semantic.staticFrame_clean row old
    · simp only [SaveRuntimeRuleBundle.payloadRows,
        speculativeSaveRuntimeRuleBundle, List.mem_cons, List.not_mem_nil,
        or_false] at payload
      rcases payload with rfl | rfl | rfl | rfl | rfl | rfl
      · exact speculativeSaveRuntimeRuleAuthority.prefixStatic
      · exact speculativeSaveRuntimeRuleAuthority.terminalStatic
      · exact speculativeSaveRuntimeRuleAuthority.proofStatic
      · exact speculativeSaveRuntimeRuleAuthority.invalidByteStatic
      · exact speculativeSaveRuntimeRuleAuthority.questionStatic
      · exact speculativeSaveRuntimeRuleAuthority.questionOpenFaultStatic
  exact
    { semantic :=
        { source_wellFormed :=
            represented.semantic.source_wellFormed.actionStep sourceStep
          staticFrame_clean := successorClean
          exact_rows := by simpa [result, successor] using exactRows }
      rows_perm := by simpa [result, successor] using rowsPerm
      list_nodup := by simpa [result] using resultListNodup
      mork_nodup := by simpa [result] using resultMorkNodup }

/-- The physical scheduler selects the source-derived save directive from any
permutation of the finite reserved boundary. -/
theorem physical_reserved_save_ruleScoped_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state} {scanner : ScannerBoundary}
    {heapCapacity nodeCapacity stackCapacity : Nat} {space : List Atom}
    (represented : PhysicalRunningBoundary context state ledger scanner
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (cFireRuleScopedSourceExecFact space compressedSaveDirective) := by
  unfold cRuleScopedSourceWorkQueueStep
  rw [physical_reserved_save_supported represented]
  rfl

/-- The reserved physical frame reconstructs the same source-derived save
output witness as the one-edge frame, without accepting a target-supplied
node, occurrence, or matcher substitution. -/
def physical_reserved_save_output_witness
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    {heapCapacity nodeCapacity stackCapacity : Nat}
    {space : List Atom}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (sourceStep : ActionStep before .save after)
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    PhysicalSaveOutputWitness context before after ledger scannerBefore
      scannerAfter space := by
  obtain ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup,
      occurrenceLookup, _heapExact⟩ := displayedHeap_save_exact ledger 0 sourceStep
  exact
    ⟨nodeId, node, sourceOccurrence, stackTop, nodeLookup, occurrenceLookup,
      physical_reserved_source_save_exact_match ledger receipt sourceStep
        stackTop nodeLookup occurrenceLookup heapAvailable stackFits represented⟩

/-- A source save over the finite reservation is an actual one-transition
MORK segment with OSLF classification and preservation of both list and
physical-support uniqueness. -/
def physical_reserved_save_scheduled_segment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    {heapCapacity nodeCapacity stackCapacity : Nat}
    {space : List Atom}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (sourceStep : ActionStep before .save after)
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length ≤ stackCapacity)
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space) :
    let result := cFireRuleScopedSourceExecFact space compressedSaveDirective
    PhysicalSaveScheduledSegment context before after ledger scannerBefore
      scannerAfter occurrence
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space result := by
  dsimp only
  have moved := physical_reserved_save_ruleScoped_step represented
  have preserved := physical_boundary_ruleScoped_step_nodup represented
    .leaveInert moved
  have sourceOutput : PhysicalSaveOutputWitness context before after ledger
      scannerBefore scannerAfter space :=
    physical_reserved_save_output_witness receipt sourceStep heapAvailable
      stackFits represented
  let executionTrace : CRuleScopedTrace .leaveInert 1 space
      (cFireRuleScopedSourceExecFact space compressedSaveDirective) :=
    .step moved (.refl)
  exact
    { scannerReceipt := receipt
      sourceStep := sourceStep
      representedBefore := represented
      sourceOutput := sourceOutput
      concreteStep := moved
      nativeType :=
        (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          .leaveInert space
          (cFireRuleScopedSourceExecFact space compressedSaveDirective)).2 moved
      trace := executionTrace
      traceSteps := by rfl
      resultListNodup := preserved.1
      resultMorkNodup := preserved.2 }

/-- One reserved save, viewed as a complete boundary-to-boundary segment.
The successor collision premises are explicit because source well-formedness
alone does not yet exclude every collision in the concrete row encoding. -/
structure PhysicalReservedSaveBoundarySegment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before after : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence)
    (heapCapacity nodeCapacity stackCapacity : Nat)
    (space result : List Atom) : Type where
  scheduled : PhysicalSaveScheduledSegment context before after ledger
    scannerBefore scannerAfter occurrence
    (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
    space result
  scannerStep : SourceStep (.request occurrence scannerBefore.phase)
    (.outcome occurrence (.decoded [.save] scannerAfter.phase))
  sourceBoundaryAfter : SourceBoundaryWellFormed context after
  occurrenceLedgerUnchanged :
    (ActionStep.occurrenceLedger scheduled.sourceStep proofPosition
      ledger).occurrences = ledger.occurrences
  representedAfter : PhysicalRunningBoundary context after
    (ActionStep.occurrenceLedger scheduled.sourceStep proofPosition ledger)
    scannerAfter
    (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity ++
      speculativeSaveRuntimeRuleBundle.payloadRows)
    result
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 1
    space result)

/-- The scanner-decoded `Z`, the source save, and the actual rule-scoped MORK
transition form one complete OSLF-classified segment returning to the shared
physical running boundary. -/
def physical_reserved_save_boundary_segment_of_successor_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before after : MachineState source target}
    {ledger : NodeOccurrenceLedger before} (proofPosition : Nat)
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence}
    (receipt : SaveByteReceipt context scannerBefore scannerAfter occurrence)
    (sourceStep : ActionStep before .save after)
    {heapCapacity nodeCapacity stackCapacity : Nat}
    (heapAvailable : before.heap.length < heapCapacity)
    (stackFits : before.stack.length <= stackCapacity)
    {space : List Atom}
    (represented : PhysicalRunningBoundary context before ledger scannerBefore
      (reservedSaveStaticFrame context heapCapacity nodeCapacity stackCapacity)
      space)
    (successorListNodup :
      (canonicalBoundaryRows context after
          (ActionStep.occurrenceLedger sourceStep proofPosition ledger)
          scannerAfter ++
        (reservedSaveStaticFrame context heapCapacity nodeCapacity
          stackCapacity ++ speculativeSaveRuntimeRuleBundle.payloadRows)).Nodup)
    (successorMorkNodup : MorkSupportNodup
      (canonicalBoundaryRows context after
          (ActionStep.occurrenceLedger sourceStep proofPosition ledger)
          scannerAfter ++
        (reservedSaveStaticFrame context heapCapacity nodeCapacity
          stackCapacity ++ speculativeSaveRuntimeRuleBundle.payloadRows))) :
    let result :=
      cFireRuleScopedSourceExecFact space compressedSaveDirective
    PhysicalReservedSaveBoundarySegment context before after ledger
      proofPosition scannerBefore scannerAfter occurrence heapCapacity
      nodeCapacity stackCapacity space result := by
  dsimp only
  let scheduled := physical_reserved_save_scheduled_segment receipt sourceStep
    heapAvailable stackFits represented
  have returned :=
    physical_reserved_save_returns_to_boundary_of_successor_nodup ledger
      proofPosition receipt sourceStep heapAvailable stackFits represented
      successorListNodup successorMorkNodup
  exact
    { scheduled := scheduled
      scannerStep := receipt.sourceStep
      sourceBoundaryAfter := represented.semantic.source_wellFormed.actionStep
        sourceStep
      occurrenceLedgerUnchanged :=
        ActionStep.save_occurrenceLedger_unchanged sourceStep proofPosition
          ledger
      representedAfter := returned
      nativeTypeTrace := ⟨scheduled.trace.toNativeTypeTrace⟩ }

/-- The source-data artifact supplies the current heap edge whenever its
linear reservation has not been exhausted. -/
theorem transformedProofData_supplies_live_save_heap_edge
    {source : SourcePrefix} (scopeOwner proofOwner : Atom)
    (sourceState : SourceState) (theoremLabel : String)
    (formula : ConstantHeadedFormula) (explicitLabels : List String)
    (bodyWords : List (List UInt8))
    (heap : List (HeapEntry source))
    (available : heap.length <
      compressedHeapCapacity sourceState formula explicitLabels bodyWords) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat heap.length).atom
          (CompressedIndexCode.ofNat (heap.length + 1)).atom ∈
        (transformCompressedProofData scopeOwner proofOwner sourceState
          theoremLabel formula explicitLabels bodyWords).heapSuccessors := by
  exact (liveHeapFrontier_mem_transformedHeapSuccessors_iff scopeOwner
    proofOwner sourceState theoremLabel formula explicitLabels bodyWords
    heap).2 available

/-- Two remaining capacity cells admit two consecutive saves without changing
the reserved spine. -/
theorem two_consecutive_save_edges_are_reserved
    (proofOwner : Atom) (heapCapacity position : Nat)
    (twoAvailable : position + 1 < heapCapacity) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom ∈
        compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
          heapCapacity ∧
      compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat (position + 1)).atom
          (CompressedIndexCode.ofNat (position + 2)).atom ∈
        compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
          heapCapacity := by
  exact
    ⟨compressedIndexSuccessorRow_mem _ heapCapacity position (by omega),
      compressedIndexSuccessorRow_mem _ heapCapacity (position + 1)
        twoAvailable⟩

/-- Negative capacity control: reserving only the current edge cannot justify
a second save. -/
theorem one_edge_reservation_does_not_admit_second_save
    (proofOwner : Atom) (position : Nat) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat (position + 1)).atom
          (CompressedIndexCode.ofNat (position + 2)).atom ∉
        compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
          (position + 1) := by
  exact compressedIndexFrontier_has_no_successor _ (position + 1)

#print axioms current_heap_successor_mem_reservedIndexRows
#print axioms current_stack_successor_mem_reservedIndexRows
#print axioms compressedIndexSuccessorRows_current_functional
#print axioms compressedIndexSuccessorRows_predecessor_functional
#print axioms reservedIndexRows_heap_current_functional
#print axioms reservedIndexRows_stack_predecessor_functional
#print axioms reservedSaveStaticFrame_supportFor
#print axioms reservedSaveStaticFrame_frontierAuthority
#print axioms reservedIndexRows_no_supported
#print axioms reservedIndexRows_capabilities
#print axioms reservedSaveStaticFrame_capabilities
#print axioms reservedSaveStaticFrame_supported
#print axioms physical_reserved_save_supported
#print axioms physical_reserved_save_matcher_self_replay
#print axioms physical_reserved_save_preserves_old_row
#print axioms physical_reserved_source_save_exact_match
#print axioms physical_reserved_save_self_support_present
#print axioms physical_reserved_save_successor_support_present
#print axioms physical_reserved_save_successor_support_complete
#print axioms physical_reserved_save_result_rows_within_successor
#print axioms physical_reserved_save_returns_to_boundary_of_successor_nodup
#print axioms physical_reserved_save_ruleScoped_step
#print axioms physical_reserved_save_output_witness
#print axioms physical_reserved_save_scheduled_segment
#print axioms physical_reserved_save_boundary_segment_of_successor_nodup
#print axioms transformedProofData_supplies_live_save_heap_edge
#print axioms two_consecutive_save_edges_are_reserved
#print axioms one_edge_reservation_does_not_admit_second_save

end Mettapedia.Languages.Metamath.MM2CompressedProofReservedSaveFrame
