import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary

/-!
# Scheduled physical drain before compressed assertion dispatch

After a compact assertion launches, four older lookup probes remain as
executable shells.  Their data premises have already been consumed.  This
module proves that the real least-key MORK scheduler selects and drains those
shells in priority order, preserving exact occurrence multiplicity and the
predecessor-head absence invariant at every boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceInventory
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- The successive physical workspaces after consuming each obsolete probe. -/
def afterProofProbe (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact space compressedProofStepDirective

def afterLookupFaultProbe (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact (afterProofProbe space)
    compressedHeapLookupFaultDirective

def afterCursorAssertionProbe (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact (afterLookupFaultProbe space)
    decoratedCursorAssertionDirective

def afterLookupAdvanceProbe (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact (afterCursorAssertionProbe space)
    compressedHeapLookupAdvanceDirective

def PostLaunchCandidatesWithin (space : List Atom) : Prop :=
  ∀ candidate ∈ cSupportedSourceExecFacts space,
    candidate ∈ assertionBridgePostLaunchDirectives

def NoAssertionPredecessorHeads (space : List Atom) : Prop :=
  ∀ atom ∈ space,
    compressedDynamicRowHead? atom ≠ some "mm-compressed-step-pending" ∧
      compressedDynamicRowHead? atom ≠ some "mm-compressed-heap-lookup"

/-- Exact hypotheses supplied by the source-derived launch boundary. -/
structure AssertionPredecessorDrainReady (space : List Atom) : Prop where
  listNodup : space.Nodup
  morkNodup : MorkSupportNodup space
  noPredecessorHeads : NoAssertionPredecessorHeads space
  candidatesWithin : PostLaunchCandidatesWithin space
  proofPresent : compressedProofStepDirective ∈ cSupportedSourceExecFacts space
  cursorAssertionPresent :
    decoratedCursorAssertionDirective ∈ cSupportedSourceExecFacts space
  lookupFaultPresent :
    compressedHeapLookupFaultDirective ∈ cSupportedSourceExecFacts space
  lookupAdvancePresent :
    compressedHeapLookupAdvanceDirective ∈ cSupportedSourceExecFacts space

theorem postLaunchCandidatesWithin_of_atomsWithin
    {space : List Atom}
    (within : AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate ∈ assertionBridgePostLaunchDirectives) space) :
    PostLaunchCandidatesWithin space := by
  intro candidate member
  rcases List.mem_filterMap.mp member with ⟨atom, atomMember, decoded⟩
  exact within atom atomMember candidate decoded

theorem proofProbe_preempts_decoratedCursorAssertion :
    lexLt (SchedulerKey.key compressedProofStepDirective)
      (SchedulerKey.key decoratedCursorAssertionDirective) = true := by
  decide +kernel

theorem lookupFaultProbe_preempts_decoratedCursorAssertion :
    lexLt (SchedulerKey.key compressedHeapLookupFaultDirective)
      (SchedulerKey.key decoratedCursorAssertionDirective) = true := by
  decide +kernel

theorem decoratedCursorAssertion_preempts_lookupAdvanceProbe :
    lexLt (SchedulerKey.key decoratedCursorAssertionDirective)
      (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true := by
  decide +kernel

private theorem right_ne_left_of_lexLt
    {left right : SourceExecFact}
    (ordered : lexLt (SchedulerKey.key left)
      (SchedulerKey.key right) = true) :
    right ≠ left := by
  intro equal
  subst right
  rw [lexLt_irrefl] at ordered
  contradiction

private theorem proofProbe_strict_minimum
    {space : List Atom} (within : PostLaunchCandidatesWithin space)
    {candidate : SourceExecFact}
    (member : candidate ∈ cSupportedSourceExecFacts space)
    (different : candidate ≠ compressedProofStepDirective) :
    lexLt (SchedulerKey.key compressedProofStepDirective)
        (SchedulerKey.key candidate) = true := by
  have allowed := within candidate member
  simp only [assertionBridgePostLaunchDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at allowed
  rcases allowed with proof | cursor | fault | advance | rejoin | bridge
  · exact (different proof).elim
  all_goals (subst candidate; decide +kernel)

private theorem lookupFaultProbe_strict_minimum
    {space : List Atom} (within : PostLaunchCandidatesWithin space)
    (proofAbsent : compressedProofStepDirective ∉
      cSupportedSourceExecFacts space)
    {candidate : SourceExecFact}
    (member : candidate ∈ cSupportedSourceExecFacts space)
    (different : candidate ≠ compressedHeapLookupFaultDirective) :
    lexLt (SchedulerKey.key compressedHeapLookupFaultDirective)
        (SchedulerKey.key candidate) = true := by
  have allowed := within candidate member
  simp only [assertionBridgePostLaunchDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at allowed
  rcases allowed with proof | cursor | fault | advance | rejoin | bridge
  · subst candidate; exact (proofAbsent member).elim
  · subst candidate; decide +kernel
  · exact (different fault).elim
  all_goals (subst candidate; decide +kernel)

private theorem cursorAssertionProbe_strict_minimum
    {space : List Atom} (within : PostLaunchCandidatesWithin space)
    (proofAbsent : compressedProofStepDirective ∉
      cSupportedSourceExecFacts space)
    (faultAbsent : compressedHeapLookupFaultDirective ∉
      cSupportedSourceExecFacts space)
    {candidate : SourceExecFact}
    (member : candidate ∈ cSupportedSourceExecFacts space)
    (different : candidate ≠ decoratedCursorAssertionDirective) :
    lexLt (SchedulerKey.key decoratedCursorAssertionDirective)
        (SchedulerKey.key candidate) = true := by
  have allowed := within candidate member
  simp only [assertionBridgePostLaunchDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at allowed
  rcases allowed with proof | cursor | fault | advance | rejoin | bridge
  · subst candidate; exact (proofAbsent member).elim
  · exact (different cursor).elim
  · subst candidate; exact (faultAbsent member).elim
  all_goals (subst candidate; decide +kernel)

private theorem lookupAdvanceProbe_strict_minimum
    {space : List Atom} (within : PostLaunchCandidatesWithin space)
    (proofAbsent : compressedProofStepDirective ∉
      cSupportedSourceExecFacts space)
    (cursorAbsent : decoratedCursorAssertionDirective ∉
      cSupportedSourceExecFacts space)
    (faultAbsent : compressedHeapLookupFaultDirective ∉
      cSupportedSourceExecFacts space)
    {candidate : SourceExecFact}
    (member : candidate ∈ cSupportedSourceExecFacts space)
    (different : candidate ≠ compressedHeapLookupAdvanceDirective) :
    lexLt (SchedulerKey.key compressedHeapLookupAdvanceDirective)
        (SchedulerKey.key candidate) = true := by
  have allowed := within candidate member
  simp only [assertionBridgePostLaunchDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at allowed
  rcases allowed with proof | cursor | fault | advance | rejoin | bridge
  · subst candidate; exact (proofAbsent member).elim
  · subst candidate; exact (cursorAbsent member).elim
  · subst candidate; exact (faultAbsent member).elim
  · exact (different advance).elim
  all_goals (subst candidate; decide +kernel)

private theorem postLaunchCandidatesWithin_of_erase
    {space : List Atom} {directive : SourceExecFact}
    (within : PostLaunchCandidatesWithin space)
    (inventory : cSupportedSourceExecFacts
        (cFireRuleScopedSourceExecFact space directive) =
      (cSupportedSourceExecFacts space).erase directive) :
    PostLaunchCandidatesWithin
      (cFireRuleScopedSourceExecFact space directive) := by
  intro candidate member
  rw [inventory] at member
  exact within candidate (List.mem_of_mem_erase member)

/-- The physical result relates an initial workspace to an explicit endpoint
and packages every scheduled transition, its exact candidate-list erosion,
and the OSLF classification of the same trace. -/
structure PhysicalAssertionPredecessorDrain
    (space final : List Atom) : Prop where
  proofStep : cRuleScopedSourceWorkQueueStep .leaveInert space =
    some (afterProofProbe space)
  lookupFaultStep :
    cRuleScopedSourceWorkQueueStep .leaveInert (afterProofProbe space) =
      some (afterLookupFaultProbe space)
  cursorAssertionStep :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (afterLookupFaultProbe space) =
      some (afterCursorAssertionProbe space)
  lookupAdvanceStep :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (afterCursorAssertionProbe space) =
      some final
  concreteTrace : Nonempty (CRuleScopedTrace .leaveInert 4 space
    final)
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 4 space
    final)
  finalExact : final = afterLookupAdvanceProbe space
  finalCandidates :
    cSupportedSourceExecFacts final =
      ((((cSupportedSourceExecFacts space).erase
        compressedProofStepDirective).erase
          compressedHeapLookupFaultDirective).erase
            decoratedCursorAssertionDirective).erase
              compressedHeapLookupAdvanceDirective
  finalNoPredecessorHeads :
    NoAssertionPredecessorHeads final
  finalListNodup : final.Nodup
  finalMorkNodup : MorkSupportNodup final

theorem physical_assertion_predecessor_drain
    (space : List Atom) (ready : AssertionPredecessorDrainReady space) :
    PhysicalAssertionPredecessorDrain space
      (afterLookupAdvanceProbe space) := by
  have noProof := ruleScoped_guarded_no_matches_of_matcher_nil space
    compressedProofStepDirective
    (compressedProofStep_no_matches_of_no_predecessor_heads space
      ready.noPredecessorHeads)
  have proofSelected : selectNextScheduled (cSupportedSourceExecFacts space) =
      some compressedProofStepDirective :=
    selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _
      ready.proofPresent (fun candidate member different =>
        proofProbe_strict_minimum ready.candidatesWithin member different)
  have proofStep : cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (afterProofProbe space) := by
    exact cRuleScopedSourceWorkQueueStep_of_selected space
      compressedProofStepDirective proofSelected
  have proofInventory : cSupportedSourceExecFacts (afterProofProbe space) =
      (cSupportedSourceExecFacts space).erase
        compressedProofStepDirective := by
    exact cSupportedSourceExecFacts_after_ruleScoped_inert space
      compressedProofStepDirective ready.listNodup ready.morkNodup
      (sourceExecFact_atom_mem_of_mem_supported ready.proofPresent)
      extract_compressedProofStepRule_exact noProof
  have proofWithin : PostLaunchCandidatesWithin (afterProofProbe space) :=
    postLaunchCandidatesWithin_of_erase ready.candidatesWithin proofInventory
  have proofListNodup : (afterProofProbe space).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ ready.listNodup
  have proofMorkNodup : MorkSupportNodup (afterProofProbe space) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ ready.morkNodup
  have proofNoHeads : NoAssertionPredecessorHeads (afterProofProbe space) := by
    exact predecessor_heads_absent_after_ruleScoped_no_match space
      compressedProofStepDirective ready.noPredecessorHeads noProof
  have initialCandidateNodup :=
    cSupportedSourceExecFacts_nodup_of_space_nodup ready.listNodup
  have proofAbsent : compressedProofStepDirective ∉
      cSupportedSourceExecFacts (afterProofProbe space) := by
    rw [proofInventory]
    exact initialCandidateNodup.not_mem_erase
  have faultPresent : compressedHeapLookupFaultDirective ∈
      cSupportedSourceExecFacts (afterProofProbe space) := by
    rw [proofInventory]
    exact (List.mem_erase_of_ne
      (right_ne_left_of_lexLt cursor_proof_preempts_cursor_fault)).2
        ready.lookupFaultPresent
  have noFault := ruleScoped_guarded_no_matches_of_matcher_nil
    (afterProofProbe space) compressedHeapLookupFaultDirective
    (compressedHeapLookupFault_no_matches_of_no_predecessor_heads
      (afterProofProbe space) proofNoHeads)
  have faultSelected : selectNextScheduled
      (cSupportedSourceExecFacts (afterProofProbe space)) =
        some compressedHeapLookupFaultDirective :=
    selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _ faultPresent
      (fun candidate member different =>
        lookupFaultProbe_strict_minimum proofWithin proofAbsent member different)
  have faultStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (afterProofProbe space) = some (afterLookupFaultProbe space) := by
    exact cRuleScopedSourceWorkQueueStep_of_selected _
      compressedHeapLookupFaultDirective faultSelected
  have faultInventory : cSupportedSourceExecFacts
      (afterLookupFaultProbe space) =
        (cSupportedSourceExecFacts
          (afterProofProbe space)).erase
            compressedHeapLookupFaultDirective := by
    exact cSupportedSourceExecFacts_after_ruleScoped_inert _
      compressedHeapLookupFaultDirective proofListNodup proofMorkNodup
      (sourceExecFact_atom_mem_of_mem_supported faultPresent)
      extract_compressedHeapLookupFaultRule_exact noFault
  have faultWithin : PostLaunchCandidatesWithin
      (afterLookupFaultProbe space) :=
    postLaunchCandidatesWithin_of_erase proofWithin faultInventory
  have faultListNodup : (afterLookupFaultProbe space).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ proofListNodup
  have faultMorkNodup : MorkSupportNodup (afterLookupFaultProbe space) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ proofMorkNodup
  have faultNoHeads : NoAssertionPredecessorHeads
      (afterLookupFaultProbe space) := by
    exact predecessor_heads_absent_after_ruleScoped_no_match _
      compressedHeapLookupFaultDirective proofNoHeads noFault
  have faultCandidateNodup :=
    cSupportedSourceExecFacts_nodup_of_space_nodup proofListNodup
  have proofAbsentAfterFault : compressedProofStepDirective ∉
      cSupportedSourceExecFacts (afterLookupFaultProbe space) := by
    rw [faultInventory]
    exact fun member => proofAbsent (List.mem_of_mem_erase member)
  have faultAbsent : compressedHeapLookupFaultDirective ∉
      cSupportedSourceExecFacts (afterLookupFaultProbe space) := by
    rw [faultInventory]
    exact faultCandidateNodup.not_mem_erase
  have cursorPresentAfterFault : decoratedCursorAssertionDirective ∈
      cSupportedSourceExecFacts (afterLookupFaultProbe space) := by
    rw [faultInventory, proofInventory]
    apply (List.mem_erase_of_ne
      (right_ne_left_of_lexLt
        lookupFaultProbe_preempts_decoratedCursorAssertion)).2
    exact (List.mem_erase_of_ne
      (right_ne_left_of_lexLt
        proofProbe_preempts_decoratedCursorAssertion)).2
      ready.cursorAssertionPresent

  have noCursor := ruleScoped_guarded_no_matches_of_matcher_nil
    (afterLookupFaultProbe space) decoratedCursorAssertionDirective
    (decoratedCursorAssertion_no_matches_of_no_predecessor_heads
      (afterLookupFaultProbe space) faultNoHeads)
  have cursorSelected : selectNextScheduled
      (cSupportedSourceExecFacts (afterLookupFaultProbe space)) =
        some decoratedCursorAssertionDirective :=
    selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _
      cursorPresentAfterFault (fun candidate member different =>
        cursorAssertionProbe_strict_minimum faultWithin proofAbsentAfterFault
          faultAbsent member different)
  have cursorStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (afterLookupFaultProbe space) = some (afterCursorAssertionProbe space) := by
    exact cRuleScopedSourceWorkQueueStep_of_selected _
      decoratedCursorAssertionDirective cursorSelected
  have cursorInventory : cSupportedSourceExecFacts
      (afterCursorAssertionProbe space) =
        (cSupportedSourceExecFacts (afterLookupFaultProbe space)).erase
          decoratedCursorAssertionDirective := by
    exact cSupportedSourceExecFacts_after_ruleScoped_inert _
      decoratedCursorAssertionDirective faultListNodup faultMorkNodup
      (sourceExecFact_atom_mem_of_mem_supported cursorPresentAfterFault)
      (by
        rw [decoratedCursorAssertionDirective_atom_exact]
        exact extract_decoratedCursorAssertionRule_exact)
      noCursor
  have cursorWithin : PostLaunchCandidatesWithin
      (afterCursorAssertionProbe space) :=
    postLaunchCandidatesWithin_of_erase faultWithin cursorInventory
  have cursorListNodup : (afterCursorAssertionProbe space).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ faultListNodup
  have cursorMorkNodup : MorkSupportNodup
      (afterCursorAssertionProbe space) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ faultMorkNodup
  have cursorNoHeads : NoAssertionPredecessorHeads
      (afterCursorAssertionProbe space) := by
    exact predecessor_heads_absent_after_ruleScoped_no_match _
      decoratedCursorAssertionDirective faultNoHeads noCursor
  have cursorCandidateNodup :=
    cSupportedSourceExecFacts_nodup_of_space_nodup faultListNodup
  have proofAbsentAfterCursor : compressedProofStepDirective ∉
      cSupportedSourceExecFacts (afterCursorAssertionProbe space) := by
    rw [cursorInventory]
    exact fun member => proofAbsentAfterFault (List.mem_of_mem_erase member)
  have faultAbsentAfterCursor : compressedHeapLookupFaultDirective ∉
      cSupportedSourceExecFacts (afterCursorAssertionProbe space) := by
    rw [cursorInventory]
    exact fun member => faultAbsent (List.mem_of_mem_erase member)
  have cursorAbsent : decoratedCursorAssertionDirective ∉
      cSupportedSourceExecFacts (afterCursorAssertionProbe space) := by
    rw [cursorInventory]
    exact cursorCandidateNodup.not_mem_erase
  have advancePresent : compressedHeapLookupAdvanceDirective ∈
      cSupportedSourceExecFacts (afterCursorAssertionProbe space) := by
    rw [cursorInventory, faultInventory, proofInventory]
    apply (List.mem_erase_of_ne
      (right_ne_left_of_lexLt
        decoratedCursorAssertion_preempts_lookupAdvanceProbe)).2
    apply (List.mem_erase_of_ne
      (right_ne_left_of_lexLt cursor_fault_preempts_cursor_advance)).2
    exact (List.mem_erase_of_ne
      (right_ne_left_of_lexLt cursor_proof_preempts_cursor_advance)).2
      ready.lookupAdvancePresent

  have noAdvance := ruleScoped_guarded_no_matches_of_matcher_nil
    (afterCursorAssertionProbe space) compressedHeapLookupAdvanceDirective
    (compressedHeapLookupAdvance_no_matches_of_no_predecessor_heads
      (afterCursorAssertionProbe space) cursorNoHeads)
  have advanceSelected : selectNextScheduled
      (cSupportedSourceExecFacts (afterCursorAssertionProbe space)) =
        some compressedHeapLookupAdvanceDirective :=
    selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _ advancePresent
      (fun candidate member different =>
        lookupAdvanceProbe_strict_minimum cursorWithin proofAbsentAfterCursor
          cursorAbsent faultAbsentAfterCursor member different)
  have advanceStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (afterCursorAssertionProbe space) =
        some (afterLookupAdvanceProbe space) := by
    exact cRuleScopedSourceWorkQueueStep_of_selected _
      compressedHeapLookupAdvanceDirective advanceSelected
  have advanceInventory : cSupportedSourceExecFacts
      (afterLookupAdvanceProbe space) =
        (cSupportedSourceExecFacts (afterCursorAssertionProbe space)).erase
          compressedHeapLookupAdvanceDirective := by
    exact cSupportedSourceExecFacts_after_ruleScoped_inert _
      compressedHeapLookupAdvanceDirective cursorListNodup cursorMorkNodup
      (sourceExecFact_atom_mem_of_mem_supported advancePresent)
      extract_compressedHeapLookupAdvanceRule_exact noAdvance
  have advanceListNodup : (afterLookupAdvanceProbe space).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ cursorListNodup
  have advanceMorkNodup : MorkSupportNodup
      (afterLookupAdvanceProbe space) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ cursorMorkNodup
  have advanceNoHeads : NoAssertionPredecessorHeads
      (afterLookupAdvanceProbe space) := by
    exact predecessor_heads_absent_after_ruleScoped_no_match _
      compressedHeapLookupAdvanceDirective cursorNoHeads noAdvance
  let trace : CRuleScopedTrace .leaveInert 4 space
      (afterLookupAdvanceProbe space) :=
    .step proofStep (.step faultStep (.step cursorStep
      (.step advanceStep .refl)))
  refine
    { proofStep := proofStep
      lookupFaultStep := faultStep
      cursorAssertionStep := cursorStep
      lookupAdvanceStep := advanceStep
      concreteTrace := ⟨trace⟩
      nativeTypeTrace := ⟨trace.toNativeTypeTrace⟩
      finalExact := rfl
      finalCandidates := ?_
      finalNoPredecessorHeads := advanceNoHeads
      finalListNodup := advanceListNodup
      finalMorkNodup := advanceMorkNodup }
  rw [advanceInventory, cursorInventory, faultInventory, proofInventory]

/-- The actual source-derived post-launch workspace satisfies every premise of
the generic drain theorem. -/
theorem sourceAssertionBridgeLaunchResult_drain_ready
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    AssertionPredecessorDrainReady
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  let result := sourceAssertionBridgeLaunchResult space
  have survives := sourceAssertionBridgeSchedulerSupported_survive_launch
    context state ledger scanner index cursor assertion listNodup morkNodup
  refine
    { listNodup := sourceAssertionBridgeLaunchResult_list_nodup context state
        ledger scanner index cursor assertion listNodup
      morkNodup := sourceAssertionBridgeLaunchResult_mork_nodup context state
        ledger scanner index cursor assertion morkNodup
      noPredecessorHeads :=
        sourceAssertionBridgeLaunchResult_no_predecessor_heads context state
          ledger scanner index cursor assertion listNodup morkNodup
      candidatesWithin := postLaunchCandidatesWithin_of_atomsWithin
        (sourceAssertionBridgeLaunchResult_supported_within context state
          ledger scanner index cursor assertion listNodup morkNodup)
      proofPresent := survives compressedProofStepDirective ?_
      cursorAssertionPresent := survives decoratedCursorAssertionDirective ?_
      lookupFaultPresent := survives compressedHeapLookupFaultDirective ?_
      lookupAdvancePresent := survives compressedHeapLookupAdvanceDirective ?_ }
  all_goals (rw [decoratedDirectAssertionSchedulerFrame_supported]; simp)

/-- Four genuine MORK transitions drain the obsolete lookup shells from every
source-derived physical assertion launch result. -/
theorem sourceAssertionBridgeLaunchResult_physical_drain
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    PhysicalAssertionPredecessorDrain
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion))
      (afterLookupAdvanceProbe
        (sourceAssertionBridgeLaunchResult
          (@sourceDecoratedAssertionBridgeReadySpace source target context state
            ledger scanner index cursor assertion))) := by
  exact physical_assertion_predecessor_drain _
    (sourceAssertionBridgeLaunchResult_drain_ready context state ledger scanner
      index cursor assertion listNodup morkNodup)

#print axioms postLaunchCandidatesWithin_of_atomsWithin
#print axioms physical_assertion_predecessor_drain
#print axioms sourceAssertionBridgeLaunchResult_drain_ready
#print axioms sourceAssertionBridgeLaunchResult_physical_drain

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
