import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalDispatchBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionSupportFrame
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceInventory
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin

/-!
# Physical assertion-to-bridge scheduling

The source-derived compressed assertion launch leaves several older verifier
directives resident.  This module characterizes the supported authority in the
actual MORK successor before proving that those inert shells are drained ahead
of the compact-to-normal bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionSupportFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceInventory
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalDispatchBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Physical result immediately after the assertion launcher fires in one
workspace. -/
def sourceAssertionBridgeLaunchResult (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact space decoratedDirectAssertionDirective

private def sourceDecoratedAssertionBridgeReadyTail
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  let launchContext := directAssertionContextAtBoundary context state scanner
    index cursor assertion
  (([launchContext.pendingRow, launchContext.lookupRow,
     launchContext.heapRow, launchContext.machineRow,
     launchContext.headerRow, launchContext.rejoinCaptureRow,
     decoratedDirectAssertionBridgeCaptureRow] ++
      decoratedDirectAssertionSchedulerFrame) ++
    sourceAssertionAdditionalRows context state ledger scanner index assertion) ++
      normalHandoffBridgeCaptureRows

private theorem sourceDecoratedAssertionBridgeReadySpace_eq_cons
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion =
      decoratedDirectAssertionDirective.atom ::
        sourceDecoratedAssertionBridgeReadyTail context state ledger scanner
          index cursor assertion := by
  rfl

private theorem sourceAssertionBridgeSchedulerFrame_atom_mem_tail
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) {atom : Atom}
    (frameMember : atom ∈ decoratedDirectAssertionSchedulerFrame) :
    atom ∈ sourceDecoratedAssertionBridgeReadyTail context state ledger scanner
      index cursor assertion := by
  unfold sourceDecoratedAssertionBridgeReadyTail
  exact List.mem_append_left normalHandoffBridgeCaptureRows
    (List.mem_append_left
      (sourceAssertionAdditionalRows context state ledger scanner index assertion)
      (List.mem_append_right
        [(directAssertionContextAtBoundary context state scanner index cursor
            assertion).pendingRow,
         (directAssertionContextAtBoundary context state scanner index cursor
            assertion).lookupRow,
         (directAssertionContextAtBoundary context state scanner index cursor
            assertion).heapRow,
         (directAssertionContextAtBoundary context state scanner index cursor
            assertion).machineRow,
         (directAssertionContextAtBoundary context state scanner index cursor
            assertion).headerRow,
         (directAssertionContextAtBoundary context state scanner index cursor
            assertion).rejoinCaptureRow,
         decoratedDirectAssertionBridgeCaptureRow]
        frameMember))

private theorem supported_atom_predecessor_key_safety
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    DecoratedAssertionPredecessorKeySafety atom := by
  obtain ⟨location, input, output, shape⟩ :=
    extractSupportedSourceExecFact_exec_shape decoded
  rw [shape]
  exact expression_head_predecessor_key_safety "exec"
    [location, input, output] (by norm_num) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- A distinct supported executable atom cannot be confused with either the
selected launcher or any of the three data controls removed by that launcher.
Consequently its exact physical representative survives the transaction. -/
private theorem supported_atom_survives_assertion_launch
    {space : List Atom} {candidate : Atom}
    (safe : DecoratedAssertionPredecessorKeySafety candidate)
    (candidateDifferent :
      candidate ≠ decoratedDirectAssertionDirective.atom)
    (candidatePresent : candidate ∈ space)
    (launcherPresent : decoratedDirectAssertionDirective.atom ∈ space)
    (morkNodup : MorkSupportNodup space) :
    candidate ∈ cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective := by
  have keyDifferent :
      morkSupportKey candidate ≠
        morkSupportKey decoratedDirectAssertionDirective.atom := by
    intro equal
    exact candidateDifferent
      (morkSupportKey_injective_on morkNodup candidatePresent launcherPresent
        equal)
  have livePresent : candidate ∈
      morkEraseSupport space decoratedDirectAssertionDirective.atom :=
    mem_morkEraseSupport_of_mem_of_key_ne candidatePresent keyDifferent
  exact physical_decorated_assertion_preserves_row_of_key_safety safe livePresent

private theorem sourceAssertionBridgeSchedulerFrame_atom_ne_launcher
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup) :
    ∀ {atom : Atom}, atom ∈ decoratedDirectAssertionSchedulerFrame →
      atom ≠ decoratedDirectAssertionDirective.atom := by
  rw [sourceDecoratedAssertionBridgeReadySpace_eq_cons] at listNodup
  intro atom member equal
  apply listNodup.notMem
  rw [← equal]
  exact sourceAssertionBridgeSchedulerFrame_atom_mem_tail context state ledger
    scanner index cursor assertion member

private theorem sourceAssertionBridgeSchedulerDirective_survives_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (candidate : Atom)
    (member : candidate ∈ decoratedDirectAssertionSchedulerFrame)
    (safe : DecoratedAssertionPredecessorKeySafety candidate)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    candidate ∈ sourceAssertionBridgeLaunchResult
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  have candidatePresent : candidate ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion := by
    rw [sourceDecoratedAssertionBridgeReadySpace_eq_cons]
    exact List.mem_cons_of_mem _
      (sourceAssertionBridgeSchedulerFrame_atom_mem_tail context state ledger
        scanner index cursor assertion member)
  have launcherPresent : decoratedDirectAssertionDirective.atom ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion := by
    rw [sourceDecoratedAssertionBridgeReadySpace_eq_cons]
    exact List.mem_cons_self
  unfold sourceAssertionBridgeLaunchResult
  exact supported_atom_survives_assertion_launch safe
    (sourceAssertionBridgeSchedulerFrame_atom_ne_launcher context state ledger
      scanner index cursor assertion listNodup member)
    candidatePresent launcherPresent morkNodup

theorem sourceAssertionBridgeSchedulerAtom_survives_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    {atom : Atom} {directive : SourceExecFact}
    (member : atom ∈ decoratedDirectAssertionSchedulerFrame)
    (decoded : extractSupportedSourceExecFact atom = some directive)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    atom ∈ sourceAssertionBridgeLaunchResult
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  exact @sourceAssertionBridgeSchedulerDirective_survives_launch source target
    context state ledger scanner index cursor assertion
    atom member (supported_atom_predecessor_key_safety decoded) listNodup
    morkNodup

/-- Every supported scheduler candidate inherited from the compact lookup has
an exact physical representative after the assertion launcher fires. -/
theorem sourceAssertionBridgeSchedulerSupported_survive_launch
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
    ∀ directive ∈
        cSupportedSourceExecFacts decoratedDirectAssertionSchedulerFrame,
      directive ∈ cSupportedSourceExecFacts
        (sourceAssertionBridgeLaunchResult
          (@sourceDecoratedAssertionBridgeReadySpace source target context state
            ledger scanner index cursor assertion)) := by
  intro directive directiveMember
  rcases List.mem_filterMap.mp directiveMember with
    ⟨atom, atomMember, decoded⟩
  exact List.mem_filterMap.mpr
    ⟨atom,
      sourceAssertionBridgeSchedulerAtom_survives_launch context state ledger
        scanner index cursor assertion atomMember decoded listNodup morkNodup,
      decoded⟩

private theorem decoratedAssertionGeneratedSupportedAtom_post_launch
    {atom : Atom} :
    DecoratedAssertionGeneratedSupportedAtom atom →
      (∀ candidate, extractSupportedSourceExecFact atom = some candidate →
        candidate ∈ assertionBridgePostLaunchDirectives) := by
  intro generated candidate decoded
  rcases generated candidate decoded with rejoin | bridge
  · subst candidate
    simp [assertionBridgePostLaunchDirectives]
  · subst candidate
    simp [assertionBridgePostLaunchDirectives]

private theorem normalHandoffBridgeCaptureRows_rejoin_capabilities :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      normalHandoffBridgeCaptureRows := by
  intro row member payload decoded
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [decodeCompressedExecutableCapture,
      compressedNormalHandoffLoaderCaptureRow,
      compressedNormalHandoffFinishCaptureRow] at decoded

private theorem normalHandoffBridgeCaptureRows_bridge_capabilities :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      normalHandoffBridgeCaptureRows := by
  intro row member payload decoded
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [decodeNormalDispatchBridgeCapture,
      compressedNormalHandoffLoaderCaptureRow,
      compressedNormalHandoffFinishCaptureRow] at decoded

theorem sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  unfold sourceDecoratedAssertionBridgeReadySpace
  exact AssertionRejoinCapabilities.append
    (sourceDecoratedAssertionRequestSpace_rejoin_capabilities context state
      ledger scanner index cursor assertion)
    normalHandoffBridgeCaptureRows_rejoin_capabilities

theorem sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  unfold sourceDecoratedAssertionBridgeReadySpace
  exact NormalDispatchBridgeCapabilities.append
    (sourceDecoratedAssertionRequestSpace_bridge_capabilities context state
      ledger scanner index cursor assertion)
    normalHandoffBridgeCaptureRows_bridge_capabilities

theorem sourceAssertionBridgeLaunchResult_list_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup) :
    (sourceAssertionBridgeLaunchResult
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)).Nodup := by
  unfold sourceAssertionBridgeLaunchResult
  exact cFireRuleScopedSourceExecFact_list_nodup _ _ listNodup

theorem sourceAssertionBridgeLaunchResult_mork_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)) :
    MorkSupportNodup
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  unfold sourceAssertionBridgeLaunchResult
  exact cFireRuleScopedSourceExecFact_mork_nodup _ _ morkNodup

/-- The physical launch consumes the compact request, lookup cursor, and
predecessor machine before any inherited scheduler shell is considered. -/
theorem sourceAssertionBridgeLaunchResult_consumes_predecessor_controls
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
    let launchContext := directAssertionContextAtBoundary context state scanner
      index cursor assertion
    launchContext.pendingRow ∉ sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion) ∧
      launchContext.lookupRow ∉ sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion) ∧
      launchContext.machineRow ∉ sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion) := by
  dsimp only
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  unfold sourceAssertionBridgeLaunchResult
  exact physical_decorated_assertion_consumes_predecessor_controls
    (sourceDecoratedAssertionBridgeReadySpace_exact_match context state ledger
      scanner index cursor assertion)
    listNodup morkNodup directivePresent
    (sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities context state
      ledger scanner index cursor assertion)
    (sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities context state
      ledger scanner index cursor assertion)

private theorem decoratedAssertionPublishedAtom_predecessor_origin
    (context : DirectAssertionContext) {atom : Atom}
    (published : DecoratedAssertionPublishedAtom atom) :
    AssertionPredecessorRowOrigin context atom := by
  rcases published with assertionContext | normalControl | normalLabel |
      reload | executable
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-compressed-assertion-context" assertionContext
      (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-normal-control" normalControl (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-linked-row" normalLabel (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-reload-compressed-normal-dispatch" reload
      (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "exec" executable (by decide) (by decide)

/-- The exact predecessor-family origin invariant survives the complete
physical launch.  Removals only shrink the live support; every possible
addition has a compiler-proved non-predecessor head. -/
theorem sourceAssertionBridgeLaunchResult_predecessor_origin
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
    let launchContext := directAssertionContextAtBoundary context state scanner
      index cursor assertion
    AtomsWithin (AssertionPredecessorRowOrigin launchContext)
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  dsimp only
  let launchContext := directAssertionContextAtBoundary context state scanner
    index cursor assertion
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  have liveWithin : AtomsWithin
      (AssertionPredecessorRowOrigin launchContext)
      (morkEraseSupport space decoratedDirectAssertionDirective.atom) := by
    intro atom member
    exact sourceDecoratedAssertionBridgeReadySpace_predecessor_origin context
      state ledger scanner index cursor assertion atom
      (List.mem_of_mem_filter member)
  unfold sourceAssertionBridgeLaunchResult
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_live_additions
    (AssertionPredecessorRowOrigin launchContext) space
      decoratedDirectAssertionDirective liveWithin
  exact @RuleScopedTemplateAdditionsWithin.mono
    DecoratedAssertionPublishedAtom
    (AssertionPredecessorRowOrigin launchContext)
    decoratedDirectAssertionDirective.rule.input
    (physicalDecoratedAssertionMatcherRows space)
    decoratedDirectAssertionDirective.rule.tmpl
    (fun atom published =>
      decoratedAssertionPublishedAtom_predecessor_origin launchContext
        published)
    (physical_decorated_assertion_additions_published listNodup morkNodup
      directivePresent
      (sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities context
        state ledger scanner index cursor assertion)
      (sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities context
        state ledger scanner index cursor assertion))

/-- After launch there is no row at either predecessor-family head.  This is
stronger than absence of the two concrete controls: wildcard cursor templates
also have no carrier from which to refire. -/
theorem sourceAssertionBridgeLaunchResult_no_predecessor_heads
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
    ∀ atom ∈ sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion),
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup" := by
  intro atom member
  let launchContext := directAssertionContextAtBoundary context state scanner
    index cursor assertion
  have origin := sourceAssertionBridgeLaunchResult_predecessor_origin context
    state ledger scanner index cursor assertion listNodup morkNodup atom member
  have consumed := sourceAssertionBridgeLaunchResult_consumes_predecessor_controls
    context state ledger scanner index cursor assertion listNodup morkNodup
  constructor
  · intro pending
    have exactRow : atom = launchContext.pendingRow := origin.1 pending
    exact consumed.1 (exactRow ▸ member)
  · intro lookup
    have exactRow : atom = launchContext.lookupRow := origin.2 lookup
    exact consumed.2.1 (exactRow ▸ member)

theorem sourceAssertionBridgeLaunchResult_supported_within
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
    AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate ∈ assertionBridgePostLaunchDirectives)
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  let live := morkEraseSupport space decoratedDirectAssertionDirective.atom
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  have liveWithin : AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate ∈ assertionBridgePostLaunchDirectives) live :=
    @sourceAssertionBridgeLaunchLive_supported_within source target context
      state ledger scanner index cursor assertion
  unfold sourceAssertionBridgeLaunchResult
  exact @physical_decorated_assertion_fire_atomsWithin_of_generated space
    (fun atom => ∀ candidate,
      extractSupportedSourceExecFact atom = some candidate →
        candidate ∈ assertionBridgePostLaunchDirectives)
    listNodup morkNodup
    directivePresent liveWithin
    (sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities context state
      ledger scanner index cursor assertion)
    (sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities context state
      ledger scanner index cursor assertion)
    (fun atom generated =>
      decoratedAssertionGeneratedSupportedAtom_post_launch generated)

#print axioms sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities
#print axioms sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities
#print axioms sourceAssertionBridgeSchedulerAtom_survives_launch
#print axioms sourceAssertionBridgeSchedulerSupported_survive_launch
#print axioms sourceAssertionBridgeLaunchResult_list_nodup
#print axioms sourceAssertionBridgeLaunchResult_mork_nodup
#print axioms sourceAssertionBridgeLaunchResult_consumes_predecessor_controls
#print axioms sourceAssertionBridgeLaunchResult_predecessor_origin
#print axioms sourceAssertionBridgeLaunchResult_no_predecessor_heads
#print axioms sourceAssertionBridgeLaunchResult_supported_within

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
