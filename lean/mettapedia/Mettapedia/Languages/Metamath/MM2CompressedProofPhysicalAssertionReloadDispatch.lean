import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeAuthority
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadPublication

/-!
# Source reload through physical launch and predecessor drain

The assertion launcher publishes one owner-bound reload.  This module shows
that row is the only live representative of its physical key after the launch
and after the four predecessor drains.  The normal-dispatch bridge therefore
meets the source proof owner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadDispatch

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadPublication
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalDispatchBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

def reloadHead : String := "mm-reload-compressed-normal-dispatch"

/-- The reload published for one source assertion boundary. -/
def sourceAssertionReloadRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) : Atom :=
  (directAssertionContextAtBoundary context state scanner index cursor
    assertion).reloadRow

theorem sourceAssertionReloadRow_eq_dispatchReload
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) :
    sourceAssertionReloadRow context state scanner index cursor assertion =
      normalDispatchBridgeReloadRow context.proofOwner := by
  rfl

theorem sourceAssertionReloadRow_shape
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) :
    ∃ tail,
      sourceAssertionReloadRow context state scanner index cursor assertion =
        .expression (.symbol reloadHead :: tail) := by
  exact ⟨[context.proofOwner], rfl⟩

/-- A live atom at the source reload key is that source reload. -/
def SourceReloadKeyReflects (reload : Atom) (row : Atom) : Prop :=
  morkSupportKey row = morkSupportKey reload → row = reload

private theorem key_ne_reload_of_head
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail))
    {row : Atom} (head : String)
    (headExact : compressedDynamicRowHead? row = some head)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ reloadHead) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases (compressedDynamicRowHead?_eq_some_iff row head).mp headExact with
    ⟨tail, rowShape⟩
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    (left := row) (right := reload) head
    reloadHead ⟨tail, rowShape⟩ reloadShape headPositive (by decide) headBound
    (by decide) different

private theorem key_ne_reload_of_exec
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail))
    {row : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact row = some directive) :
    morkSupportKey row ≠ morkSupportKey reload := by
  obtain ⟨location, input, output, shape⟩ :=
    extractSupportedSourceExecFact_exec_shape decoded
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    (left := row) (right := reload) "exec"
    reloadHead ⟨[location, input, output], shape⟩ reloadShape (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem dataSlice_key_ne_reload
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ decoratedDirectAssertionDataSlice context)
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail)) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases decoratedDirectAssertionDataSlice_head_cases context member with
    pending | lookup | heap | machine | header | rejoin | bridge
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-step-pending"
      pending (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-heap-lookup"
      lookup (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape
      "mm-compressed-heap-assertion" heap (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-machine"
      machine (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-assertion-header" header
      (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape
      "mm-compressed-owned-runtime-rule" rejoin (by decide) (by decide)
      (by decide)
  · exact key_ne_reload_of_head reload reloadShape
      "mm-internal-compressed-normal-dispatch-bridge" bridge (by decide)
      (by decide) (by decide)

private theorem scheduler_key_ne_reload
    {row : Atom} (member : row ∈ decoratedDirectAssertionSchedulerFrame)
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail)) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases List.mem_cons.mp member with proof | member
  · intro keyEqual
    exact key_ne_reload_of_exec (row := compressedProofStepDirective.atom)
      (directive := compressedProofStepDirective) reload reloadShape
      extract_compressedProofStepRule_exact
      ((congrArg morkSupportKey proof).symm.trans keyEqual)
  rcases List.mem_cons.mp member with cursor | member
  · intro keyEqual
    exact key_ne_reload_of_exec
      (row := decoratedCursorAssertionDirective.atom)
      (directive := decoratedCursorAssertionDirective) reload reloadShape
      ((congrArg extractSupportedSourceExecFact
        decoratedCursorAssertionDirective_atom_exact).trans
          extract_decoratedCursorAssertionRule_exact)
      ((congrArg morkSupportKey cursor).symm.trans keyEqual)
  rcases List.mem_cons.mp member with fault | member
  · intro keyEqual
    exact key_ne_reload_of_exec
      (row := compressedHeapLookupFaultDirective.atom)
      (directive := compressedHeapLookupFaultDirective) reload reloadShape
      extract_compressedHeapLookupFaultRule_exact
      ((congrArg morkSupportKey fault).symm.trans keyEqual)
  rcases List.mem_cons.mp member with advance | member
  · intro keyEqual
    exact key_ne_reload_of_exec
      (row := compressedHeapLookupAdvanceDirective.atom)
      (directive := compressedHeapLookupAdvanceDirective) reload reloadShape
      extract_compressedHeapLookupAdvanceRule_exact
      ((congrArg morkSupportKey advance).symm.trans keyEqual)
  exact (List.not_mem_nil member).elim

private theorem canonical_key_ne_reload
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ canonicalDecoratedDirectAssertionSpace context)
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail)) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases (mem_canonicalDecoratedDirectAssertionSpace_iff context row).mp
      member with matched | scheduled
  rcases (mem_decoratedDirectAssertionMatchSlice_iff context row).mp matched
      with directive | data
  · intro keyEqual
    exact key_ne_reload_of_exec
      (row := decoratedDirectAssertionDirective.atom)
      (directive := decoratedDirectAssertionDirective) reload reloadShape
      decoratedDirectAssertionDirective_decodes
      ((congrArg morkSupportKey directive).symm.trans keyEqual)
  · exact dataSlice_key_ne_reload context data reload reloadShape
  · exact scheduler_key_ne_reload scheduled reload reloadShape

private theorem additional_key_ne_reload
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈ sourceAssertionAdditionalRows context state ledger scanner
      index assertion)
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail)) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases sourceAssertionAdditionalRows_head_cases context state ledger scanner
      index assertion member with
    scan | heapProof | heapAssertion | node | compactStack | normalStack | save
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-scan" scan
      (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-heap-proof"
      heapProof (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape
      "mm-compressed-heap-assertion" heapAssertion (by decide) (by decide)
      (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-node" node
      (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-compressed-stack-cell"
      compactStack (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape "mm-stack-cell" normalStack
      (by decide) (by decide) (by decide)
  · exact key_ne_reload_of_head reload reloadShape
      "mm-compressed-save-receipt" save (by decide) (by decide) (by decide)

private theorem capture_key_ne_reload
    {row : Atom} (member : row ∈ normalHandoffBridgeCaptureRows)
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail)) :
    morkSupportKey row ≠ morkSupportKey reload := by
  rcases List.mem_cons.mp member with loader | member
  · intro keyEqual
    exact key_ne_reload_of_head
      (row := compressedNormalHandoffLoaderCaptureRow) reload reloadShape
      "mm-internal-compressed-normal-handoff-loader"
      rfl (by decide) (by decide) (by decide)
      ((congrArg morkSupportKey loader).symm.trans keyEqual)
  rcases List.mem_cons.mp member with finish | member
  · intro keyEqual
    exact key_ne_reload_of_head
      (row := compressedNormalHandoffFinishCaptureRow) reload reloadShape
      "mm-internal-compressed-normal-handoff-finish"
      rfl (by decide) (by decide) (by decide)
      ((congrArg morkSupportKey finish).symm.trans keyEqual)
  exact (List.not_mem_nil member).elim

theorem source_ready_row_key_ne_reload
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) :
    morkSupportKey row ≠
      morkSupportKey
        (sourceAssertionReloadRow context state scanner index cursor
          assertion) := by
  let reload := sourceAssertionReloadRow context state scanner index cursor
    assertion
  have reloadShape := sourceAssertionReloadRow_shape context state scanner
    index cursor assertion
  rcases (mem_sourceDecoratedAssertionBridgeReadySpace_iff context state ledger
      scanner index cursor assertion row).mp member with request | capture
  rcases (mem_sourceDecoratedAssertionRequestSpace_iff context state ledger
      scanner index cursor assertion row).mp request with canonical | additional
  · exact canonical_key_ne_reload
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) canonical reload reloadShape
  · exact additional_key_ne_reload context state ledger scanner index assertion
      additional reload reloadShape
  · exact capture_key_ne_reload capture reload reloadShape

private theorem directAssertionContextTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionContextTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionNormalControlTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionNormalControlTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionNormalLabelTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionNormalLabelTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionReloadTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionReloadTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionRejoinTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.var "compressed-assertion-rejoin-rule") = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionBridgeTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.var "normal-bridge-rule") = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem instantiated_symbol_shape
    (substitution : Subst) (head : String) (tail : List Atom)
    (inherited : ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.expression (.symbol head :: tail)) = true)
    {atom : Atom}
    (instantiated : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.expression (.symbol head :: tail)) = some atom) :
    ∃ atomTail, atom = .expression (.symbol head :: atomTail) := by
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ inherited] at instantiated
  cases covered : templateCovered substitution
      (.expression (.symbol head :: tail)) with
  | false => simp [instantiateTemplateAtom?, covered] at instantiated
  | true =>
      have instantiatedExact := instantiateTemplateAtom_of_covered substitution
        (.expression (.symbol head :: tail)) covered
      have atomExact : atom =
          applySubst substitution (.expression (.symbol head :: tail)) :=
        Option.some.inj (instantiated.symm.trans instantiatedExact)
      rw [atomExact, applySubst_expression_symbol]
      exact ⟨_, rfl⟩

private theorem published_head_key_ne_reload
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail))
    (substitution : Subst) (head : String) (tail : List Atom)
    (inherited : ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.expression (.symbol head :: tail)) = true)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ reloadHead)
    {atom : Atom}
    (instantiated : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.expression (.symbol head :: tail)) = some atom) :
    morkSupportKey atom ≠ morkSupportKey reload := by
  obtain ⟨atomTail, atomShape⟩ := instantiated_symbol_shape substitution head
    tail inherited instantiated
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    (left := atom) (right := reload) head
    reloadHead ⟨atomTail, atomShape⟩ reloadShape headPositive (by decide)
    headBound (by decide) different

private theorem physicalMatcherRow_rejoin_exact
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (capabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    payload = compressedAssertionRejoinRule := by
  have ordinary := physicalDecoratedAssertionMatcherRows_subset listNodup
    morkNodup directivePresent rowMember
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ directAssertionRejoinTemplate_inherited] at instantiates
  exact decoratedAssertionMatcherRow_rejoin_exact capabilities ordinary
    instantiates

private theorem physicalMatcherRow_bridge_exact
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (capabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.var "normal-bridge-rule") = some payload) :
    payload = compressedNormalDispatchBridgeRule := by
  have ordinary := physicalDecoratedAssertionMatcherRows_subset listNodup
    morkNodup directivePresent rowMember
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ directAssertionBridgeTemplate_inherited] at instantiates
  exact decoratedAssertionMatcherRow_bridge_exact capabilities ordinary
    instantiates

private theorem exec_rule_key_ne_reload
    (reload : Atom)
    (reloadShape : ∃ tail, reload = .expression (.symbol reloadHead :: tail))
    {rule : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact rule = some directive)
    (payload : Atom) (payloadExact : payload = rule) :
    morkSupportKey payload ≠ morkSupportKey reload := by
  subst payload
  exact key_ne_reload_of_exec reload reloadShape decoded

theorem source_launch_reload_additions_reflect
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion))
    (directivePresent : decoratedDirectAssertionDirective.atom ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) :
    let space := @sourceDecoratedAssertionBridgeReadySpace source target
      context state ledger scanner index cursor assertion
    let reload := sourceAssertionReloadRow context state scanner index cursor
      assertion
    RuleScopedTemplateAdditionsWithin (SourceReloadKeyReflects reload)
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl := by
  intro space reload sink sinkMember
  have reloadShape := sourceAssertionReloadRow_shape context state scanner
    index cursor assertion
  rw [decoratedDirectAssertionDirective_sinks_exact] at sinkMember
  simp only [decoratedDirectAssertionSinks, directAssertionSinks,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · intro substitution _ atom instantiated keyEqual
    exact (published_head_key_ne_reload reload reloadShape substitution
      "mm-compressed-assertion-context" _ directAssertionContextTemplate_inherited
      (by decide) (by decide) (by decide) instantiated keyEqual).elim
  · intro substitution _ atom instantiated keyEqual
    exact (published_head_key_ne_reload reload reloadShape substitution
      "mm-normal-control" _ directAssertionNormalControlTemplate_inherited
      (by decide) (by decide) (by decide) instantiated keyEqual).elim
  · intro substitution _ atom instantiated keyEqual
    exact (published_head_key_ne_reload reload reloadShape substitution
      "mm-linked-row" _ directAssertionNormalLabelTemplate_inherited
      (by decide) (by decide) (by decide) instantiated keyEqual).elim
  · intro substitution substitutionMember atom instantiated keyEqual
    have atomExact := physicalMatcherRow_reload_exact
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion)
      space directivePresent
      (sourceDecoratedAssertionBridgeReadySpace_predecessor_origin context
        state ledger scanner index cursor assertion)
      substitutionMember instantiated
    exact atomExact
  · intro substitution substitutionMember atom instantiated keyEqual
    have atomExact := physicalMatcherRow_rejoin_exact listNodup morkNodup
      directivePresent
      (sourceDecoratedAssertionBridgeReadySpace_rejoin_capabilities context
        state ledger scanner index cursor assertion)
      substitutionMember instantiated
    exact (exec_rule_key_ne_reload reload reloadShape
      extract_compressedAssertionRejoinRule_exact atom atomExact keyEqual).elim
  · intro substitution substitutionMember atom instantiated keyEqual
    have atomExact := physicalMatcherRow_bridge_exact listNodup morkNodup
      directivePresent
      (sourceDecoratedAssertionBridgeReadySpace_bridge_capabilities context
        state ledger scanner index cursor assertion)
      substitutionMember instantiated
    exact (exec_rule_key_ne_reload reload reloadShape
      extract_compressedNormalDispatchBridgeRule_exact atom atomExact
      keyEqual).elim

theorem source_launch_reload_key_reflects
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion))
    (directivePresent : decoratedDirectAssertionDirective.atom ∈
      @sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) :
    AtomsWithin
      (SourceReloadKeyReflects
        (sourceAssertionReloadRow context state scanner index cursor
          assertion))
      (sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  unfold sourceAssertionBridgeLaunchResult
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_live_additions
    (SourceReloadKeyReflects
      (sourceAssertionReloadRow context state scanner index cursor assertion))
    space decoratedDirectAssertionDirective
  · exact morkEraseSupport_atomsWithin_key_reflects_of_fresh space
      decoratedDirectAssertionDirective.atom
      (sourceAssertionReloadRow context state scanner index cursor assertion)
      (fun row member _ =>
        source_ready_row_key_ne_reload context state ledger scanner index
          cursor assertion member)
  · change RuleScopedTemplateAdditionsWithin
      (SourceReloadKeyReflects
        (sourceAssertionReloadRow context state scanner index cursor
          assertion))
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl
    exact source_launch_reload_additions_reflect context state ledger scanner
      index cursor assertion listNodup morkNodup directivePresent

theorem source_launch_reload_mem
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
    sourceAssertionReloadRow context state scanner index cursor assertion ∈
      sourceAssertionBridgeLaunchResult
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  have support := physical_decorated_assertion_launch_support_present
    (sourceDecoratedAssertionBridgeReadySpace_exact_match context state ledger
      scanner index cursor assertion)
    listNodup morkNodup directivePresent
  apply mem_of_morkSupportContains_of_key_reflection support.2.2.2.1
  exact source_launch_reload_key_reflects context state ledger scanner index
    cursor assertion listNodup morkNodup directivePresent

private theorem predecessor_head_absent_after_erase
    {before after : List Atom} {selected : Atom}
    (afterExact : after = morkEraseSupport before selected)
    (absent : ∀ atom ∈ before,
      compressedDynamicRowHead? atom ≠ some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠ some "mm-compressed-heap-lookup") :
    ∀ atom ∈ after,
      compressedDynamicRowHead? atom ≠ some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠ some "mm-compressed-heap-lookup" := by
  exact atomsWithin_of_eq_morkEraseSupport afterExact absent

private theorem reload_key_reflects_after_probes
    (space : List Atom) (reload : Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠ some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠ some "mm-compressed-heap-lookup")
    (reflects : AtomsWithin (SourceReloadKeyReflects reload) space) :
    AtomsWithin (SourceReloadKeyReflects reload)
      (afterLookupAdvanceProbe space) := by
  have proofDrains := compressedProofStep_drains_of_no_predecessor_heads space
    absent
  have proofReflects := atomsWithin_of_eq_morkEraseSupport proofDrains reflects
  have proofAbsent := predecessor_head_absent_after_erase proofDrains absent
  have faultDrains := compressedHeapLookupFault_drains_of_no_predecessor_heads
    (afterProofProbe space) proofAbsent
  have faultReflects := atomsWithin_of_eq_morkEraseSupport faultDrains
    proofReflects
  have faultAbsent := predecessor_head_absent_after_erase faultDrains
    proofAbsent
  have cursorDrains := decoratedCursorAssertion_drains_of_no_predecessor_heads
    (afterLookupFaultProbe space) faultAbsent
  have cursorReflects := atomsWithin_of_eq_morkEraseSupport cursorDrains
    faultReflects
  have cursorAbsent := predecessor_head_absent_after_erase cursorDrains
    faultAbsent
  have advanceDrains :=
    compressedHeapLookupAdvance_drains_of_no_predecessor_heads
      (afterCursorAssertionProbe space) cursorAbsent
  exact atomsWithin_of_eq_morkEraseSupport advanceDrains cursorReflects

theorem source_drained_reload_key_reflects
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
    let launched := sourceAssertionBridgeLaunchResult
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)
    AtomsWithin
      (SourceReloadKeyReflects
        (sourceAssertionReloadRow context state scanner index cursor
          assertion))
      (afterLookupAdvanceProbe launched) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  exact reload_key_reflects_after_probes _
    (sourceAssertionReloadRow context state scanner index cursor assertion)
    (sourceAssertionBridgeLaunchResult_no_predecessor_heads context state
      ledger scanner index cursor assertion listNodup morkNodup)
    (source_launch_reload_key_reflects context state ledger scanner index
      cursor assertion listNodup morkNodup directivePresent)

theorem source_drained_reload_mem
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
    let launched := sourceAssertionBridgeLaunchResult
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion)
    sourceAssertionReloadRow context state scanner index cursor assertion ∈
      afterLookupAdvanceProbe launched := by
  let launched := sourceAssertionBridgeLaunchResult
    (@sourceDecoratedAssertionBridgeReadySpace source target context state
      ledger scanner index cursor assertion)
  have ready := sourceAssertionBridgeLaunchResult_drain_ready context state
    ledger scanner index cursor assertion listNodup morkNodup
  have drain := sourceAssertionBridgeLaunchResult_physical_drain context state
    ledger scanner index cursor assertion listNodup morkNodup
  have present := source_launch_reload_mem context state ledger scanner index
    cursor assertion listNodup morkNodup
  exact expression_symbol_row_survives_physical_predecessor_drain launched
    (afterLookupAdvanceProbe launched) ready drain reloadHead [context.proofOwner]
    (by decide) (by decide) (by decide) present

#print axioms sourceAssertionReloadRow_eq_dispatchReload
#print axioms source_ready_row_key_ne_reload
#print axioms source_launch_reload_key_reflects
#print axioms source_launch_reload_mem
#print axioms source_drained_reload_key_reflects
#print axioms source_drained_reload_mem

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadDispatch
