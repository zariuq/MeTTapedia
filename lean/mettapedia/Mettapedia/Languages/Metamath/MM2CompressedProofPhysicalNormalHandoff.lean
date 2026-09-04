import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation

/-!
# Physical compressed-to-normal handoff

The compressed assertion launcher and the normal verifier are connected by
two opaque compiler-owned captures.  This module places those exact captures
beside the source-derived assertion request, proves their provenance in the
generated verifier program, and transports the scheduled physical launch to
that bridge-ready state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- The two opaque rules consumed by the compact-to-normal bridge. -/
def normalHandoffBridgeCaptureRows : List Atom :=
  [compressedNormalHandoffLoaderCaptureRow,
   compressedNormalHandoffFinishCaptureRow]

theorem normalHandoffBridgeCaptureRows_in_bridgeRows :
    ∀ row ∈ normalHandoffBridgeCaptureRows,
      row ∈ compressedNormalDispatchBridgeRows := by
  intro row member
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with h | h <;> subst row <;>
    simp [compressedNormalDispatchBridgeRows]

/-- Both handoff captures are emitted by the same generated verifier program
that emits the assertion launcher and bridge. -/
theorem normalHandoffBridgeCaptureRows_in_program :
    ∀ row ∈ normalHandoffBridgeCaptureRows,
      row ∈ compressedSpeculativeOrderedVerifierExtensionProgram := by
  intro row member
  have bridgeMember := normalHandoffBridgeCaptureRows_in_bridgeRows row member
  unfold compressedSpeculativeOrderedVerifierExtensionProgram
  apply List.mem_append_left [compressedDispatchReloadCaptureRow]
  exact List.mem_append_right _ bridgeMember

/-- Capture rows carry executable atoms as opaque values, but are not
themselves executable directives at the outer scheduler level. -/
theorem normalHandoffBridgeCaptureRows_no_supported :
    cSupportedSourceExecFacts normalHandoffBridgeCaptureRows = [] := by
  decide +kernel

theorem normalHandoffBridgeCaptureRows_distinct :
    compressedNormalHandoffLoaderCaptureRow ≠
      compressedNormalHandoffFinishCaptureRow := by
  decide

/-- Source-derived assertion state enriched only with the compiler-owned
captures required by the next normal-dispatch bridge. -/
def sourceDecoratedAssertionBridgeReadySpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  sourceDecoratedAssertionRequestSpace context state ledger scanner index
      cursor assertion ++ normalHandoffBridgeCaptureRows

/-- Membership in the bridge-ready assertion workspace decomposes at the
source-request/captured-code boundary. -/
theorem mem_sourceDecoratedAssertionBridgeReadySpace_iff
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) (row : Atom) :
    row ∈ sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
        index cursor assertion ↔
      row ∈ sourceDecoratedAssertionRequestSpace context state ledger scanner
          index cursor assertion ∨
        row ∈ normalHandoffBridgeCaptureRows := by
  simp [sourceDecoratedAssertionBridgeReadySpace]

#print axioms mem_sourceDecoratedAssertionBridgeReadySpace_iff

theorem sourceDecoratedAssertionBridgeReadySpace_exact_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    ExactDecoratedDirectAssertionLaunch
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion)
      (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
        index cursor assertion) := by
  unfold sourceDecoratedAssertionBridgeReadySpace
  unfold sourceDecoratedAssertionRequestSpace
  rw [List.append_assoc]
  exact canonical_exact_decorated_direct_assertion_launch_append
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion)
    (sourceAssertionAdditionalRows context state ledger scanner index
      assertion ++ normalHandoffBridgeCaptureRows)

theorem sourceDecoratedAssertionBridgeReadySpace_no_new_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
      (sourceAssertionAdditionalRows context state ledger scanner index
        assertion ++ normalHandoffBridgeCaptureRows) = [] := by
  rw [cSupportedSourceExecFacts_append_inert]
  · exact sourceAssertionAdditionalRows_no_supported context state ledger
      scanner index assertion
  · exact normalHandoffBridgeCaptureRows_no_supported

/-- The actual rule-scoped scheduler still selects the compiler-produced
assertion launcher in the bridge-ready state. -/
theorem sourceDecoratedAssertionBridgeReadySpace_steps
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
          index cursor assertion) =
      some (cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
          index cursor assertion)
        decoratedDirectAssertionDirective) := by
  unfold sourceDecoratedAssertionBridgeReadySpace
  unfold sourceDecoratedAssertionRequestSpace
  rw [List.append_assoc]
  unfold cRuleScopedSourceWorkQueueStep
  rw [canonicalDecoratedDirectAssertionSpace_append_selects
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion)
    (sourceAssertionAdditionalRows context state ledger scanner index
      assertion ++ normalHandoffBridgeCaptureRows)
    (sourceDecoratedAssertionBridgeReadySpace_no_new_supported context state
      ledger scanner index assertion)]

/-- Physical compact-key matching over the bridge-ready state retains the
exact source-derived positive launch witness. -/
theorem sourceDecoratedAssertionBridgeReadySpace_physical_match
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    (listNodup :
      (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
        index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
        index cursor assertion)) :
    PhysicalExactDecoratedAssertionLaunch
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion)
      (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
        index cursor assertion) := by
  apply physical_decorated_assertion_exact_match
    (sourceDecoratedAssertionBridgeReadySpace_exact_match context state ledger
      scanner index cursor assertion) listNodup morkNodup
  simp [sourceDecoratedAssertionBridgeReadySpace,
    sourceDecoratedAssertionRequestSpace,
    canonicalDecoratedDirectAssertionSpace,
    decoratedDirectAssertionMatchSlice]

private theorem applySubstList_length (substitution : Subst) :
    ∀ atoms,
      (applySubst.applySubstList substitution atoms).length = atoms.length
  | [] => rfl
  | _ :: tail => by
      simp [applySubst.applySubstList, applySubstList_length substitution tail]

/-- Instantiating an inherited expression template cannot change its symbolic
head.  Consequently a compiler-owned capture with a different head has a
different physical MORK identity from every instantiated predecessor row. -/
private theorem instantiated_expression_symbol_head_key_ne
    (input : InputSpec) (substitution : Subst)
    (candidateHead authoredHead : String)
    (candidateTail authoredTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (authoredArity : authoredTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (authoredPositive : 0 < (morkUtf8Bytes authoredHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (authoredBound : (morkUtf8Bytes authoredHead).length < 64)
    (different : candidateHead ≠ authoredHead)
    (inherited : ruleTemplateVariablesInherited input
      (.expression (.symbol authoredHead :: authoredTail)) = true)
    {removed : Atom}
    (instantiates : instantiateRuleTemplateAtom? input substitution
      (.expression (.symbol authoredHead :: authoredTail)) = some removed) :
    morkSupportKey (.expression (.symbol candidateHead :: candidateTail)) ≠
      morkSupportKey removed := by
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    input substitution _ inherited] at instantiates
  cases covered : templateCovered substitution
      (.expression (.symbol authoredHead :: authoredTail)) with
  | false => simp [instantiateTemplateAtom?, covered] at instantiates
  | true =>
      have instantiatedExact := instantiateTemplateAtom_of_covered substitution
        (.expression (.symbol authoredHead :: authoredTail)) covered
      have removedExact : removed = applySubst substitution
          (.expression (.symbol authoredHead :: authoredTail)) :=
        Option.some.inj (instantiates.symm.trans instantiatedExact)
      subst removed
      simp only [applySubst, applySubst.applySubstList]
      apply morkSupportKey_expression_symbol_head_ne
      · exact candidateArity
      · simpa [applySubstList_length substitution] using authoredArity
      · exact candidatePositive
      · exact authoredPositive
      · exact candidateBound
      · exact authoredBound
      · exact different

/-- Instantiated pending controls remain physically distinct from an
expression whose symbolic head is different. -/
theorem instantiated_directAssertionPending_key_ne
    (substitution : Subst) (candidateHead : String)
    (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (different : candidateHead ≠ "mm-compressed-step-pending")
    {removed : Atom}
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionPendingTemplate = some removed) :
    morkSupportKey (.expression (.symbol candidateHead :: candidateTail)) ≠
      morkSupportKey removed := by
  exact instantiated_expression_symbol_head_key_ne
    decoratedDirectAssertionDirective.rule.input substitution
    candidateHead "mm-compressed-step-pending" candidateTail _
    candidateArity (by norm_num) candidatePositive (by decide)
    candidateBound (by decide) different
    directAssertionPendingTemplate_inherited instantiates

theorem instantiated_directAssertionLookup_key_ne
    (substitution : Subst) (candidateHead : String)
    (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (different : candidateHead ≠ "mm-compressed-heap-lookup")
    {removed : Atom}
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionLookupTemplate = some removed) :
    morkSupportKey (.expression (.symbol candidateHead :: candidateTail)) ≠
      morkSupportKey removed := by
  exact instantiated_expression_symbol_head_key_ne
    decoratedDirectAssertionDirective.rule.input substitution
    candidateHead "mm-compressed-heap-lookup" candidateTail _
    candidateArity (by norm_num) candidatePositive (by decide)
    candidateBound (by decide) different
    directAssertionLookupTemplate_inherited instantiates

theorem instantiated_directAssertionMachine_key_ne
    (substitution : Subst) (candidateHead : String)
    (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (different : candidateHead ≠ "mm-compressed-machine")
    {removed : Atom}
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionMachineTemplate = some removed) :
    morkSupportKey (.expression (.symbol candidateHead :: candidateTail)) ≠
      morkSupportKey removed := by
  exact instantiated_expression_symbol_head_key_ne
    decoratedDirectAssertionDirective.rule.input substitution
    candidateHead "mm-compressed-machine" candidateTail _
    candidateArity (by norm_num) candidatePositive (by decide)
    candidateBound (by decide) different
    directAssertionMachineTemplate_inherited instantiates

#print axioms normalHandoffBridgeCaptureRows_in_program
#print axioms normalHandoffBridgeCaptureRows_no_supported
#print axioms sourceDecoratedAssertionBridgeReadySpace_exact_match
#print axioms sourceDecoratedAssertionBridgeReadySpace_steps
#print axioms sourceDecoratedAssertionBridgeReadySpace_physical_match
#print axioms instantiated_directAssertionPending_key_ne
#print axioms instantiated_directAssertionLookup_key_ne
#print axioms instantiated_directAssertionMachine_key_ne

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
