import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternCaptureOrigin

/-!
# Executable origin at the compressed assertion seam

The direct assertion matcher republishes an opaque rejoin rule captured by
its final premise.  The generic arbitrary-premise origin theorem connects
that output to an actual inert carrier, while the compiler-selected
presentation fixes the carrier's exact executable payload.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionCapabilityOrigin

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Exact carrier relation for the assertion-rejoin role.  Family and kind
are part of the relation, so an executable from another role is not an
acceptable witness. -/
def AssertionRejoinCapture (carrier payload : Atom) : Prop :=
  decodeCompressedExecutableCapture carrier =
    some ⟨.runtime, "assertion-rejoin", payload⟩

theorem decodeCompressedExecutableCapture_eq_none_of_dynamic
    {row : Atom} (dynamic : isDynamicRow row = true) :
    decodeCompressedExecutableCapture row = none := by
  unfold decodeCompressedExecutableCapture
  split <;> simp_all [isDynamicRow, dynamicRowHeads]

private theorem directAssertionDirective_not_capture :
    decodeCompressedExecutableCapture
      speculativeDirectAssertionDirective.atom = none := by
  rfl

private theorem proofStepDirective_not_capture :
    decodeCompressedExecutableCapture compressedProofStepDirective.atom =
      none := by
  rfl

private theorem assertionLaunchDirective_not_capture :
    decodeCompressedExecutableCapture compressedAssertionLaunchDirective.atom =
      none := by
  rfl

private theorem lookupFaultDirective_not_capture :
    decodeCompressedExecutableCapture compressedHeapLookupFaultDirective.atom =
      none := by
  rfl

private theorem lookupAdvanceDirective_not_capture :
    decodeCompressedExecutableCapture
      compressedHeapLookupAdvanceDirective.atom = none := by
  rfl

theorem sourceAssertionAdditionalRows_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      (sourceAssertionAdditionalRows context state ledger scanner index
        assertion) := by
  intro row member
  unfold CompressedExecutableCarrierAuthorized
  rw [decodeCompressedExecutableCapture_eq_none_of_dynamic
    (sourceAssertionAdditionalRows_all_dynamic context state ledger scanner
      index assertion row member)]
  trivial

theorem canonicalDirectAssertionSpace_capabilities
    (context : DirectAssertionContext) :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      (canonicalDirectAssertionSpace context) := by
  intro row member
  simp only [canonicalDirectAssertionSpace, directAssertionMatchSlice,
    directAssertionSchedulerFrame, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl)
  · simp [CompressedExecutableCarrierAuthorized,
      directAssertionDirective_not_capture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.pendingRow,
      decodeCompressedExecutableCapture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.lookupRow,
      decodeCompressedExecutableCapture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.heapRow,
      decodeCompressedExecutableCapture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.machineRow,
      decodeCompressedExecutableCapture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.headerRow,
      decodeCompressedExecutableCapture]
  · simp [CompressedExecutableCarrierAuthorized,
      DirectAssertionContext.rejoinCaptureRow,
      compressedOwnedRuntimeRuleRow,
      decodeCompressedExecutableCapture,
      speculativeBaseExecutablePresentation, executablePresentationOf,
      compressedBaseExecutableRule?]
  · simp [CompressedExecutableCarrierAuthorized,
      proofStepDirective_not_capture]
  · simp [CompressedExecutableCarrierAuthorized,
      assertionLaunchDirective_not_capture]
  · simp [CompressedExecutableCarrierAuthorized,
      lookupFaultDirective_not_capture]
  · simp [CompressedExecutableCarrierAuthorized,
      lookupAdvanceDirective_not_capture]

theorem sourceAssertionRequestSpace_capabilities
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      (sourceAssertionRequestSpace context state ledger scanner index cursor
        assertion) := by
  intro row member
  rcases List.mem_append.mp member with canonical | additional
  · exact canonicalDirectAssertionSpace_capabilities
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) row canonical
  · exact sourceAssertionAdditionalRows_capabilities context state ledger
      scanner index assertion row additional

private theorem matchAtom_directAssertionRejoin_captures
    {beforeCapture afterCapture : Subst} {carrier : Atom}
    (matched : cmatchAtom beforeCapture directAssertionRejoinCaptureTemplate
      carrier = some afterCapture) :
    ∃ payload,
      Subst.lookup afterCapture "compressed-assertion-rejoin-rule" =
          some payload ∧
        AssertionRejoinCapture carrier payload := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons kindMatched tail2 =>
          cases kindMatched
          cases tail2 with
          | expr_cons payloadMatched finalTail =>
              cases finalTail
              cases payloadMatched with
              | var_fresh lookup =>
                  rename_i payload
                  exact ⟨payload, by simp [Subst.lookup], rfl⟩
              | var_bound lookup =>
                  rename_i payload
                  exact ⟨payload, lookup, rfl⟩

private theorem speculativeDirectAssertion_not_rejoin_capture
    (payload : Atom) :
    ¬ AssertionRejoinCapture speculativeDirectAssertionDirective.atom
      payload := by
  intro captured
  unfold AssertionRejoinCapture at captured
  rw [directAssertionDirective_not_capture] at captured
  contradiction

/-- Every rejoin value published by an arbitrary matcher row comes from an
actual assertion-rejoin carrier in the pre-state. -/
theorem directAssertionMatcherRow_rejoin_origin
    {space : List Atom} {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    ∃ carrier ∈ space, AssertionRejoinCapture carrier payload := by
  have rowMember' : substitution ∈
      (cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        (.compat (mkPattern
          ([directAssertionSelfTemplate, directAssertionPendingTemplate,
            directAssertionLookupTemplate, directAssertionHeapTemplate,
            directAssertionMachineTemplate, directAssertionHeaderTemplate] ++
            directAssertionRejoinCaptureTemplate :: [])))).map Prod.fst := by
    rw [speculative_direct_assertion_input_exact] at rowMember
    exact rowMember
  obtain ⟨carrier, capturedPayload, carrierMember, capturedLookup, captured⟩ :=
    cmatchInputSpec_capture_origin AssertionRejoinCapture
      "compressed-assertion-rejoin-rule"
      (speculativeDirectAssertionDirective.atom ::
        space.erase speculativeDirectAssertionDirective.atom)
      [directAssertionSelfTemplate, directAssertionPendingTemplate,
       directAssertionLookupTemplate, directAssertionHeapTemplate,
       directAssertionMachineTemplate, directAssertionHeaderTemplate]
      directAssertionRejoinCaptureTemplate [] rowMember'
      matchAtom_directAssertionRejoin_captures
  have payloadLookup :
      Subst.lookup substitution "compressed-assertion-rejoin-rule" =
        some payload :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution
      "compressed-assertion-rejoin-rule" payload).1 instantiates
  have payloadEqual : capturedPayload = payload :=
    Option.some.inj (capturedLookup.symm.trans payloadLookup)
  subst capturedPayload
  rcases List.mem_cons.mp carrierMember with selected | prior
  · exact False.elim
      (speculativeDirectAssertion_not_rejoin_capture payload
        (selected ▸ captured))
  · exact ⟨carrier, List.mem_of_mem_erase prior, captured⟩

/-- Capability origin fixes the opaque rejoin output to the exact rule
selected by the admitted speculative presentation. -/
theorem directAssertionMatcherRow_rejoin_exact
    {space : List Atom}
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    payload = compressedAssertionRejoinRule := by
  obtain ⟨carrier, member, captured⟩ :=
    directAssertionMatcherRow_rejoin_origin rowMember instantiates
  have authorized := capabilities carrier member
  unfold CompressedExecutableCarrierAuthorized at authorized
  rw [captured] at authorized
  simpa [speculativeBaseExecutablePresentation, executablePresentationOf,
    compressedBaseExecutableRule?] using authorized.symm

#print axioms decodeCompressedExecutableCapture_eq_none_of_dynamic
#print axioms sourceAssertionRequestSpace_capabilities
#print axioms directAssertionMatcherRow_rejoin_origin
#print axioms directAssertionMatcherRow_rejoin_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionCapabilityOrigin
