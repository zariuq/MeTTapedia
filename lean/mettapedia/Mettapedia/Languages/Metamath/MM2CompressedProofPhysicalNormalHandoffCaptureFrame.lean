import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff

/-!
# Physical normal-handoff capture frame

Expression-head separation transports opaque compiler-owned rows through the
complete physical compressed-assertion launch without inspecting their
payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-- One expression head is physically separated from every instantiation of
all three predecessor controls. -/
theorem expression_head_predecessor_key_safety
    (candidateHead : String) (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (pendingDifferent : candidateHead ≠ "mm-compressed-step-pending")
    (lookupDifferent : candidateHead ≠ "mm-compressed-heap-lookup")
    (machineDifferent : candidateHead ≠ "mm-compressed-machine") :
    DecoratedAssertionPredecessorKeySafety
      (.expression (.symbol candidateHead :: candidateTail)) where
  pending := by
    intro substitution removed instantiates
    exact instantiated_directAssertionPending_key_ne substitution candidateHead
      candidateTail candidateArity candidatePositive candidateBound
      pendingDifferent instantiates
  lookup := by
    intro substitution removed instantiates
    exact instantiated_directAssertionLookup_key_ne substitution candidateHead
      candidateTail candidateArity candidatePositive candidateBound
      lookupDifferent instantiates
  machine := by
    intro substitution removed instantiates
    exact instantiated_directAssertionMachine_key_ne substitution candidateHead
      candidateTail candidateArity candidatePositive candidateBound
      machineDifferent instantiates

/-- An ordinary row with a non-executable symbolic head survives erasure of
the selected assertion directive. -/
theorem expression_head_survives_assertion_directive_erasure
    {space : List Atom} (candidateHead : String) (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (executableDifferent : candidateHead ≠ "exec")
    (present : .expression (.symbol candidateHead :: candidateTail) ∈ space) :
    .expression (.symbol candidateHead :: candidateTail) ∈
      morkEraseSupport space decoratedDirectAssertionDirective.atom := by
  obtain ⟨location, input, output, ruleShape⟩ :=
    extractSupportedSourceExecFact_exec_shape
      extract_decoratedDirectAssertionRule_exact
  have directiveShape :
      decoratedDirectAssertionDirective.atom =
        .expression [.symbol "exec", location, input, output] := by
    rw [decoratedDirectAssertionDirective_atom_exact]
    exact ruleShape
  apply mem_morkEraseSupport_of_mem_of_key_ne present
  rw [directiveShape]
  apply morkSupportKey_expression_symbol_head_ne
  · exact candidateArity
  · norm_num
  · exact candidatePositive
  · decide
  · exact candidateBound
  · decide
  · exact executableDifferent

/-- A physically present non-executable expression row whose head also differs
from every predecessor control survives the complete assertion launch. -/
theorem physical_decorated_assertion_preserves_expression_head_row
    {space : List Atom} (candidateHead : String) (candidateTail : List Atom)
    (candidateArity : candidateTail.length + 1 < 64)
    (candidatePositive : 0 < (morkUtf8Bytes candidateHead).length)
    (candidateBound : (morkUtf8Bytes candidateHead).length < 64)
    (executableDifferent : candidateHead ≠ "exec")
    (pendingDifferent : candidateHead ≠ "mm-compressed-step-pending")
    (lookupDifferent : candidateHead ≠ "mm-compressed-heap-lookup")
    (machineDifferent : candidateHead ≠ "mm-compressed-machine")
    (present : .expression (.symbol candidateHead :: candidateTail) ∈ space) :
    .expression (.symbol candidateHead :: candidateTail) ∈
      cFireRuleScopedSourceExecFact space
        decoratedDirectAssertionDirective := by
  apply physical_decorated_assertion_preserves_row_of_key_safety
    (expression_head_predecessor_key_safety candidateHead candidateTail
      candidateArity candidatePositive candidateBound pendingDifferent
      lookupDifferent machineDifferent)
  exact expression_head_survives_assertion_directive_erasure candidateHead
    candidateTail candidateArity candidatePositive candidateBound
    executableDifferent present

/-- The compiler-owned finite-loader capture is still present after the
physical assertion launcher fires. -/
theorem compressedNormalHandoffLoaderCaptureRow_survives_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    compressedNormalHandoffLoaderCaptureRow ∈
      cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
          index cursor assertion)
        decoratedDirectAssertionDirective := by
  change
    Atom.expression
        [.symbol "mm-internal-compressed-normal-handoff-loader",
          compressedNormalHandoffLoadRule] ∈ _
  apply physical_decorated_assertion_preserves_expression_head_row
    "mm-internal-compressed-normal-handoff-loader"
    [compressedNormalHandoffLoadRule]
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  unfold sourceDecoratedAssertionBridgeReadySpace
  apply List.mem_append_right
  exact List.mem_cons_self

/-- The compiler-owned terminal-loader capture is still present after the
physical assertion launcher fires. -/
theorem compressedNormalHandoffFinishCaptureRow_survives_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    compressedNormalHandoffFinishCaptureRow ∈
      cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
          index cursor assertion)
        decoratedDirectAssertionDirective := by
  change
    Atom.expression
        [.symbol "mm-internal-compressed-normal-handoff-finish",
          compressedNormalHandoffFinishRule] ∈ _
  apply physical_decorated_assertion_preserves_expression_head_row
    "mm-internal-compressed-normal-handoff-finish"
    [compressedNormalHandoffFinishRule]
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  unfold sourceDecoratedAssertionBridgeReadySpace
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

/-- Every compiler-owned row needed by the compressed-to-normal bridge
survives the complete physical assertion launch. -/
theorem normalHandoffBridgeCaptureRows_survive_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    ∀ row ∈ normalHandoffBridgeCaptureRows,
      row ∈ cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionBridgeReadySpace context state ledger scanner
          index cursor assertion)
        decoratedDirectAssertionDirective := by
  intro row member
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact compressedNormalHandoffLoaderCaptureRow_survives_launch context
      state ledger scanner index cursor assertion
  · exact compressedNormalHandoffFinishCaptureRow_survives_launch context
      state ledger scanner index cursor assertion

#print axioms expression_head_predecessor_key_safety
#print axioms expression_head_survives_assertion_directive_erasure
#print axioms physical_decorated_assertion_preserves_expression_head_row
#print axioms compressedNormalHandoffLoaderCaptureRow_survives_launch
#print axioms compressedNormalHandoffFinishCaptureRow_survives_launch
#print axioms normalHandoffBridgeCaptureRows_survive_launch

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame
