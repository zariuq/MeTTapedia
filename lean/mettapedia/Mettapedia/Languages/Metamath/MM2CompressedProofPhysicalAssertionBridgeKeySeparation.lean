import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame

/-!
# Physical key separation at the compressed assertion bridge

The compact MORK support identity of the captured normal-dispatch bridge is
distinct from every predecessor scheduler shell, every dynamic runtime row,
and the dormant assertion rejoin.  All comparisons use opaque row shapes;
the executable bodies are never normalized by downstream proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A dynamic runtime row cannot occupy the physical key of the captured
normal-dispatch executable. -/
theorem dynamicRow_key_ne_normalDispatchBridge
    {row : Atom} (head : String)
    (headExact : compressedDynamicRowHead? row = some head)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "exec") :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  rcases (compressedDynamicRowHead?_eq_some_iff row head).mp headExact with
    ⟨tail, rowShape⟩
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    head "exec" ⟨tail, rowShape⟩ compressedNormalDispatchBridgeRule_head_shape
      headPositive (by decide) headBound (by decide) different

private theorem bridge_exec_shape :
    ∃ input output,
      compressedNormalDispatchBridgeRule =
        .expression
          [.symbol "exec",
           .expression
             [.symbol "31", .symbol "mm-compressed-normal-dispatch-bridge"],
           input, output] := by
  exact compressedNormalDispatchBridgeRule_exec_shape

private theorem executable_before_bridge_key_ne
    {row : Atom} (priority name : String)
    (shape : ∃ input output,
      row =
        .expression
          [.symbol "exec", .expression [.symbol priority, .symbol name],
           input, output])
    (priorityPositive : 0 < (morkUtf8Bytes priority).length)
    (priorityBound : (morkUtf8Bytes priority).length < 64)
    (namePositive : 0 < (morkUtf8Bytes name).length)
    (nameBound : (morkUtf8Bytes name).length < 64)
    (priorityDifferent : priority ≠ "31")
    (prefixOrdered : ∀ leftRest rightRest,
      lexLt
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes priority ++ compactSymbolBytes name ++ leftRest)
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "31" ++
            compactSymbolBytes "mm-compressed-normal-dispatch-bridge" ++
              rightRest) = true) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule :=
  morkSupportKey_exec_two_symbol_location_ne_of_shapes
    priority name "31" "mm-compressed-normal-dispatch-bridge" shape
      bridge_exec_shape priorityPositive priorityBound namePositive nameBound
      (by decide) (by decide) (by decide) (by decide) priorityDifferent
      prefixOrdered

private theorem symbolic_row_key_ne_executable
    (rowHead : String) (rowTail : List Atom) {executable : Atom}
    (executableShape : ∃ location input output,
      executable =
        .expression [.symbol "exec", location, input, output])
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec") :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey executable := by
  obtain ⟨location, input, output, shape⟩ := executableShape
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    rowHead "exec" ⟨rowTail, rfl⟩ ⟨[location, input, output], shape⟩
      rowHeadPositive (by decide) rowHeadBound (by decide) nonExecutable

/-- A non-executable symbolic row cannot be erased with the compact proof-step
shell.  The shell body remains opaque at every downstream use. -/
theorem symbolicRow_key_ne_compressedProofStep
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec") :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey compressedProofStepDirective.atom := by
  change morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
    morkSupportKey compressedProofStepRule
  obtain ⟨input, output, shape⟩ := compressedProofStepRule_exec_shape
  exact symbolic_row_key_ne_executable rowHead rowTail
    ⟨_, input, output, shape⟩ rowHeadPositive rowHeadBound nonExecutable

/-- A non-executable symbolic row cannot be erased with the lookup-fault
shell. -/
theorem symbolicRow_key_ne_compressedHeapLookupFault
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec") :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey compressedHeapLookupFaultDirective.atom := by
  change morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
    morkSupportKey compressedHeapLookupFaultRule
  obtain ⟨input, output, shape⟩ := compressedHeapLookupFaultRule_exec_shape
  exact symbolic_row_key_ne_executable rowHead rowTail
    ⟨_, input, output, shape⟩ rowHeadPositive rowHeadBound nonExecutable

/-- A non-executable symbolic row cannot be erased with the cursor-assertion
shell. -/
theorem symbolicRow_key_ne_decoratedCursorAssertion
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec") :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey decoratedCursorAssertionDirective.atom := by
  have atomExact : decoratedCursorAssertionDirective.atom =
      compressedAssertionLaunchRuleWithNormalBridge := by
    rw [decoratedCursorAssertionDirective_atom_exact]
    exact decoratedSpeculativeBody_sourceOpaque_exact
  obtain ⟨input, output, shape⟩ :=
    compressedAssertionLaunchRuleWithNormalBridge_exec_shape
  exact symbolic_row_key_ne_executable rowHead rowTail
    ⟨_, input, output, atomExact.trans shape⟩ rowHeadPositive rowHeadBound
      nonExecutable

/-- A non-executable symbolic row cannot be erased with the lookup-advance
shell. -/
theorem symbolicRow_key_ne_compressedHeapLookupAdvance
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec") :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey compressedHeapLookupAdvanceDirective.atom := by
  change morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
    morkSupportKey compressedHeapLookupAdvanceRule
  obtain ⟨input, output, shape⟩ := compressedHeapLookupAdvanceRule_exec_shape
  exact symbolic_row_key_ne_executable rowHead rowTail
    ⟨_, input, output, shape⟩ rowHeadPositive rowHeadBound nonExecutable

theorem compressedProofStep_key_ne_normalDispatchBridge :
    morkSupportKey compressedProofStepDirective.atom ≠
      morkSupportKey compressedNormalDispatchBridgeRule := by
  change morkSupportKey compressedProofStepRule ≠
    morkSupportKey compressedNormalDispatchBridgeRule
  exact executable_before_bridge_key_ne "08" "mm-compressed-proof-step"
    compressedProofStepRule_exec_shape (by decide) (by decide) (by decide)
      (by decide) (by decide) (by intro _ _; rfl)

theorem decoratedCursorAssertion_key_ne_normalDispatchBridge :
    morkSupportKey decoratedCursorAssertionDirective.atom ≠
      morkSupportKey compressedNormalDispatchBridgeRule := by
  have atomExact : decoratedCursorAssertionDirective.atom =
      compressedAssertionLaunchRuleWithNormalBridge := by
    rw [decoratedCursorAssertionDirective_atom_exact]
    exact decoratedSpeculativeBody_sourceOpaque_exact
  exact executable_before_bridge_key_ne "08"
    "mm-compressed-proof-step-assertion"
      (by
        obtain ⟨input, output, launchShape⟩ :=
          compressedAssertionLaunchRuleWithNormalBridge_exec_shape
        exact ⟨input, output, atomExact.trans launchShape⟩)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro _ _; rfl)

theorem compressedHeapLookupFault_key_ne_normalDispatchBridge :
    morkSupportKey compressedHeapLookupFaultDirective.atom ≠
      morkSupportKey compressedNormalDispatchBridgeRule := by
  change morkSupportKey compressedHeapLookupFaultRule ≠
    morkSupportKey compressedNormalDispatchBridgeRule
  exact executable_before_bridge_key_ne "08"
    "mm-compressed-heap-lookup-fault" compressedHeapLookupFaultRule_exec_shape
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro _ _; rfl)

theorem compressedHeapLookupAdvance_key_ne_normalDispatchBridge :
    morkSupportKey compressedHeapLookupAdvanceDirective.atom ≠
      morkSupportKey compressedNormalDispatchBridgeRule := by
  change morkSupportKey compressedHeapLookupAdvanceRule ≠
    morkSupportKey compressedNormalDispatchBridgeRule
  exact executable_before_bridge_key_ne "09"
    "mm-compressed-heap-lookup-advance"
      compressedHeapLookupAdvanceRule_exec_shape (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro _ _; rfl)

theorem compressedAssertionRejoin_key_ne_normalDispatchBridge :
    morkSupportKey compressedAssertionRejoinRule ≠
      morkSupportKey compressedNormalDispatchBridgeRule := by
  exact Ne.symm
    (morkSupportKey_exec_two_symbol_location_ne_of_shapes
      "31" "mm-compressed-normal-dispatch-bridge"
        "32" "mm-compressed-assertion-rejoin" bridge_exec_shape
        compressedAssertionRejoinRule_exec_shape (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by intro _ _; rfl))

#print axioms dynamicRow_key_ne_normalDispatchBridge
#print axioms compressedProofStep_key_ne_normalDispatchBridge
#print axioms decoratedCursorAssertion_key_ne_normalDispatchBridge
#print axioms compressedHeapLookupFault_key_ne_normalDispatchBridge
#print axioms compressedHeapLookupAdvance_key_ne_normalDispatchBridge
#print axioms compressedAssertionRejoin_key_ne_normalDispatchBridge
#print axioms symbolicRow_key_ne_compressedProofStep
#print axioms symbolicRow_key_ne_compressedHeapLookupFault
#print axioms symbolicRow_key_ne_decoratedCursorAssertion
#print axioms symbolicRow_key_ne_compressedHeapLookupAdvance

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
