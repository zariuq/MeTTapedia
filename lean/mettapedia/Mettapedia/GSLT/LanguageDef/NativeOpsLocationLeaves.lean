import Mettapedia.GSLT.LanguageDef.NativeOpsExpressionLeaves

/-!
# Actual lowering of source local locations

A local address is the existing invocation cell, not the address of a private
C temporary. Both relations preserve its exact alias and the whole state.
Neither non-nullness nor name admission certifies a later live dereference.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)

theorem source_variable_location_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (name : String) (before : SourceState World) (out : SourceLocationOutcome World) :
    SourceLocationEval interface heap calls frame (.variable name) before out ↔
      ∃ address, sourceLocalAddress frame name = some address ∧ out = ⟨.ok address, before⟩ := by
  constructor
  · intro ran
    cases ran with
    | strict operands evaluated operation =>
        cases Option.some.inj operands
        cases (source_arguments_nil_exact before _).mp evaluated
        exact operation
    | strictFault operands evaluated =>
        cases Option.some.inj operands
        cases (source_arguments_nil_exact before _).mp evaluated
  · rintro ⟨address, located, same⟩
    subst out
    exact .strict rfl (.nil before) ⟨address, located, rfl⟩

theorem target_local_address_exact {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) (name : String) (type : NativeType)
    (address : Address) :
    TargetAtomEval interface frame state (.localAddress name type) (.reference (some address)) ↔
      targetLocalAddress frame name = some address := by
  constructor
  · intro read; cases read with | localAddress found => exact found
  · exact TargetAtomEval.localAddress

theorem actual_variable_location_run_exact {SourceWorld TargetWorld : Type}
    {interface : Interface} {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (name : String) (scope : Scope)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression)
    (compiled : NativeLowering.location? interface scope (.variable name) supply = some output)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (result : NativeType) (root : List Instruction)
    (sourceOut : SourceLocationOutcome SourceWorld) (out : TargetBlockOutcome TargetWorld) :
    (SourceLocationEval interface sourceHeap sourceCalls sourceFrame (.variable name) source sourceOut ∧
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) ↔
    ∃ address, TargetAtomEval interface targetFrame target output.result (.reference (some address)) ∧
      sourceOut = ⟨.ok address, source⟩ ∧ out = ⟨.normal, targetFrame, target⟩ := by
  cases admitted : lookupVariable scope name with
  | none => simp only [NativeLowering.location?, inferLocation, admitted] at compiled; cases compiled
  | some type =>
      simp only [NativeLowering.location?, inferLocation, admitted] at compiled
      cases Option.some.inj compiled
      change (SourceLocationEval interface sourceHeap sourceCalls sourceFrame (.variable name) source sourceOut ∧
        TargetRun interface targetHeap targetCalls result root [] targetFrame target out) ↔ _
      rw [source_variable_location_exact, target_run_empty_exact]
      constructor
      · rintro ⟨⟨address, located, exactSource⟩, exactTarget⟩
        exact ⟨address, .localAddress ((local_address_correspondence frames name).trans located),
          exactSource, exactTarget⟩
      · rintro ⟨address, read, exactSource, exactTarget⟩
        have located := (target_local_address_exact interface targetFrame target name type address).mp read
        rw [local_address_correspondence frames] at located
        exact ⟨⟨address, located, exactSource⟩, exactTarget⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
