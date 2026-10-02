import Mettapedia.GSLT.LanguageDef.NativeOpsCanonicalExecution
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarControls

/-! Execution controls for typed initializer normalization and scoped transfers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.CanonicalControls

open NativeIR (Instruction Atom)

theorem scoped_zero_return_executes {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat)
    (unused : frame.temporaryNames.contains identity = false) :
    TargetRun interface heap calls .word []
      (canonicalCode [.scope [.temporary identity .word (.zero .word),
        .return (.temporary identity .word)]]) frame state
      (targetCloseBlock frame
        ⟨.returned (.word 0), targetDeclareTemporary frame identity (.word 0), state⟩) := by
  apply (canonical_run_empty_root_exact _ _ _ _ _ _ _ _).mpr
  have inner : TargetRun interface heap calls .word
      [.temporary identity .word (.zero .word), .return (.temporary identity .word)]
      [.temporary identity .word (.zero .word), .return (.temporary identity .word)] frame state
      ⟨.returned (.word 0), targetDeclareTemporary frame identity (.word 0), state⟩ :=
    .next (.temporary unused (.zero .unsignedWord))
      (.return (.return (declared_temporary_atom _ _ _ _ _ _)))
  exact .return (.scope inner)

theorem scoped_zero_jump_resumes_after_unwind {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat)
    (label : NativeIR.Label) (unused : frame.temporaryNames.contains identity = false) :
    let closed := targetCloseBlock frame
      ⟨.jumped label, targetDeclareTemporary frame identity (.bool false), state⟩
    let code := [.scope [.temporary identity .bool (.zero .bool), .jump label],
      .label label, .return (.word 7)]
    TargetRun interface heap calls .word (canonicalCode code) (canonicalCode code)
      frame state ⟨.returned (.word 7), closed.frame, closed.state⟩ := by
  dsimp only
  apply (canonical_run_exact _ _ _ _ _ _ _ _ _).mpr
  have inner : TargetRun interface heap calls .word
      [.temporary identity .bool (.zero .bool), .jump label]
      [.temporary identity .bool (.zero .bool), .jump label] frame state
      ⟨.jumped label, targetDeclareTemporary frame identity (.bool false), state⟩ :=
    .next (.temporary unused (.zero .boolean))
      (.escape (.jump label _ _) (by simp only [targetAfterLabel?]))
  exact .resume (suffix := [.return (.word 7)]) (.scope inner)
    (by simp [targetAfterLabel?]) (.return (.return (.word 7)))

theorem zero_iteration_loop_prunes_normalized_body {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (counter : Nat)
    (body : List Instruction) (unused : frame.temporaryNames.contains counter = false) :
    TargetInstructionEval interface heap calls .word
      (canonicalInstruction (.forWord counter (.word 0) body)) frame state
      (targetCloseBlock frame
        ⟨.normal, targetDeclareTemporary frame counter (.word 0), state⟩) := by
  apply (canonical_instruction_exact _ _ _ _ _ _ _ _).mpr
  apply TargetInstructionEval.forWord unused
  apply TargetForEval.done
  · exact .iterationCounter (declare_temporary_read _ _ _)
      (by simp [targetDeclareTemporary])
  · exact .word 0
  · decide +kernel

theorem existing_fault_cannot_be_normalized_to_success {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame after : TargetFrame) (state post : TargetState World)
    (fault : NativeWord64.Fault) (failed : state.fault = some fault) :
    ¬ TargetRun interface heap calls .bool [] (canonicalCode [.checkContext])
      frame state ⟨.normal, after, post⟩ := by
  intro ran
  have original := (canonical_run_empty_root_exact _ _ _ _ [.checkContext] _ _ _).mp ran
  cases original with
  | next first _ =>
      cases first with
      | contextClear clear => rw [failed] at clear; cases clear
  | resume first _ _ => cases first

theorem normalization_does_not_restore_a_deleted_guard {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : BitVec 64)
    (out : TargetBlockOutcome World) :
    ¬ TargetRun interface heap calls .word []
      (canonicalCode [.temporary identity .word
        (.binary (.word .div) (.word left) (.word 0))]) frame state out := by
  intro ran
  have original := (canonical_run_empty_root_exact _ _ _ _ _ _ _ _).mp ran
  exact ScalarControls.missing_division_guard_has_no_run interface heap calls frame state identity left out original

end Mettapedia.GSLT.LanguageDef.NativeOps.CanonicalControls
