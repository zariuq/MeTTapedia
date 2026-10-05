import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsTemporaryFrames
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarObservation

/-!
# Exact native execution of constant-return switch arms

These laws execute the existing target relation. A selected arm declares a
private word and returns it; closing the arm discards that temporary while
retaining the selector, all caller locals and the complete runtime state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)

theorem target_select_case_map {Item : Type} (items : List Item)
    (key : Item → BitVec 64) (body : Item → List Instruction)
    (selector : BitVec 64) (otherwise : List Instruction) :
    targetSelectCase selector (items.map fun item => (key item, body item)) otherwise =
      match items.find? (fun item => key item == selector) with
      | some item => body item
      | none => otherwise := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      by_cases selected : key item == selector
      · simp [targetSelectCase, selected]
      · simpa [targetSelectCase, selected] using ih

theorem close_private_return {World : Type} (frame : TargetFrame) (state : TargetState World)
    (identity : Nat) (value : TargetValue)
    (unused : frame.temporaryNames.contains identity = false) (hscope : TemporariesScoped frame) :
    targetCloseBlock frame ⟨.returned value, targetDeclareTemporary frame identity value, state⟩ =
      ⟨.returned value, frame, state⟩ := by
  have temporaries : (fun candidate => if frame.temporaryNames.contains candidate then
        (targetDeclareTemporary frame identity value).temporaries candidate else none) = frame.temporaries := by
    funext candidate
    by_cases live : frame.temporaryNames.contains candidate = true
    · have different : candidate ≠ identity := by
        intro same
        subst candidate
        rw [unused] at live
        cases live
      simp only [if_pos live, targetDeclareTemporary, different, if_false]
    · have absent := Bool.eq_false_iff.mpr live
      rw [if_neg live, hscope candidate absent]
  change (fun candidate => if frame.temporaryNames.contains candidate then
    (if candidate = identity then some value else frame.temporaries candidate) else none) = frame.temporaries at temporaries
  simp only [targetCloseBlock, targetLeaveScope, targetDeclareTemporary, targetDropLocals_empty]
  rw [temporaries]

theorem target_literal_return_run_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (value : BitVec 64)
    (unused : frame.temporaryNames.contains identity = false)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.temporary identity .word (.word value) :: .return (.temporary identity .word) :: rest)
      frame state out ↔
      out = ⟨.returned (.word value), targetDeclareTemporary frame identity (.word value), state⟩ := by
  rw [target_normal_then_exact (target_temporary_instruction_exact unused (.word value))]
  exact target_return_then_exact (declared_temporary_atom _ _ _ _ _ _) root rest out

theorem target_switch_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {selector : Atom} {value : BitVec 64} {frame : TargetFrame} {state : TargetState World}
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    (read : TargetAtomEval interface frame state selector (.word value))
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.switch selector arms otherwise) frame state out ↔
      ∃ inner,
        TargetRun interface heap calls result (targetSelectCase value arms otherwise)
          (targetSelectCase value arms otherwise) frame state inner ∧
        out = targetCloseBlock frame inner := by
  constructor
  · intro ran
    cases ran with
    | switch otherRead body =>
        cases target_atom_unique read otherRead
        exact ⟨_, body, rfl⟩
  · rintro ⟨inner, body, same⟩
    subst out
    exact .switch read body

theorem target_literal_switch_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {selector : Atom} {key value : BitVec 64} {frame : TargetFrame} {state : TargetState World}
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction} {identity : Nat}
    (read : TargetAtomEval interface frame state selector (.word key))
    (selected : targetSelectCase key arms otherwise =
      [.temporary identity .word (.word value), .return (.temporary identity .word)])
    (unused : frame.temporaryNames.contains identity = false) (hscope : TemporariesScoped frame)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.switch selector arms otherwise) frame state out ↔
      out = ⟨.returned (.word value), frame, state⟩ := by
  rw [target_switch_instruction_exact read]
  constructor
  · rintro ⟨inner, ran, same⟩
    rw [selected] at ran
    cases (target_literal_return_run_exact frame state identity value unused _ [] _).mp ran
    exact same.trans (close_private_return frame state identity (.word value) unused hscope)
  · intro same
    subst out
    refine ⟨⟨.returned (.word value), targetDeclareTemporary frame identity (.word value), state⟩, ?_, ?_⟩
    · rw [selected]
      exact (target_literal_return_run_exact frame state identity value unused _ [] _).mpr rfl
    · exact (close_private_return frame state identity (.word value) unused hscope).symm

theorem target_literal_switch_run_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {selector : Atom} {key value : BitVec 64} {frame : TargetFrame} {state : TargetState World}
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction} {identity : Nat}
    (read : TargetAtomEval interface frame state selector (.word key))
    (selected : targetSelectCase key arms otherwise =
      [.temporary identity .word (.word value), .return (.temporary identity .word)])
    (unused : frame.temporaryNames.contains identity = false) (hscope : TemporariesScoped frame)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.switch selector arms otherwise :: rest) frame state out ↔
      out = ⟨.returned (.word value), frame, state⟩ :=
  target_returning_then_exact (target_literal_switch_instruction_exact read selected unused hscope) root rest out

end Mettapedia.GSLT.LanguageDef.NativeOps
