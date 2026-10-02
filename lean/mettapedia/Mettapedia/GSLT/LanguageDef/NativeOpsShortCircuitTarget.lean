import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitFacts

/-!
# Exact target execution of a short-circuit constructor

Selected arms execute the real right-operand fragment before assignment and
scope closure. Skipped arms require no right-operand read or execution. The
split retains raw early returns and the complete actual post-state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom Condition)
open NativeLowering (Expression)

theorem target_assign_temporary_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {type : NativeType}
    {atom : Atom} {value : TargetValue} (read : TargetAtomEval interface frame state atom value)
    (live : frame.temporaryNames.contains identity = true) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.assign (.temporary identity type) atom) frame state out ↔
      out = ⟨.normal, targetUpdateTemporary frame identity value, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | assign otherRead stored =>
        cases target_atom_unique read otherRead
        cases stored
        rfl
  · intro same
    subst out
    exact .assign read (.temporary live)

theorem target_assign_temporary_run_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {type : NativeType}
    {atom : Atom} {value : TargetValue} (read : TargetAtomEval interface frame state atom value)
    (live : frame.temporaryNames.contains identity = true) (root : List Instruction)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.assign (.temporary identity type) atom] frame state out ↔
      out = ⟨.normal, targetUpdateTemporary frame identity value, state⟩ := by
  rw [target_normal_then_exact (target_assign_temporary_instruction_exact read live)]
  exact target_run_empty_exact _ _ _ _

theorem short_circuit_condition_evaluates {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {value : Bool}
    (continueValue : Bool) (read : TargetAtomEval interface frame state atom (.bool value)) :
    TargetConditionEval interface frame state (shortCircuitCondition continueValue atom)
      (value == continueValue) := by
  cases continueValue <;> cases value
  · exact .negated read
  · exact .negated read
  · exact .value read
  · exact .value read

/-- Only the selected body needs a no-outward-jump certificate. -/
theorem target_single_branch_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : Condition} {yes no : List Instruction} {selected : Bool}
    {frame : TargetFrame} {state : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected)
    (checked : jumpFreeCode (if selected then yes else no) = true)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.branch condition yes no] frame state out ↔
      ∃ inner, TargetRun interface heap calls result
          (if selected then yes else no) (if selected then yes else no) frame state inner ∧
        out = targetCloseBlock frame inner := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
        cases remaining
        exact (target_branch_instruction_exact tested _).mp first
    | «return» first => exact (target_branch_instruction_exact tested _).mp first
    | resume first _ _ | escape first _ =>
        obtain ⟨inner, innerRan, same⟩ := (target_branch_instruction_exact tested _).mp first
        have jumped := (congrArg TargetBlockOutcome.flow same).symm
        exact False.elim (jump_free_run_cannot_jump innerRan _ checked jumped)
  · rintro ⟨inner, innerRan, same⟩
    subst out
    cases flow : inner.flow with
    | normal =>
        rcases inner with ⟨innerFlow, after, post⟩
        cases flow
        exact .next (.branch tested innerRan) (.nil _ _ _)
    | returned value =>
        rcases inner with ⟨innerFlow, after, post⟩
        cases flow
        exact .return (.branch tested innerRan)
    | jumped label =>
        exact False.elim (jump_free_run_cannot_jump innerRan label checked flow)

theorem target_short_circuit_skip_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (continueValue : Bool) {atom : Atom} {frame : TargetFrame} {state : TargetState World}
    (hscope : TemporariesScoped frame)
    (read : TargetAtomEval interface frame state atom (.bool (!continueValue)))
    (right : List Instruction) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.branch (shortCircuitCondition continueValue atom) right []] frame state out ↔
      out = ⟨.normal, frame, state⟩ := by
  have selected : ((!continueValue) == continueValue) = false := by cases continueValue <;> rfl
  have tested := short_circuit_condition_evaluates continueValue read
  rw [selected] at tested
  rw [target_single_branch_exact tested (by simp only [Bool.false_eq_true, if_false, jumpFreeCode])]
  constructor
  · rintro ⟨inner, ran, same⟩
    cases (target_run_empty_exact _ _ _ _).mp ran
    simpa only [targetCloseBlock, targetLeaveScope_self frame state hscope] using same
  · intro same
    subst out
    exact ⟨⟨.normal, frame, state⟩, .nil _ _ _, by
      simp only [targetCloseBlock, targetLeaveScope_self frame state hscope]⟩

/-- The selected right operand may alter memory or return; those effects are retained verbatim. -/
theorem target_short_circuit_taken_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (continueValue : Bool) {atom : Atom} {identity : Nat} {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state atom (.bool continueValue))
    (right : Expression) (checked : jumpFreeCode right.code = true)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.branch (shortCircuitCondition continueValue atom)
        (right.code ++ [.assign (.temporary identity .bool) right.result]) []] frame state out ↔
      (∃ after post value,
        TargetRun interface heap calls result
          (right.code ++ [.assign (.temporary identity .bool) right.result]) right.code frame state
          ⟨.normal, after, post⟩ ∧
        TargetAtomEval interface after post right.result value ∧
        after.temporaryNames.contains identity = true ∧
        out = targetCloseBlock frame ⟨.normal, targetUpdateTemporary after identity value, post⟩) ∨
      (∃ value after post,
        TargetRun interface heap calls result
          (right.code ++ [.assign (.temporary identity .bool) right.result]) right.code frame state
          ⟨.returned value, after, post⟩ ∧
        out = targetCloseBlock frame ⟨.returned value, after, post⟩) := by
  have tested := short_circuit_condition_evaluates continueValue read
  have self : (continueValue == continueValue) = true := by cases continueValue <;> rfl
  rw [self] at tested
  have bodyChecked : jumpFreeCode (right.code ++ [.assign (.temporary identity .bool) right.result]) = true := by
    simp only [jump_free_append, checked, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
  rw [target_single_branch_exact tested (by exact bodyChecked)]
  constructor
  · rintro ⟨inner, ran, same⟩
    rcases target_split_jump_free_prefix _ right.code
      [.assign (.temporary identity .bool) right.result] checked ran with
      ⟨after, post, beforeRan, suffix⟩ | ⟨value, after, post, beforeRan, exactInner⟩
    · cases suffix with
      | next first remaining =>
          cases first with
          | assign read stored =>
              cases stored with
              | temporary live =>
                  cases remaining
                  exact .inl ⟨after, post, _, beforeRan, read, live, same⟩
      | «return» first | resume first _ _ | escape first _ => cases first
    · cases exactInner
      exact .inr ⟨value, after, post, beforeRan, same⟩
  · rintro (⟨after, post, value, beforeRan, read, live, same⟩ | ⟨value, after, post, beforeRan, same⟩)
    · refine ⟨⟨.normal, targetUpdateTemporary after identity value, post⟩, ?_, same⟩
      exact target_append_normal _ _ _ checked beforeRan
        ((target_assign_temporary_run_exact read live _ _).mpr rfl)
    · exact ⟨⟨.returned value, after, post⟩,
        target_append_returned _ _ _ checked beforeRan, same⟩

theorem target_short_circuit_copy_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {left : Atom} {value : Bool}
    (unused : frame.temporaryNames.contains identity = false)
    (read : TargetAtomEval interface frame state left (.bool value))
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.temporary identity .bool (.copy left) :: rest) frame state out ↔
      TargetRun interface heap calls result root rest
        (targetDeclareTemporary frame identity (.bool value)) state out :=
  target_normal_then_exact (target_temporary_instruction_exact unused (.copy read)) root rest out

theorem updated_temporary_atom {World : Type} (interface : Interface) (frame : TargetFrame)
    (state : TargetState World) (identity : Nat) (type : NativeType) (value : TargetValue)
    (live : frame.temporaryNames.contains identity = true) :
    TargetAtomEval interface (targetUpdateTemporary frame identity value) state
      (.temporary identity type) value :=
  .temporary (by simp only [targetUpdateTemporary, if_true]) live

theorem close_updated_temporary_read {World : Type} (interface : Interface)
    (marker current : TargetFrame) (state : TargetState World)
    (identity : Nat) (type : NativeType) (value : TargetValue)
    (outer : marker.temporaryNames.contains identity = true)
    (inner : current.temporaryNames.contains identity = true) :
    TargetAtomEval interface
      (targetCloseBlock marker ⟨.normal, targetUpdateTemporary current identity value, state⟩).frame
      (targetCloseBlock marker ⟨.normal, targetUpdateTemporary current identity value, state⟩).state
      (.temporary identity type) value :=
  close_block_preserves_temporary_read outer (updated_temporary_atom interface current state identity type value inner)

theorem close_updated_temporary_protection {World : Type} {lower upper identity : Nat}
    {marker current : TargetFrame} (hscope : TemporariesScoped marker)
    (protection : TemporaryProtection upper marker current) (within : lower ≤ upper)
    (fresh : lower < identity) (value : TargetValue) (state : TargetState World) :
    TemporaryProtection lower marker
      (targetCloseBlock marker ⟨.normal, targetUpdateTemporary current identity value, state⟩).frame :=
  close_block_temporary_protection hscope
    (temporary_protection_trans (temporary_protection_weaken within protection)
      (update_temporary_protects current value fresh)) state

end Mettapedia.GSLT.LanguageDef.NativeOps
