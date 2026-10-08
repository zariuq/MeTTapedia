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

/-- A proved normally returning selected arm supplies its whole frame and
state. Its lexical closure is the branch's only additional operation. -/
theorem target_normal_branch_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : Condition} {yes no : List Instruction} {selected : Bool}
    {frame after : TargetFrame} {state post : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected)
    (armExact : ∀ inner, TargetRun interface heap calls result
      (if selected then yes else no) (if selected then yes else no) frame state inner ↔
      inner = ⟨.normal, after, post⟩)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.branch condition yes no) frame state out ↔
      out = targetCloseBlock frame ⟨.normal, after, post⟩ := by
  rw [target_branch_instruction_exact tested]
  constructor
  · rintro ⟨inner, ran, same⟩
    cases (armExact _).mp ran
    exact same
  · intro same
    exact ⟨⟨.normal, after, post⟩, (armExact _).mpr rfl, same⟩

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

/-- The selected short-circuit arm updates the inherited result cell and
closes its private scope. The skipped arm retains the incoming frame. -/
def shortCircuitFrame {World : Type} (continueValue : Bool) (marker current : TargetFrame)
    (state : TargetState World) (identity : Nat) (ready value : Bool) : TargetFrame :=
  if ready = continueValue then
    (targetCloseBlock marker ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩).frame
  else marker

/-- Exact execution for a pure normally returning right operand, including
its private scope. Right-operand evidence is needed only when it is selected. -/
theorem short_circuit_rhs_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (continueValue : Bool) {marker current : TargetFrame} {state : TargetState World}
    {identity : Nat} {ready value : Bool} {rhs : List Instruction} {resultAtom : Atom}
    (hscope : TemporariesScoped marker)
    (condition : TargetAtomEval interface marker state (.temporary identity .bool) (.bool ready))
    (checked : jumpFreeCode rhs = true)
    (rhsExact : ready = continueValue → ∀ root out,
      TargetRun interface heap calls .bool root rhs marker state out ↔
        out = ⟨.normal, current, state⟩)
    (resultRead : TargetAtomEval interface current state resultAtom (.bool value))
    (live : current.temporaryNames.contains identity = true)
    (sameLocals : current.nextLocal = marker.nextLocal)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls .bool
      (.branch (shortCircuitCondition continueValue (.temporary identity .bool))
        (rhs ++ [.assign (.temporary identity .bool) resultAtom]) []) marker state out ↔
      out = ⟨.normal, shortCircuitFrame continueValue marker current state identity ready value, state⟩ := by
  have tested := short_circuit_condition_evaluates continueValue condition
  by_cases selected : ready = continueValue
  · have sameBool : (ready == continueValue) = true := beq_iff_eq.mpr selected
    rw [sameBool] at tested
    have armExact (inner : TargetBlockOutcome World) :
        TargetRun interface heap calls .bool
          (rhs ++ [.assign (.temporary identity .bool) resultAtom])
          (rhs ++ [.assign (.temporary identity .bool) resultAtom]) marker state inner ↔
          inner = ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩ := by
      rw [target_normal_prefix_then_exact checked (rhsExact selected _)]
      exact target_assign_temporary_run_exact resultRead live _ inner
    rw [target_normal_branch_instruction_exact tested (by simpa only [if_true] using armExact)]
    have stateKept := @target_close_block_state_no_locals World marker
      ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩ sameLocals
    simp only [shortCircuitFrame, selected, if_true]
    apply iff_of_eq
    apply congrArg (fun final => out = final)
    change (targetCloseBlock marker
      ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩).state = state at stateKept
    have flowKept : (targetCloseBlock marker
      ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩).flow = .normal := rfl
    generalize closedEq : targetCloseBlock marker
      ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩ = closed at flowKept stateKept ⊢
    cases closed
    cases flowKept
    cases stateKept
    rfl
  · have differentBool : (ready == continueValue) = false := by
      cases ready <;> cases continueValue <;> simp_all
    rw [differentBool] at tested
    rw [target_normal_branch_instruction_exact tested
      (by simpa only [Bool.false_eq_true, if_false] using
        (fun inner => @target_run_empty_exact World interface heap calls .bool [] marker state inner))]
    simp only [shortCircuitFrame, selected, if_false, targetCloseBlock,
      targetLeaveScope_self marker state hscope]

theorem short_circuit_frame_read {World : Type} {interface : Interface}
    (continueValue : Bool) {marker current : TargetFrame}
    {state : TargetState World} {identity : Nat} {ready value : Bool}
    (condition : TargetAtomEval interface marker state (.temporary identity .bool) (.bool ready))
    (live : current.temporaryNames.contains identity = true)
    (sameLocals : current.nextLocal = marker.nextLocal) :
    TargetAtomEval interface (shortCircuitFrame continueValue marker current state identity ready value) state
      (.temporary identity .bool) (.bool (if continueValue then ready && value else ready || value)) := by
  have selectedValue : (if ready = continueValue then value else ready) =
      (if continueValue then ready && value else ready || value) := by
    cases continueValue <;> cases ready <;> rfl
  rw [← selectedValue]
  have outer : marker.temporaryNames.contains identity = true := by
    cases condition with | temporary _ live => exact live
  by_cases selected : ready = continueValue
  · have kept := close_updated_temporary_read interface marker current state identity .bool (.bool value) outer live
    have stateKept := @target_close_block_state_no_locals World marker
      ⟨.normal, targetUpdateTemporary current identity (.bool value), state⟩ sameLocals
    simpa only [shortCircuitFrame, selected, if_true, stateKept] using kept
  · simpa only [shortCircuitFrame, selected, if_false] using condition

theorem short_circuit_frame_protects {World : Type} (continueValue : Bool)
    {lower identity : Nat} {marker current : TargetFrame} (hscope : TemporariesScoped marker)
    (protection : TemporaryProtection lower marker current) (fresh : lower < identity)
    (state : TargetState World) (ready value : Bool) :
    TemporaryProtection lower marker (shortCircuitFrame continueValue marker current state identity ready value) := by
  unfold shortCircuitFrame
  split
  · exact close_block_temporary_protection hscope
      (temporary_protection_trans protection (update_temporary_protects current _ fresh)) state
  · exact temporary_protection_refl lower marker

theorem short_circuit_frame_bound {World : Type} (continueValue : Bool)
    {bound : Nat} {marker current : TargetFrame}
    (bounded : TemporaryNamesBound marker bound) (state : TargetState World)
    (identity : Nat) (ready value : Bool) :
    TemporaryNamesBound (shortCircuitFrame continueValue marker current state identity ready value) bound := by
  unfold shortCircuitFrame
  split
  · exact close_block_temporary_bound bounded _
  · exact bounded

theorem short_circuit_frame_scoped {World : Type} (continueValue : Bool)
    {marker current : TargetFrame} (hscope : TemporariesScoped marker) (state : TargetState World)
    (identity : Nat) (ready value : Bool) :
    TemporariesScoped (shortCircuitFrame continueValue marker current state identity ready value) := by
  unfold shortCircuitFrame
  split
  · exact target_close_block_scoped marker _
  · exact hscope

theorem short_circuit_condition_boolean {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {value : TargetValue}
    (continueValue : Bool) (read : TargetAtomEval interface frame state atom value)
    {selected : Bool}
    (tested : TargetConditionEval interface frame state (shortCircuitCondition continueValue atom) selected) :
    ∃ boolean, value = .bool boolean := by
  cases continueValue
  · cases tested with | negated otherRead => exact ⟨_, target_atom_unique read otherRead⟩
  · cases tested with | value otherRead => exact ⟨_, target_atom_unique read otherRead⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
