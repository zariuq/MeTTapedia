import Mettapedia.GSLT.LanguageDef.NativeOpsScalarLowering

/-!
Exact instruction composition for the native target relation. Normal
instructions retain their full post-frame and state for the next instruction;
returns stop the remainder, writes preserve their actual memory effects, and
branches execute the selected body before explicitly closing its scope.
These laws do not establish source-expression or whole-function adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction PureOperation)
open NativeWord64 (Word Fault WordOp encode)

/-- A private target temporary allocates no source-visible local cell. -/
theorem target_temporary_next_local (frame : TargetFrame) (identity : Nat) (value : TargetValue) :
    (targetDeclareTemporary frame identity value).nextLocal = frame.nextLocal := rfl

/-- A declared external action supplies its actual value and whole post-state.
The call stores that value in one fresh private temporary. This law does not
grant the action's contract merely from its declared name or signature. -/
theorem target_call_temporary_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state final : TargetState World} {identity : Nat}
    {value : TargetValue}
    (unused : frame.temporaryNames.contains identity = false)
    (operands : TargetAtomsEval interface frame state arguments values)
    (action : ∀ raw post, calls target values state raw post ↔ raw = value ∧ post = final)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.call (some (.temporary identity type)) target arguments) frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity value, final⟩ := by
  constructor
  · intro ran
    cases ran with
    | call otherOperands called stored =>
        cases target_atoms_unique operands otherOperands
        obtain ⟨sameValue, sameState⟩ := (action _ _).mp called
        subst_vars
        cases stored with
        | fresh => rfl
        | existing notTemporary _ => exact False.elim (notTemporary identity type rfl)
  · intro same
    subst out
    exact .call operands ((action value final).mpr ⟨rfl, rfl⟩) (.fresh unused)

/-- An exactly normal instruction continues with its complete post-frame and
post-state. Early returns and jumps cannot supply another execution of this
prefix. This law is shared by pure assignments, guards and defined writes. -/
theorem target_normal_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {before after : TargetFrame}
    {pre post : TargetState World}
    (instructionExact : ∀ out, TargetInstructionEval interface heap calls result
      instruction before pre out ↔ out = ⟨.normal, after, post⟩)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (instruction :: rest) before pre out ↔
      TargetRun interface heap calls result root rest after post out := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
        cases (instructionExact _).mp first
        exact remaining
    | «return» first => cases (instructionExact _).mp first
    | resume first _ _ => cases (instructionExact _).mp first
    | escape first _ => cases (instructionExact _).mp first
  · intro ran
    exact .next ((instructionExact _).mpr rfl) ran

/-- An exactly returning instruction retains its complete post-state and
never runs the remainder of its enclosing block. -/
theorem target_returning_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {before after : TargetFrame}
    {pre post : TargetState World} {value : TargetValue}
    (instructionExact : ∀ out, TargetInstructionEval interface heap calls result
      instruction before pre out ↔ out = ⟨.returned value, after, post⟩)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (instruction :: rest) before pre out ↔
      out = ⟨.returned value, after, post⟩ := by
  constructor
  · intro ran
    cases ran with
    | next first _ => cases (instructionExact _).mp first
    | «return» first => exact (instructionExact _).mp first
    | resume first _ _ => cases (instructionExact _).mp first
    | escape first _ => cases (instructionExact _).mp first
  · intro same
    subst out
    exact .return ((instructionExact _).mpr rfl)

theorem target_return_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {atom : Atom} {frame : TargetFrame} {state : TargetState World} {value : TargetValue}
    (read : TargetAtomEval interface frame state atom value)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.return atom) frame state out ↔
      out = ⟨.returned value, frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | «return» otherRead =>
        cases target_atom_unique read otherRead
        rfl
  · intro same
    subst out
    exact .return read

/-- Returning never evaluates a subsequent instruction, even when that
instruction would otherwise have a defined effect. -/
theorem target_return_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {atom : Atom} {frame : TargetFrame} {state : TargetState World} {value : TargetValue}
    (read : TargetAtomEval interface frame state atom value)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.return atom :: rest) frame state out ↔
      out = ⟨.returned value, frame, state⟩ := by
  exact target_returning_then_exact (target_return_instruction_exact read) root rest out

theorem target_write_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {pointer replacement : Atom} {address : Address} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World} {memory : TargetMemory}
    (located : TargetAtomEval interface frame state pointer (.reference (some address)))
    (read : TargetAtomEval interface frame state replacement value)
    (stored : targetWrite state.memory address value = some memory)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.write pointer replacement) frame state out ↔
      out = ⟨.normal, frame, { state with memory := memory }⟩ := by
  constructor
  · intro ran
    cases ran with
    | write otherLocated otherRead otherStored =>
        cases target_atom_unique located otherLocated
        cases target_atom_unique read otherRead
        cases Option.some.inj (stored.symm.trans otherStored)
        rfl
  · intro same
    subst out
    exact .write located read stored

theorem target_condition_unique {World : Type} {interface : Interface}
    {condition : NativeIR.Condition} {frame : TargetFrame} {state : TargetState World}
    {first second : Bool}
    (left : TargetConditionEval interface frame state condition first)
    (right : TargetConditionEval interface frame state condition second) : first = second := by
  cases left with
  | value leftRead =>
      cases right with
      | value rightRead => exact TargetValue.bool.inj (target_atom_unique leftRead rightRead)
  | negated leftRead =>
      cases right with
      | negated rightRead =>
          exact congrArg Bool.not (TargetValue.bool.inj (target_atom_unique leftRead rightRead))

/-- A branch executes exactly the selected body and then closes its lexical
scope. The scope close remains explicit in the returned complete state. -/
theorem target_branch_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : NativeIR.Condition} {whenTrue whenFalse : List Instruction}
    {frame : TargetFrame} {state : TargetState World} {selected : Bool}
    (tested : TargetConditionEval interface frame state condition selected)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.branch condition whenTrue whenFalse) frame state out ↔
      ∃ inner, TargetRun interface heap calls result
          (if selected then whenTrue else whenFalse)
          (if selected then whenTrue else whenFalse) frame state inner ∧
        out = targetCloseBlock frame inner := by
  constructor
  · intro ran
    cases ran with
    | branch otherTested body =>
        cases target_condition_unique tested otherTested
        exact ⟨_, body, rfl⟩
  · rintro ⟨inner, body, same⟩
    subst out
    exact .branch tested body

/-- A fresh private temporary disappears at its enclosing scope boundary;
the complete caller frame and state survive. The declared-name condition
rules out a stale private-map value being lost during scope cleanup. -/
theorem target_leave_declared_temporary {World : Type} (frame : TargetFrame)
    (state : TargetState World) (identity : Nat) (value : TargetValue)
    (unused : frame.temporaryNames.contains identity = false)
    (completeNames : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none) :
    targetLeaveScope frame (targetDeclareTemporary frame identity value) state =
      (frame, state) := by
  have values : (fun candidate => if frame.temporaryNames.contains candidate then
      (if candidate = identity then some value else frame.temporaries candidate) else none) =
      frame.temporaries := by
    funext candidate
    by_cases same : candidate = identity
    · subst candidate
      simp only [unused, Bool.false_eq_true, if_false, completeNames identity unused]
    · by_cases present : frame.temporaryNames.contains candidate = true
      · simp only [present, if_true, same, if_false]
      · have absent := Bool.eq_false_iff.mpr present
        simp only [absent, Bool.false_eq_true, if_false, completeNames candidate absent]
  simp only [targetLeaveScope, targetDeclareTemporary, targetDropLocals_empty, values]

theorem target_declared_names_complete (frame : TargetFrame) (identity : Nat) (value : TargetValue)
    (complete : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none) :
    ∀ candidate, (targetDeclareTemporary frame identity value).temporaryNames.contains candidate = false →
      (targetDeclareTemporary frame identity value).temporaries candidate = none := by
  intro candidate absent
  have different : candidate ≠ identity := by
    intro same
    subst candidate
    simp [targetDeclareTemporary] at absent
  have oldAbsent : frame.temporaryNames.contains candidate = false := by
    simpa [targetDeclareTemporary, different] using absent
  simp only [targetDeclareTemporary, different, if_false, complete candidate oldAbsent]

/-- A false query skips an arbitrary observed arm. No contract for that
arm's services is used: its instructions are never executed. The query's
whole post-state is retained; inactivity alone cannot make it state-free. -/
theorem target_inactive_call_guard_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {target : NativeIR.CallTarget} {identity : Nat} {observed : List Instruction}
    {frame : TargetFrame} {state final : TargetState World}
    (unused : frame.temporaryNames.contains identity = false)
    (complete : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none)
    (query : ∀ raw post, calls target [] state raw post ↔ raw = .bool false ∧ post = final)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .word root
      [.call (some (.temporary identity .bool)) target [],
       .branch (.value (.temporary identity .bool)) observed [.return (.word 0)]]
      frame state out ↔
      out = ⟨.returned (.word 0), targetDeclareTemporary frame identity (.bool false), final⟩ := by
  rw [target_normal_then_exact
    (target_call_temporary_instruction_exact unused .nil query)]
  let saved := targetDeclareTemporary frame identity (.bool false)
  have tested : TargetConditionEval interface saved final
      (.value (.temporary identity .bool)) false :=
    .value (.temporary (declare_temporary_read frame identity (.bool false))
      (by simp [saved, targetDeclareTemporary]))
  have branchExact (result : TargetBlockOutcome World) :
      TargetInstructionEval interface heap calls .word
        (.branch (.value (.temporary identity .bool)) observed [.return (.word 0)])
        saved final result ↔ result = ⟨.returned (.word 0), saved, final⟩ := by
    rw [target_branch_instruction_exact tested]
    simp only [Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨inner, ran, same⟩
      cases (target_return_then_exact (.word 0) _ [] inner).mp ran
      simpa only [targetCloseBlock,
        targetLeaveScope_self saved final (target_declared_names_complete _ _ _ complete)] using same
    · intro same
      subst result
      exact ⟨⟨.returned (.word 0), saved, final⟩,
        (target_return_then_exact (.word 0) _ [] _).mpr rfl, by
          simp only [targetCloseBlock,
            targetLeaveScope_self saved final (target_declared_names_complete _ _ _ complete)]⟩
  exact target_returning_then_exact branchExact root [] out

/-- A guard with a pure early-return arm either returns the computed value
or continues unchanged. The selected arm's temporary and its lexical scope
are executed and released through the actual target relation. -/
theorem target_early_return_branch_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {condition : NativeIR.Condition} {selected : Bool} {identity : Nat}
    {operation : PureOperation} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected)
    (unused : frame.temporaryNames.contains identity = false)
    (computed : TargetPureEval interface frame state operation value)
    (completeNames : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.branch condition [.temporary identity type operation,
        .return (.temporary identity type)] []) frame state out ↔
      out = ⟨if selected then .returned value else .normal, frame, state⟩ := by
  have armExact (inner : TargetBlockOutcome World) :
      TargetRun interface heap calls result
        [.temporary identity type operation, .return (.temporary identity type)]
        [.temporary identity type operation, .return (.temporary identity type)]
        frame state inner ↔
        inner = ⟨.returned value, targetDeclareTemporary frame identity value, state⟩ := by
    rw [target_normal_then_exact (target_temporary_instruction_exact unused computed)]
    exact target_return_then_exact
      (.temporary (declare_temporary_read frame identity value)
        (by simp [targetDeclareTemporary])) _ _ _
  rw [target_branch_instruction_exact tested]
  cases selected
  · simp only [Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨inner, ran, same⟩
      cases (target_run_empty_exact _ _ _ _).mp ran
      simpa only [targetCloseBlock, targetLeaveScope_self frame state completeNames] using same
    · intro same
      subst out
      exact ⟨⟨.normal, frame, state⟩, .nil _ _ _, by
        simp only [targetCloseBlock, targetLeaveScope_self frame state completeNames]⟩
  · simp only [if_true]
    constructor
    · rintro ⟨inner, ran, same⟩
      cases (armExact inner).mp ran
      simpa only [targetCloseBlock,
        target_leave_declared_temporary frame state identity value unused completeNames] using same
    · intro same
      subst out
      exact ⟨⟨.returned value, targetDeclareTemporary frame identity value, state⟩,
        (armExact _).mpr rfl, by simp only [targetCloseBlock,
          target_leave_declared_temporary frame state identity value unused completeNames]⟩

/-- A taken early-return guard skips the remaining code; a skipped guard
retains the complete frame and state for that code. -/
theorem target_early_return_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {condition : NativeIR.Condition} {selected : Bool} {identity : Nat}
    {operation : PureOperation} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected)
    (unused : frame.temporaryNames.contains identity = false)
    (computed : TargetPureEval interface frame state operation value)
    (completeNames : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.branch condition [.temporary identity type operation,
        .return (.temporary identity type)] [] :: rest) frame state out ↔
      if selected then out = ⟨.returned value, frame, state⟩
      else TargetRun interface heap calls result root rest frame state out := by
  have exactInstruction := target_early_return_branch_exact
    (heap := heap) (calls := calls) (result := result) (type := type)
    tested unused computed completeNames
  cases selected
  · exact target_normal_then_exact exactInstruction root rest out
  · exact target_returning_then_exact exactInstruction root rest out

end Mettapedia.GSLT.LanguageDef.NativeOps
