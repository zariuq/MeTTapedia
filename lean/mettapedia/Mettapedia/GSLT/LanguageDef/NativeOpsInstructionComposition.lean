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

theorem target_context_exists_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result .checkContextExists frame state out ↔
      out = ⟨.normal, frame, state⟩ := by
  constructor
  · intro ran; cases ran; rfl
  · intro same; subst out; exact .contextExists _ _

theorem target_context_clear_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (frame : TargetFrame) (state : TargetState World) (clear : state.fault = none)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result .checkContext frame state out ↔
      out = ⟨.normal, frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | contextClear _ => rfl
    | contextFault failed _ => rw [clear] at failed; cases failed
  · intro same; subst out; exact .contextClear clear

theorem target_context_fault_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (frame : TargetFrame) (state : TargetState World) {fault : NativeWord64.Fault}
    (failed : state.fault = some fault) {default : TargetValue}
    (zero : TargetZero interface result default) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result .checkContext frame state out ↔
      out = ⟨.returned default, frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | contextClear clear => rw [failed] at clear; cases clear
    | contextFault _ otherZero => cases target_zero_unique zero otherZero; rfl
  · intro same; subst out; exact .contextFault failed zero

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

/-- A partial pure operation continues only after an actual computed value.
In particular, an undefined load cannot supply a default to the suffix. -/
theorem target_pure_temporary_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {operation : PureOperation} {frame : TargetFrame} {state : TargetState World} {identity : Nat}
    (unused : frame.temporaryNames.contains identity = false)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.temporary identity type operation :: rest) frame state out ↔
      ∃ value, TargetPureEval interface frame state operation value ∧
        TargetRun interface heap calls result root rest
          (targetDeclareTemporary frame identity value) state out := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
        cases first with
        | temporary _ computed => exact ⟨_, computed, remaining⟩
    | «return» first | resume first _ _ | escape first _ => cases first
  · rintro ⟨value, computed, remaining⟩
    exact .next (.temporary unused computed) remaining

/-- An external call continues with each actual result and its whole
post-state. The service may be partial or nondeterministic; no existence or
single-result assumption is introduced by sequencing it. -/
theorem target_call_temporary_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat}
    (unused : frame.temporaryNames.contains identity = false)
    (operands : TargetAtomsEval interface frame state arguments values)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.call (some (.temporary identity type)) target arguments :: rest) frame state out ↔
      ∃ value post, calls target values state value post ∧
        TargetRun interface heap calls result root rest
          (targetDeclareTemporary frame identity value) post out := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
      cases first with
      | call otherOperands called stored =>
        cases target_atoms_unique operands otherOperands
        cases stored with
        | fresh => exact ⟨_, _, called, remaining⟩
        | existing notTemporary _ => exact False.elim (notTemporary identity type rfl)
    | «return» first => cases first
    | resume first _ _ => cases first
    | escape first _ => cases first
  · rintro ⟨value, post, called, remaining⟩
    exact .next (.call operands called (.fresh unused)) remaining

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

/-- A context fault stops the suffix and retains every preceding effect.
The typed default is only the function's return protocol, not a successful
expression result. -/
theorem target_context_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {default : TargetValue} (zero : TargetZero interface result default)
    (frame : TargetFrame) (state : TargetState World)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.checkContext :: rest) frame state out ↔
      match state.fault with
      | none => TargetRun interface heap calls result root rest frame state out
      | some _ => out = ⟨.returned default, frame, state⟩ := by
  cases failed : state.fault with
  | none =>
      exact target_normal_then_exact (target_context_clear_exact frame state failed) root rest out
  | some fault =>
      exact target_returning_then_exact
        (target_context_fault_exact frame state failed zero) root rest out

/-- Discarding a unit call's raw return does not discard its state effects.
No result is invented for a service with no actual call derivation. -/
theorem target_call_discard_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (operands : TargetAtomsEval interface frame state arguments values)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.call none target arguments :: rest)
      frame state out ↔
      ∃ raw post, calls target values state raw post ∧
        TargetRun interface heap calls result root rest frame post out := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
        cases first with
        | call otherOperands called stored =>
            cases target_atoms_unique operands otherOperands
            cases stored
            exact ⟨_, _, called, remaining⟩
    | «return» first | resume first _ _ | escape first _ => cases first
  · rintro ⟨raw, post, called, remaining⟩
    exact .next (.call operands called (.discard raw frame post)) remaining

theorem target_call_temporary_checked_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {default : TargetValue}
    (unused : frame.temporaryNames.contains identity = false)
    (operands : TargetAtomsEval interface frame state arguments values)
    (zero : TargetZero interface result default)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.call (some (.temporary identity type)) target arguments :: .checkContext :: rest)
      frame state out ↔
      ∃ raw post, calls target values state raw post ∧
        match post.fault with
        | none => TargetRun interface heap calls result root rest
            (targetDeclareTemporary frame identity raw) post out
        | some _ => out = ⟨.returned default, targetDeclareTemporary frame identity raw, post⟩ := by
  rw [target_call_temporary_then_iff unused operands]
  simp only [target_context_then_exact zero]

theorem target_call_discard_checked_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {default : TargetValue}
    (operands : TargetAtomsEval interface frame state arguments values)
    (zero : TargetZero interface result default)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (.call none target arguments :: .checkContext :: rest) frame state out ↔
      ∃ raw post, calls target values state raw post ∧
        match post.fault with
        | none => TargetRun interface heap calls result root rest frame post out
        | some _ => out = ⟨.returned default, frame, post⟩ := by
  rw [target_call_discard_then_iff operands]
  simp only [target_context_then_exact zero]

theorem target_call_temporary_checked_fragment_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {default : TargetValue}
    (unused : frame.temporaryNames.contains identity = false)
    (operands : TargetAtomsEval interface frame state arguments values)
    (zero : TargetZero interface result default)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.call (some (.temporary identity type)) target arguments, .checkContext] frame state out ↔
      ∃ raw post, calls target values state raw post ∧
        out = match post.fault with
          | none => ⟨.normal, targetDeclareTemporary frame identity raw, post⟩
          | some _ => ⟨.returned default, targetDeclareTemporary frame identity raw, post⟩ := by
  rw [target_call_temporary_checked_then_iff unused operands zero]
  apply exists_congr
  intro raw
  apply exists_congr
  intro post
  cases failed : post.fault <;> simp only [target_run_empty_exact]

theorem target_call_discard_checked_fragment_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {default : TargetValue}
    (operands : TargetAtomsEval interface frame state arguments values)
    (zero : TargetZero interface result default)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.call none target arguments, .checkContext] frame state out ↔
      ∃ raw post, calls target values state raw post ∧
        out = match post.fault with
          | none => ⟨.normal, frame, post⟩
          | some _ => ⟨.returned default, frame, post⟩ := by
  rw [target_call_discard_checked_then_iff operands zero]
  apply exists_congr
  intro raw
  apply exists_congr
  intro post
  cases failed : post.fault <;> simp only [target_run_empty_exact]

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

/-- Returning the fresh result of a call preserves exactly the service's
result relation, including all post-states and the possibility of no result. -/
theorem target_call_return_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {target : NativeIR.CallTarget} {arguments : List Atom} {values : List TargetValue}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat}
    (unused : frame.temporaryNames.contains identity = false)
    (operands : TargetAtomsEval interface frame state arguments values)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.call (some (.temporary identity type)) target arguments,
       .return (.temporary identity type)] frame state out ↔
      ∃ value post, calls target values state value post ∧
        out = ⟨.returned value, targetDeclareTemporary frame identity value, post⟩ := by
  rw [target_call_temporary_then_iff unused operands]
  constructor
  · rintro ⟨value, post, called, remaining⟩
    exact ⟨value, post, called, (target_return_then_exact
      (.temporary (declare_temporary_read frame identity value)
        (by simp [targetDeclareTemporary])) root [] out).mp remaining⟩
  · rintro ⟨value, post, called, same⟩
    refine ⟨value, post, called, ?_⟩
    exact (target_return_then_exact
      (.temporary (declare_temporary_read frame identity value)
        (by simp [targetDeclareTemporary])) root [] out).mpr same

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

/-- A defined write passes its actual complete memory to the suffix. The
destination may alias other observations; no disjointness is assumed. -/
theorem target_write_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {pointer replacement : Atom} {address : Address} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (located : TargetAtomEval interface frame state pointer (.reference (some address)))
    (read : TargetAtomEval interface frame state replacement value)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.write pointer replacement :: rest) frame state out ↔
      ∃ memory, targetWrite state.memory address value = some memory ∧
        TargetRun interface heap calls result root rest frame { state with memory := memory } out := by
  constructor
  · intro ran
    cases ran with
    | next first remaining =>
        cases first with
        | write otherLocated otherRead stored =>
            cases target_atom_unique located otherLocated
            cases target_atom_unique read otherRead
            exact ⟨_, stored, remaining⟩
    | «return» first | resume first _ _ | escape first _ => cases first
  · rintro ⟨memory, stored, remaining⟩
    exact .next (.write located read stored) remaining

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

/-- One actual false response constructs the inactive path without any
response or totality assumption about the unselected arm. -/
theorem target_inactive_call_guard_of_call {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {target : NativeIR.CallTarget} {identity : Nat} {observed : List Instruction}
    {frame : TargetFrame} {state final : TargetState World}
    (unused : frame.temporaryNames.contains identity = false)
    (complete : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none)
    (query : calls target [] state (.bool false) final) (root : List Instruction) :
    TargetRun interface heap calls .word root
      [.call (some (.temporary identity .bool)) target [],
       .branch (.value (.temporary identity .bool)) observed [.return (.word 0)]]
      frame state ⟨.returned (.word 0), targetDeclareTemporary frame identity (.bool false), final⟩ := by
  let saved := targetDeclareTemporary frame identity (.bool false)
  have tested : TargetConditionEval interface saved final
      (.value (.temporary identity .bool)) false :=
    .value (.temporary (declare_temporary_read frame identity (.bool false))
      (by simp [saved, targetDeclareTemporary]))
  have branch : TargetInstructionEval interface heap calls .word
      (.branch (.value (.temporary identity .bool)) observed [.return (.word 0)]) saved final
      (targetCloseBlock saved ⟨.returned (.word 0), saved, final⟩) := by
    apply TargetInstructionEval.branch tested
    simp only [Bool.false_eq_true, if_false]
    exact .return (.return (.word 0))
  have closed : targetCloseBlock saved ⟨.returned (.word 0), saved, final⟩ =
      ⟨.returned (.word 0), saved, final⟩ := by
    simp only [targetCloseBlock,
      targetLeaveScope_self saved final (target_declared_names_complete _ _ _ complete)]
  rw [closed] at branch
  exact .next (.call .nil query (.fresh unused)) (.return branch)

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

/-- Two actual service responses construct an enabled guarded call, even
when their response relations are nondeterministic. This local witness is
also usable with occurrence-indexed invocation ledgers. -/
theorem target_active_call_guard_of_calls {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {queryTarget target : NativeIR.CallTarget} {queryIdentity identity : Nat}
    {arguments : List Atom} {values : List TargetValue} {unselected : List Instruction}
    {frame : TargetFrame} {state queried post : TargetState World} {value : TargetValue}
    (unusedQuery : frame.temporaryNames.contains queryIdentity = false)
    (unusedResult : (targetDeclareTemporary frame queryIdentity (.bool true)).temporaryNames.contains
      identity = false)
    (complete : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none)
    (query : calls queryTarget [] state (.bool true) queried)
    (operands : TargetAtomsEval interface
      (targetDeclareTemporary frame queryIdentity (.bool true)) queried arguments values)
    (observed : calls target values queried value post) (root : List Instruction) :
    TargetRun interface heap calls result root
      [.call (some (.temporary queryIdentity .bool)) queryTarget [],
       .branch (.value (.temporary queryIdentity .bool))
         [.call (some (.temporary identity type)) target arguments,
          .return (.temporary identity type)] unselected]
      frame state
      ⟨.returned value, targetDeclareTemporary frame queryIdentity (.bool true), post⟩ := by
  let saved := targetDeclareTemporary frame queryIdentity (.bool true)
  have tested : TargetConditionEval interface saved queried
      (.value (.temporary queryIdentity .bool)) true :=
    .value (.temporary (declare_temporary_read frame queryIdentity (.bool true))
      (by simp [saved, targetDeclareTemporary]))
  have called := (target_call_return_exact (heap := heap) (result := result) (type := type)
    unusedResult operands
    [.call (some (.temporary identity type)) target arguments,
      .return (.temporary identity type)] _).mpr ⟨value, post, observed, rfl⟩
  have branch : TargetInstructionEval interface heap calls result
      (.branch (.value (.temporary queryIdentity .bool))
        [.call (some (.temporary identity type)) target arguments,
         .return (.temporary identity type)] unselected) saved queried
      (targetCloseBlock saved ⟨.returned value, targetDeclareTemporary saved identity value, post⟩) :=
    .branch tested (by simpa only [if_true] using called)
  have closed : targetCloseBlock saved
      ⟨.returned value, targetDeclareTemporary saved identity value, post⟩ =
      ⟨.returned value, saved, post⟩ := by
    simp only [targetCloseBlock, target_leave_declared_temporary saved post identity value
      unusedResult (target_declared_names_complete _ _ _ complete)]
  rw [closed] at branch
  exact .next (.call .nil query (.fresh unusedQuery)) (.return branch)

/-- An enabled service guard runs exactly its selected call. The query and
service have separate post-states; scope exit drops the private result
temporary while retaining every service effect. -/
theorem target_active_call_guard_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result type : NativeType}
    {queryTarget target : NativeIR.CallTarget} {queryIdentity identity : Nat}
    {arguments : List Atom} {values : List TargetValue} {unselected : List Instruction}
    {frame : TargetFrame} {state queried : TargetState World}
    (unusedQuery : frame.temporaryNames.contains queryIdentity = false)
    (unusedResult : (targetDeclareTemporary frame queryIdentity (.bool true)).temporaryNames.contains
      identity = false)
    (complete : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none)
    (query : ∀ raw post, calls queryTarget [] state raw post ↔
      raw = .bool true ∧ post = queried)
    (operands : TargetAtomsEval interface
      (targetDeclareTemporary frame queryIdentity (.bool true)) queried arguments values)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.call (some (.temporary queryIdentity .bool)) queryTarget [],
       .branch (.value (.temporary queryIdentity .bool))
         [.call (some (.temporary identity type)) target arguments,
          .return (.temporary identity type)] unselected]
      frame state out ↔
      ∃ value post, calls target values queried value post ∧
        out = ⟨.returned value, targetDeclareTemporary frame queryIdentity (.bool true), post⟩ := by
  rw [target_normal_then_exact
    (target_call_temporary_instruction_exact unusedQuery .nil query)]
  let saved := targetDeclareTemporary frame queryIdentity (.bool true)
  have tested : TargetConditionEval interface saved queried
      (.value (.temporary queryIdentity .bool)) true :=
    .value (.temporary (declare_temporary_read frame queryIdentity (.bool true))
      (by simp [saved, targetDeclareTemporary]))
  have completeSaved := target_declared_names_complete frame queryIdentity (.bool true) complete
  have branchExact (other : TargetBlockOutcome World) :
      TargetInstructionEval interface heap calls result
        (.branch (.value (.temporary queryIdentity .bool))
          [.call (some (.temporary identity type)) target arguments,
           .return (.temporary identity type)] unselected) saved queried other ↔
        ∃ value post, calls target values queried value post ∧
          other = ⟨.returned value, saved, post⟩ := by
    rw [target_branch_instruction_exact tested]
    simp only [if_true]
    constructor
    · rintro ⟨inner, ran, same⟩
      obtain ⟨value, post, called, innerEq⟩ :=
        (target_call_return_exact unusedResult operands _ inner).mp ran
      subst inner
      refine ⟨value, post, called, ?_⟩
      change other = targetCloseBlock saved
        ⟨.returned value, targetDeclareTemporary saved identity value, post⟩ at same
      simpa only [targetCloseBlock,
        target_leave_declared_temporary saved post identity value unusedResult completeSaved] using same
    · rintro ⟨value, post, called, same⟩
      subst other
      refine ⟨⟨.returned value, targetDeclareTemporary saved identity value, post⟩,
        (target_call_return_exact unusedResult operands _ _).mpr ⟨value, post, called, rfl⟩, ?_⟩
      simp only [targetCloseBlock,
        target_leave_declared_temporary saved post identity value unusedResult completeSaved]
  constructor
  · intro ran
    cases ran with
    | next first _ =>
      obtain ⟨_, _, _, impossible⟩ := (branchExact _).mp first
      cases impossible
    | «return» first => exact (branchExact _).mp first
    | resume first _ _ =>
      obtain ⟨_, _, _, impossible⟩ := (branchExact _).mp first
      cases impossible
    | escape first _ =>
      obtain ⟨_, _, _, impossible⟩ := (branchExact _).mp first
      cases impossible
  · rintro ⟨value, post, called, same⟩
    subst out
    exact .return ((branchExact _).mpr ⟨value, post, called, rfl⟩)

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

theorem target_branch_test_of_run {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root rest yes no : List Instruction} {condition : NativeIR.Condition}
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root (.branch condition yes no :: rest) frame state out) :
    ∃ selected, TargetConditionEval interface frame state condition selected := by
  have instruction {inner : TargetBlockOutcome World}
      (executed : TargetInstructionEval interface heap calls result (.branch condition yes no) frame state inner) :
      ∃ selected, TargetConditionEval interface frame state condition selected := by
    cases executed with | branch tested _ => exact ⟨_, tested⟩
  cases ran with
  | next first _ => exact instruction first
  | «return» first => exact instruction first
  | resume first _ _ => exact instruction first
  | escape first _ => exact instruction first

end Mettapedia.GSLT.LanguageDef.NativeOps
