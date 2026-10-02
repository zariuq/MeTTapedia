import Mettapedia.Languages.VibeITP.Native.BuiltinArityLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetSwitchReturns
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts

/-!
# Exact independent execution of the lowered builtin signature

Every unsigned slot is covered by the actual compiler output. Both construction
and inversion retain the complete runtime state after parameter teardown.
Invocation-frame availability is explicit; an existing context fault returns
zero before the selector is read. Concrete C layout and the physical live-context
ABI are separate realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityTarget

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeIR
open NativeWord64 (Word bounded encode)
open Spec
open BuiltinArityLowering

/-- Selection couples the arm's private identity with its specified result. -/
theorem actual_dispatch_exact (slot : Word) :
    ∃ identity, 1 < identity ∧
      targetSelectCase (encode slot) actualArms actualOtherwise =
        [.temporary identity .word (.word (encode (BuiltinAritySource.signatureArity slot))),
          .return (.temporary identity .word)] := by
  rw [actualArms, target_select_case_map]
  have predicates : (fun builtin : Builtin => encode (bounded 64 builtin.slot) == encode slot) =
      (fun builtin => builtin.slot == slot.val) := by
    funext builtin
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← BitVec.toNat_inj, NativeWord64.encode_toNat,
      BuiltinAritySource.builtin_slot_bounded]
  rw [predicates]
  cases found : Builtin.all.find? (fun builtin => builtin.slot == slot.val) with
  | none =>
      refine ⟨13, by decide, ?_⟩
      simp [actualOtherwise, BuiltinAritySource.signatureArity, found]
      rfl
  | some builtin =>
      refine ⟨builtin.slot, ?_, ?_⟩
      · cases builtin <;> decide
      · simp [BuiltinAritySource.signatureArity, found]

theorem actual_body_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {slot : Word}
    (read : targetLocalValue frame state "slot" = some (.word (encode slot)))
    (clear : state.fault = none) (boundedNames : TemporaryNamesBound frame 0)
    (hscope : TemporariesScoped frame) (root : List Instruction)
    (out : TargetBlockOutcome World) :
    TargetRun NativeOpsSourceGuestSnapshot.expectedInterface heap calls .word root actualFunction.body
      frame state out ↔
      out = ⟨.returned (.word (encode (BuiltinAritySource.signatureArity slot))),
        targetDeclareTemporary frame 1 (.word (encode slot)), state⟩ := by
  change TargetRun _ _ _ .word root
    [.checkContextExists, .checkContext, .temporary 1 .word (.readLocal "slot"),
      .switch (.temporary 1 .word) actualArms actualOtherwise] frame state out ↔ _
  rw [target_normal_then_exact (target_context_exists_exact frame state)]
  rw [target_normal_then_exact (target_context_clear_exact frame state clear)]
  have unused : frame.temporaryNames.contains 1 = false :=
    temporary_bound_fresh boundedNames (by decide)
  rw [target_normal_then_exact (target_temporary_instruction_exact unused (.local read))]
  obtain ⟨identity, above, selected⟩ := actual_dispatch_exact slot
  have extended := declared_temporary_bound boundedNames (by decide : 0 ≤ 1)
    (by decide : 1 ≤ 1) (.word (encode slot))
  exact target_literal_switch_run_exact (declared_temporary_atom _ _ _ _ _ _)
    selected (temporary_bound_fresh extended above)
    (declared_temporaries_completeNames hscope 1 (.word (encode slot))) root [] out

theorem actual_body_entry_fault_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (frame : TargetFrame) (state : TargetState World) {fault : NativeWord64.Fault}
    (failed : state.fault = some fault) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun NativeOpsSourceGuestSnapshot.expectedInterface heap calls .word root actualFunction.body
      frame state out ↔ out = ⟨.returned (.word 0), frame, state⟩ := by
  change TargetRun _ _ _ .word root
    [.checkContextExists, .checkContext, .temporary 1 .word (.readLocal "slot"),
      .switch (.temporary 1 .word) actualArms actualOtherwise] frame state out ↔ _
  rw [target_normal_then_exact (target_context_exists_exact frame state)]
  exact target_returning_then_exact (target_context_fault_exact frame state failed .unsignedWord) root _ out

theorem actual_function_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (slot : Word) (out : TargetRawResult World)
    (clear : state.fault = none) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state out ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        out = ⟨.word (encode (BuiltinAritySource.signatureArity slot)), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound outcome raw fresh parameters body returned =>
        change some (targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))) =
          some (frame, bound) at parameters
        cases Option.some.inj parameters
        have read := target_singleton_parameter_readback state storage ⟨"slot", .word⟩ (.word (encode slot))
        have names : TemporaryNamesBound
            (targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))).1 0 := by
          intro identity live; cases live
        have hscope : TemporariesScoped
            (targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))).1 := by
          intro identity _; rfl
        cases (actual_body_exact read clear names hscope _ outcome).mp body
        cases TargetFlow.returned.inj returned
        exact ⟨⟨storage, fresh⟩, congrArg
          (TargetRawResult.mk (.word (encode (BuiltinAritySource.signatureArity slot))))
          (target_singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word (encode slot))
            fresh _ rfl rfl)⟩
  · rintro ⟨⟨storage, fresh⟩, same⟩
    subst out
    let bound := targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))
    have read : targetLocalValue bound.1 bound.2 "slot" = some (.word (encode slot)) :=
      target_singleton_parameter_readback state storage ⟨"slot", .word⟩ (.word (encode slot))
    have names : TemporaryNamesBound bound.1 0 := by intro identity live; cases live
    have hscope : TemporariesScoped bound.1 := by intro identity _; rfl
    have body : TargetRun NativeOpsSourceGuestSnapshot.expectedInterface heap calls .word
        actualFunction.body actualFunction.body bound.1 bound.2
        ⟨.returned (.word (encode (BuiltinAritySource.signatureArity slot))),
          targetDeclareTemporary bound.1 1 (.word (encode slot)), bound.2⟩ :=
      (actual_body_exact read clear names hscope _ _).mpr rfl
    have ran := TargetFunctionBody.run (function := actualFunction)
      (raw := .word (encode (BuiltinAritySource.signatureArity slot))) fresh
      (by rfl : targetBindParameters actualFunction.header.parameters [.word (encode slot)]
        (targetEmptyFrame storage) state = some bound) body (by rfl)
    have teardown : (targetLeaveScope (targetEmptyFrame storage)
        (targetDeclareTemporary bound.1 1 (.word (encode slot))) bound.2).2 = state :=
      target_singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word (encode slot)) fresh _ rfl rfl
    rw [teardown] at ran
    exact ran

theorem actual_function_entry_fault_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (slot : Word) (out : TargetRawResult World)
    {fault : NativeWord64.Fault} (failed : state.fault = some fault) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state out ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧ out = ⟨.word 0, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound outcome raw fresh parameters body returned =>
        change some (targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))) =
          some (frame, bound) at parameters
        cases Option.some.inj parameters
        have boundFault : (targetDeclareLocal (targetEmptyFrame storage) state "slot" .word
            (.word (encode slot))).2.fault = some fault := failed
        cases (actual_body_entry_fault_exact _ _ boundFault _ outcome).mp body
        cases TargetFlow.returned.inj returned
        exact ⟨⟨storage, fresh⟩, congrArg (TargetRawResult.mk (.word 0))
          (target_singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word (encode slot))
            fresh _ rfl rfl)⟩
  · rintro ⟨⟨storage, fresh⟩, same⟩
    subst out
    let bound := targetDeclareLocal (targetEmptyFrame storage) state "slot" .word (.word (encode slot))
    have body : TargetRun NativeOpsSourceGuestSnapshot.expectedInterface heap calls .word
        actualFunction.body actualFunction.body bound.1 bound.2 ⟨.returned (.word 0), bound.1, bound.2⟩ :=
      (actual_body_entry_fault_exact bound.1 bound.2
        (show bound.2.fault = some fault from failed) _ _).mpr rfl
    have ran := TargetFunctionBody.run (function := actualFunction) (raw := .word 0) fresh
      (by rfl : targetBindParameters actualFunction.header.parameters [.word (encode slot)]
        (targetEmptyFrame storage) state = some bound) body (by rfl)
    have teardown : (targetLeaveScope (targetEmptyFrame storage) bound.1 bound.2).2 = state :=
      target_singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word (encode slot)) fresh _ rfl rfl
    rw [teardown] at ran
    exact ran

end Mettapedia.Languages.VibeITP.Native.BuiltinArityTarget
