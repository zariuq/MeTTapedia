import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot
import Mettapedia.GSLT.LanguageDef.NativeOpsFunctionParameters
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceSwitchReturns
import Mettapedia.Languages.VibeITP.Spec.Basic

/-!
# Actual guest dispatch agrees with the independent builtin signature

The admitted guest function is executed through the shared source semantics,
including parameter storage and teardown. Every 64-bit slot is covered:
kernel constants have their specified arity, and all other slots return zero.
This is source-body correspondence; generated C and concrete pointer binding
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinAritySource

open Mettapedia.GSLT.LanguageDef
open NativeOps
open NativeWord64 (Word bounded)
open Spec


/-- The independent signature, including the zero used for nonconstant slots. -/
def signatureArity (slot : Word) : Word :=
  bounded 64 (Option.getD (Option.map Builtin.arity
    (Builtin.all.find? fun builtin => builtin.slot == slot.val)) 0)

/-- Arms read from the admitted operational function, not reauthored here. -/
def actualArms : List (Word × List Statement) :=
  match NativeOpsSourceGuestSnapshot.function_040.body with
  | [.switch _ arms _] => arms
  | _ => []

theorem actual_function_in_program :
    NativeOpsSourceGuestSnapshot.expectedProgram.functions[19]? =
      some NativeOpsSourceGuestSnapshot.function_040 := rfl

theorem actual_body_shape : NativeOpsSourceGuestSnapshot.function_040.body =
    [.switch (.variable "slot") actualArms [.return (some (.word (bounded 64 0)))]] := rfl

theorem actual_arms_match_signature : actualArms = Builtin.all.map (fun builtin =>
    (bounded 64 builtin.slot, [.return (some (.word (bounded 64 builtin.arity)))])) := rfl

theorem builtin_slot_bounded (builtin : Builtin) :
    (bounded 64 builtin.slot).val = builtin.slot := by
  cases builtin <;> rfl

theorem actual_dispatch_exact (slot : Word) :
    sourceSelectCase slot actualArms [.return (some (.word (bounded 64 0)))] =
      [.return (some (.word (signatureArity slot)))] := by
  rw [actual_arms_match_signature, source_select_return_map]
  have predicates : (fun builtin : Builtin => bounded 64 builtin.slot == slot) =
      (fun builtin => builtin.slot == slot.val) := by
    funext builtin
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Fin.ext_iff, builtin_slot_bounded]
  rw [predicates]
  cases found : Builtin.all.find? (fun builtin => builtin.slot == slot.val) <;>
    simp [signatureArity, found]

theorem actual_body_exact {World : Type}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {frame : SourceFrame} {state : SourceState World} {slot : Word}
    (read : sourceLocalValue frame state "slot" = some (.word slot))
    (out : SourceBlockOutcome World) :
    SourceBlockEval NativeOpsSourceGuestSnapshot.expectedInterface heap calls NativeOpsSourceGuestSnapshot.function_040.body frame state out ↔
      out = ⟨.returned (.word (signatureArity slot)), frame, state⟩ := by
  rw [actual_body_shape]
  exact source_return_switch_block_exact read (actual_dispatch_exact slot) out []

theorem actual_function_exact {World : Type}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (state : SourceState World) (slot : Word) (out : SourceRawResult World)
    (clear : state.fault = none) :
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls NativeOpsSourceGuestSnapshot.function_040 [.word slot] state out ↔
      (∃ storage, sourceFreshFrame state.memory storage) ∧
        out = ⟨.word (signatureArity slot), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | entryFault arity failed zero => simp [clear] at failed
    | @run storage frame bound outcome raw entryClear fresh parameters body returned =>
        change some (sourceDeclareLocal ⟨storage, 0, []⟩ state "slot" .word (.word slot)) =
          some (frame, bound) at parameters
        have boundEq := Option.some.inj parameters
        cases boundEq
        have read := singleton_parameter_readback state storage ⟨"slot", .word⟩ (.word slot)
        cases (actual_body_exact read outcome).mp body
        change raw = .word (signatureArity slot) at returned
        subst raw
        exact ⟨⟨storage, fresh⟩, congrArg (SourceRawResult.mk (.word (signatureArity slot)))
          (singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word slot) fresh)⟩
  · rintro ⟨⟨storage, fresh⟩, same⟩
    subst out
    let bound := sourceDeclareLocal ⟨storage, 0, []⟩ state "slot" .word (.word slot)
    have read : sourceLocalValue bound.1 bound.2 "slot" = some (.word slot) :=
      singleton_parameter_readback state storage ⟨"slot", .word⟩ (.word slot)
    have body : SourceBlockEval NativeOpsSourceGuestSnapshot.expectedInterface heap calls NativeOpsSourceGuestSnapshot.function_040.body
        bound.1 bound.2 ⟨.returned (.word (signatureArity slot)), bound.1, bound.2⟩ :=
      (actual_body_exact read _).mpr rfl
    have ran := SourceFunctionBody.run (function := NativeOpsSourceGuestSnapshot.function_040)
      (raw := .word (signatureArity slot)) clear fresh
      (by rfl : sourceBindParameters NativeOpsSourceGuestSnapshot.function_040.header.parameters [.word slot]
        ⟨storage, 0, []⟩ state = some bound) body (by rfl)
    have teardown : (sourceLeaveScope ⟨storage, 0, []⟩ bound.1 bound.2).2 = state :=
      singleton_parameter_teardown state storage ⟨"slot", .word⟩ (.word slot) fresh
    rw [teardown] at ran
    exact ran

theorem actual_function_entry_fault_exact {World : Type}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (state : SourceState World) (slot : Word) (out : SourceRawResult World)
    {fault : NativeWord64.Fault} (failed : state.fault = some fault) :
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_040 [.word slot] state out ↔
      out = ⟨.word 0, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | entryFault _ _ zero =>
        change SourceZero _ .word _ at zero
        cases zero
        rfl
    | run clear _ _ _ _ => simp [failed] at clear
  · intro same
    subst out
    exact .entryFault rfl failed .word

theorem all_builtin_arities (builtin : Builtin) :
    signatureArity (bounded 64 builtin.slot) = bounded 64 builtin.arity := by
  cases builtin <;> decide +kernel

theorem marker_slots_return_zero :
    signatureArity (bounded 64 0) = bounded 64 0 ∧
      signatureArity (bounded 64 1) = bounded 64 0 := by decide +kernel

theorem largest_word_returns_zero :
    signatureArity (bounded 64 (2^64 - 1)) = bounded 64 0 := by decide +kernel

theorem wrong_arity_has_no_source_run {World : Type}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (state : SourceState World) (clear : state.fault = none) :
    ¬ SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls NativeOpsSourceGuestSnapshot.function_040
      [.word (bounded 64 Builtin.litAdd.slot)] state ⟨.word (bounded 64 1), state⟩ := by
  intro ran
  have exactResult := ((actual_function_exact state _ _ clear).mp ran).2
  have wrong : signatureArity (bounded 64 Builtin.litAdd.slot) = bounded 64 2 :=
    all_builtin_arities .litAdd
  rw [wrong] at exactResult
  have impossible := congrArg (fun raw => raw.value) exactResult
  have values := SourceValue.word.inj impossible
  have numbers := congrArg Fin.val values
  contradiction

end Mettapedia.Languages.VibeITP.Native.BuiltinAritySource
