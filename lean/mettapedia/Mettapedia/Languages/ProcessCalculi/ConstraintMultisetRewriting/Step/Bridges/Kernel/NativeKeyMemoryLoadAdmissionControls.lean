import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeKeyMemoryLoadAdmission

/-!
# Checked occurrence and native execution in the owner's actual load fixture

The memory image, descriptors, entry and CPU profile are reused directly from
X86MemoryFieldLoad.entryFixture. Only the control cell, occurrence generations
and proposed destination are prepared here. No native run or desired-result
proof is included in that entry package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeKeyMemoryLoadAdmissionControls

open Mettapedia.Machines.TIsa Cells CellEffects Control
open _root_.X86Registers X86RegisterRefinement X86Execution
open NativeKeyMemoryLoadAdmission

local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable section

private abbrev fixture := X86MemoryFieldLoad.entryFixture
private def point : Word := fixture.origin.address.signExtend 64
private def next : Word := (X86Execution.address fixture.base 316).signExtend 64
private def invalid : Word := (X86Execution.address fixture.base 590).signExtend 64
private def highWord : Word := 0x80000001000000ff#64

private def snapshot : Snapshot where
  keys := scope fixture.view 0
  values := fun location => match location with
    | .inl activation => if activation = 0 then point else 0
    | .inr key => fixture.values key
  generations := fun _ => 0

private def candidate : Key → Word := Function.update fixture.values (.register 6) highWord
private def afterValues : Location Key → Word :=
  CheckedAdmission.commit (success fixture.address 0 point next) snapshot.values candidate

theorem actual_checked :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues := by
  have allowed : CheckedAdmission.eligible (success fixture.address 0 point next)
      snapshot.keys snapshot.values candidate := by decide +kernel
  change (if CheckedAdmission.eligible (success fixture.address 0 point next)
    snapshot.keys snapshot.values candidate then some afterValues else none) = some afterValues
  rw [if_pos allowed]

theorem actual_occurrence :
    ∃ admitted : (CellOccurrences.step (edges fixture.address 0 point next invalid)).Admits
        (s := snapshot) (firing fixture.address 0 point next invalid candidate),
      ((CellOccurrences.step (edges fixture.address 0 point next invalid)).result
        (firing fixture.address 0 point next invalid candidate) admitted).values = afterValues :=
  checked_occurrence fixture.address 0 point next invalid snapshot candidate afterValues actual_checked

theorem actual_named_load (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ admitted : (CellOccurrences.step (edges fixture.address 0 point next invalid)).Admits
        (s := snapshot) (firing fixture.address 0 point next invalid candidate),
    ∃ after nextFlags,
      ((CellOccurrences.step (edges fixture.address 0 point next invalid)).result
        (firing fixture.address 0 point next invalid candidate) admitted).values = afterValues ∧
      (X86FuelPrefix.fetches 10).run fixture.native = .ok () after ∧
      X86MemoryView.represents fixture.view
        (Cells.encode fixture.view.keys (fun key => afterValues (.inr key))) after ∧
      X86MemoryView.readback fixture.view.modes after (.register 6) = some highWord ∧
      fixture.native.regs.get? .rip = some (snapshot.values (.inl 0)) ∧
      after.regs.get? .rip = some (afterValues (.inl 0)) ∧
      after.regs.get? .rflags = some nextFlags ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after fixture.base ∧
      X86ControlFlags.Preserved fixture.native after ∧ fixture.profile.Holds after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨admitted, after, nextFlags, same, run, _frame, represented, beforeRip, afterRip,
      flagsRead, image, control, stable⟩ := checked_load_executes other extra vector fixture.view snapshot
    fixture.native fixture.base fixture.origin fixture.profile fixture.flags fixture.address 0 point next invalid
    candidate afterValues rfl fixture.known rfl rfl fixture.frameArea fixture.frameAligned fixture.holds
    fixture.flagsKnown fixture.quiet fixture.placed fixture.upper fixture.loaded fixture.rangeFits
    fixture.pointerLower fixture.pointerUpper fixture.aligned actual_checked
  have result : X86MemoryView.readback fixture.view.modes after (.register 6) = some highWord := by
    obtain ⟨values, encoded, seen⟩ := represented
    have equal := ((Cells.encode_le_iff fixture.view.keys fixture.view.keys values
      (fun key => afterValues (.inr key))).mp (le_of_eq encoded.symm)).2
      (.register 6) (fixture.view.registers 6)
    have read := (seen (.register 6) (fixture.view.registers 6)).trans (congrArg some equal)
    have destination : afterValues (.inr (.register 6)) = highWord := by rfl
    exact read.trans (congrArg some destination)
  have ac : (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
    obtain ⟨_controls, _visible, flags, observed, active⟩ := stable
    rw [observed]
    simpa only [Option.map_some, show fixture.profile.ac = (1#1) from rfl] using congrArg some active
  exact ⟨admitted, after, nextFlags, same, run, represented, result, beforeRip, afterRip,
    flagsRead, image, control, stable, ac⟩

theorem truncated_result_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0 snapshot.keys snapshot.values
      (Function.update fixture.values (.register 6) (255#64)) = none := by decide +kernel

theorem wrong_control_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0 snapshot.keys
      (Function.update snapshot.values (.inl 0) (point + 1)) candidate = none := by decide +kernel

theorem missing_mode_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0
      (snapshot.keys.erase (.inr (.capabilityMode 0))) snapshot.values candidate = none := by decide +kernel

theorem missing_byte_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0
      (snapshot.keys.erase (.inr (.byte 36879))) snapshot.values candidate = none := by decide +kernel

theorem denied_mode_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0 snapshot.keys
      (Function.update snapshot.values (.inr (.capabilityMode 0)) (0#64)) candidate = none := by decide +kernel

private def deniedView : X86MemoryView.View :=
  { fixture.view with modes := Function.update fixture.view.modes 0 (0#64) }

private def deniedSnapshot : Snapshot :=
  { snapshot with
    keys := scope deniedView 0
    values := Function.update snapshot.values (.inr (.capabilityMode 0)) (0#64) }

theorem denied_known (key : Key) (present : key ∈ deniedView.keys) :
    X86MemoryView.readback deniedView.modes fixture.native key = some (data deniedSnapshot key) := by
  by_cases same : key = .capabilityMode 0
  · subst key
    rfl
  · have different : (Sum.inr key : Location Key) ≠ .inr (.capabilityMode 0) :=
      fun equal => same (Sum.inr.inj equal)
    have unchanged : data deniedSnapshot key = fixture.values key := by
      change Function.update snapshot.values (.inr (.capabilityMode 0)) (0#64) (.inr key) = fixture.values key
      rw [Function.update_of_ne different]
      rfl
    rw [unchanged]
    have old := fixture.known key present
    cases key with
    | register register => exact old
    | byte address => exact old
    | capabilityBase region => exact old
    | capabilityLength region => exact old
    | capabilityMode region =>
        have nonzero : region ≠ 0 := fun equal => same (by rw [equal])
        simp only [deniedView, X86MemoryView.readback] at old ⊢
        by_cases frame : region = 255
        · simpa only [if_pos frame] using old
        · by_cases inside : region < 9
          · have differentIndex : (⟨region, inside⟩ : Fin 9) ≠ 0 :=
              fun equal => nonzero (congrArg Fin.val equal)
            simpa only [if_neg frame, dif_pos inside, Function.update_of_ne differentIndex] using old
          · simpa only [if_neg frame, dif_neg inside] using old

theorem denied_represents : X86MemoryView.represents deniedView
    (Cells.encode deniedView.keys (data deniedSnapshot)) fixture.native :=
  ⟨data deniedSnapshot, rfl, denied_known⟩

theorem denied_view_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0
      deniedSnapshot.keys deniedSnapshot.values candidate = none := denied_mode_refused

theorem raw_span_with_readback_is_not_admission (other : OtherOpcodeHandlers)
    (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86MemoryView.represents deniedView
      (Cells.encode deniedView.keys (data deniedSnapshot)) fixture.native ∧
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 0
      deniedSnapshot.keys deniedSnapshot.values candidate = none ∧
    ∃ after, (X86FuelPrefix.fetches 10).run fixture.native = .ok () after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_admitted, after, _flags, _same, run, _rest⟩ := actual_named_load other extra vector
  exact ⟨denied_represents, denied_view_refused, after, run⟩

theorem missing_ordinal_refused :
    CheckedAdmission.step? (edges fixture.address 0 point next invalid) 3
      snapshot.keys snapshot.values candidate = none := rfl

theorem wrong_source_width_refused :
    X86P1FieldLoadCapture.image.source.body.atPath ([1,1,1,1] ++ List.replicate 7 0 ++ [1]) ≠
      some (.instruction (.load .u32z .word32 0 6 1 (8#32))) := by
  rw [X86P1FieldLoadCapture.source_instruction]
  intro impossible
  cases impossible

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeKeyMemoryLoadAdmissionControls
