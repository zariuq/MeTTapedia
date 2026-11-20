import Mettapedia.Machines.TIsa.X86PlacedRegisterMove
import Mettapedia.Machines.TIsa.X86PlacedJcc
import Mettapedia.Machines.TIsa.X86PlacedMemory
import Mettapedia.Machines.TIsa.X86PreparedLea
import Mettapedia.Machines.TIsa.X86Bounds
import Mettapedia.Machines.TIsa.X86FrameCompare

/-! # A checked indexed address in the prepared frame region -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 900000

namespace Mettapedia.Machines.TIsa.X86PlacedFrameAddress

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode)
open X86PlacedMemory (Cell Controls Reads)
open X86PreparedLea (Index)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev nativeBase (other : OtherOpcodeHandlers) :=
  X86Bounds.baseHandlers (X86PreparedLea.linked other)

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PlacedScalar.handlers (nativeBase other) extra

private def extentCode (amount : X86PositiveImmediate.Immediate) : List Nat :=
  registerCode 0x81 0 15 ++ X86Bounds.little32 (X86PositiveImmediate.immediate32 amount)
private def compareExtent (displacement : BitVec 32) : List Nat :=
  [0x4c, 0x3b, 0xbf] ++ X86Bounds.little32 displacement
private abbrev compareLength : List Nat := compareExtent 8
def displacedCode (index : Index) (displacement : Fin 128) : List Nat :=
  [0x4d, 0x8d, 0x44, index.sib.toNat, displacement.val]

def addressCode (index : Index) : List Nat := displacedCode index 0

private def extent (displacement : Fin 128) : X86PositiveImmediate.Immediate :=
  ⟨displacement.val + 8, by have := displacement.isLt; omega⟩

private def delta (start target : Nat) : BitVec 32 := .ofInt 32 ((target : Int) - start)

def AccessChecked (image : NativeImage.View) (start reject : Nat) (index : Index) (displacement : Fin 128) : Prop :=
  start + 34 ≤ image.size ∧ reject ≤ image.size ∧
  (reject : Int) = start + 16 + (delta (start + 16) reject).toInt ∧
  (reject : Int) = start + 29 + (delta (start + 29) reject).toInt ∧
  Code image start (registerCode 0x89 index.register 15) ∧
  Code image (start + 3) (extentCode (extent displacement)) ∧
  Code image (start + 10) (X86NativeJcc.code (.ordinary .below) (delta (start + 16) reject)) ∧
  Code image (start + 16) compareLength ∧
  Code image (start + 23) (X86NativeJcc.code (.ordinary .above) (delta (start + 29) reject)) ∧
  Code image (start + 29) (displacedCode index displacement)

instance (image : NativeImage.View) (start reject : Nat) (index : Index) (displacement : Fin 128) :
    Decidable (AccessChecked image start reject index displacement) := inferInstanceAs (Decidable (_ ∧ _))

abbrev Checked (image : NativeImage.View) (start reject : Nat) (index : Index) : Prop :=
  AccessChecked image start reject index 0

private theorem codeByte {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start ≤ image.size) {bytes : List Nat}
    (code : Code image start bytes) (offset value : Nat) (found : bytes[offset]? = some value) :
    state.mem.get? ((address base.toInt (start + offset)).signExtend 52).toNat = some (.ofNat 8 value) := by
  have byte := point.bytes _ inside bytes code offset value found
  rwa [point.relative_address start offset inside] at byte

private theorem loads_displacement {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start + 7 ≤ image.size) {bytes : List Nat}
    (code : Code image start bytes)
    (immediate : BitVec 32)
    (encoded : ∀ i : Fin 4, bytes[3 + i.val]? = some (immediate.extractLsb' (8 * i.val) 8).toNat) :
    ∀ offset < 4, state.mem.get?
      ((address (point.basis (by omega)).next.toInt offset).signExtend 52).toNat =
      some (immediate.extractLsb' (8 * offset) 8) := by
  intro offset fits
  change state.mem.get? ((address (address base.toInt (start + 3)).toInt offset).signExtend 52).toNat = _
  rw [point.relative_address (start + 3) offset (by omega), Nat.add_assoc]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    codeByte point (by omega) code _ _ (encoded ⟨offset, fits⟩)

private theorem adds_extent (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 7 ≤ image.size)
    (amount : X86PositiveImmediate.Immediate) (code : Code image start (extentCode amount)) (offset : Word) (known : lookup state 15 = some offset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.r15, .rflags, .rip} state after ∧ lookup after 15 = some (offset + X86PositiveImmediate.immediate64 amount) ∧
      ∃ next : At image after base (start + 7),
        Functions._get_rflagsbits_cf next.flags = Functions.bool_to_bits (2^64 ≤ offset.toNat + amount.val) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin : X86LegacyFetch.Window state 0x81 true 0 15 :=
    { toBasis := point.basis (by omega)
      prefixByte := by
        change state.mem.get? ((address base.toInt start).signExtend 52).toNat = some (0x49#8)
        simpa only [Nat.add_zero] using codeByte point (by omega) code 0 0x49 rfl
      opcodeByte := codeByte point (by omega) code 1 0x81 rfl
      modrmByte := codeByte point (by omega) code 2 0xc7 rfl }
  let next := address base.toInt (start + 7)
  have extent : origin.next.toInt + 4 = next.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have immediate := loads_displacement point inside code (X86PositiveImmediate.immediate32 amount)
    (by intro index; fin_cases index <;> rfl)
  obtain ⟨after, flags, ran, framed, found, flagKnown, rip, carry⟩ :=
    X86PositiveImmediate.fetched_frame (handlers other extra) vector state amount
      15 origin next offset point.flags extent known point.knownFlags point.quiet immediate
  exact ⟨after, ran, framed, found, point.advance framed (by decide) rip flags flagKnown, carry⟩

private theorem compares_extent (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 7 ≤ image.size)
    {displacement : BitVec 32} (code : Code image start (compareExtent displacement)) (controls : Controls state)
    (frame ending length : Word) (cell : Cell frame displacement)
    (frameKnown : lookup state 7 = some frame) (endKnown : lookup state 15 = some ending)
    (lengthRead : Reads state cell.address length) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame {.rflags, .rip} state after ∧
      ∃ next : At image after base (start + 7),
        X86BranchCondition.value .above next.flags = decide (length.toNat < ending.toNat) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let next := address base.toInt (start + 7)
  have extent : origin.next.toInt + 4 = next.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  obtain ⟨output, ran, calculated⟩ := X86FrameCompare.fetched 15 (handlers other extra) vector state
    origin next cell.address controls.visible controls.controls frame ending length point.flags displacement extent cell.upper
    frameKnown endKnown controls.controlsKnown point.knownFlags controls.visibleKnown point.quiet cell.effective
    cell.aligned (by
      change state.mem.get? ((address base.toInt start).signExtend 52).toNat = some (0x4c#8)
      simpa only [Nat.add_zero] using codeByte point (by omega) code 0 0x4c rfl)
    (codeByte point (by omega) code 1 0x3b rfl) (codeByte point (by omega) code 2 0xbf rfl)
    (loads_displacement point inside code displacement (by intro index; fin_cases index <;> rfl)) lengthRead
  let flags := X86Flags.mergeFlags point.flags output
  let after := X86Move.putPointer (X86Flags.putFlags state flags) next
  have kept : RegisterFrame {.rflags, .rip} state after := (flags_frame _ _).trans (pointer_frame _ _)
  have flagKnown : after.regs.get? .rflags = some flags := by
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, kept,
    point.advance kept (by decide) (X86FuelPrefix.pointer_rip _ _) flags flagKnown,
    X86P1LoadBounds.above_sense ending length flags calculated.carry calculated.zero⟩

/-- A placed unsigned end-of-access check. Both guards branch to the same
invalid continuation, with a possibly shorter path on addition overflow. -/
def ExtentChecked (image : NativeImage.View) (start reject : Nat) (source : Fin 16)
    (amount : X86PositiveImmediate.Immediate) (lengthDisp : BitVec 32) : Prop :=
  start + 29 ≤ image.size ∧ reject ≤ image.size ∧
  (reject : Int) = start + 16 + (delta (start + 16) reject).toInt ∧
  (reject : Int) = start + 29 + (delta (start + 29) reject).toInt ∧
  Code image start (registerCode 0x89 source 15) ∧
  Code image (start + 3) (extentCode amount) ∧
  Code image (start + 10) (X86NativeJcc.code (.ordinary .below) (delta (start + 16) reject)) ∧
  Code image (start + 16) (compareExtent lengthDisp) ∧
  Code image (start + 23) (X86NativeJcc.code (.ordinary .above) (delta (start + 29) reject))

instance (image : NativeImage.View) (start reject : Nat) (source : Fin 16)
    (amount : X86PositiveImmediate.Immediate) (lengthDisp : BitVec 32) :
    Decidable (ExtentChecked image start reject source amount lengthDisp) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev extentWrites : Finset Register := {.r15, .rflags, .rip}

theorem checks_extent (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48} {start reject : Nat}
    (point : At image state base start) (source : Fin 16) (amount : X86PositiveImmediate.Immediate)
    {lengthDisp : BitVec 32} (code : ExtentChecked image start reject source amount lengthDisp)
    (controls : Controls state) (frame offset length : Word) (cell : Cell frame lengthDisp)
    (frameKnown : lookup state 7 = some frame) (offsetKnown : lookup state source = some offset)
    (lengthRead : Reads state cell.address length) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if 2^64 ≤ offset.toNat + amount.val then 3 else 5)).run state = .ok () after ∧
      RegisterFrame extentWrites state after ∧
      Nonempty (At image after base (if offset.toNat + amount.val ≤ length.toNat then start + 29 else reject)) := by
  let h := handlers other extra
  obtain ⟨span, target, firstDelta, nextDelta, copy, add, carryGate, cmp, rangeGate⟩ := code
  obtain ⟨moved, copied, copyFrame, word, ⟨atAdd⟩⟩ :=
    X86PlacedRegisterMove.executes h vector point (by omega) source 15 offset offsetKnown copy
  obtain ⟨added, increased, addFrame, ending, atCarry, carry⟩ :=
    adds_extent other extra vector atAdd (by omega) amount add offset word
  obtain ⟨brought, passedCarry, carryFrame, ⟨branch⟩⟩ :=
    X86PlacedJcc.executes (nativeBase other) extra vector atCarry (by omega) target (.ordinary .below) _ firstDelta carryGate
  have carryChoice : X86NativeJcc.selects (.ordinary .below) atCarry.flags = decide (2^64 ≤ offset.toNat + amount.val) := by
    change X86BranchCondition.value .below atCarry.flags = _
    rw [X86BranchCondition.value, carry, X86P1QwordBounds.carry_bit_sense]
  rw [carryChoice] at branch
  let beforeCmp := (copyFrame.trans addFrame).trans carryFrame
  have pre : RegisterFrame extentWrites state brought := beforeCmp.mono (by decide)
  have a := @X86FuelPrefix.fetches_then h vector 1 1 state moved added copied increased
  have b := @X86FuelPrefix.fetches_then h vector 2 1 state added brought a passedCarry
  by_cases wraps : 2^64 ≤ offset.toNat + amount.val
  · have exceeds : ¬ offset.toNat + amount.val ≤ length.toNat := by have := length.isLt; omega
    rw [if_pos wraps]
    rw [if_pos (by simpa only [decide_eq_true_eq] using wraps)] at branch
    exact ⟨brought, b, pre, by rw [if_neg exceeds]; exact ⟨branch⟩⟩
  rw [if_neg wraps]
  rw [if_neg (by simpa only [decide_eq_true_eq] using wraps)] at branch
  let cmpControls := controls.transport (X86StateFrame.registerOnly pre) (by decide)
  obtain ⟨compared, comparedRun, cmpFrame, atRange, condition⟩ :=
    compares_extent other extra vector branch (by omega) cmp cmpControls frame
      (offset + X86PositiveImmediate.immediate64 amount) length cell
      ((pre.lookup 7 (by decide)).trans frameKnown) ((carryFrame.lookup 15 (by decide)).trans ending)
      (lengthRead.preserved (X86StateFrame.registerOnly pre) (by simp))
  obtain ⟨checked, passedRange, rangeFrame, ⟨reached⟩⟩ :=
    X86PlacedJcc.executes (nativeBase other) extra vector atRange (by omega) target (.ordinary .above) _ nextDelta rangeGate
  have endExact : (offset + X86PositiveImmediate.immediate64 amount).toNat = offset.toNat + amount.val := by
    rw [BitVec.toNat_add_of_lt, X86PositiveImmediate.word_nat]
    rw [X86PositiveImmediate.word_nat]
    omega
  have rangeChoice : X86NativeJcc.selects (.ordinary .above) atRange.flags =
      decide (length.toNat < offset.toNat + amount.val) := by
    change X86BranchCondition.value .above atRange.flags = _
    rw [condition, endExact]
  rw [rangeChoice] at reached
  have c := @X86FuelPrefix.fetches_then h vector 3 1 state brought compared b comparedRun
  have d := @X86FuelPrefix.fetches_then h vector 4 1 state compared checked c passedRange
  refine ⟨checked, d, ((pre.trans cmpFrame).trans rangeFrame).mono (by decide), ?_⟩
  by_cases fits : offset.toNat + amount.val ≤ length.toNat
  · rw [if_pos fits]
    rw [if_neg (by simpa only [decide_eq_true_eq] using Nat.not_lt.mpr fits)] at reached
    exact ⟨reached⟩
  · rw [if_neg fits]
    rw [if_pos (by simpa only [decide_eq_true_eq] using Nat.lt_of_not_ge fits)] at reached
    exact ⟨reached⟩

private theorem forms_displaced (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 5 ≤ image.size)
    (index : Index) (displacement : Fin 128) (code : Code image start (displacedCode index displacement)) (frames offset : Word)
    (frameKnown : lookup state 13 = some frames) (offsetKnown : lookup state index.register = some offset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.r8, .rip} state after ∧ lookup after 8 = some (frames + offset + BitVec.ofNat 64 displacement.val) ∧
      Nonempty (At image after base (start + 5)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let atByte := address base.toInt (start + 4)
  let next := address base.toInt (start + 5)
  have extent : origin.next.toInt + 1 = atByte.toInt := by
    change (address base.toInt (start + 3)).toInt + 1 = (address base.toInt (start + 4)).toInt
    rw [point.location _ (by omega), point.location _ (by omega)]
    omega
  have advance : atByte.toInt + 1 = next.toInt := by
    change (address base.toInt (start + 4)).toInt + 1 = (address base.toInt (start + 5)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have encoded : (BitVec.ofNat 8 displacement.val).signExtend 64 = BitVec.ofNat 64 displacement.val := by
    have all : ∀ disp : Fin 128, (BitVec.ofNat 8 disp.val).signExtend 64 = BitVec.ofNat 64 disp.val := by decide +kernel
    exact all displacement
  have ran := X86PreparedLea.fetched_displaced (handlers other extra) vector state index origin atByte next frames
    offset (BitVec.ofNat 8 displacement.val) extent advance frameKnown offsetKnown point.quiet
    (by simpa only [origin, At.basis, Nat.add_zero] using codeByte point (by omega) code 0 0x4d rfl)
    (codeByte point (by omega) code 1 0x8d rfl) (codeByte point (by omega) code 2 0x44 rfl)
    (by simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      codeByte point (by omega) code 3 _ rfl)
    (codeByte point (by omega) code 4 displacement.val rfl)
  rw [encoded] at ran
  let after := X86Move.putPointer (put state 8 (frames + offset + BitVec.ofNat 64 displacement.val)) next
  have kept : RegisterFrame {.r8, .rip} state after :=
    ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by decide)
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, kept, by rw [show after = X86Move.putPointer _ _ from rfl,
    X86Move.lookup_putPointer, lookup_put_same], ⟨point.advance kept (by decide)
    (X86FuelPrefix.pointer_rip _ _) point.flags ((kept.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

private theorem forms_address (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 5 ≤ image.size)
    (index : Index) (code : Code image start (addressCode index)) (frames offset : Word)
    (frameKnown : lookup state 13 = some frames) (offsetKnown : lookup state index.register = some offset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.r8, .rip} state after ∧ lookup after 8 = some (frames + offset) ∧
      Nonempty (At image after base (start + 5)) := by
  obtain ⟨after, ran, frame, value, next⟩ := forms_displaced other extra vector point inside index 0 code frames offset
    frameKnown offsetKnown
  have zero : BitVec.ofNat 64 (0 : Fin 128).val = (0#64) := rfl
  exact ⟨after, ran, frame, by simpa only [zero, BitVec.add_zero] using value, next⟩

abbrev writes : Finset Register := {.r8, .r15, .rflags, .rip}

theorem access_succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (index : Index) (displacement : Fin 128)
    (code : AccessChecked image start reject index displacement) (controls : Controls state)
    (frames frame offset length : Word) (cell : Cell frame 8)
    (baseKnown : lookup state 13 = some frames) (frameKnown : lookup state 7 = some frame)
    (offsetKnown : lookup state index.register = some offset) (lengthRead : Reads state cell.address length)
    (fits : offset.toNat + displacement.val + 8 ≤ length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 8 = some (frames + offset + BitVec.ofNat 64 displacement.val) ∧
      Nonempty (At image after base (start + 34)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨span, target, firstDelta, nextDelta, copy, add, carryGate, cmp, rangeGate, lea⟩ := code
  have guard : ExtentChecked image start reject index.register (extent displacement) 8 :=
    ⟨by omega, target, firstDelta, nextDelta, copy, add, carryGate, cmp, rangeGate⟩
  obtain ⟨checked, tested, kept, ⟨atLea⟩⟩ :=
    checks_extent other extra vector point index.register (extent displacement) guard controls frame offset length
      cell frameKnown offsetKnown lengthRead
  have enough : offset.toNat + (extent displacement).val ≤ length.toNat := by
    change offset.toNat + (displacement.val + 8) ≤ _
    omega
  have nowrap : ¬ 2^64 ≤ offset.toNat + (extent displacement).val := by have := length.isLt; omega
  rw [if_pos enough] at atLea
  rw [if_neg nowrap] at tested
  have indexFixed : key index.register ∉ extentWrites := by
    have low : ∀ r : Fin 8, ∀ h : r.val ≠ 4, key (Index.register ⟨r, h⟩) ∉ extentWrites := by decide +kernel
    exact low index.val index.property
  obtain ⟨after, formed, leaFrame, addressKnown, next⟩ :=
    forms_displaced other extra vector atLea (by omega) index displacement lea frames offset ((kept.lookup 13 (by decide)).trans baseKnown)
      ((kept.lookup _ indexFixed).trans offsetKnown)
  let h := handlers other extra
  exact ⟨after, @X86FuelPrefix.fetches_then h vector 5 1 state checked after tested formed,
    (kept.trans leaFrame).mono (by decide), addressKnown, next⟩

theorem succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (index : Index)
    (code : Checked image start reject index) (controls : Controls state)
    (frames frame offset length : Word) (cell : Cell frame 8)
    (baseKnown : lookup state 13 = some frames) (frameKnown : lookup state 7 = some frame)
    (offsetKnown : lookup state index.register = some offset) (lengthRead : Reads state cell.address length)
    (fits : offset.toNat + 8 ≤ length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 8 = some (frames + offset) ∧
      Nonempty (At image after base (start + 34)) := by
  obtain ⟨after, ran, preserved, value, next⟩ := access_succeeds other extra vector point index 0 code controls
    frames frame offset length cell baseKnown frameKnown offsetKnown lengthRead fits
  have zero : BitVec.ofNat 64 (0 : Fin 128).val = (0#64) := rfl
  exact ⟨after, ran, preserved, by simpa only [zero, BitVec.add_zero] using value, next⟩

def OffsetChecked (image : NativeImage.View) (start reject : Nat) (index : Index) : Prop :=
  start + 21 ≤ image.size ∧ reject ≤ image.size ∧
  (reject : Int) = start + 16 + (delta (start + 16) reject).toInt ∧
  Code image start (registerCode 0x89 index.register 15) ∧
  Code image (start + 3) compareLength ∧
  Code image (start + 10) (X86NativeJcc.code (.ordinary .above) (delta (start + 16) reject)) ∧
  Code image (start + 16) (addressCode index)

instance (image : NativeImage.View) (start reject : Nat) (index : Index) :
    Decidable (OffsetChecked image start reject index) := inferInstanceAs (Decidable (_ ∧ _))

/-- Form the cursor address after checking only its position. Subsequent
loads and stores have their own extent checks. -/
theorem offset_succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (index : Index)
    (code : OffsetChecked image start reject index) (controls : Controls state)
    (frames frame offset length : Word) (cell : Cell frame 8)
    (baseKnown : lookup state 13 = some frames) (frameKnown : lookup state 7 = some frame)
    (offsetKnown : lookup state index.register = some offset) (lengthRead : Reads state cell.address length)
    (fits : offset.toNat ≤ length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 8 = some (frames + offset) ∧
      Nonempty (At image after base (start + 21)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, target, relative, copy, cmp, branch, lea⟩ := code
  obtain ⟨moved, copied, copyFrame, word, ⟨atCmp⟩⟩ :=
    X86PlacedRegisterMove.executes (handlers other extra) vector point (by omega) _ 15 offset offsetKnown copy
  let cmpControls := controls.transport (X86StateFrame.registerOnly copyFrame) (by decide)
  obtain ⟨compared, comparedRun, cmpFrame, atBranch, condition⟩ :=
    compares_extent other extra vector atCmp (by omega) cmp cmpControls frame offset length cell
      ((copyFrame.lookup 7 (by decide)).trans frameKnown) word
      (lengthRead.preserved (X86StateFrame.registerOnly copyFrame) (by simp))
  obtain ⟨checked, passed, branchFrame, ⟨atLea⟩⟩ := X86PlacedJcc.executes (nativeBase other) extra vector
    atBranch (by omega) target (.ordinary .above) _ relative branch
  have inRange : X86NativeJcc.selects (.ordinary .above) atBranch.flags = false := by
    change X86BranchCondition.value .above atBranch.flags = false
    rw [condition, decide_eq_false (Nat.not_lt.mpr fits)]
  rw [if_neg (by simp [inRange])] at atLea
  have indexFixed : key index.register ∉ writes := by
    have low : ∀ r : Fin 8, ∀ h : r.val ≠ 4, key (Index.register ⟨r, h⟩) ∉ writes := by decide +kernel
    exact low index.val index.property
  have beforeLea : RegisterFrame writes state checked :=
    ((copyFrame.trans cmpFrame).trans branchFrame).mono (by decide)
  obtain ⟨after, formed, leaFrame, bound, atEnd⟩ := forms_address other extra vector atLea (by omega) index lea
    frames offset ((beforeLea.lookup 13 (by decide)).trans baseKnown)
    ((beforeLea.lookup _ indexFixed).trans offsetKnown)
  let h := handlers other extra
  have r2 := @X86FuelPrefix.fetches_then h vector 1 1 state moved compared copied comparedRun
  have r3 := @X86FuelPrefix.fetches_then h vector 2 1 state compared checked r2 passed
  exact ⟨after, @X86FuelPrefix.fetches_then h vector 3 1 state checked after r3 formed,
    (beforeLea.trans leaFrame).mono (by decide), bound, atEnd⟩

end Mettapedia.Machines.TIsa.X86PlacedFrameAddress
