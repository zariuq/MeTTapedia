import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.X86P1QwordBounds
import Mettapedia.Machines.TIsa.X86BoundedLoad

/-!
# The matching-arm qword read in the actual consumer image

R_DERIVE_IS_PROP reads its full 64-bit field at premise offset16. The source
instruction and containing 56-byte span at offset 80 are checked in the captured
bundle. Its final seven bytes at 129..135 instantiate the original qword MOV fetch
contract. Arbitrary canonical placement and the complete loaded image supply
the exact native bytes, with no assumed execution or trusted span labels.

The complete 56-byte span is the parameterized bounded load with displacement
16 and rejection target 590, the image's invalid-input entry; it composes the
original overflow, length and range checks with the qword read. All raw bytes are checked against the captured
image. Rejection reaches the invalid-input continuation without reading the
candidate data bytes. The source access guard agrees on admitted pointers.
Whole-consumer execution, actual admission/hosting and ABI composition remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1QwordLoadCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev image := X86P1LoadCapture.propImage

theorem source_instruction : image.source.body.atPath [1,1,0,0] =
    some (.instruction (.load .u64 .word64 0 6 1 (16#32))) := by kernel_reflexivity

theorem containing_span : image.spans.any (fun span =>
    span.offset == 80 && span.length == 56 && span.kind == "LOAD" && span.path == some [1,1,0,0]) = true := by
  kernel_reflexivity

theorem tail_bytes (index : Fin 7) : image.view.read (129 + index.val) =
    ((X86QwordLoad.code 10 6 (16#32))[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem tail_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 129) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86QwordLoad.code 10 6 (16#32)) := by
  intro index byte present
  have within : index < 7 := by simpa only [X86QwordLoad.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := tail_bytes ⟨index,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (129 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (129 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

def tailInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (pointer value : Word) (dataAddress : BitVec 48) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (placed : origin.address.toInt = base + 129) (upper : base + 647 < (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (pointerKnown : lookup state 6 = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer + (16#32).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (loaded : X86P1LoadCapture.Loaded image state base)
    (bytes : ∀ index < 8, state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)) : X86QwordLoad.Inputs state 10 6 (16#32) := {
  origin with
  noSib := by decide
  noStack := by decide
  visible := visible
  controls := controls
  baseValue := pointer
  value := value
  flags := flags
  dataAddress := dataAddress
  baseKnown := pointerKnown
  controlKnown := controlKnown
  flagsKnown := flagsKnown
  visibleKnown := visibleKnown
  quiet := quiet
  upper := by rw [placed]; omega
  dataUpper := dataUpper
  effective := effective
  aligned := aligned
  loaded := tail_loaded state base origin placed loaded
  dataPresent := bytes }

theorem tail_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (pointer value : Word) (dataAddress : BitVec 48) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (placed : origin.address.toInt = base + 129) (upper : base + 647 < (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (pointerKnown : lookup state 6 = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer + (16#32).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (loaded : X86P1LoadCapture.Loaded image state base)
    (bytes : ∀ index < 8, state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame {.r10,.rip} state after ∧
      lookup after 10 = some value ∧ after.regs.get? .rip = some ((address base 136).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ X86P1LoadCapture.Loaded image after base := by
  let prepared := tailInput state base origin pointer value dataAddress flags visible controls placed upper dataUpper
    pointerKnown controlKnown flagsKnown visibleKnown quiet effective aligned loaded bytes
  obtain ⟨after,run,frame,result,rip⟩ := X86QwordLoad.executes other vector state 10 6 (16#32) prepared
  refine ⟨after,run,frame,result,?_,?_,?_⟩
  · have point : address prepared.address.toInt 7 = address base 136 := by
      change address origin.address.toInt 7 = address base 136
      unfold address
      rw [placed]
      congr 1
      omega
    rw [point] at rip
    exact rip
  · exact (frame.registers .rflags (by decide)).trans flagsKnown
  · intro index within
    rw [frame.memory]
    exact loaded index within

/-- The span as the parameterized bounded load: logical destination 6 (R10), logical base 1
(RSI), region 0, displacement 16, eight bytes, rejecting to the invalid handler 510 bytes after
its start. -/
def site : X86BoundedLoad.Instruction where
  wide := true
  destination := 6
  base := 1
  region := 0
  offset := ⟨16, by decide⟩
  reject := 510
  unlocked := by decide
  noSib := by decide
  noStack := by decide

theorem site_registers :
    X86BoundedLoad.physical site.destination = 10 ∧ X86BoundedLoad.physical site.base = 6 := by
  decide

theorem site_length : (X86BoundedLoad.bytes site).length = 56 := by
  rw [X86BoundedLoad.bytes_length]
  rfl

theorem site_tail : X86BoundedLoad.tail site = X86QwordLoad.code 10 6 (16#32) := by decide

theorem span_bytes (index : Fin 56) : image.view.read (80 + index.val) =
    ((X86BoundedLoad.bytes site)[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem span_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 80) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86BoundedLoad.bytes site) := by
  intro index byte present
  have within : index < 56 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    rwa [site_length] at bounded
  have captured := span_bytes ⟨index,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (80 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (80 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

/-- The bounds geometry of the span: the image extends `647 - 80` bytes past its start. -/
def context (start : BitVec 48) (upper : start.toInt + 567 < (2 ^ 47 : Int)) :
    X86Bounds.Context (X86BoundedLoad.layout site) start where
  extent := 567
  upper := upper
  codeWithin := by decide
  rejectWithin := by decide
  overflowDelta := by decide
  shortDelta := by decide
  rangeDelta := by decide

def spanInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 567) (placed : origin.address.toInt = base + 80)
    (loaded : X86P1LoadCapture.Loaded image state base) : X86BoundedLoad.Inputs site state origin where
  frame := facts.frame
  base := facts.base
  pointer := facts.pointer
  length := facts.length
  baseAddress := facts.baseAddress
  lengthAddress := facts.lengthAddress
  controls := facts.controls
  visible := facts.visible
  flags := facts.flags
  frameKnown := facts.frameKnown
  pointerKnown := by
    rw [show (X86BoundedLoad.layout site).pointer = 6 from site_registers.2]
    exact facts.pointerKnown
  baseEffective := by
    rw [show (X86Bounds.baseDisplacement (X86BoundedLoad.layout site)).signExtend 64 = 0#64 from by decide,
      BitVec.add_zero]
    exact facts.baseEffective
  lengthEffective := by
    rw [show X86Bounds.lengthDisplacement (X86BoundedLoad.layout site) = (8#32) from by decide]
    exact facts.lengthEffective
  baseUpper := facts.baseUpper
  lengthUpper := facts.lengthUpper
  baseAligned := facts.baseAligned
  lengthAligned := facts.lengthAligned
  controlKnown := facts.controlKnown
  visibleKnown := facts.visibleKnown
  flagsKnown := facts.flagsKnown
  quiet := facts.quiet
  baseBytes := facts.baseBytes
  lengthBytes := facts.lengthBytes
  geometry := context origin.address facts.upper
  tailWithin := show X86Bounds.exitAt (X86BoundedLoad.layout site) + 10 ≤ 567 by decide
  loaded := span_loaded state base origin placed loaded

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 80) (offset : Nat) :
    X86Bounds.position start offset = address base (80 + offset) := by
  unfold X86Bounds.position address
  rw [placed]
  congr 1
  omega

/-- Fetch count of the bounds prefix: four on offset overflow, seven on a short region, nine
otherwise. -/
theorem steps (base pointer length : Word) :
    X86Bounds.boundsSteps (X86BoundedLoad.layout site) base pointer length =
      if 2 ^ 64 ≤ (pointer - base).toNat + 16 then 4 else if length.toNat < 8 then 7 else 9 := rfl

theorem bounds_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 567) (placed : origin.address.toInt = base + 80)
    (loaded : X86P1LoadCapture.Loaded image state base) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches
        (X86Bounds.boundsSteps (X86BoundedLoad.layout site) facts.base facts.pointer facts.length)).run state =
          .ok () after ∧
      RegisterFrame X86Bounds.writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if (facts.pointer - facts.base).toNat + 24 ≤ facts.length.toNat then address base 129
          else address base 590).signExtend 64) ∧ X86P1LoadCapture.Loaded image after base := by
  obtain ⟨after,run,frame,rip⟩ :=
    X86Bounds.classifies other extra vector _ state origin (spanInput state base origin facts placed loaded).bounds
  change after.regs.get? .rip = some
    ((if (facts.pointer - facts.base).toNat + 16 + 8 ≤ facts.length.toNat then X86Bounds.position origin.address 49
      else X86Bounds.position origin.address 510).signExtend 64) at rip
  rw [position_in_image origin.address base placed 49, position_in_image origin.address base placed 510,
    Nat.add_assoc] at rip
  refine ⟨after,run,frame,frame.lookup 10 (by decide),rip,?_⟩
  intro index within
  rw [frame.memory]
  exact loaded index within

theorem bounds_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 567) (placed : origin.address.toInt = base + 80)
    (loaded : X86P1LoadCapture.Loaded image state base)
    (rangeFits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (pointerLower : facts.base.toNat ≤ facts.pointer.toNat)
    (pointerUpper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches
        (X86Bounds.boundsSteps (X86BoundedLoad.layout site) facts.base facts.pointer facts.length)).run state =
          .ok () after ∧
      RegisterFrame X86Bounds.writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if Memory.access? facts.base facts.length facts.pointer (16#32).toInt 8 = some (facts.pointer.toNat + 16)
          then address base 129 else address base 590).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  obtain ⟨after,run,frame,unchanged,rip,image⟩ := bounds_classifies other extra vector state base origin facts placed loaded
  refine ⟨after,run,frame,unchanged,?_,image⟩
  simpa only [X86P1QwordBounds.source_guard facts.base facts.length facts.pointer rangeFits pointerLower pointerUpper] using rip

theorem load_observes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 567) (placed : origin.address.toInt = base + 80)
    (loaded : X86P1LoadCapture.Loaded image state base) (value : Word)
    (readable : X86P1QwordBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 24 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 10).run state = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) state after ∧ lookup after 10 = some value ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some ((address base 136).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  let input := spanInput state base origin facts placed loaded
  let data : X86BoundedLoad.Readable input := {
    word := value
    dataAddress := readable.dataAddress
    upper := readable.upper
    effective := by
      change facts.pointer + (X86BoundedLoad.displacement site).signExtend 64 = _
      rw [show (X86BoundedLoad.displacement site).signExtend 64 = 16#64 from by decide]
      exact readable.effective
    safe := Or.inr readable.aligned
    present := readable.bytes }
  obtain ⟨after,flags,run,frame,valueRead,rip,flagsRead,-⟩ :=
    X86BoundedLoad.succeeds other extra vector site state origin input (by
      change (facts.pointer - facts.base).toNat + 16 + 8 ≤ facts.length.toNat
      omega) data
  have clobbers : X86BoundedLoad.writes site = insert .r10 X86Bounds.writes := by decide
  change lookup after (X86BoundedLoad.physical site.destination) = some (X86DataLoad.value true value) at valueRead
  rw [site_registers.1] at valueRead
  change after.regs.get? .rip = some ((address origin.address.toInt 56).signExtend 64) at rip
  rw [show address origin.address.toInt 56 = address base 136 from by
    unfold address
    rw [placed]
    congr 1
    omega] at rip
  refine ⟨after,flags,run,clobbers ▸ frame,valueRead,flagsRead,rip,?_⟩
  intro index within
  rw [frame.memory]
  exact loaded index within

namespace Controls

/-- The span rejects to `mov eax, 3`, the invalid-input outcome code. -/
theorem reject_target_is_invalid_input : 80 + site.reject = 590 ∧
    image.view.read 590 = some (0xb8#8) ∧ image.view.read 591 = some (0x03#8) := by
  refine ⟨rfl, ?_, ?_⟩ <;> kernel_reflexivity

/-- A rejection label one byte off the invalid-input entry does not describe the captured span:
the image's short-region branch displacement byte is `0xd6`. -/
theorem shifted_reject_not_loaded : image.view.read (80 + 36) = some (0xd6#8) ∧
    (X86BoundedLoad.bytes { site with reject := 511 })[36]? = some 0xd7 := by
  refine ⟨?_, by decide⟩
  kernel_reflexivity

end Controls

#print axioms span_bytes
#print axioms bounds_agree
#print axioms load_observes

end Mettapedia.Machines.TIsa.X86P1QwordLoadCapture
