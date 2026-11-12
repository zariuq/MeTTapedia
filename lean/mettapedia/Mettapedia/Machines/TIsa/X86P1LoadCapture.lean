import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86P1LoadBounds
import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.P1Memory

/-!
# Actual p1 LOAD bytes joined to original Sail execution

The named R_DERIVE_IS_PROP image supplies its source instruction and complete
43-byte LOAD span at offset 9, including its seven-byte MOV-load tail at
offsets 45 through 51. The image bytes come from the p1-v2 bundle, selected
by its actual name. Loaded bytes and address geometry derive every fetch field.

Original Sail execution reaches the bounds exits or the zero-extended register
result. Under nonwrapping capability and pointer bounds, native range tests
agree with the source access predicate. The resource theorem realizes the
same typed read value. Invalid-handler execution, the whole program, actual
admission and ABI still require their own composition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1LoadCapture

open _root_.X86Registers X86RegisterRefinement
open X86Execution X86P1LoadBounds
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable def propImage : P1Capture.Program :=
  ImportedP1.programs[1]'(by rw [ImportedP1.exact_count.2]; decide)

theorem selected_by_name :
    ImportedP1.programs.find? (fun program => program.name == "R_DERIVE_IS_PROP") = some propImage := by
  kernel_reflexivity

theorem source_instruction : propImage.source.body.atPath [0, 0] =
    some (.instruction (.load .u32z .word32 0 6 1 0)) := by kernel_reflexivity

theorem byte_extent : propImage.size = 646 := by kernel_reflexivity

theorem containing_span : propImage.spans.any (fun span =>
    span.offset == 9 && span.length == 43 && span.kind == "LOAD" && span.path == some [0, 0]) = true := by
  kernel_reflexivity

theorem header_bytes :
    propImage.view.read 45 = some (0x44#8) ∧
    propImage.view.read 46 = some (0x8b#8) ∧
    propImage.view.read 47 = some (0x96#8) := by
  constructor
  · kernel_reflexivity
  · constructor <;> kernel_reflexivity

theorem displacement_bytes (index : Nat) (within : index < 4) :
    propImage.view.read (48 + index) = some (0#8) := by
  interval_cases index <;> kernel_reflexivity

def Loaded (image : P1Capture.Program) (state : State) (base : Int) : Prop :=
  ∀ offset < image.size,
    state.mem.get? ((X86Execution.address base offset).signExtend 52).toNat = image.view.read offset

theorem captured_fields (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 45) (loaded : Loaded propImage state base) :
    state.mem.get? (origin.address.signExtend 52).toNat = some (0x44#8) ∧
    state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8) ∧
    state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x96#8) ∧
    ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat = some (0#8) := by
  have at0 : X86Execution.address base 45 = origin.address := by
    change BitVec.ofInt 48 (base + (45 : Int)) = origin.address
    rw [← placed, BitVec.ofInt_toInt]
  have at1 : X86Execution.address base 46 = origin.opcodeAddress := by
    change BitVec.ofInt 48 (base + (46 : Int)) = origin.opcodeAddress
    have position : base + 46 = origin.opcodeAddress.toInt := by have := origin.step1; omega
    rw [position, BitVec.ofInt_toInt]
  have at2 : X86Execution.address base 47 = origin.modrmAddress := by
    change BitVec.ofInt 48 (base + (47 : Int)) = origin.modrmAddress
    have position : base + 47 = origin.modrmAddress.toInt := by have := origin.step2; omega
    rw [position, BitVec.ofInt_toInt]
  have atNext : origin.next.toInt = base + 48 := by
    have := origin.step2
    have := origin.step3
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [at0] using (loaded 45 (by rw [byte_extent]; decide)).trans header_bytes.1
  · simpa only [at1] using (loaded 46 (by rw [byte_extent]; decide)).trans header_bytes.2.1
  · simpa only [at2] using (loaded 47 (by rw [byte_extent]; decide)).trans header_bytes.2.2
  · intro index within
    have shifted : X86Execution.address base (48 + index) = X86Execution.address origin.next.toInt index := by
      unfold X86Execution.address
      rw [atNext]
      congr 1
      omega
    simpa only [shifted] using (loaded (48 + index) (by rw [byte_extent]; omega)).trans
      (displacement_bytes index within)

theorem p1_value (value : BitVec 32) :
    P1Memory.loadValue .u32z (Memory.byteWords (unpackBytes 4 (value.zeroExtend 64))) =
      some (value.zeroExtend 64) := by
  have low : low32 (value.zeroExtend 64) = value := low32_extend32 false value
  have packed : packBytes (unpackBytes 4 (value.zeroExtend 64)) = value.zeroExtend 64 := by
    rw [pack_unpack32]
    change (low32 (value.zeroExtend 64)).zeroExtend 64 = value.zeroExtend 64
    rw [low]
  rw [P1Memory.load_byteWords, packed]
  change some (extend32 false (low32 (value.zeroExtend 64))) = some (value.zeroExtend 64)
  rw [low]
  rfl

theorem resource_step (keys : Finset P1Memory.Key) (before : P1Memory.Key → Word)
    (address : Nat) (value : BitVec 32)
    (included : (P1Memory.loadRecipe .u32z .word32 0 6 1 0 address).support ⊆ keys)
    (mode : before (.capabilityMode 0) = 1 ∨ before (.capabilityMode 0) = 2)
    (access : Memory.access? (before (.capabilityBase 0)) (before (.capabilityLength 0))
      (before (.register 1)) 0 4 = some address)
    (bytes : (Memory.byteKeys address 4).map before = Memory.byteWords (unpackBytes 4 (value.zeroExtend 64))) :
    (CellEffects.profile [P1Memory.loadRecipe .u32z .word32 0 6 1 0 address]).theory.rewrites
      (Cells.encode keys before)
      (Cells.encode keys (Function.update before (.register 6) (value.zeroExtend 64))) := by
  apply (P1Memory.load_rewrite_iff _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨value.zeroExtend 64, included, mode, access, ?_, rfl⟩
  change P1Memory.loadValue .u32z ((Memory.byteKeys address 4).map before) = some (value.zeroExtend 64)
  rw [bytes, p1_value]

theorem source_recipe (address : Nat) :
    (propImage.source.body.atPath [0, 0]).bind (fun statement => match statement with
      | .instruction instruction => P1Memory.memoryRecipe? instruction address
      | _ => none) = some (P1Memory.loadRecipe .u32z .word32 0 6 1 0 address) := by
  rw [source_instruction]
  rfl

theorem captured_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer : Word) (value : BitVec 32) (flags : BitVec 32)
    (placed : origin.address.toInt = base + 45) (loaded : Loaded propImage state base)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state 6 = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (dataPresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 10 (value.zeroExtend 64)) finish) := by
  obtain ⟨rexLoaded, opcode, modrm, displacement⟩ := captured_fields state base origin placed loaded
  exact X86DwordLoad.fetched_dword other vector state 10 6 (by decide) (by decide) origin finish dataAddress
    visible controls pointer value flags (0#32) advance dataUpper baseKnown controlKnown flagsKnown visibleKnown quiet
    (by simpa using effective) aligned rexLoaded opcode modrm (by simpa using displacement) dataPresent


theorem span_bytes (index : Fin 43) :
    propImage.view.read (9 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem span_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 9) (loaded : Loaded propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 43 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 43 at bounded
    exact bounded
  have capture := span_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (9 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (9 + index) (by rw [byte_extent]; omega)).trans capture


theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 9) (offset : Nat) :
    position start offset = address base (9 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

def inputs (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 9)
    (loaded : Loaded propImage state base) : Inputs state origin :=
  ⟨facts, span_loaded state base origin placed loaded⟩

theorem bounds_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 9) (loaded : Loaded propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if facts.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat then address base 45
          else address base 607).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, unchanged, rip⟩ := X86P1LoadBounds.bounds_classifies other extra vector state origin
    (inputs state base origin facts placed loaded)
  refine ⟨after, executed, framed, unchanged, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 36, position_in_image origin.address base placed 598] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 9) (loaded : Loaded propImage state base)
    (value : BitVec 32) (readable : Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      RegisterFrame (insert .r10 writes) state after ∧ lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some ((address base 52).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, valueRead, rip⟩ := X86P1LoadBounds.load_executes other extra vector state origin
    (inputs state base origin facts placed loaded) value readable fits
  refine ⟨after, executed, framed, valueRead, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 43] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem source_guard (base length pointer : Word) (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat) (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat) :
    (pointer - base).toNat + 4 ≤ length.toNat ↔
      Memory.access? base length pointer 0 4 = some pointer.toNat := by
  have subtract : (pointer - base).toNat = pointer.toNat - base.toNat :=
    BitVec.toNat_sub_of_le (by change base.toNat ≤ pointer.toNat; exact pointerLower)
  change (pointer - base).toNat + 4 ≤ length.toNat ↔
    Memory.access? base length pointer (0#32).toInt 4 = some pointer.toNat
  rw [subtract, P1Memory.access?_iff_inside base length pointer (0#32) 4 pointer.toNat
    rangeFits pointerLower pointerUpper]
  change pointer.toNat - base.toNat + 4 ≤ length.toNat ↔
    (base.toNat : Int) ≤ (pointer.toNat : Int) + 0 ∧
    (pointer.toNat : Int) + 0 + 4 ≤ (base.toNat : Int) + length.toNat ∧
    pointer.toNat = ((pointer.toNat : Int) + 0).toNat
  simp only [Int.add_zero, Int.toNat_natCast, and_true]
  omega

theorem bounds_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 9) (loaded : Loaded propImage state base)
    (rangeFits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (pointerLower : facts.base.toNat ≤ facts.pointer.toNat)
    (pointerUpper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if facts.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if Memory.access? facts.base facts.length facts.pointer 0 4 = some facts.pointer.toNat then address base 45
          else address base 607).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, unchanged, rip, image⟩ := bounds_classifies other extra vector state base origin
    facts placed loaded
  refine ⟨after, executed, framed, unchanged, ?_, image⟩
  simpa only [source_guard facts.base facts.length facts.pointer rangeFits pointerLower pointerUpper] using rip

end Mettapedia.Machines.TIsa.X86P1LoadCapture
