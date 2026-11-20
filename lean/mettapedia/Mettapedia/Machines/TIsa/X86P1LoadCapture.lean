import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86BoundedLoad
import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.P1Memory

/-!
# Actual p1 LOAD bytes joined to original Sail execution

The named R_DERIVE_IS_PROP image supplies its source instruction and complete
43-byte LOAD span at offset 24, after the prologue that saves the callee
registers and loads the allowance register, including its seven-byte MOV-load
tail at offsets 60 through 66. The image bytes come from the p1-v2 allowance
bundle, selected by its actual name. Loaded bytes and address geometry derive
every fetch field.

The span is the parameterized bounded-load template whose rejection target is
the image's invalid handler at offset 590; the rejection label of the previous
image (32 bytes later) does not match its branch displacements (`Controls`). Original Sail
execution reaches the bounds exits or the zero-extended register result.
Under nonwrapping capability and pointer bounds, native range tests agree with
the source access predicate. The resource theorem realizes the same typed read
value. Invalid-handler execution, the whole program, actual admission and ABI
still require their own composition.
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

theorem byte_extent : propImage.size = 647 := by kernel_reflexivity

theorem containing_span : propImage.spans.any (fun span =>
    span.offset == 24 && span.length == 43 && span.kind == "LOAD" && span.path == some [0, 0]) = true := by
  kernel_reflexivity

theorem header_bytes :
    propImage.view.read 60 = some (0x44#8) ∧
    propImage.view.read 61 = some (0x8b#8) ∧
    propImage.view.read 62 = some (0x96#8) := by
  constructor
  · kernel_reflexivity
  · constructor <;> kernel_reflexivity

theorem displacement_bytes (index : Nat) (within : index < 4) :
    propImage.view.read (63 + index) = some (0#8) := by
  interval_cases index <;> kernel_reflexivity

def Loaded (image : P1Capture.Program) (state : State) (base : Int) : Prop :=
  ∀ offset < image.size,
    state.mem.get? ((X86Execution.address base offset).signExtend 52).toNat = image.view.read offset

theorem captured_fields (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 60) (loaded : Loaded propImage state base) :
    state.mem.get? (origin.address.signExtend 52).toNat = some (0x44#8) ∧
    state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8) ∧
    state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x96#8) ∧
    ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat = some (0#8) := by
  have at0 : X86Execution.address base 60 = origin.address := by
    change BitVec.ofInt 48 (base + (60 : Int)) = origin.address
    rw [← placed, BitVec.ofInt_toInt]
  have at1 : X86Execution.address base 61 = origin.opcodeAddress := by
    change BitVec.ofInt 48 (base + (61 : Int)) = origin.opcodeAddress
    have position : base + 61 = origin.opcodeAddress.toInt := by have := origin.step1; omega
    rw [position, BitVec.ofInt_toInt]
  have at2 : X86Execution.address base 62 = origin.modrmAddress := by
    change BitVec.ofInt 48 (base + (62 : Int)) = origin.modrmAddress
    have position : base + 62 = origin.modrmAddress.toInt := by have := origin.step2; omega
    rw [position, BitVec.ofInt_toInt]
  have atNext : origin.next.toInt = base + 63 := by
    have := origin.step2
    have := origin.step3
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [at0] using (loaded 60 (by rw [byte_extent]; decide)).trans header_bytes.1
  · simpa only [at1] using (loaded 61 (by rw [byte_extent]; decide)).trans header_bytes.2.1
  · simpa only [at2] using (loaded 62 (by rw [byte_extent]; decide)).trans header_bytes.2.2
  · intro index within
    have shifted : X86Execution.address base (63 + index) = X86Execution.address origin.next.toInt index := by
      unfold X86Execution.address
      rw [atNext]
      congr 1
      omega
    simpa only [shifted] using (loaded (63 + index) (by rw [byte_extent]; omega)).trans
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

theorem captured_executes_checked (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer : Word) (value : BitVec 32) (flags : BitVec 32)
    (placed : origin.address.toInt = base + 60) (loaded : Loaded propImage state base)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state 6 = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48))
    (dataPresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 10 (value.zeroExtend 64)) finish) := by
  obtain ⟨rexLoaded, opcode, modrm, displacement⟩ := captured_fields state base origin placed loaded
  exact X86DwordLoad.fetched_dword_checked other vector state 10 6 (by decide) (by decide) origin finish dataAddress
    visible controls pointer value flags (0#32) advance dataUpper baseKnown controlKnown flagsKnown visibleKnown quiet
    (by simpa using effective) safe rexLoaded opcode modrm (by simpa using displacement) dataPresent


theorem captured_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer : Word) (value : BitVec 32) (flags : BitVec 32)
    (placed : origin.address.toInt = base + 60) (loaded : Loaded propImage state base)
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
  exact captured_executes_checked other vector state base origin finish dataAddress visible controls
    pointer value flags placed loaded advance dataUpper baseKnown controlKnown flagsKnown visibleKnown
    quiet effective (Or.inr aligned) dataPresent


/-- The span as the parameterized bounded load: logical destination 6 (R10), logical base 1
(RSI), region 0, displacement 0, rejecting to the invalid handler 566 bytes after its start. -/
def site : X86BoundedLoad.Instruction where
  wide := false
  destination := 6
  base := 1
  region := 0
  offset := ⟨0, by decide⟩
  reject := 566
  unlocked := by decide
  noSib := by decide
  noStack := by decide

theorem site_registers :
    X86BoundedLoad.physical site.destination = 10 ∧ X86BoundedLoad.physical site.base = 6 := by
  decide

theorem site_length : (X86BoundedLoad.bytes site).length = 43 := by
  rw [X86BoundedLoad.bytes_length]
  rfl

theorem span_bytes (index : Fin 43) :
    propImage.view.read (24 + index.val) =
      ((X86BoundedLoad.bytes site)[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem span_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 24) (loaded : Loaded propImage state base) :
    codeLoaded state origin.address.toInt (X86BoundedLoad.bytes site) := by
  intro index byte present
  have bounded : index < 43 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    rwa [site_length] at bounded
  have capture := span_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (24 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (24 + index) (by rw [byte_extent]; omega)).trans capture

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 24) (offset : Nat) :
    X86Bounds.position start offset = address base (24 + offset) := by
  unfold X86Bounds.position address
  rw [placed]
  congr 1
  omega

/-- The bounds geometry of the span: the image extends `647 - 24` bytes past its start. -/
def context (start : BitVec 48) (upper : start.toInt + 623 < (2 ^ 47 : Int)) :
    X86Bounds.Context (X86BoundedLoad.layout site) start where
  extent := 623
  upper := upper
  codeWithin := by decide
  rejectWithin := by decide
  overflowDelta := by decide
  shortDelta := by decide
  rangeDelta := by decide

def inputs (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : Loaded propImage state base) : X86BoundedLoad.Inputs site state origin where
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
  tailWithin := show X86Bounds.exitAt (X86BoundedLoad.layout site) + 10 ≤ 623 by decide
  loaded := span_loaded state base origin placed loaded

/-- Region-0 descriptor observations through RSI, located at a fetch position: any bounds layout
whose pointer is RSI and whose region is 0 supplies the premise facts of the span. -/
def located {state : State} {layout : X86Bounds.Layout} (pointer : layout.pointer = 6) (region : layout.region = 0)
    (facts : X86Bounds.Facts layout state) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 623 < (2 ^ 47 : Int)) : Facts state origin 623 where
  upper := upper
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
  pointerKnown := by rw [← pointer]; exact facts.pointerKnown
  baseEffective := by
    have effective := facts.baseEffective
    rw [X86Bounds.baseDisplacement, region] at effective
    simpa using effective
  lengthEffective := by
    have effective := facts.lengthEffective
    rw [X86Bounds.lengthDisplacement, region] at effective
    exact effective
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

theorem bounds_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : Loaded propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if facts.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat then address base 60
          else address base 590).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, rip⟩ :=
    X86Bounds.classifies other extra vector _ state origin (inputs state base origin facts placed loaded).bounds
  have steps : X86Bounds.boundsSteps (X86BoundedLoad.layout site) facts.base facts.pointer facts.length =
      if facts.length.toNat < 4 then 5 else 7 := by
    have noWrap := (facts.pointer - facts.base).isLt
    have offsetZero : (X86BoundedLoad.layout site).offset.val = 0 := rfl
    have countFour : (X86BoundedLoad.layout site).count.val = 4 := rfl
    have twoSteps : X86Bounds.offsetSteps (X86BoundedLoad.layout site) = 2 := rfl
    simp only [X86Bounds.boundsSteps, offsetZero, countFour, twoSteps, Nat.add_zero]
    rw [if_neg (by omega)]
  change after.regs.get? .rip = some
    ((if (facts.pointer - facts.base).toNat + 0 + 4 ≤ facts.length.toNat then X86Bounds.position origin.address 36
      else X86Bounds.position origin.address 566).signExtend 64) at rip
  rw [Nat.add_zero, position_in_image origin.address base placed 36,
    position_in_image origin.address base placed 566] at rip
  refine ⟨after, steps ▸ executed, framed, framed.lookup 10 (by decide), rip, ?_⟩
  intro offset within
  rw [framed.memory]
  exact loaded offset within

theorem low_bytes (value : BitVec 32) (index : Nat) (within : index < 4) :
    (value.zeroExtend 64).extractLsb' (8 * index) 8 = value.extractLsb' (8 * index) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  simp only [BitVec.getLsbD_extractLsb', bounded, decide_true, Bool.true_and,
    BitVec.getLsbD_setWidth]
  have inside : 8 * index + bit < 64 := by omega
  simp [inside]

theorem low_value (value : BitVec 32) :
    X86DataLoad.value false (value.zeroExtend 64) = value.zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  simp only [X86DataLoad.value, Bool.false_eq_true, ite_false, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases low : bit < 32
  · simp [low]
  · simp only [low, decide_false, Bool.false_and, Bool.and_false]
    simp [BitVec.getLsbD_of_ge value bit (by omega)]

theorem load_observes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : Loaded propImage state base)
    (value : BitVec 32) (readable : Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      RegisterFrame (insert .r10 writes) state after ∧ lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address base 67).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := inputs state base origin facts placed loaded
  let data : X86BoundedLoad.Readable input := {
    word := value.zeroExtend 64
    dataAddress := readable.dataAddress
    upper := readable.upper
    effective := by
      change facts.pointer + (X86BoundedLoad.displacement site).signExtend 64 = _
      rw [show (X86BoundedLoad.displacement site).signExtend 64 = 0#64 from by decide, BitVec.add_zero]
      exact readable.effective
    safe := Or.inr readable.aligned
    present := fun index within => by
      rw [low_bytes value index within]
      exact readable.bytes index within }
  obtain ⟨after, flags, executed, framed, valueRead, rip, flagsRead, -⟩ :=
    X86BoundedLoad.succeeds other extra vector site state origin input fits data
  have clobbers : X86BoundedLoad.writes site = insert .r10 writes := by decide
  change lookup after (X86BoundedLoad.physical site.destination) =
    some (X86DataLoad.value false (value.zeroExtend 64)) at valueRead
  rw [site_registers.1, low_value] at valueRead
  change after.regs.get? .rip = some ((X86Bounds.position origin.address 43).signExtend 64) at rip
  rw [position_in_image origin.address base placed 43] at rip
  refine ⟨after, flags, executed, clobbers ▸ framed, valueRead, flagsRead, rip, ?_⟩
  intro offset within
  rw [framed.memory]
  exact loaded offset within

theorem load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : Loaded propImage state base)
    (value : BitVec 32) (readable : Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      RegisterFrame (insert .r10 writes) state after ∧ lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some ((address base 67).signExtend 64) ∧ Loaded propImage after base := by
  obtain ⟨after, -, executed, framed, valueRead, -, rip, image⟩ :=
    load_observes other extra vector state base origin facts placed loaded value readable fits
  exact ⟨after, executed, framed, valueRead, rip, image⟩

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
    (facts : Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : Loaded propImage state base)
    (rangeFits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (pointerLower : facts.base.toNat ≤ facts.pointer.toNat)
    (pointerUpper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if facts.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if Memory.access? facts.base facts.length facts.pointer 0 4 = some facts.pointer.toNat then address base 60
          else address base 590).signExtend 64) ∧ Loaded propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, unchanged, rip, image⟩ := bounds_classifies other extra vector state base origin
    facts placed loaded
  refine ⟨after, executed, framed, unchanged, ?_, image⟩
  simpa only [source_guard facts.base facts.length facts.pointer rangeFits pointerLower pointerUpper] using rip

namespace Controls

/-- Both bounds branches of the span reject to `mov eax, 3`, the invalid-input outcome code. -/
theorem reject_target_is_invalid_input : 24 + site.reject = 590 ∧
    propImage.view.read 590 = some (0xb8#8) ∧ propImage.view.read 591 = some (0x03#8) := by
  refine ⟨rfl, ?_, ?_⟩ <;> kernel_reflexivity

/-- The previous image's handler sat 598 bytes after this span's start; that rejection label does
not describe the loaded span: its short-region branch displacement byte would be `0x3b`, while the
image holds `0x1b` at offset `24 + 23`. -/
theorem previous_reject_not_loaded : propImage.view.read 47 = some (0x1b#8) ∧
    (X86BoundedLoad.bytes { site with reject := 598 })[23]? = some 0x3b ∧
    (X86BoundedLoad.bytes site)[23]? = some 0x1b := by
  refine ⟨?_, by decide, by decide⟩
  kernel_reflexivity

end Controls

end Mettapedia.Machines.TIsa.X86P1LoadCapture
