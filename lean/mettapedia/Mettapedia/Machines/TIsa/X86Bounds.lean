import Mettapedia.Machines.TIsa.X86BoundsArithmetic
import Mettapedia.Machines.TIsa.X86P1QwordBounds
import Mettapedia.Machines.TIsa.X86ControlFlags

/-!
# Parameterized native memory-bounds templates

The pointer register, capability slot, nonnegative displacement, access count
and rejection continuation are parameters. Zero displacement omits ADD/JB;
nonzero displacement retains the checked-add path. Byte geometry is explicit
and checked independently of the memory-access semantics. The finer contracts
retain every nonarithmetic flag bit through all prefixes and bounds outcomes;
the original interfaces are projected corollaries of those same executions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Bounds
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

structure Layout where
  pointer : Fin 16
  region : Fin 9
  offset : X86BoundsArithmetic.Offset
  count : Fin 128
  reject : Nat

def extra (layout : Layout) : Nat := if layout.offset.val = 0 then 0 else 13
def lengthAt (layout : Layout) : Nat := 10 + extra layout
def subtractAt (layout : Layout) : Nat := 17 + extra layout
def shortAt (layout : Layout) : Nat := 21 + extra layout
def compareAt (layout : Layout) : Nat := 27 + extra layout
def rangeAt (layout : Layout) : Nat := 30 + extra layout
def exitAt (layout : Layout) : Nat := 36 + extra layout
def baseDisplacement (layout : Layout) : BitVec 32 := BitVec.ofNat 32 (16 * layout.region.val)
def lengthDisplacement (layout : Layout) : BitVec 32 := BitVec.ofNat 32 (16 * layout.region.val + 8)
def branchDelta (layout : Layout) (next : Nat) : BitVec 32 := BitVec.ofInt 32 ((layout.reject : Int) - next)
def little32 (word : BitVec 32) : List Nat :=
  (List.range 4).map (fun index => (word.extractLsb' (8 * index) 8).toNat)

def addCode (layout : Layout) : List Nat :=
  [0x49,0x81,0xc6] ++ little32 (X86PositiveImmediate.immediate32 layout.offset) ++
    [0x0f,0x82] ++ little32 (branchDelta layout 23)

def headCode (layout : Layout) : List Nat :=
  [(rex true layout.pointer 14).toNat,0x89,(modRM layout.pointer 14).toNat] ++
    ([0x4c,0x2b,0xb7] ++ little32 (baseDisplacement layout))

def offsetCode (layout : Layout) : List Nat := if layout.offset.val = 0 then [] else addCode layout

def tailCode (layout : Layout) : List Nat :=
  ([0x4c,0x8b,0xbf] ++ little32 (lengthDisplacement layout)) ++
  [0x49,0x83,0xef,layout.count.val] ++
  ([0x0f,0x82] ++ little32 (branchDelta layout (compareAt layout))) ++
  [0x4d,0x39,0xfe] ++
  ([0x0f,0x87] ++ little32 (branchDelta layout (exitAt layout)))

def code (layout : Layout) : List Nat := (headCode layout ++ offsetCode layout) ++ tailCode layout

theorem little32_length (word : BitVec 32) : (little32 word).length = 4 := by simp [little32]
theorem addCode_length (layout : Layout) : (addCode layout).length = 13 := by simp [addCode,little32_length]
theorem code_length (layout : Layout) : (code layout).length = exitAt layout := by
  by_cases zero : layout.offset.val = 0 <;>
    simp [code,headCode,offsetCode,tailCode,exitAt,extra,zero,little32_length,addCode_length]

theorem headCode_length (layout : Layout) : (headCode layout).length = 10 := by simp [headCode,little32_length]

theorem prefix_length (layout : Layout) : (headCode layout ++ offsetCode layout).length = lengthAt layout := by
  by_cases zero : layout.offset.val = 0 <;>
    simp [headCode_length,offsetCode,lengthAt,extra,zero,addCode_length]

theorem tail_byte (layout : Layout) (index : Nat) :
    (code layout)[lengthAt layout + index]? = (tailCode layout)[index]? := by
  rw [code,List.getElem?_append_right (by rw [prefix_length]; omega),prefix_length,Nat.add_sub_cancel_left]

abbrev writes : Finset Register := {.rip,.rflags,.r14,.r15}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev baseHandlers := X86P1QwordBounds.baseHandlers
noncomputable abbrev handlers := X86P1QwordBounds.handlers
def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

structure Context (layout : Layout) (start : BitVec 48) where
  extent : Nat
  upper : start.toInt + extent < (2 ^ 47 : Int)
  codeWithin : exitAt layout ≤ extent
  rejectWithin : layout.reject ≤ extent
  overflowDelta : (branchDelta layout 23).toInt = (layout.reject : Int) - 23
  shortDelta : (branchDelta layout (compareAt layout)).toInt = (layout.reject : Int) - compareAt layout
  rangeDelta : (branchDelta layout (exitAt layout)).toInt = (layout.reject : Int) - exitAt layout

theorem position_exact (layout : Layout) (start : BitVec 48) (context : Context layout start)
    (offset : Nat) (within : offset ≤ context.extent) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) context.upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by simp [position,address]

theorem position_shift (layout : Layout) (start : BitVec 48) (context : Context layout start)
    (offset index : Nat) (within : offset ≤ context.extent) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact layout start context offset within]
  simp only [position,address,Nat.cast_add,Int.add_assoc]

structure Facts (layout : Layout) (state : State) where
  frame : Word
  base : Word
  pointer : Word
  length : Word
  baseAddress : BitVec 48
  lengthAddress : BitVec 48
  controls : Vector (BitVec 64) 17
  visible : Vector (BitVec 16) 6
  flags : BitVec 32
  frameKnown : lookup state 7 = some frame
  pointerKnown : lookup state layout.pointer = some pointer
  baseEffective : frame + (baseDisplacement layout).signExtend 64 = baseAddress.signExtend 64
  lengthEffective : frame + (lengthDisplacement layout).signExtend 64 = lengthAddress.signExtend 64
  baseUpper : baseAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  lengthUpper : lengthAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  baseAligned : baseAddress &&& (7#48) = (0#48)
  lengthAligned : lengthAddress &&& (7#48) = (0#48)
  controlKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  baseBytes : ∀ index < 8,
    state.mem.get? ((address baseAddress.toInt index).signExtend 52).toNat = some (base.extractLsb' (8 * index) 8)
  lengthBytes : ∀ index < 8,
    state.mem.get? ((address lengthAddress.toInt index).signExtend 52).toNat = some (length.extractLsb' (8 * index) 8)

structure Inputs (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state) extends Facts layout state where
  geometry : Context layout origin.address
  loaded : codeLoaded state origin.address.toInt (code layout)

/-- Descriptor observations survive any frame that keeps the frame and pointer registers and the
descriptor words. -/
def Facts.transport {layout : Layout} {before after : State} {registers : Finset Register} {written : Finset Nat}
    (facts : Facts layout before) (frame : X86StateFrame.Frame registers written before after)
    (dataOnly : registers ⊆ dataRegisters) (frameKept : key 7 ∉ registers) (pointerKept : key layout.pointer ∉ registers)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags)
    (baseApart : ∀ byte < 8, ((address facts.baseAddress.toInt byte).signExtend 52).toNat ∉ written)
    (lengthApart : ∀ byte < 8, ((address facts.lengthAddress.toInt byte).signExtend 52).toNat ∉ written) :
    Facts layout after := by
  let kept (register : Register) (outside : register ∉ dataRegisters) :=
    frame.registers register (fun member => outside (dataOnly member))
  exact {
    facts with
    flags := flags
    frameKnown := (frame.lookup 7 frameKept).trans facts.frameKnown
    pointerKnown := (frame.lookup layout.pointer pointerKept).trans facts.pointerKnown
    controlKnown := (kept .ctrs (by decide)).trans facts.controlKnown
    visibleKnown := (kept .seg_visibles (by decide)).trans facts.visibleKnown
    flagsKnown := flagsKnown
    quiet := (kept .log_register_writes (by decide)).trans facts.quiet
    baseBytes := fun byte within => (frame.memory _ (baseApart byte within)).trans (facts.baseBytes byte within)
    lengthBytes := fun byte within => (frame.memory _ (lengthApart byte within)).trans (facts.lengthBytes byte within) }

theorem loaded_word32 (layout : Layout) (state : State) (start : BitVec 48) (context : Context layout start)
    (loaded : codeLoaded state start.toInt (code layout)) (offset : Nat) (within : offset ≤ context.extent)
    (word : BitVec 32) (encoded : ∀ index : Fin 4,
      (code layout)[offset + index.val]? = some (word.extractLsb' (8 * index.val) 8).toNat) :
    ∀ index < 4, state.mem.get? ((address (position start offset).toInt index).signExtend 52).toNat =
      some (word.extractLsb' (8 * index) 8) := by
  intro index bounded
  rw [position_shift layout start context offset index within]
  simpa only [position,BitVec.ofNat_toNat,BitVec.setWidth_eq] using loaded _ _ (encoded ⟨index,bounded⟩)

theorem merged_control (before middle : State) (flags output : BitVec 32) (next : BitVec 48)
    (known : before.regs.get? .rflags = some flags) :
    X86ControlFlags.Preserved before
      (X86Move.putPointer (X86Flags.putFlags middle (X86Flags.mergeFlags flags output)) next) := by
  unfold X86ControlFlags.Preserved
  rw [(pointer_frame _ next).registers .rflags (by decide)]
  simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self,known,Option.map_some,X86ControlFlags.arithmetic_mask]

theorem move_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step state after ∧ RegisterFrame {.r14,.rip} state after ∧ lookup after 14 = some input.pointer ∧
      after.regs.get? .rip = some ((position origin.address 3).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have within : 3 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin
    have bound : 36 ≤ exitAt layout := by simp [exitAt]
    omega
  let site := windowAt state state origin (RegisterFrame.refl dataRegisters state) input.geometry.upper 0 within
    (by simpa [address] using origin.rip) (code layout) input.loaded layout.pointer 14 (0x89#8)
    (by simp [code,headCode]) (by simp [code,headCode]) (by simp [code,headCode])
  have run := X86InstructionFetch.fetch_register64 state site.address site.opcodeAddress site.modrmAddress site.next
    site.control site.attributes layout.pointer 14 site.step1 site.step2 site.step3 site.status site.fault site.msrs
    site.segments site.longMode site.codeMode site.application site.rip site.prefixByte site.opcodeByte site.modrmByte
    input.pointer input.pointerKnown input.quiet
  let after := X86Move.putPointer (put state 14 input.pointer) (position origin.address 3)
  refine ⟨after,run,?_,?_,?_⟩
  · simpa only [after,show key (14 : Fin 16) = .r14 from rfl,Finset.singleton_union] using
      (put_frame state 14 input.pointer).trans (pointer_frame _ (position origin.address 3))
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]

theorem subtract_step_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftKnown : lookup current 14 = some input.pointer) (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 3).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r14,.rflags,.rip} current after ∧
      lookup after 14 = some (input.pointer - input.base) ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 10).signExtend 64) ∧ X86ControlFlags.Preserved current after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have bound : 36 ≤ exitAt layout := by simp [exitAt]
  have ten : 10 ≤ input.geometry.extent := by have := input.geometry.codeWithin; omega
  let site := rebase state current origin (framed.mono writes_data) input.geometry.upper 3 (by omega) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 6).toInt + 4 = (position origin.address 10).toInt := by
    rw [position_exact layout _ input.geometry 6 (by omega),position_exact layout _ input.geometry 10 ten]
    omega
  obtain ⟨output,run⟩ := X86Funding.GenericMemory.fetched_subtract (handlers other extraHandlers) vector current site
    (position origin.address 10) input.baseAddress input.visible input.controls input.frame input.pointer input.base flags
    (baseDisplacement layout) advance input.baseUpper ((framed.lookup 7 (by decide)).trans input.frameKnown) leftKnown
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet) input.baseEffective input.baseAligned
    (loaded 3 0x4c (by simp [code,headCode])) (loaded 4 0x2b (by simp [code,headCode])) (loaded 5 0xb7 (by simp [code,headCode]))
    (loaded_word32 layout current origin.address input.geometry loaded 6 (by omega) (baseDisplacement layout)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.baseBytes index within)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put current 14 (input.pointer - input.base)) nextFlags)
    (position origin.address 10)
  refine ⟨after,nextFlags,run,?_,?_,?_,?_,?_⟩
  · exact (((put_frame current 14 (input.pointer - input.base)).trans (flags_frame _ nextFlags)).trans
      (pointer_frame _ (position origin.address 10))).mono (by decide)
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ (position origin.address 10)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
  · exact merged_control current (put current 14 (input.pointer - input.base)) flags output (position origin.address 10) flagsKnown

theorem subtract_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftKnown : lookup current 14 = some input.pointer) (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 3).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r14,.rflags,.rip} current after ∧
      lookup after 14 = some (input.pointer - input.base) ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 10).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,value,flagsRead,next,_control⟩ := subtract_step_control other extraHandlers vector layout state current origin input framed flags leftKnown flagsKnown rip
  exact ⟨after,nextFlags,run,frame,value,flagsRead,next⟩

theorem tail_at (layout : Layout) (offset index : Nat) (relative : offset = lengthAt layout + index) :
    (code layout)[offset]? = (tailCode layout)[index]? := by rw [relative,tail_byte]

theorem length_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address (lengthAt layout)).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.r15,.rip} current after ∧ lookup after 15 = some input.length ∧
      after.regs.get? .rip = some ((position origin.address (subtractAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have span : lengthAt layout + 26 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin
    simp only [lengthAt,exitAt] at *
    omega
  have next : subtractAt layout = lengthAt layout + 7 := by simp only [subtractAt,lengthAt]; omega
  let site := rebase state current origin (framed.mono writes_data) input.geometry.upper (lengthAt layout) (by omega) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address (lengthAt layout + 3)).toInt + 4 =
      (position origin.address (subtractAt layout)).toInt := by
    rw [position_exact layout _ input.geometry _ (by omega),position_exact layout _ input.geometry _ (by omega)]
    omega
  have run := X86FrameLoad.fetched_frame (handlers other extraHandlers) vector current 15 site
    (position origin.address (subtractAt layout)) input.lengthAddress input.visible input.controls input.frame input.length flags
    (lengthDisplacement layout) advance input.lengthUpper ((framed.lookup 7 (by decide)).trans input.frameKnown)
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet) input.lengthEffective input.lengthAligned
    (loaded _ 0x4c (by rw [tail_at layout _ 0 (by omega)]; rfl))
    (loaded _ 0x8b (by rw [tail_at layout _ 1 (by omega)]; rfl))
    (loaded _ 0xbf (by rw [tail_at layout _ 2 (by omega)]; rfl))
    (loaded_word32 layout current origin.address input.geometry loaded (lengthAt layout + 3) (by omega)
      (lengthDisplacement layout) (by intro index; rw [tail_at layout _ (3 + index.val) (by omega)]; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.lengthBytes index within)
  let after := X86Move.putPointer (put current 15 input.length) (position origin.address (subtractAt layout))
  refine ⟨after,run,?_,?_,?_⟩
  · simpa only [after,show key (15 : Fin 16) = .r15 from rfl,Finset.singleton_union] using
      (put_frame current 15 input.length).trans (pointer_frame _ (position origin.address (subtractAt layout)))
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]

theorem subtract_count_step_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags) (lengthKnown : lookup current 15 = some input.length)
    (rip : current.regs.get? .rip = some ((position origin.address (subtractAt layout)).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r15,.rflags,.rip} current after ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      current.mem = after.mem ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags = Functions.bool_to_bits (input.length.toNat < layout.count.val) ∧
      after.regs.get? .rip = some ((position origin.address (shortAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved current after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have span : lengthAt layout + 26 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin
    simp only [lengthAt,exitAt] at *
    omega
  have first : subtractAt layout = lengthAt layout + 7 := by simp only [subtractAt,lengthAt]; omega
  have last : shortAt layout = lengthAt layout + 11 := by simp only [shortAt,lengthAt]; omega
  let site := rebase state current origin (framed.mono writes_data) input.geometry.upper (subtractAt layout) (by omega) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address (subtractAt layout + 3)).toInt + 1 =
      (position origin.address (shortAt layout)).toInt := by
    rw [position_exact layout _ input.geometry _ (by omega),position_exact layout _ input.geometry _ (by omega)]
    omega
  obtain ⟨output,run,carry⟩ := X86SubByteImmediate.fetched (handlers other extraHandlers) vector current layout.count site
    (position origin.address (shortAt layout)) input.length flags advance lengthKnown flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded _ 0x49 (by rw [tail_at layout _ 7 (by omega)]; rfl))
    (loaded _ 0x83 (by rw [tail_at layout _ 8 (by omega)]; rfl))
    (loaded _ 0xef (by rw [tail_at layout _ 9 (by omega)]; rfl))
    (loaded _ layout.count.val (by rw [tail_at layout _ 10 (by omega)]; rfl))
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put current 15 (input.length - X86SubByteImmediate.word layout.count)) nextFlags)
    (position origin.address (shortAt layout))
  have frame := X86SubByteImmediate.result_frame current layout.count input.length flags output (position origin.address (shortAt layout))
  refine ⟨after,nextFlags,run,frame,?_,frame.memory.symm,?_,carry,?_,?_⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ (position origin.address (shortAt layout))).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
  · exact merged_control current (put current 15 (input.length - X86SubByteImmediate.word layout.count)) flags output (position origin.address (shortAt layout)) flagsKnown

theorem subtract_count_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags) (lengthKnown : lookup current 15 = some input.length)
    (rip : current.regs.get? .rip = some ((position origin.address (subtractAt layout)).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r15,.rflags,.rip} current after ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      current.mem = after.mem ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags = Functions.bool_to_bits (input.length.toNat < layout.count.val) ∧
      after.regs.get? .rip = some ((position origin.address (shortAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,value,memory,flagsRead,carry,next,_control⟩ := subtract_count_step_control other extraHandlers vector layout state current origin input framed flags flagsKnown lengthKnown rip
  exact ⟨after,nextFlags,run,frame,value,memory,flagsRead,carry,next⟩

theorem add_byte (layout : Layout) (nonzero : layout.offset.val ≠ 0) (index : Nat) (within : index < 13) :
    (code layout)[10 + index]? = (addCode layout)[index]? := by
  rw [code,List.getElem?_append_left (by rw [prefix_length]; simp only [lengthAt,extra,if_neg nonzero]; omega)]
  rw [List.getElem?_append_right (by rw [headCode_length]; omega),headCode_length,Nat.add_sub_cancel_left]
  simp only [offsetCode,if_neg nonzero]

theorem add_step_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (nonzero : layout.offset.val ≠ 0)
    (state current : State) (origin : X86LegacyFetch.Basis state) (input : Inputs layout state origin)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (offsetKnown : lookup current 14 = some (input.pointer - input.base))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 10).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r14,.rflags,.rip} current after ∧
      lookup after 14 = some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      after.regs.get? .rflags = some nextFlags ∧ Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits (2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val) ∧
      after.regs.get? .rip = some ((position origin.address 17).signExtend 64) ∧ X86ControlFlags.Preserved current after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have extent : 49 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin
    simpa only [exitAt,extra,if_neg nonzero] using this
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  let site := windowAt state current origin (framed.mono writes_data) input.geometry.upper 10 (by omega) rip
    (code layout) loaded 0 14 (0x81#8)
    (by rw [add_byte layout nonzero 0 (by decide)]; rfl)
    (by rw [add_byte layout nonzero 1 (by decide)]; rfl)
    (by rw [add_byte layout nonzero 2 (by decide)]; rfl)
  have advance : (position origin.address 13).toInt + 4 = (position origin.address 17).toInt := by
    rw [position_exact layout _ input.geometry 13 (by omega),position_exact layout _ input.geometry 17 (by omega)]
    omega
  obtain ⟨output,run,carry⟩ := X86PositiveImmediate.fetched (handlers other extraHandlers) vector current layout.offset 14 site
    (position origin.address 17) (input.pointer - input.base) flags advance offsetKnown flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded_word32 layout current origin.address input.geometry loaded 13 (by omega)
      (X86PositiveImmediate.immediate32 layout.offset)
      (by intro index; have shift : 13 + index.val = 10 + (3 + index.val) := by omega
          rw [shift,add_byte layout nonzero _ (by omega)]; fin_cases index <;> rfl))
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer
    (X86Flags.putFlags (put current 14 (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset)) nextFlags)
    (position origin.address 17)
  refine ⟨after,nextFlags,run,X86RegisterIncrement.result_frame current 14 _ nextFlags _,?_,?_,carry,?_,?_⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ (position origin.address 17)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
  · exact merged_control current (put current 14 (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset)) flags output (position origin.address 17) flagsKnown

theorem add_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (nonzero : layout.offset.val ≠ 0)
    (state current : State) (origin : X86LegacyFetch.Basis state) (input : Inputs layout state origin)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (offsetKnown : lookup current 14 = some (input.pointer - input.base))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 10).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r14,.rflags,.rip} current after ∧
      lookup after 14 = some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      after.regs.get? .rflags = some nextFlags ∧ Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits (2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val) ∧
      after.regs.get? .rip = some ((position origin.address 17).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,value,flagsRead,carry,next,_control⟩ := add_step_control other extraHandlers vector layout nonzero state current origin input framed flags offsetKnown flagsKnown rip
  exact ⟨after,nextFlags,run,frame,value,flagsRead,carry,next⟩

theorem branch_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current)
    (condition : X86BranchCondition.Condition) (offset : Nat) (delta : BitVec 32) (flags : BitVec 32)
    (within : offset + 6 ≤ input.geometry.extent) (jumpOffset : (offset : Int) + 6 + delta.toInt = layout.reject)
    (escape : (code layout)[offset]? = some 0x0f)
    (opcode : (code layout)[offset + 1]? = some (X86BranchCondition.opcode condition).toNat)
    (displacement : ∀ index : Fin 4, (code layout)[offset + 2 + index.val]? =
      some (delta.extractLsb' (8 * index.val) 8).toNat)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address offset).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.rip} current after ∧ after.regs.get? .rip = some
      ((if X86BranchCondition.value condition flags then position origin.address layout.reject
        else position origin.address (offset + 6)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have step1 : (position origin.address offset).toInt + 1 = (position origin.address (offset + 1)).toInt := by
    rw [position_exact layout _ input.geometry _ (by omega),position_exact layout _ input.geometry _ (by omega)]
    omega
  have step2 : (position origin.address (offset + 1)).toInt + 1 = (position origin.address (offset + 2)).toInt := by
    rw [position_exact layout _ input.geometry _ (by omega),position_exact layout _ input.geometry _ (by omega)]
    omega
  have advance : (position origin.address (offset + 2)).toInt + 4 = (position origin.address (offset + 6)).toInt := by
    rw [position_exact layout _ input.geometry _ (by omega),position_exact layout _ input.geometry _ within]
    omega
  have jump : (position origin.address layout.reject).toInt = (position origin.address (offset + 6)).toInt + delta.toInt := by
    rw [position_exact layout _ input.geometry _ input.geometry.rejectWithin,position_exact layout _ input.geometry _ within]
    omega
  have run := X86EscapeFetch.fetched_branch (baseHandlers other) extraHandlers vector condition current
    (position origin.address offset) (position origin.address (offset + 1)) (position origin.address (offset + 2))
    (position origin.address (offset + 6)) (position origin.address layout.reject)
    origin.control origin.attributes flags delta step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans origin.status)
    ((framed.registers .fault_reg (by decide)).trans origin.fault)
    ((framed.registers .msrs (by decide)).trans origin.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans origin.segments)
    origin.longMode origin.codeMode ((framed.registers .app_view (by decide)).trans origin.application)
    rip flagsKnown ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded _ _ escape)
    (by simpa only [position,BitVec.ofNat_toNat,BitVec.setWidth_eq] using loaded _ _ opcode)
    (loaded_word32 layout current origin.address input.geometry loaded (offset + 2) (by omega) delta displacement)
  refine ⟨_,run,pointer_frame _ _,?_⟩
  simp only [X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]

theorem compare_step_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftKnown : lookup current 14 = some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset))
    (rightKnown : lookup current 15 = some (input.length - X86SubByteImmediate.word layout.count))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address (compareAt layout)).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.rflags,.rip} current after ∧
      after.regs.get? .rflags = some nextFlags ∧ X86BranchCondition.value .above nextFlags =
        decide ((input.length - X86SubByteImmediate.word layout.count).toNat <
          (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat) ∧
      after.regs.get? .rip = some ((position origin.address (rangeAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved current after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have span : lengthAt layout + 26 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin
    simp only [lengthAt,exitAt] at *
    omega
  have first : compareAt layout = lengthAt layout + 17 := by simp only [compareAt,lengthAt]; omega
  have last : rangeAt layout = compareAt layout + 3 := by simp only [rangeAt,compareAt]; omega
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  let site := windowAt state current origin (framed.mono writes_data) input.geometry.upper (compareAt layout) (by omega) rip
    (code layout) loaded 15 14 (0x39#8)
    (by rw [tail_at layout _ 17 (by omega)]; rfl)
    (by rw [tail_at layout _ 18 (by omega)]; rfl)
    (by rw [tail_at layout _ 19 (by omega)]; rfl)
  obtain ⟨output,run,carry,zero⟩ := X86Comparison.fetched_compare64 (handlers other extraHandlers) vector current 15 14 site
    (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset)
    (input.length - X86SubByteImmediate.word layout.count) flags rightKnown leftKnown flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags current nextFlags) site.next
  refine ⟨after,nextFlags,run,X86Comparison.status_frame current nextFlags site.next,?_,?_,?_,?_⟩
  · rw [(pointer_frame _ site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · exact X86P1QwordBounds.above_sense _ _ _ ((X86Comparison.merged_carry flags output).trans carry)
      ((X86Comparison.merged_zero flags output).trans zero)
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    have point : site.next = position origin.address (rangeAt layout) := by
      change address origin.address.toInt (compareAt layout + 3) = position origin.address (rangeAt layout)
      rw [← last]
      rfl
    rw [point]
  · exact merged_control current current flags output site.next flagsKnown

#print axioms subtract_step_control
#print axioms subtract_count_step_control
#print axioms add_step_control
#print axioms compare_step_control

theorem compare_step (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftKnown : lookup current 14 = some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset))
    (rightKnown : lookup current 15 = some (input.length - X86SubByteImmediate.word layout.count))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address (compareAt layout)).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.rflags,.rip} current after ∧
      after.regs.get? .rflags = some nextFlags ∧ X86BranchCondition.value .above nextFlags =
        decide ((input.length - X86SubByteImmediate.word layout.count).toNat <
          (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat) ∧
      after.regs.get? .rip = some ((position origin.address (rangeAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,flagsRead,sense,next,_control⟩ := compare_step_control other extraHandlers vector layout state current origin input framed flags leftKnown rightKnown flagsKnown rip
  exact ⟨after,nextFlags,run,frame,flagsRead,sense,next⟩

def offsetSteps (layout : Layout) : Nat := if layout.offset.val = 0 then 2 else 4

theorem head_prefix_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 14 = some (input.pointer - input.base) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((position origin.address 10).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨s1,first,frame1,pointer1,rip1⟩ := move_step other extraHandlers vector layout state origin input
  have flags1 := (frame1.registers .rflags (by decide)).trans input.flagsKnown
  obtain ⟨s2,flags,last,frame2,offset2,flags2,rip2,control2⟩ := subtract_step_control other extraHandlers vector layout state s1 origin input
    (frame1.mono (by decide)) input.flags pointer1 flags1 rip1
  exact ⟨s2,flags,X86FuelPrefix.fetches_cons 1 state s1 s2 first (X86FuelPrefix.fetches_one s1 s2 last),
    (frame1.trans frame2).mono (by decide),offset2,flags2,rip2,
    (X86ControlFlags.of_register_frame frame1 (by decide)).trans control2⟩

theorem head_prefix (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 14 = some (input.pointer - input.base) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((position origin.address 10).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,flagsRead,next,_control⟩ := head_prefix_control other extraHandlers vector layout state origin input
  exact ⟨after,flags,run,frame,value,flagsRead,next⟩

theorem offset_prefix_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val then position origin.address layout.reject
          else position origin.address (lengthAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨s2,f2,first,frame2,offset2,flags2,rip2,control2⟩ := head_prefix_control other extraHandlers vector layout state origin input
  by_cases zero : layout.offset.val = 0
  · have immediateZero : X86PositiveImmediate.immediate64 layout.offset = (0#64) := by
      simp [X86PositiveImmediate.immediate64,zero]
    have noOverflow : ¬ 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val := by
      have := (input.pointer - input.base).isLt
      omega
    exact ⟨s2,f2,by simpa only [offsetSteps,if_pos zero] using first,frame2,
      by simpa only [immediateZero,BitVec.add_zero] using offset2,flags2,
      by simpa only [if_neg noOverflow,lengthAt,extra,if_pos zero] using rip2,control2⟩
  · have extent : 49 ≤ input.geometry.extent := by
      have := input.geometry.codeWithin
      simpa only [exitAt,extra,if_neg zero] using this
    obtain ⟨s3,f3,step3,frame3,offset3,flags3,carry3,rip3,control3⟩ :=
      add_step_control other extraHandlers vector layout zero state s2 origin input frame2 f2 offset2 flags2 rip2
    have frame03 : RegisterFrame writes state s3 := (frame2.trans frame3).mono (by decide)
    obtain ⟨s4,step4,frame4,rip4⟩ := branch_step other extraHandlers vector layout state s3 origin input frame03
      .below 17 (branchDelta layout 23) f3 (by omega)
      (by have := input.geometry.overflowDelta; omega)
      (by rw [add_byte layout zero 7 (by decide)]; rfl)
      (by rw [add_byte layout zero 8 (by decide)]; rfl)
      (by intro index; have shift : 17 + 2 + index.val = 10 + (9 + index.val) := by omega
          rw [shift,add_byte layout zero _ (by omega)]; fin_cases index <;> rfl)
      flags3 rip3
    have sense : X86BranchCondition.value .below f3 =
        decide (2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val) := by
      simp only [X86BranchCondition.value,carry3,X86P1QwordBounds.carry_bit_sense]
    rw [sense] at rip4
    refine ⟨s4,f3,?_,(frame03.trans frame4).mono (by decide),
      (frame4.lookup 14 (by decide)).trans offset3,(frame4.registers .rflags (by decide)).trans flags3,?_,
      (control2.trans control3).trans (X86ControlFlags.of_register_frame frame4 (by decide))⟩
    · simpa only [offsetSteps,if_neg zero] using X86FuelPrefix.fetches_then 2 2 state s2 s4 first
        (X86FuelPrefix.fetches_cons 1 s2 s3 s4 step3 (X86FuelPrefix.fetches_one s3 s4 step4))
    · simpa only [Bool.ite_eq_true_distrib,decide_eq_true_eq,lengthAt,extra,if_neg zero] using rip4

theorem offset_prefix (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val then position origin.address layout.reject
          else position origin.address (lengthAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,flagsRead,next,_control⟩ := offset_prefix_control other extraHandlers vector layout state origin input
  exact ⟨after,flags,run,frame,value,flagsRead,next⟩

theorem arithmetic_prefix_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 2)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ Functions._get_rflagsbits_cf flags =
        Functions.bool_to_bits (input.length.toNat < layout.count.val) ∧
      after.regs.get? .rip = some ((position origin.address (shortAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨s0,f0,first,frame0,offset0,flags0,rip0,control0⟩ := offset_prefix_control other extraHandlers vector layout state origin input
  have fallthrough : s0.regs.get? .rip = some ((position origin.address (lengthAt layout)).signExtend 64) := by
    simpa only [if_neg (by omega : ¬ 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val)] using rip0
  obtain ⟨s1,step1,frame1,length1,rip1⟩ := length_step other extraHandlers vector layout state s0 origin input frame0 f0 flags0 fallthrough
  have frame01 : RegisterFrame writes state s1 := (frame0.trans frame1).mono (by decide)
  have flags1 := (frame1.registers .rflags (by decide)).trans flags0
  obtain ⟨s2,f2,step2,frame2,length2,_,flags2,carry2,rip2,control2⟩ :=
    subtract_count_step_control other extraHandlers vector layout state s1 origin input frame01 f0 flags1 length1 rip1
  refine ⟨s2,f2,X86FuelPrefix.fetches_then (offsetSteps layout) 2 state s0 s2 first
    (X86FuelPrefix.fetches_cons 1 s0 s1 s2 step1 (X86FuelPrefix.fetches_one s1 s2 step2)),
    (frame01.trans frame2).mono (by decide),?_,length2,flags2,carry2,rip2,
    (control0.trans (X86ControlFlags.of_register_frame frame1 (by decide))).trans control2⟩
  exact (frame2.lookup 14 (by decide)).trans ((frame1.lookup 14 (by decide)).trans offset0)

theorem arithmetic_prefix (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 2)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ Functions._get_rflagsbits_cf flags =
        Functions.bool_to_bits (input.length.toNat < layout.count.val) ∧
      after.regs.get? .rip = some ((position origin.address (shortAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,offset,length,flagsRead,carry,next,_control⟩ := arithmetic_prefix_control other extraHandlers vector layout state origin input noWrap
  exact ⟨after,flags,run,frame,offset,length,flagsRead,carry,next⟩

theorem borrow_prefix_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 3)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if input.length.toNat < layout.count.val then position origin.address layout.reject
          else position origin.address (compareAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,first,framed,offsetRead,lengthRead,flagsRead,carry,middleRip,control⟩ :=
    arithmetic_prefix_control other extraHandlers vector layout state origin input noWrap
  have span : lengthAt layout + 26 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin; simp only [lengthAt,exitAt] at *; omega
  have firstAt : shortAt layout = lengthAt layout + 11 := by simp only [shortAt,lengthAt]; omega
  have nextAt : shortAt layout + 6 = compareAt layout := by simp only [shortAt,compareAt]; omega
  obtain ⟨after,last,lastFrame,rip⟩ := branch_step other extraHandlers vector layout state middle origin input framed
    .below (shortAt layout) (branchDelta layout (compareAt layout)) flags (by omega)
    (by have := input.geometry.shortDelta; omega)
    (by rw [tail_at layout _ 11 (by omega)]; rfl)
    (by rw [tail_at layout _ 12 (by omega)]; rfl)
    (by intro index; rw [tail_at layout _ (13 + index.val) (by omega)]; fin_cases index <;> rfl)
    flagsRead middleRip
  have sense : X86BranchCondition.value .below flags = decide (input.length.toNat < layout.count.val) := by
    simp only [X86BranchCondition.value,carry,X86P1QwordBounds.carry_bit_sense]
  rw [sense,nextAt] at rip
  refine ⟨after,flags,?_,(framed.trans lastFrame).mono (by decide),
    (lastFrame.lookup 14 (by decide)).trans offsetRead,(lastFrame.lookup 15 (by decide)).trans lengthRead,
    (lastFrame.registers .rflags (by decide)).trans flagsRead,?_,
    control.trans (X86ControlFlags.of_register_frame lastFrame (by decide))⟩
  · simpa only [Nat.add_assoc] using X86FuelPrefix.fetches_then (offsetSteps layout + 2) 1 state middle after first
      (X86FuelPrefix.fetches_one middle after last)
  · simpa only [Bool.ite_eq_true_distrib,decide_eq_true_eq] using rip

theorem borrow_prefix (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 3)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if input.length.toNat < layout.count.val then position origin.address layout.reject
          else position origin.address (compareAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,offset,length,flagsRead,next,_control⟩ := borrow_prefix_control other extraHandlers vector layout state origin input noWrap
  exact ⟨after,flags,run,frame,offset,length,flagsRead,next⟩

theorem range_prefix_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64)
    (enough : layout.count.val ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 5)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if (input.length - X86SubByteImmediate.word layout.count).toNat <
          (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat then position origin.address layout.reject
          else position origin.address (exitAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨s0,f0,first,frame0,offset0,length0,flags0,rip0,control0⟩ := borrow_prefix_control other extraHandlers vector layout state origin input noWrap
  have fallthrough : s0.regs.get? .rip = some ((position origin.address (compareAt layout)).signExtend 64) := by
    simpa only [if_neg (by omega : ¬ input.length.toNat < layout.count.val)] using rip0
  obtain ⟨s1,f1,step1,frame1,flags1,sense1,rip1,control1⟩ :=
    compare_step_control other extraHandlers vector layout state s0 origin input frame0 f0 offset0 length0 flags0 fallthrough
  have frame01 : RegisterFrame writes state s1 := (frame0.trans frame1).mono (by decide)
  have span : lengthAt layout + 26 ≤ input.geometry.extent := by
    have := input.geometry.codeWithin; simp only [lengthAt,exitAt] at *; omega
  have firstAt : rangeAt layout = lengthAt layout + 20 := by simp only [rangeAt,lengthAt]; omega
  have nextAt : rangeAt layout + 6 = exitAt layout := by simp only [rangeAt,exitAt]; omega
  obtain ⟨s2,step2,frame2,rip2⟩ := branch_step other extraHandlers vector layout state s1 origin input frame01
    .above (rangeAt layout) (branchDelta layout (exitAt layout)) f1 (by omega)
    (by have := input.geometry.rangeDelta; omega)
    (by rw [tail_at layout _ 20 (by omega)]; rfl)
    (by rw [tail_at layout _ 21 (by omega)]; rfl)
    (by intro index; rw [tail_at layout _ (22 + index.val) (by omega)]; fin_cases index <;> rfl)
    flags1 rip1
  rw [sense1,nextAt] at rip2
  refine ⟨s2,f1,?_,(frame01.trans frame2).mono (by decide),?_,?_,?_,?_,
    (control0.trans control1).trans (X86ControlFlags.of_register_frame frame2 (by decide))⟩
  · simpa only [Nat.add_assoc] using X86FuelPrefix.fetches_then (offsetSteps layout + 3) 2 state s0 s2 first
      (X86FuelPrefix.fetches_cons 1 s0 s1 s2 step1 (X86FuelPrefix.fetches_one s1 s2 step2))
  · exact (frame2.lookup 14 (by decide)).trans ((frame1.lookup 14 (by decide)).trans offset0)
  · exact (frame2.lookup 15 (by decide)).trans ((frame1.lookup 15 (by decide)).trans length0)
  · exact (frame2.registers .rflags (by decide)).trans flags1
  · simpa only [Bool.ite_eq_true_distrib,decide_eq_true_eq] using rip2

theorem range_prefix (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64)
    (enough : layout.count.val ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 5)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 =
        some (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset) ∧
      lookup after 15 = some (input.length - X86SubByteImmediate.word layout.count) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if (input.length - X86SubByteImmediate.word layout.count).toNat <
          (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat then position origin.address layout.reject
          else position origin.address (exitAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,offset,length,flagsRead,next,_control⟩ := range_prefix_control other extraHandlers vector layout state origin input noWrap enough
  exact ⟨after,flags,run,frame,offset,length,flagsRead,next⟩

def boundsSteps (layout : Layout) (base pointer length : Word) : Nat :=
  if 2 ^ 64 ≤ (pointer - base).toNat + layout.offset.val then offsetSteps layout
  else if length.toNat < layout.count.val then offsetSteps layout + 3 else offsetSteps layout + 5

theorem classifies_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (boundsSteps layout input.base input.pointer input.length)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rip = some
        ((if (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat
          then position origin.address (exitAt layout) else position origin.address layout.reject).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  by_cases overflow : 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val
  · obtain ⟨after,_,run,frame,_,_,rip,control⟩ := offset_prefix_control other extraHandlers vector layout state origin input
    have notFits : ¬ (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat := by
      have := input.length.isLt; omega
    exact ⟨after,by simpa only [boundsSteps,if_pos overflow] using run,frame,
      by simpa only [if_pos overflow,if_neg notFits] using rip,control⟩
  · have noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64 := by omega
    by_cases short : input.length.toNat < layout.count.val
    · obtain ⟨after,_,run,frame,_,_,_,rip,control⟩ := borrow_prefix_control other extraHandlers vector layout state origin input noWrap
      have notFits : ¬ (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat := by omega
      exact ⟨after,by simpa only [boundsSteps,if_neg overflow,if_pos short] using run,frame,
        by simpa only [if_pos short,if_neg notFits] using rip,control⟩
    · have enough : layout.count.val ≤ input.length.toNat := by omega
      obtain ⟨after,_,run,frame,_,_,_,rip,control⟩ := range_prefix_control other extraHandlers vector layout state origin input noWrap enough
      have condition : (input.length - X86SubByteImmediate.word layout.count).toNat <
          (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat ↔
          ¬ (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat := by
        rw [X86BoundsArithmetic.relative_add_nat input.pointer input.base layout.offset noWrap,
          X86BoundsArithmetic.remaining_nat input.length layout.count enough]
        omega
      exact ⟨after,by simpa only [boundsSteps,if_neg overflow,if_neg short] using run,frame,
        by simpa only [condition,ite_not] using rip,control⟩

theorem classifies (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (boundsSteps layout input.base input.pointer input.length)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rip = some
        ((if (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat
          then position origin.address (exitAt layout) else position origin.address layout.reject).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,next,_control⟩ := classifies_control other extraHandlers vector layout state origin input
  exact ⟨after,run,frame,next⟩

theorem source_classifies_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (rangeFits : input.base.toNat + input.length.toNat < 2 ^ 64)
    (pointerLower : input.base.toNat ≤ input.pointer.toNat) (pointerUpper : input.pointer.toNat ≤ input.base.toNat + input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (boundsSteps layout input.base input.pointer input.length)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rip = some
        ((if Memory.access? input.base input.length input.pointer (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
          some (input.pointer.toNat + layout.offset.val) then position origin.address (exitAt layout)
          else position origin.address layout.reject).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  obtain ⟨after,run,frame,rip,control⟩ := classifies_control other extraHandlers vector layout state origin input
  refine ⟨after,run,frame,?_,control⟩
  simpa only [X86BoundsArithmetic.source_guard input.base input.length input.pointer layout.offset layout.count
    rangeFits pointerLower pointerUpper] using rip

theorem source_classifies (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (rangeFits : input.base.toNat + input.length.toNat < 2 ^ 64)
    (pointerLower : input.base.toNat ≤ input.pointer.toNat) (pointerUpper : input.pointer.toNat ≤ input.base.toNat + input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (boundsSteps layout input.base input.pointer input.length)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rip = some
        ((if Memory.access? input.base input.length input.pointer (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
          some (input.pointer.toNat + layout.offset.val) then position origin.address (exitAt layout)
          else position origin.address layout.reject).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,next,_control⟩ := source_classifies_control other extraHandlers vector layout state origin input rangeFits pointerLower pointerUpper
  exact ⟨after,run,frame,next⟩

theorem succeeds_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : X86Bounds.Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin)
    (fits : (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 5)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((position origin.address (exitAt layout)).signExtend 64) ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  have noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64 := by have := input.length.isLt; omega
  have enough : layout.count.val ≤ input.length.toNat := by omega
  obtain ⟨after,flags,run,frame,_,_,flagsRead,rip,control⟩ := range_prefix_control other extraHandlers vector layout state origin input noWrap enough
  have notAbove : ¬ (input.length - X86SubByteImmediate.word layout.count).toNat <
      (input.pointer - input.base + X86PositiveImmediate.immediate64 layout.offset).toNat := by
    rw [X86BoundsArithmetic.relative_add_nat input.pointer input.base layout.offset noWrap,
      X86BoundsArithmetic.remaining_nat input.length layout.count enough]
    omega
  exact ⟨after,flags,run,frame,flagsRead,by simpa only [if_neg notAbove] using rip,control⟩

theorem succeeds (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin)
    (fits : (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (offsetSteps layout + 5)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((position origin.address (exitAt layout)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,flagsRead,next,_control⟩ := succeeds_control other extraHandlers vector layout state origin input fits
  exact ⟨after,flags,run,frame,flagsRead,next⟩

namespace Controls

def zeroLayout : Layout := ⟨2,1,⟨0,by decide⟩,4,600⟩
def positiveLayout : Layout := ⟨2,1,⟨16,by decide⟩,8,600⟩

def zeroContext : Context zeroLayout (4096#48) where
  extent := 646
  upper := by decide
  codeWithin := by decide
  rejectWithin := by decide
  overflowDelta := by decide
  shortDelta := by decide
  rangeDelta := by decide

def positiveContext : Context positiveLayout (4096#48) where
  extent := 646
  upper := by decide
  codeWithin := by decide
  rejectWithin := by decide
  overflowDelta := by decide
  shortDelta := by decide
  rangeDelta := by decide

theorem zero_byte_count : (code zeroLayout).length = 36 := by decide
theorem positive_byte_count : (code positiveLayout).length = 49 := by decide
theorem zero_instruction_count : offsetSteps zeroLayout + 5 = 7 := by decide
theorem positive_instruction_count : offsetSteps positiveLayout + 5 = 9 := by decide

def unpatchableLayout : Layout := { positiveLayout with reject := 2147483671 }

theorem unpatchable_rejected (start : BitVec 48) : ¬ Nonempty (Context unpatchableLayout start) := by
  rintro ⟨context⟩
  have impossible := context.overflowDelta
  have wrong : (branchDelta unpatchableLayout 23).toInt ≠ (unpatchableLayout.reject : Int) - 23 := by decide
  exact wrong impossible

example : Memory.access? (12288#64) (24#64) (12288#64) (16#32).toInt 8 = some 12304 := by decide
example : Memory.access? (12288#64) (23#64) (12288#64) (16#32).toInt 8 = none := by decide

end Controls

#print axioms Controls.unpatchable_rejected
#print axioms succeeds
#print axioms classifies
#print axioms source_classifies
#print axioms head_prefix
#print axioms offset_prefix
#print axioms add_step
#print axioms branch_step
#print axioms compare_step
#print axioms length_step
#print axioms subtract_count_step
#print axioms move_step
#print axioms subtract_step

end Mettapedia.Machines.TIsa.X86Bounds
