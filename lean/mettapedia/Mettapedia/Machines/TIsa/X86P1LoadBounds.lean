import Mettapedia.Machines.TIsa.X86SubImmediate
import Mettapedia.Machines.TIsa.X86DwordLoad

/-!
# Complete fetched p1 LOAD span and bounds exits

This 43-byte span is the first region-0, displacement-0, U32 load in the
R_DERIVE_IS_PROP p1 image. Original Sail execution composes the scratch copy,
frame-base subtraction, length read, immediate subtraction, JB, CMP, JA and
zero-extending data read. Bounds classification covers both invalid exits
without requiring any bytes at the rejected data address.

Successful execution takes eight fetched instructions. A short region reaches
the invalid handler in five; an out-of-range offset reaches it in seven.
These contracts preserve all memory and registers outside the declared frame.
Handler execution, the enclosing consumer and the generic emitter theorem
remain separate. The containing-image capture is joined in X86P1LoadCapture.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1LoadBounds

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def code : List Nat := [
  0x49,0x89,0xf6,
  0x4c,0x2b,0xb7,0,0,0,0,
  0x4c,0x8b,0xbf,8,0,0,0,
  0x49,0x83,0xef,4,
  0x0f,0x82,0x3b,2,0,0,
  0x4d,0x39,0xfe,
  0x0f,0x87,0x32,2,0,0,
  0x44,0x8b,0x96,0,0,0,0]

abbrev writes : Finset Register := {.rip,.rflags,.r14,.r15}

theorem writes_data : writes ⊆ dataRegisters := by decide

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameIncrement.linkedHandlers (X86Funding.Placed.baseHandlers other)
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (baseHandlers other) extra

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 637 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 637) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by
  simp [position, address]

theorem position_shift (start : BitVec 48) (upper : start.toInt + 637 < (2 ^ 47 : Int))
    (offset index : Nat) (within : offset ≤ 637) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact start upper offset within]
  simp only [position, address, Nat.cast_add, Int.add_assoc]

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 637 < (2 ^ 47 : Int)
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
  pointerKnown : lookup state 6 = some pointer
  baseEffective : frame = baseAddress.signExtend 64
  lengthEffective : frame + (8#32).signExtend 64 = lengthAddress.signExtend 64
  baseUpper : baseAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  lengthUpper : lengthAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  baseAligned : baseAddress &&& (7#48) = (0#48)
  lengthAligned : lengthAddress &&& (7#48) = (0#48)
  controlKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  baseBytes : ∀ index < 8,
    state.mem.get? ((address baseAddress.toInt index).signExtend 52).toNat =
      some (base.extractLsb' (8 * index) 8)
  lengthBytes : ∀ index < 8,
    state.mem.get? ((address lengthAddress.toInt index).signExtend 52).toNat =
      some (length.extractLsb' (8 * index) 8)

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends Facts state origin where
  loaded : codeLoaded state origin.address.toInt code

structure Readable (state : State) (pointer : Word) (value : BitVec 32) where
  dataAddress : BitVec 48
  effective : pointer = dataAddress.signExtend 64
  upper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int)
  aligned : dataAddress &&& (3#48) = (0#48)
  bytes : ∀ index < 4,
    state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)

theorem loaded_word32 (state : State) (start : BitVec 48)
    (upper : start.toInt + 637 < (2 ^ 47 : Int))
    (loaded : codeLoaded state start.toInt code)
    (offset : Nat) (within : offset ≤ 637) (value : BitVec 32)
    (encoded : ∀ index : Fin 4, code[offset + index.val]? =
      some (value.extractLsb' (8 * index.val) 8).toNat) :
    ∀ index < 4,
      state.mem.get? ((address (position start offset).toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8) := by
  intro index bounded
  rw [position_shift start upper offset index within]
  simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    loaded _ _ (encoded ⟨index, bounded⟩)

theorem move_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step state after ∧ RegisterFrame {.r14,.rip} state after ∧
      lookup after 14 = some input.pointer ∧
      after.regs.get? .rip = some ((position origin.address 3).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have rip : state.regs.get? .rip = some ((position origin.address 0).signExtend 64) := by
    simpa only [position_zero] using origin.rip
  let site := windowAt state state origin (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) rip code input.loaded 6 14 (0x89#8) (by rfl) (by rfl) (by rfl)
  have result := X86InstructionFetch.fetch_register64 state site.address site.opcodeAddress
    site.modrmAddress site.next site.control site.attributes 6 14 site.step1 site.step2 site.step3
    site.status site.fault site.msrs site.segments site.longMode site.codeMode site.application site.rip
    site.prefixByte site.opcodeByte site.modrmByte input.pointer input.pointerKnown input.quiet
  let after := X86Move.putPointer (put state 14 input.pointer) (position origin.address 3)
  refine ⟨after, result, ?_, ?_, ?_⟩
  · simpa [after, key] using (put_frame state 14 input.pointer).trans (pointer_frame _ (position origin.address 3))
  · rw [X86Move.lookup_putPointer, lookup_put_same]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem subtract_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftKnown : lookup current 14 = some input.pointer)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 3).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r14,.rflags,.rip} current after ∧
      lookup after 14 = some (input.pointer - input.base) ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 10).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 3 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 6).toInt + 4 = (position origin.address 10).toInt := by
    rw [position_exact _ input.upper 6 (by decide), position_exact _ input.upper 10 (by decide)]
    omega
  obtain ⟨output, result⟩ := X86Funding.GenericMemory.fetched_subtract (handlers other extra) vector current site
    (position origin.address 10) input.baseAddress input.visible input.controls input.frame input.pointer input.base flags
    (0#32) advance input.baseUpper ((framed.lookup 7 (by decide)).trans input.frameKnown) leftKnown
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (by simpa using input.baseEffective) input.baseAligned
    (loaded 3 0x4c (by rfl)) (loaded 4 0x2b (by rfl)) (loaded 5 0xb7 (by rfl))
    (loaded_word32 current origin.address input.upper loaded 6 (by decide) (0#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.baseBytes index within)
  let updated := put current 14 (input.pointer - input.base)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags updated nextFlags) (position origin.address 10)
  have tailFrame := (flags_frame updated nextFlags).trans (pointer_frame _ (position origin.address 10))
  refine ⟨after, nextFlags, result, ?_, ?_, ?_, ?_⟩
  · exact ((put_frame current 14 (input.pointer - input.base)).trans tailFrame).mono (by decide)
  · exact (tailFrame.lookup 14 (by decide)).trans (lookup_put_same current 14 (input.pointer - input.base))
  · rw [(pointer_frame (X86Flags.putFlags updated nextFlags) (position origin.address 10)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem length_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 10).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.r15,.rip} current after ∧
      lookup after 15 = some input.length ∧
      after.regs.get? .rip = some ((position origin.address 17).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 10 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 13).toInt + 4 = (position origin.address 17).toInt := by
    rw [position_exact _ input.upper 13 (by decide), position_exact _ input.upper 17 (by decide)]
    omega
  have result := X86FrameLoad.fetched_frame (handlers other extra) vector current 15 site
    (position origin.address 17) input.lengthAddress input.visible input.controls input.frame input.length flags
    (8#32) advance input.lengthUpper ((framed.lookup 7 (by decide)).trans input.frameKnown)
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    input.lengthEffective input.lengthAligned
    (loaded 10 0x4c (by rfl)) (loaded 11 0x8b (by rfl)) (loaded 12 0xbf (by rfl))
    (loaded_word32 current origin.address input.upper loaded 13 (by decide) (8#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.lengthBytes index within)
  let after := X86Move.putPointer (put current 15 input.length) (position origin.address 17)
  refine ⟨after, result, ?_, ?_, ?_⟩
  · simpa [after, key] using (put_frame current 15 input.length).trans (pointer_frame _ (position origin.address 17))
  · rw [X86Move.lookup_putPointer, lookup_put_same]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem subtract4_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (lengthKnown : lookup current 15 = some input.length)
    (rip : current.regs.get? .rip = some ((position origin.address 17).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.r15,.rflags,.rip} current after ∧
      lookup after 15 = some (input.length - (4#64)) ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags = Functions.bool_to_bits (input.length.toNat < 4) ∧
      after.regs.get? .rip = some ((position origin.address 21).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 17 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 20).toInt + 1 = (position origin.address 21).toInt := by
    rw [position_exact _ input.upper 20 (by decide), position_exact _ input.upper 21 (by decide)]
    omega
  obtain ⟨output, result, carry⟩ := X86SubImmediate.fetched_sub4 (handlers other extra) vector current site
    (position origin.address 21) input.length flags advance lengthKnown flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 17 0x49 (by rfl)) (loaded 18 0x83 (by rfl)) (loaded 19 0xef (by rfl)) (loaded 20 4 (by rfl))
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put current 15 (input.length - (4#64))) nextFlags)
    (position origin.address 21)
  refine ⟨after, nextFlags, result, X86SubImmediate.result_frame current input.length flags output _, ?_, ?_, carry, ?_⟩
  · rw [X86Move.lookup_putPointer, X86Flags.putFlags_gpr, lookup_put_same]
  · rw [(pointer_frame (X86Flags.putFlags (put current 15 (input.length - (4#64))) nextFlags)
      (position origin.address 21)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem arithmetic_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (input.pointer - input.base) ∧
      lookup after 15 = some (input.length - (4#64)) ∧ after.regs.get? .rflags = some flags ∧
      Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (input.length.toNat < 4) ∧
      after.regs.get? .rip = some ((position origin.address 21).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨s1, step1, frame1, pointer1, rip1⟩ := move_step other extra vector state origin input
  have flags1 := (frame1.registers .rflags (by decide)).trans input.flagsKnown
  obtain ⟨s2, f2, step2, frame2, offset2, flags2, rip2⟩ :=
    subtract_step other extra vector state s1 origin input (frame1.mono (by decide)) input.flags pointer1 flags1 rip1
  have frame02 : RegisterFrame writes state s2 := (frame1.trans frame2).mono (by decide)
  obtain ⟨s3, step3, frame3, length3, rip3⟩ := length_step other extra vector state s2 origin input frame02 f2 flags2 rip2
  have frame03 : RegisterFrame writes state s3 := (frame02.trans frame3).mono (by decide)
  have flags3 := (frame3.registers .rflags (by decide)).trans flags2
  obtain ⟨s4, f4, step4, frame4, length4, flags4, carry4, rip4⟩ :=
    subtract4_step other extra vector state s3 origin input frame03 f2 flags3 length3 rip3
  refine ⟨s4, f4, ?_, (frame03.trans frame4).mono (by decide), ?_, length4, flags4, carry4, rip4⟩
  · exact X86FuelPrefix.fetches_cons 3 state s1 s4 step1
      (X86FuelPrefix.fetches_cons 2 s1 s2 s4 step2
        (X86FuelPrefix.fetches_cons 1 s2 s3 s4 step3 (X86FuelPrefix.fetches_one s3 s4 step4)))
  · exact (frame4.lookup 14 (by decide)).trans ((frame3.lookup 14 (by decide)).trans offset2)

theorem branch_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current)
    (condition : X86BranchCondition.Condition) (offset : Nat) (delta : BitVec 32) (flags : BitVec 32)
    (within : offset + 6 ≤ 637) (jumpOffset : (offset : Int) + 6 + delta.toInt = 598)
    (escape : code[offset]? = some 0x0f)
    (opcode : code[offset + 1]? = some (X86BranchCondition.opcode condition).toNat)
    (displacement : ∀ index : Fin 4, code[offset + 2 + index.val]? =
      some (delta.extractLsb' (8 * index.val) 8).toNat)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address offset).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.rip} current after ∧
      after.regs.get? .rip = some ((if X86BranchCondition.value condition flags then position origin.address 598
        else position origin.address (offset + 6)).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have step1 : (position origin.address offset).toInt + 1 = (position origin.address (offset + 1)).toInt := by
    rw [position_exact _ input.upper offset (by omega), position_exact _ input.upper (offset + 1) (by omega)]
    omega
  have step2 : (position origin.address (offset + 1)).toInt + 1 =
      (position origin.address (offset + 2)).toInt := by
    rw [position_exact _ input.upper (offset + 1) (by omega), position_exact _ input.upper (offset + 2) (by omega)]
    omega
  have advance : (position origin.address (offset + 2)).toInt + 4 =
      (position origin.address (offset + 6)).toInt := by
    rw [position_exact _ input.upper (offset + 2) (by omega), position_exact _ input.upper (offset + 6) within]
    omega
  have jump : (position origin.address 598).toInt =
      (position origin.address (offset + 6)).toInt + delta.toInt := by
    rw [position_exact _ input.upper 598 (by decide), position_exact _ input.upper (offset + 6) within]
    omega
  have result := X86EscapeFetch.fetched_branch (baseHandlers other) extra vector condition current
    (position origin.address offset) (position origin.address (offset + 1)) (position origin.address (offset + 2))
    (position origin.address (offset + 6)) (position origin.address 598)
    origin.control origin.attributes flags delta step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans origin.status)
    ((framed.registers .fault_reg (by decide)).trans origin.fault)
    ((framed.registers .msrs (by decide)).trans origin.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans origin.segments)
    origin.longMode origin.codeMode ((framed.registers .app_view (by decide)).trans origin.application)
    rip flagsKnown ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded _ _ escape) (by simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ opcode)
    (loaded_word32 current origin.address input.upper loaded (offset + 2) (by omega) delta displacement)
  refine ⟨_, result, pointer_frame _ _, ?_⟩
  simp only [X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem borrow_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (input.pointer - input.base) ∧
      lookup after 15 = some (input.length - (4#64)) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.length.toNat < 4 then position origin.address 598
        else position origin.address 27).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, offsetRead, lengthRead, flagsRead, carry, middleRip⟩ :=
    arithmetic_prefix other extra vector state origin input
  obtain ⟨after, last, lastFrame, finalRip⟩ := branch_step other extra vector state middle origin input framed
    .below 21 (571#32) flags (by decide) (by decide) (by rfl) (by rfl)
    (by intro index; fin_cases index <;> rfl) flagsRead middleRip
  have sense : X86BranchCondition.value .below flags = decide (input.length.toNat < 4) := by
    simp only [X86BranchCondition.value, carry]
    by_cases below : input.length.toNat < 4 <;> simp [Functions.bool_to_bits, below]
  rw [sense] at finalRip
  refine ⟨after, flags, X86FuelPrefix.fetches_then 4 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last), (framed.trans lastFrame).mono (by decide),
    (lastFrame.lookup 14 (by decide)).trans offsetRead, (lastFrame.lookup 15 (by decide)).trans lengthRead,
    (lastFrame.registers .rflags (by decide)).trans flagsRead, ?_⟩
  simpa only [Bool.ite_eq_true_distrib, decide_eq_true_eq] using finalRip

theorem above_sense (left right : Word) (flags : BitVec 32)
    (carry : Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (left.toNat < right.toNat))
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec (left - right).toNat) :
    X86BranchCondition.value .above flags = decide (right.toNat < left.toNat) := by
  have zeroEq : (left - right).toNat = 0 ↔ left = right := by
    constructor
    · intro zero
      apply BitVec.eq_of_toNat_eq
      have := left.isLt
      have := right.isLt
      have := BitVec.toNat_sub left right
      omega
    · intro same
      subst right
      simp only [BitVec.sub_self]
      rfl
  simp only [X86BranchCondition.value, carry, zero]
  by_cases below : left.toNat < right.toNat
  · have notAbove : ¬ right.toNat < left.toNat := by omega
    simp [Functions.bool_to_bits, below, notAbove]
  · by_cases same : left = right
    · subst right
      simp [Functions.bool_to_bits, Functions.zf_spec]
    · have notZero : (left - right).toNat ≠ 0 := fun zero => same (zeroEq.mp zero)
      have notSame : left.toNat ≠ right.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      have above : right.toNat < left.toNat := by omega
      have zflag : Functions.zf_spec (left - right).toNat = (0#1) := by
        simp only [Functions.zf_spec, show ((left - right).toNat == 0) = false from beq_eq_false_iff_ne.mpr notZero,
          Bool.false_eq_true, ite_false]
      rw [zflag]
      simp [Functions.bool_to_bits, below, above]

theorem compare_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (leftRead : lookup current 14 = some (input.pointer - input.base))
    (rightRead : lookup current 15 = some (input.length - (4#64)))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 27).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, Step current after ∧ RegisterFrame {.rflags,.rip} current after ∧
      after.regs.get? .rflags = some nextFlags ∧
      X86BranchCondition.value .above nextFlags =
        decide ((input.length - (4#64)).toNat < (input.pointer - input.base).toNat) ∧
      after.regs.get? .rip = some ((position origin.address 30).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  let site := windowAt state current origin (framed.mono writes_data) input.upper 27 (by decide) rip
    code loaded 15 14 (0x39#8) (by rfl) (by rfl) (by rfl)
  obtain ⟨output, result, carry, zero⟩ := X86Comparison.fetched_compare64 (handlers other extra) vector current
    15 14 site (input.pointer - input.base) (input.length - (4#64)) flags rightRead leftRead flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags current nextFlags) site.next
  refine ⟨after, nextFlags, result, X86Comparison.status_frame current nextFlags site.next, ?_, ?_, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags current nextFlags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · exact above_sense _ _ _ ((X86Comparison.merged_carry flags output).trans carry)
      ((X86Comparison.merged_zero flags output).trans zero)
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl

theorem range_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (enough : 4 ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 7).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (input.pointer - input.base) ∧
      lookup after 15 = some (input.length - (4#64)) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if (input.length - (4#64)).toNat < (input.pointer - input.base).toNat then position origin.address 598
          else position origin.address 36).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨s5, f5, first, frame5, offset5, length5, flags5, rip5⟩ := borrow_prefix other extra vector state origin input
  have notShort : ¬ input.length.toNat < 4 := by omega
  have fallthrough : s5.regs.get? .rip = some ((position origin.address 27).signExtend 64) := by
    simpa only [if_neg notShort] using rip5
  obtain ⟨s6, f6, step6, frame6, flags6, sense6, rip6⟩ :=
    compare_step other extra vector state s5 origin input frame5 f5 offset5 length5 flags5 fallthrough
  have frame06 : RegisterFrame writes state s6 := (frame5.trans frame6).mono (by decide)
  obtain ⟨s7, step7, frame7, rip7⟩ := branch_step other extra vector state s6 origin input frame06
    .above 30 (562#32) f6 (by decide) (by decide) (by rfl) (by rfl)
    (by intro index; fin_cases index <;> rfl) flags6 rip6
  rw [sense6] at rip7
  refine ⟨s7, f6, X86FuelPrefix.fetches_then 5 2 state s5 s7 first
    (X86FuelPrefix.fetches_cons 1 s5 s6 s7 step6 (X86FuelPrefix.fetches_one s6 s7 step7)),
    (frame06.trans frame7).mono (by decide), ?_, ?_, ?_, ?_⟩
  · exact (frame7.lookup 14 (by decide)).trans ((frame6.lookup 14 (by decide)).trans offset5)
  · exact (frame7.lookup 15 (by decide)).trans ((frame6.lookup 15 (by decide)).trans length5)
  · exact (frame7.registers .rflags (by decide)).trans flags6
  · simpa only [Bool.ite_eq_true_distrib, decide_eq_true_eq] using rip7

theorem length_remaining (length : Word) (enough : 4 ≤ length.toNat) :
    (length - (4#64)).toNat = length.toNat - 4 := by
  change (length - (4#64)).toNat = length.toNat - (4#64).toNat
  exact BitVec.toNat_sub_of_le (by change 4 ≤ length.toNat; exact enough)

theorem short_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (short : input.length.toNat < 4) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some ((position origin.address 598).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, _, _, _, rip⟩ := borrow_prefix other extra vector state origin input
  refine ⟨after, executed, framed, framed.lookup 10 (by decide), ?_⟩
  simpa only [if_pos short] using rip

theorem range_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (enough : 4 ≤ input.length.toNat)
    (outside : input.length.toNat < (input.pointer - input.base).toNat + 4) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some ((position origin.address 598).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, _, _, _, rip⟩ := range_prefix other extra vector state origin input enough
  have above : (input.length - (4#64)).toNat < (input.pointer - input.base).toNat := by
    rw [length_remaining input.length enough]
    omega
  refine ⟨after, executed, framed, framed.lookup 10 (by decide), ?_⟩
  simpa only [if_pos above] using rip

theorem bounds_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if input.length.toNat < 4 then 5 else 7)).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 10 = lookup state 10 ∧
      after.regs.get? .rip = some
        ((if (input.pointer - input.base).toNat + 4 ≤ input.length.toNat then position origin.address 36
          else position origin.address 598).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases short : input.length.toNat < 4
  · obtain ⟨after, executed, framed, unchanged, rip⟩ := short_rejects other extra vector state origin input short
    have notFits : ¬ (input.pointer - input.base).toNat + 4 ≤ input.length.toNat := by omega
    exact ⟨after, by simpa only [if_pos short] using executed, framed, unchanged,
      by simpa only [if_neg notFits] using rip⟩
  · have enough : 4 ≤ input.length.toNat := by omega
    obtain ⟨after, _, executed, framed, _, _, _, rip⟩ := range_prefix other extra vector state origin input enough
    refine ⟨after, by simpa only [if_neg short] using executed, framed, framed.lookup 10 (by decide), ?_⟩
    by_cases fits : (input.pointer - input.base).toNat + 4 ≤ input.length.toNat
    · have notAbove : ¬ (input.length - (4#64)).toNat < (input.pointer - input.base).toNat := by
        rw [length_remaining input.length enough]
        omega
      simpa only [if_pos fits, if_neg notAbove] using rip
    · have above : (input.length - (4#64)).toNat < (input.pointer - input.base).toNat := by
        rw [length_remaining input.length enough]
        omega
      simpa only [if_neg fits, if_pos above] using rip

theorem data_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current)
    (value : BitVec 32) (readable : Readable state input.pointer value) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 36).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.r10,.rip} current after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some ((position origin.address 43).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 36 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 39).toInt + 4 = (position origin.address 43).toInt := by
    rw [position_exact _ input.upper 39 (by decide), position_exact _ input.upper 43 (by decide)]
    omega
  have result := X86DwordLoad.fetched_dword (handlers other extra) vector current 10 6 (by decide) (by decide)
    site (position origin.address 43) readable.dataAddress input.visible input.controls input.pointer value flags
    (0#32) advance readable.upper ((framed.lookup 6 (by decide)).trans input.pointerKnown)
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (by simpa using readable.effective) readable.aligned
    (loaded 36 0x44 (by rfl)) (loaded 37 0x8b (by rfl)) (loaded 38 0x96 (by rfl))
    (loaded_word32 current origin.address input.upper loaded 39 (by decide) (0#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact readable.bytes index within)
  let after := X86Move.putPointer (put current 10 (value.zeroExtend 64)) (position origin.address 43)
  refine ⟨after, result, ?_, ?_, ?_⟩
  · simpa [after, key] using (put_frame current 10 (value.zeroExtend 64)).trans
      (pointer_frame _ (position origin.address 43))
  · rw [X86Move.lookup_putPointer, lookup_put_same]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem load_observes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : X86P1LoadBounds.Inputs state origin) (value : BitVec 32)
    (readable : X86P1LoadBounds.Readable state input.pointer value)
    (fits : (input.pointer - input.base).toNat + 4 ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := X86P1LoadBounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      RegisterFrame (insert .r10 X86P1LoadBounds.writes) state after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((X86P1LoadBounds.position origin.address 43).signExtend 64) := by
  let : OtherOpcodeHandlers := X86P1LoadBounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  have enough : 4 ≤ input.length.toNat := by omega
  obtain ⟨middle, flags, first, framed, _, _, flagsRead, middleRip⟩ :=
    X86P1LoadBounds.range_prefix other extra vector state origin input enough
  have notAbove : ¬ (input.length - (4#64)).toNat < (input.pointer - input.base).toNat := by
    rw [X86P1LoadBounds.length_remaining input.length enough]
    omega
  have fallthrough : middle.regs.get? .rip =
      some ((X86P1LoadBounds.position origin.address 36).signExtend 64) := by
    simpa only [if_neg notAbove] using middleRip
  obtain ⟨after, last, lastFrame, valueRead, finalRip⟩ :=
    X86P1LoadBounds.data_step other extra vector state middle origin input framed value readable flags flagsRead fallthrough
  exact ⟨after, flags, X86FuelPrefix.fetches_then 7 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last), (framed.trans lastFrame).mono (by decide), valueRead,
    (lastFrame.registers .rflags (by decide)).trans flagsRead, finalRip⟩

theorem load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (value : BitVec 32) (readable : Readable state input.pointer value)
    (fits : (input.pointer - input.base).toNat + 4 ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      RegisterFrame (insert .r10 writes) state after ∧ lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some ((position origin.address 43).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, valueRead, _, rip⟩ :=
    load_observes other extra vector state origin input value readable fits
  exact ⟨after, executed, framed, valueRead, rip⟩

namespace Controls

private theorem positive_address (base offset : Nat) (within : base + offset < 2 ^ 47) :
    ((address (base : Int) offset).signExtend 52).toNat = base + offset := by
  let bits := (address (base : Int) offset).signExtend 52
  have signed : bits.toInt = ((base + offset : Nat) : Int) := by
    dsimp only [bits]
    rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 52),
      address_toInt (extent := offset) (base : Int) (by omega) (by exact_mod_cast within) offset (by omega)]
    simp
  have nonnegative : 0 ≤ bits.toInt := by rw [signed]; omega
  have unsigned := BitVec.toInt_eq_toNat_of_lt (BitVec.toInt_pos_iff.mp nonnegative)
  rw [signed] at unsigned
  exact_mod_cast unsigned.symm

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def cells (length : Word) : List (Nat × BitVec 8) :=
  (List.range 43).map (fun index => (4096 + index, BitVec.ofNat 8 ((code[index]?).getD 0))) ++
  (List.range 8).map (fun index => (8192 + index, (12288#64).extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (8200 + index, length.extractLsb' (8 * index) 8)) ++
  (List.range 4).map (fun index => (12288 + index, (0x89abcdef#32).extractLsb' (8 * index) 8))

private theorem distinct (length : Word) :
    (cells length).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells length).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (length pointer : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi pointer
  let registers := registers.insert .r10 (0xffffffffffffffff#64)
  let registers := registers.insert .r11 (0x0123456789abcdef#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells length), (), 0, #[]⟩

private theorem cell (length pointer : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells length) :
    (before length pointer).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct length) present

private theorem image (length pointer : Word) : codeLoaded (before length pointer) 4096 code := by
  intro index byte present
  have within : index < 43 := by
    have within := (List.getElem?_eq_some_iff.mp present).choose
    change index < 43 at within
    exact within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells length := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  have place := positive_address 4096 index (by omega)
  change ((address 4096 index).signExtend 52).toNat = 4096 + index at place
  rw [place]
  exact cell length pointer _ _ member

private def origin (length pointer : Word) : X86LegacyFetch.Basis (before length pointer) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]

private def input (length pointer : Word) : Inputs (before length pointer) (origin length pointer) where
  upper := by change (4096#48).toInt + 637 < (2 ^ 47 : Int); decide
  frame := 8192#64
  base := 12288#64
  pointer := pointer
  length := length
  baseAddress := 8192#48
  lengthAddress := 8200#48
  controls := controls
  visible := visible
  flags := 0x200#32
  frameKnown := by
    change ((before length pointer).regs.get? .rdi).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  pointerKnown := by
    change ((before length pointer).regs.get? .rsi).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  baseEffective := by decide
  lengthEffective := by decide
  baseUpper := by decide
  lengthUpper := by decide
  baseAligned := by decide
  lengthAligned := by decide
  controlKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  baseBytes := by
    intro index within
    change (before length pointer).mem.get? ((address 8192 index).signExtend 52).toNat = _
    have place := positive_address 8192 index (by omega)
    change ((address 8192 index).signExtend 52).toNat = 8192 + index at place
    rw [place]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩
  lengthBytes := by
    intro index within
    change (before length pointer).mem.get? ((address 8200 index).signExtend 52).toNat = _
    have place := positive_address 8200 index (by omega)
    change ((address 8200 index).signExtend 52).toNat = 8200 + index at place
    rw [place]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩
  loaded := image length pointer

private def readable (length : Word) : Readable (before length (12288#64)) (12288#64) (0x89abcdef#32) where
  dataAddress := 12288#48
  effective := by decide
  upper := by decide
  aligned := by decide
  bytes := by
    intro index within
    change (before length (12288#64)).mem.get? ((address 12288 index).signExtend 52).toNat = _
    have place := positive_address 12288 index (by omega)
    change ((address 12288 index).signExtend 52).toNat = 12288 + index at place
    rw [place]
    apply cell
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

private theorem input_values (length pointer : Word) :
    (input length pointer).pointer = pointer ∧ (input length pointer).base = (12288#64) ∧
      (input length pointer).length = length := ⟨rfl,rfl,rfl⟩

private theorem origin_address (length pointer : Word) : (origin length pointer).address = (4096#48) := rfl

theorem accepts (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (length : Word) (enough : 4 ≤ length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run (before length (12288#64)) = .ok () after ∧
      lookup after 10 = some (0x0000000089abcdef#64) ∧
      lookup after 11 = some (0x0123456789abcdef#64) ∧
      after.regs.get? .rip = some (4139#64) ∧ after.mem = (before length (12288#64)).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have fits : ((input length (12288#64)).pointer - (input length (12288#64)).base).toNat + 4 ≤
      (input length (12288#64)).length.toNat := by
    rw [(input_values length (12288#64)).1, (input_values length (12288#64)).2.1,
      (input_values length (12288#64)).2.2]
    exact enough
  obtain ⟨after, executed, framed, valueRead, rip⟩ := load_executes other extra vector _ _ (input length (12288#64))
    (0x89abcdef#32) (readable length) fits
  have next : ((position (origin length (12288#64)).address 43).signExtend 64) = (4139#64) := by
    rw [origin_address]
    rfl
  rw [next] at rip
  refine ⟨after, executed, valueRead, ?_, rip, framed.memory⟩
  rw [framed.lookup 11 (by decide)]
  change ((before length (12288#64)).regs.get? .r11).map (fun word : Word => word) = _
  simp [before, Std.ExtDHashMap.get?_insert]

theorem boundary_accepts (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run (before 4 (12288#64)) = .ok () after ∧
      lookup after 10 = some (0x0000000089abcdef#64) ∧
      lookup after 11 = some (0x0123456789abcdef#64) ∧
      after.regs.get? .rip = some (4139#64) ∧ after.mem = (before 4 (12288#64)).mem :=
  accepts other extra vector 4 (by decide)

theorem interior_accepts (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run (before 32 (12288#64)) = .ok () after ∧
      lookup after 10 = some (0x0000000089abcdef#64) ∧
      lookup after 11 = some (0x0123456789abcdef#64) ∧
      after.regs.get? .rip = some (4139#64) ∧ after.mem = (before 32 (12288#64)).mem :=
  accepts other extra vector 32 (by decide)

theorem short_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (length : Word) (short : length.toNat < 4) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run (before length (12288#64)) = .ok () after ∧
      lookup after 10 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (4694#64) ∧ after.mem = (before length (12288#64)).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, unchanged, rip⟩ := short_rejects other extra vector _ _
    (input length (12288#64)) short
  have next : ((position (origin length (12288#64)).address 598).signExtend 64) = (4694#64) := by
    rw [origin_address]
    rfl
  rw [next] at rip
  refine ⟨after, executed, ?_, rip, framed.memory⟩
  rw [unchanged]
  change ((before length (12288#64)).regs.get? .r10).map (fun word : Word => word) = _
  simp [before, Std.ExtDHashMap.get?_insert]

theorem empty_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run (before 0 (12288#64)) = .ok () after ∧
      lookup after 10 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (4694#64) ∧ after.mem = (before 0 (12288#64)).mem :=
  short_control other extra vector 0 (by decide)

theorem short_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run (before 3 (12288#64)) = .ok () after ∧
      lookup after 10 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (4694#64) ∧ after.mem = (before 3 (12288#64)).mem :=
  short_control other extra vector 3 (by decide)

theorem end_pointer_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run (before 32 (12320#64)) = .ok () after ∧
      lookup after 10 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (4694#64) ∧ after.mem = (before 32 (12320#64)).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, unchanged, rip⟩ := range_rejects other extra vector _ _
    (input 32 (12320#64)) (by decide) (by decide)
  refine ⟨after, executed, ?_, rip, framed.memory⟩
  rw [unchanged]
  change ((before 32 (12320#64)).regs.get? .r10).map (fun word : Word => word) = _
  simp [before, Std.ExtDHashMap.get?_insert]

theorem end_pointer_unmapped : (before 32 (12320#64)).mem.get? 12320 = none := by
  exact Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (l := cells 32) (k := 12320) (by decide)

end Controls

end Mettapedia.Machines.TIsa.X86P1LoadBounds
