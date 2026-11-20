import Mettapedia.Machines.TIsa.X86AddImmediate

/-!
# Fetched ADD for every nonnegative signed-32-bit immediate

Original immediate decoding preserves every constant below 2^31. The complete
seven-byte register ADD fetch covers every destination register, modular
results, defined flags, carry, RIP and the exact register/memory frame.
No immediate enumeration or assumed compiler execution is used.

The high-bit boundary is included as a negative control: 2^31 sign-extends
to -2^31 and lies outside this positive-immediate contract. Negative offsets
use the separate register-subtraction lowering.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PositiveImmediate
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Immediate := Fin (2 ^ 31)
def immediate32 (value : Immediate) : BitVec 32 := BitVec.ofNat 32 value.val
def immediate64 (value : Immediate) : Word := BitVec.ofNat 64 value.val

theorem sign_slice (value : Immediate) : Sail.get_slice_int 1 (value.val : Int) 31 = (0#1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.get_slice_int,BitVec.ofInt_natCast,BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  have within : value.val < 2 ^ (31 + 1 + 1) := by have := value.isLt; omega
  rw [Nat.mod_eq_of_lt within,Nat.div_eq_of_lt value.isLt]

theorem logbit31 (state : State) (value : Immediate) :
    (Functions.logbitp_int 31 (value.val : Int)).run state = .ok false state := by
  unfold Functions.logbitp_int
  simp only [show ((31 : Int) ≥b 0) = true from rfl,run_bind,run_assert,ite_true]
  rw [show Int.toNat (31 : Int) = 31 from rfl,sign_slice value]
  rfl

theorem loghead31 (value : Immediate) : Functions.loghead_int 31 (value.val : Int) = (value.val : Int) := by
  unfold Functions.loghead_int
  simp only [show ((31 : Int) == 0) = false from rfl,Bool.false_eq_true,ite_false]
  change Sail.BitVec.toNatInt (Functions.bits_of_int (value.val : Int) 31) = _
  rw [X86Alu.bits_of_int_eq,BitVec.ofInt_natCast]
  simp only [Sail.BitVec.toNatInt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt value.isLt]
  rfl

theorem loghead64 (value : Immediate) : Functions.loghead_int 64 (value.val : Int) = (value.val : Int) := by
  unfold Functions.loghead_int
  simp only [show ((64 : Int) == 0) = false from rfl,Bool.false_eq_true,ite_false]
  change Sail.BitVec.toNatInt (Functions.bits_of_int (value.val : Int) 64) = _
  rw [X86Alu.bits_of_int_eq,BitVec.ofInt_natCast]
  simp only [Sail.BitVec.toNatInt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := value.isLt; omega : value.val < 2 ^ 64)]
  rfl

theorem logext32 (state : State) (value : Immediate) :
    (Functions.binary_logext 32 (value.val : Int)).run state = .ok (value.val : Int) state := by
  unfold Functions.binary_logext
  simp only [show ((0 : Int) <b 32) = true from rfl,run_bind,run_assert,ite_true]
  rw [show (32 : Int) - 1 = 31 from rfl,logbit31 state value]
  simp only [Bool.false_eq_true,ite_false,pure_bind,run_pure]
  unfold Functions.binary_logapp
  rw [loghead31]
  simp

theorem word_nat (value : Immediate) : (immediate64 value).toNat = value.val := by
  simp only [immediate64,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := value.isLt; omega)

theorem normalized (value : Immediate) :
    Functions.bits_of_int (Functions.loghead_int 64 (value.val : Int)) 64 = immediate64 value := by
  rw [loghead64,X86Alu.bits_of_int_eq,BitVec.ofInt_natCast]
  rfl

theorem immediate_value (value : Immediate) :
    Sail.BitVec.toNatInt (Sail.BitVec.truncate ((immediate32 value).zeroExtend 128) 32) = (value.val : Int) := by
  have cut : Sail.BitVec.truncate ((immediate32 value).zeroExtend 128) 32 = immediate32 value := by
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    simp [Sail.BitVec.truncate,within]
  rw [cut]
  simp only [immediate32,Sail.BitVec.toNatInt,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := value.isLt; omega : value.val < 2 ^ 32)]
  rfl

example (state : State) : (Functions.binary_logext 32 2147483648).run state = .ok (-2147483648 : Int) state := by rfl

#print axioms logext32

theorem word_bits (value : Immediate) : Functions.bits_of_int (value.val : Int) 64 = immediate64 value := by
  rw [X86Alu.bits_of_int_eq,BitVec.ofInt_natCast]
  rfl

theorem handler (state : State) (constant : Immediate) (destination : Fin 16) (start immediate next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : immediate.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediate.toInt index).signExtend 52).toNat =
        some ((immediate32 constant).extractLsb' (8 * index) 8)) :
    ∃ output, (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start immediate
      prefixes (rex true 0 destination) (0x81#8) (modRM 0 destination) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (value + immediate64 constant)) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (2 ^ 64 ≤ value.toNat + constant.val) := by
  obtain ⟨output,calculated⟩ := X86Alu.add_executes_defined state value (immediate64 constant) flags
  have carry := X86AddImmediate.add_carry state value (immediate64 constant) flags
  simp only [map_eq_pure_bind,run_bind,calculated,run_pure] at carry
  have cf := (EStateM.Result.ok.inj carry).1
  refine ⟨output,?_,by simpa only [word_nat] using
    (X86Comparison.merged_carry flags output).trans cf⟩
  have size := X86Move.operand_size64 (0 : Fin 16) destination prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x81#8) == (0x80#8)) = false from rfl,
    show ((0x81#8) == (0x82#8)) = false from rfl,
    show ((0x81#8) == (0xf6#8)) = false from rfl,
    show ((0x81#8) == (0x83#8)) = false from rfl,Bool.false_or]
  rw [size,run_bind,run_pure]
  dsimp only
  have immediateSize : Functions.select_operand_size .Mode_64bit false (rex true 0 destination) true prefixes
      false false false = (pure 4 : SailM Int) := by
    simp [Functions.select_operand_size,Functions.in_64bit_mode,operandOverride]
  rw [immediateSize]
  simp only [pure_bind,show Functions.check_range 1 4 4 = (pure 4 : SailM Int) from rfl]
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,show Functions.bits_of_int 4 3 = (4#3) from rfl,
    run_bind,X86AddImmediate.operand state destination value prefixes immediate (4#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl,run_bind,X86Move.add_pointer_zero]
  dsimp only
  have addressWidth : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressSize]
  rw [addressWidth]
  simp only [pure_bind,bind_assoc,show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,Sail.BitVec.signExtend]
  have upper : immediate.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := next)
    omega
  rw [run_bind,X86FrameStore.read_dword state immediate pointer attributes (immediate32 constant)
    upper segments application rip bytes]
  dsimp only
  rw [show Functions.ash_left_int 4 3 = 32 from rfl,
    immediate_value constant,
    run_bind,logext32 state constant]
  dsimp only
  rw [show Functions.ash_left_int 8 3 = 64 from rfl,
    loghead64 constant,
    show Functions.bits_of_int 4 48 = (4#48) from rfl,run_bind,
    X86PrefixRead.add_pointer_checked state immediate (4#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate,word_bits]
  change (do
    let (result,resultFlags,undefined) ← Functions.gpr_add_spec_8 value (immediate64 constant) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (Sail.BitVec.zeroExtend result 128) 3
      (0#64) prefixes (rex true 0 destination)
      (Functions._get_modr_m_r_m (modRM 0 destination)) (3#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,calculated]
  dsimp only
  rw [run_bind,X86MovePrefix.write_operand_register64 state 0 destination (value + (immediate64 constant)) prefixes quiet]
  dsimp only
  rw [run_bind,X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide),diagnostic_put]
  exact quiet

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (constant : Immediate) (destination : Fin 16)
    (site : X86LegacyFetch.Window state (0x81#8) true 0 destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32)
    (advance : site.next.toInt + 4 = next.toInt)
    (known : lookup state destination = some value) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some ((immediate32 constant).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (value + immediate64 constant)) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (2 ^ 64 ≤ value.toNat + constant.val) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (0x81#8)
    ((X86LegacyFetch.checkOpcode_iff _).mp (by decide)) true state 0 destination site,
    X86AddImmediate.dispatch_add16]
  apply handler state constant destination site.address site.next next (X86LegacyFetch.packet (0x81#8))
    site.attributes (site.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _)
    (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _) advance _ site.segments site.application
    site.rip known flagsKnown quiet bytes
  apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
  have := site.step2
  have := site.step3
  omega

theorem fetched_frame (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (constant : Immediate) (destination : Fin 16)
    (site : X86LegacyFetch.Window state (0x81#8) true 0 destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32)
    (advance : site.next.toInt + 4 = next.toInt)
    (known : lookup state destination = some value) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some ((immediate32 constant).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after output, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes destination) state after ∧
      lookup after destination = some (value + immediate64 constant) ∧
      after.regs.get? .rflags = some output ∧ after.regs.get? .rip = some (next.signExtend 64) ∧
      Functions._get_rflagsbits_cf output = Functions.bool_to_bits (2 ^ 64 ≤ value.toNat + constant.val) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output,run,carry⟩ := fetched other vector state constant destination site next value flags advance known flagsKnown quiet bytes
  let resultFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination (value + immediate64 constant)) resultFlags) next
  refine ⟨after,resultFlags,X86FuelPrefix.fetches_one state after run,
    X86RegisterIncrement.result_frame state destination _ resultFlags next,?_,?_,?_,carry⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]

example (state : State) : (Functions.binary_logext 32 2147483647).run state = .ok (2147483647 : Int) state :=
  logext32 state ⟨2147483647,by decide⟩

example (state : State) : (Functions.binary_logext 32 0).run state = .ok (0 : Int) state :=
  logext32 state ⟨0,by decide⟩

#print axioms fetched_frame
#print axioms handler
#print axioms fetched

end Mettapedia.Machines.TIsa.X86PositiveImmediate
