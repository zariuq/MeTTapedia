import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86PlainFetch

/-!
# Fetched stack operations used by the public native wrapper

The retained original stack-pointer helpers and PUSH/POP/RET handlers execute against
the existing byte-memory implementation. The C3 return theorem retains the
canonical-return check. The POP theorem retains alignment, full-width register
restoration and stack-pointer aliasing behavior. PUSH saves the source before
updating RSP, including when that source is RSP. Bare and REX-prefixed fetch
contracts derive decoder inputs from architectural state and actual bytes.

The rme16 definition is retained only as a dependency of the complete original
RET body; no C2 coverage is claimed. Program saved-register layout, wrapper/ABI,
OS placement and complete emitter refinement remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/StackFunctions.lean.inc"
  sha256 "979aac5508f515cec64249da2a96964a60e3d07c1253cb5224666fc1c8157146"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86Stack
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

theorem read_pointer (state : State) (value : Word) (known : lookup state 4 = some value) :
    (Functions.read_sptr .Mode_64bit).run state = .ok value state := by
  unfold Functions.read_sptr
  have read := rgfi_exact state (4 : Fin 16) value known
  change (Functions.rgfi 4).run state = .ok value state at read
  rw [run_bind, read]
  rfl

theorem write_pointer (state : State) (value : Word)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_sptr .Mode_64bit value).run state = .ok () (put state 4 value) := by
  change (Functions.write_rgfi 4 value).run state = _
  exact write_rgfi_exact state 4 value quiet

theorem truncate_pointer65 (value : BitVec 48) :
    Sail.BitVec.truncate (value.signExtend 65) 64 = value.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have wide : index < 65 := by omega
  simp [Sail.BitVec.truncate, within, wide, BitVec.getElem_signExtend]

theorem add_pointer (state : State) (source target : BitVec 48) (delta : Word)
    (sum : source.toInt + delta.toInt = target.toInt) :
    (Functions.add_to_sptr .Mode_64bit (source.signExtend 64) delta).run state =
      .ok (target.signExtend 64) state := by
  have extended : Functions.bits_of_int ((source.signExtend 64).toInt + delta.toInt) 65 = target.signExtend 65 := by
    rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64), sum,
      X86Alu.bits_of_int_eq]
    rw [← BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 65)]
    exact BitVec.ofInt_toInt
  have canonical : (Functions.canonical_address_p (target.signExtend 64).toInt).run state = .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using X86Move.canonical48 state target
  unfold Functions.add_to_sptr
  simp only [Functions.in_64bit_mode, ite_true]
  rw [extended, truncate_pointer65, run_bind, canonical]
  rfl

theorem stack_segment (address : Word) (alignment : Bool) :
    Functions.load_bytes_from_ea .Mode_64bit 8 8 address none 2 ":R" alignment false =
      Functions.load_bytes_from_ea .Mode_64bit 8 8 address none 3 ":R" alignment false := by
  rfl

theorem read_word (state : State) (base : BitVec 48) (pointer value : Word)
    (attributes : Vector (BitVec 16) 6) (alignment : Bool)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : alignment = false ∨ base &&& (7#48) = (0#48))
    (present : ∀ index < 8,
      state.mem.get? (X86WriteWords.physicalAddress base index) = some (value.extractLsb' (8 * index) 8)) :
    (Functions.rme_size .Mode_64bit 8 8 (base.signExtend 64) none 2 ":R" alignment false).run state =
      .ok (value.zeroExtend 128) state := by
  unfold Functions.rme_size
  rw [stack_segment, run_bind, X86ReadWords.load_word_exact state base none attributes pointer value ":R"
    alignment false upper segments application rip safe present]
  rfl

def popOpcode (destination : Fin 16) : BitVec 8 := BitVec.ofNat 8 (0x58 + destination.val % 8)
def popRex (destination : Fin 16) : BitVec 8 :=
  if destination.val < 8 then (0#8) else X86RegisterEncoding.rex false 0 destination

theorem pop_destination : ∀ destination : Fin 16,
    Functions.reg_index (Sail.BitVec.truncate (popOpcode destination &&& (7#8)) 3) (popRex destination) (0#2) =
      BitVec.ofNat 4 destination.val := by decide
theorem pop_no_wide : ∀ destination : Fin 16, Functions.logbitp_bits 3 (popRex destination) = false := by decide

theorem pop_operand_size (destination : Fin 16) (prefixes : BitVec 52)
    (noOverride : Functions._get_prefixes_opr prefixes = (0#8)) :
    Functions.select_operand_size .Mode_64bit false (popRex destination) false prefixes true false false =
      (pure 8 : SailM Int) := by
  simp [Functions.select_operand_size, Functions.in_64bit_mode, pop_no_wide, noOverride]

def popResult (state : State) (destination : Fin 16) (value : Word) (nextStack next : BitVec 48) : State :=
  X86Move.putPointer (put (put state 4 (nextStack.signExtend 64)) destination value) next

theorem pop_handler (state : State) (destination : Fin 16) (start next stack nextStack : BitVec 48)
    (prefixes : BitVec 52) (value : Word)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (noOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (noAddressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advanceStack : stack.toInt + 8 = nextStack.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (stackUpper : stack.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : stack &&& (7#48) = (0#48))
    (present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress stack index) =
      some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_pop_general_register .Mode_64bit start next prefixes (popRex destination)
      (popOpcode destination) (0#8) (0#8)).run state =
      .ok () (popResult state destination value nextStack next) := by
  unfold Functions.x86_pop_general_register
  dsimp only
  rw [pop_operand_size destination prefixes noOverride, run_bind, run_pure]
  dsimp only
  rw [run_bind, read_pointer state (stack.signExtend 64) stackKnown]
  dsimp only
  rw [show Functions.bits_of_int 8 64 = (8#64) from rfl,
    run_bind, add_pointer state stack nextStack (8#64) (by simpa using advanceStack)]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, noAddressOverride]
  rw [addressSize]
  simp only [pure_bind, bind_assoc, show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind, X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  rw [run_bind, read_word state stack (start.signExtend 64) value attributes
    (X86FrameLoad.alignmentEnabled controls flags visible) stackUpper segments application rip (Or.inr aligned) present]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, write_pointer state (nextStack.signExtend 64) quiet]
  dsimp only
  have narrow : Sail.BitVec.truncate (value.zeroExtend 128) 64 = value := X86Move.widen_truncate value
  rw [pop_destination, narrow]
  have quietStack := (put_other_register state (4 : Fin 16) (nextStack.signExtend 64)
    .log_register_writes (by decide)).trans quiet
  have action : Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value (popRex destination) =
      Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value (X86FrameLoad.frameRex destination) := rfl
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl, action, run_bind,
    X86FrameLoad.write_destination _ destination value quietStack]
  exact X86Move.write_pointer64 _ next
    ((put_other_register _ destination value .log_register_writes (key_ne_diagnostic destination)).trans quietStack)

theorem read_signed_word (state : State) (base : BitVec 48) (pointer value : Word)
    (attributes : Vector (BitVec 16) 6) (alignment : Bool)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : alignment = false ∨ base &&& (7#48) = (0#48))
    (present : ∀ index < 8,
      state.mem.get? (X86WriteWords.physicalAddress base index) = some (value.extractLsb' (8 * index) 8)) :
    (Functions.rime_size .Mode_64bit 8 8 (base.signExtend 64) none 2 ":R" alignment false).run state = .ok value state := by
  unfold Functions.rime_size
  rw [stack_segment, run_bind, X86ReadWords.load_word_exact state base none attributes pointer value ":R"
    alignment false upper segments application rip safe present]
  dsimp only
  have same : Sail.BitVec.signExtend value 64 = value := by
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    simp [Sail.BitVec.signExtend, within]
  rw [same]
  rfl

def retResult (state : State) (nextStack target : BitVec 48) : State :=
  X86Move.putPointer (put state 4 (nextStack.signExtend 64)) target

theorem ret_handler (state : State) (start next stack nextStack target : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (noAddressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advanceStack : stack.toInt + 8 = nextStack.toInt)
    (stackUpper : stack.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : stack &&& (7#48) = (0#48))
    (present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress stack index) =
      some ((target.signExtend 64).extractLsb' (8 * index) 8)) :
    (Functions.x86_ret .Mode_64bit start next prefixes (0#8) (0xc3#8) (0#8) (0#8)).run state =
      .ok () (retResult state nextStack target) := by
  unfold Functions.x86_ret
  dsimp only
  rw [run_bind, read_pointer state (stack.signExtend 64) stackKnown]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit false (0#8) false (Functions.Mk_prefixes (0#52))
      true true true = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, show Functions.check_range 2 8 8 = (pure 8 : SailM Int) from rfl,
    show ((0xc3#8) == (0xc3#8)) = true from rfl, ite_true]
  rw [show Functions.bits_of_int 8 64 = (8#64) from rfl,
    run_bind, run_bind, add_pointer state stack nextStack (8#64) (by simpa using advanceStack)]
  dsimp only
  rw [X86ReadWords.truncate48]
  simp only [run_pure, show ((0xc3#8) == (0xc2#8)) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  rw [run_bind, X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, noAddressOverride]
  rw [addressSize]
  simp only [pure_bind, show ((8 : Int) == 8) = true from rfl, ite_true,
    show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind, read_signed_word state stack (start.signExtend 64) (target.signExtend 64) attributes
    (X86FrameLoad.alignmentEnabled controls flags visible) stackUpper segments application rip (Or.inr aligned) present]
  dsimp only
  simp only [Functions.in_64bit_mode, ite_true]
  have canonical : (Functions.canonical_address_p (target.signExtend 64).toInt).run state = .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using X86Move.canonical48 state target
  rw [run_bind, canonical]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  have widenStack : Sail.BitVec.signExtend nextStack 64 = nextStack.signExtend 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    simp [Sail.BitVec.signExtend, BitVec.getElem_signExtend, within]
  rw [widenStack, run_bind, write_pointer state (nextStack.signExtend 64) quiet, X86ReadWords.truncate48]
  change (Functions.write_iptr .Mode_64bit target).run (put state 4 (nextStack.signExtend 64)) = _
  exact X86Move.write_pointer64 _ target
    ((put_other_register state (4 : Fin 16) (nextStack.signExtend 64) .log_register_writes (by decide)).trans quiet)

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with
    x86_push_general_register := Functions.x86_push_general_register
    x86_pop_general_register := Functions.x86_pop_general_register
    x86_ret := Functions.x86_ret }

def popLength (destination : Fin 16) : Nat := if destination.val < 8 then 1 else 2
def popPacket (destination : Fin 16) : BitVec 52 :=
  X86PlainFetch.packet (popOpcode destination) (if destination.val < 8 then (0#4) else (1#4))

theorem pop_shape : ∀ destination : Fin 16, X86PlainFetch.checkOpcode (popOpcode destination) = true := by decide
theorem pop_packet_operand : ∀ destination : Fin 16, Functions._get_prefixes_opr (popPacket destination) = (0#8) := by decide
theorem pop_packet_address : ∀ destination : Fin 16, Functions._get_prefixes_adr (popPacket destination) = (0#8) := by decide

theorem dispatch_pop (other : OtherOpcodeHandlers) (destination : Fin 16) (start next : BitVec 48) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next (popPacket destination) (popRex destination)
      (popOpcode destination) (0#8) (0#8) =
    Functions.x86_pop_general_register .Mode_64bit start next (popPacket destination) (popRex destination)
      (popOpcode destination) (0#8) (0#8) := by
  fin_cases destination <;> rfl

theorem pop_fetch_to_handler (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (context : X86PlainFetch.Facts state)
    (start opcodeAddress next : BitVec 48)
    (opcodeLocation : opcodeAddress.toInt = start.toInt + (if destination.val < 8 then 0 else 1))
    (advance : start.toInt + popLength destination = next.toInt)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (prefixByte : ¬destination.val < 8 → state.mem.get? (start.signExtend 52).toNat = some (popRex destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (popOpcode destination)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.x86_pop_general_register .Mode_64bit start next (popPacket destination) (popRex destination)
        (popOpcode destination) (0#8) (0#8)).run state := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape := (X86PlainFetch.checkOpcode_iff _).mp (pop_shape destination)
  by_cases low : destination.val < 8
  · have same : opcodeAddress = start := BitVec.eq_of_toInt_eq (by simpa only [low, ite_true, Int.add_zero] using opcodeLocation)
    rw [same] at opcodeByte
    have step : start.toInt + 1 = next.toInt := by
      simp only [popLength, low, ite_true] at advance
      omega
    rw [X86PlainFetch.fetch_to_dispatch (popOpcode destination) shape state start next context.control context.attributes
      step context.status context.fault context.msrs context.segments context.longMode context.codeMode
      context.application rip opcodeByte]
    have dispatched := congrArg (fun action : SailM Unit => action.run state) (dispatch_pop other destination start next)
    simpa only [popPacket, popRex, low, ite_true] using dispatched
  · have step : start.toInt + 1 = opcodeAddress.toInt := by simpa only [low, ite_false] using opcodeLocation.symm
    have finish : start.toInt + 2 = next.toInt := by
      simp only [popLength, low, ite_false] at advance
      omega
    have byte : state.mem.get? (start.signExtend 52).toNat = some (X86RegisterEncoding.rex false 0 destination) := by
      simpa only [popRex, low, ite_false] using prefixByte low
    rw [X86PlainFetch.fetch_rex_to_dispatch (popOpcode destination) shape state start opcodeAddress next
      context.control context.attributes destination step finish context.status context.fault context.msrs context.segments
      context.longMode context.codeMode context.application rip byte opcodeByte]
    have dispatched := congrArg (fun action : SailM Unit => action.run state) (dispatch_pop other destination start next)
    simpa only [popPacket, popRex, low, ite_false] using dispatched

theorem fetched_pop (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (context : X86PlainFetch.Facts state)
    (start opcodeAddress next stack nextStack : BitVec 48) (value : Word)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (opcodeLocation : opcodeAddress.toInt = start.toInt + (if destination.val < 8 then 0 else 1))
    (advance : start.toInt + popLength destination = next.toInt)
    (advanceStack : stack.toInt + 8 = nextStack.toInt)
    (stackUpper : stack.toInt + 8 ≤ (2 ^ 47 : Int))
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : stack &&& (7#48) = (0#48))
    (prefixByte : ¬destination.val < 8 → state.mem.get? (start.signExtend 52).toNat = some (popRex destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (popOpcode destination))
    (present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress stack index) =
      some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (popResult state destination value nextStack next) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [pop_fetch_to_handler other vector state destination context start opcodeAddress next opcodeLocation advance rip prefixByte opcodeByte]
  apply pop_handler state destination start next stack nextStack (popPacket destination) value context.attributes visible controls
    flags (pop_packet_operand destination) (pop_packet_address destination) advanceStack
  · apply X86FrameLoad.length_from_distance _ _ (popLength destination)
    · unfold popLength; split <;> decide
    · omega
  · exact stackUpper
  · exact context.segments
  · exact context.application
  · exact rip
  · exact stackKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact aligned
  · exact present

theorem fetched_ret (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (context : X86PlainFetch.Facts state) (start next stack nextStack target : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (advance : start.toInt + 1 = next.toInt) (advanceStack : stack.toInt + 8 = nextStack.toInt)
    (stackUpper : stack.toInt + 8 ≤ (2 ^ 47 : Int))
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : stack &&& (7#48) = (0#48))
    (opcodeByte : state.mem.get? (start.signExtend 52).toNat = some (0xc3#8))
    (present : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress stack index) =
      some ((target.signExtend 64).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (retResult state nextStack target) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape := (X86PlainFetch.checkOpcode_iff (0xc3#8)).mp (by decide)
  rw [X86PlainFetch.fetch_to_dispatch (0xc3#8) shape state start next context.control context.attributes advance
    context.status context.fault context.msrs context.segments context.longMode context.codeMode context.application rip opcodeByte]
  change (Functions.x86_ret .Mode_64bit start next (X86PlainFetch.packet (0xc3#8) (0#4))
    (0#8) (0xc3#8) (0#8) (0#8)).run state = _
  apply ret_handler state start next stack nextStack target (X86PlainFetch.packet (0xc3#8) (0#4))
    context.attributes visible controls flags (by decide) advanceStack stackUpper context.segments context.application rip
    stackKnown controlKnown flagsKnown visibleKnown quiet aligned present

theorem pop_frame (state : State) (destination : Fin 16) (value : Word) (nextStack next : BitVec 48) :
    X86Execution.RegisterFrame {.rsp, key destination, .rip} state (popResult state destination value nextStack next) := by
  apply ((X86Execution.put_frame state 4 (nextStack.signExtend 64)).trans
    ((X86Execution.put_frame _ destination value).trans (X86Execution.pointer_frame _ next))).mono
  intro register present
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, show key 4 = Register.rsp from rfl] at present ⊢
  tauto

theorem ret_frame (state : State) (nextStack target : BitVec 48) :
    X86Execution.RegisterFrame {.rsp, .rip} state (retResult state nextStack target) := by
  simpa [retResult, key] using (X86Execution.put_frame state 4 (nextStack.signExtend 64)).trans
    (X86Execution.pointer_frame _ target)

theorem pop_stack (state : State) (destination : Fin 16) (value : Word) (nextStack next : BitVec 48)
    (separate : destination ≠ (4 : Fin 16)) :
    lookup (popResult state destination value nextStack next) 4 = some (nextStack.signExtend 64) := by
  rw [popResult, X86Move.lookup_putPointer, lookup_put_other _ destination 4 value separate, lookup_put_same]

theorem pop_value (state : State) (destination : Fin 16) (value : Word) (nextStack next : BitVec 48) :
    lookup (popResult state destination value nextStack next) destination = some value := by
  rw [popResult, X86Move.lookup_putPointer, lookup_put_same]

theorem pop_other (state : State) (destination observed : Fin 16) (value : Word) (nextStack next : BitVec 48)
    (apart : destination ≠ observed) (notStack : (4 : Fin 16) ≠ observed) :
    lookup (popResult state destination value nextStack next) observed = lookup state observed := by
  rw [popResult, X86Move.lookup_putPointer, lookup_put_other _ destination observed value apart,
    lookup_put_other state 4 observed _ notStack]

theorem ret_stack (state : State) (nextStack target : BitVec 48) :
    lookup (retResult state nextStack target) 4 = some (nextStack.signExtend 64) := by
  rw [retResult, X86Move.lookup_putPointer, lookup_put_same]

theorem ret_other (state : State) (observed : Fin 16) (nextStack target : BitVec 48)
    (notStack : (4 : Fin 16) ≠ observed) :
    lookup (retResult state nextStack target) observed = lookup state observed := by
  rw [retResult, X86Move.lookup_putPointer, lookup_put_other state 4 observed _ notStack]

open X86Execution

def pushOpcode (source : Fin 16) : BitVec 8 := BitVec.ofNat 8 (0x50 + source.val % 8)
def pushRex (source : Fin 16) : BitVec 8 :=
  if source.val < 8 then (0#8) else X86RegisterEncoding.rex false 0 source

theorem push_source : ∀ source : Fin 16,
    Functions.reg_index (Functions.loghead_bits 3 (pushOpcode source)) (pushRex source) (0#2) =
      BitVec.ofNat 4 source.val := by decide

theorem push_operand_size (source : Fin 16) (prefixes : BitVec 52)
    (noOverride : Functions._get_prefixes_opr prefixes = (0#8)) :
    Functions.select_operand_size .Mode_64bit false (pushRex source) false prefixes true false false =
      (pure 8 : SailM Int) := by
  exact X86Stack.pop_operand_size source prefixes noOverride

theorem write_word (state : State) (base : BitVec 48) (pointer value : Word)
    (attributes : Vector (BitVec 16) 6) (alignment : Bool)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : alignment = false ∨ base &&& (7#48) = (0#48)) :
    (Functions.wme_size .Mode_64bit 8 8 (base.signExtend 64) none 2 (Sail.BitVec.zeroExtend value 128)
      alignment false).run state = .ok () (X86WriteWords.storeBytes 8 state base value) := by
  have same : Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) none 2 value alignment false =
      Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) none 3 value alignment false := rfl
  change (Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) none 2
    (Sail.BitVec.truncate (Sail.BitVec.zeroExtend value 128) 64) alignment false).run state = _
  rw [X86Move.widen_truncate, same]
  exact X86WriteWords.store_word_exact state base none attributes pointer value alignment false upper
    segments application rip safe

def pushResult (state : State) (value : Word) (nextStack next : BitVec 48) : State :=
  X86Move.putPointer (put (X86WriteWords.storeBytes 8 state nextStack value) 4 (nextStack.signExtend 64)) next

theorem push_handler (state : State) (source : Fin 16) (start next stack nextStack : BitVec 48)
    (prefixes : BitVec 52) (value : Word)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (noOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (noAddressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advanceStack : nextStack.toInt + 8 = stack.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (stackUpper : nextStack.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : nextStack &&& (7#48) = (0#48)) :
    (Functions.x86_push_general_register .Mode_64bit start next prefixes (pushRex source)
      (pushOpcode source) (0#8) (0#8)).run state =
      .ok () (pushResult state value nextStack next) := by
  unfold Functions.x86_push_general_register
  dsimp only
  rw [push_operand_size source prefixes noOverride, run_bind, run_pure]
  dsimp only
  rw [run_bind, X86Stack.read_pointer state (stack.signExtend 64) stackKnown]
  dsimp only
  rw [show Functions.bits_of_int (-(8 : Int)) 64 = (0xfffffffffffffff8#64) from rfl,
    run_bind, X86Stack.add_pointer state stack nextStack (0xfffffffffffffff8#64)
      (by change stack.toInt + (-8) = nextStack.toInt; omega)]
  dsimp only
  rw [push_source, show Functions.bits_of_int 8 4 = (8#4) from rfl, run_bind,
    X86Move.read_register64 state source (pushRex source) value sourceKnown]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, noAddressOverride]
  rw [addressSize]
  simp only [pure_bind]
  rw [run_bind, X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  simp only [show Int.toNat (8 : Int) = 8 from rfl]
  rw [X86ReadWords.truncate48,
    show Sail.BitVec.signExtend nextStack 64 = nextStack.signExtend 64 from rfl, run_bind,
    write_word state nextStack (start.signExtend 64) value attributes
      (X86FrameLoad.alignmentEnabled controls flags visible) stackUpper segments application rip (Or.inr aligned)]
  dsimp only
  have quietStored := ((X86WriteWords.storeBytes_frame 8 state nextStack value).registers_equal)
  have quietNext : (X86WriteWords.storeBytes 8 state nextStack value).regs.get? .log_register_writes = some false := by
    rw [quietStored]; exact quiet
  rw [run_bind, X86Stack.write_pointer _ (nextStack.signExtend 64) quietNext]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  exact X86Move.write_pointer64 _ next
    ((put_other_register _ (4 : Fin 16) (nextStack.signExtend 64) .log_register_writes (by decide)).trans quietNext)

theorem push_frame (state : State) (value : Word) (nextStack next : BitVec 48) :
    X86StateFrame.Frame {.rsp, .rip} (X86WriteWords.written nextStack (List.range 8))
      state (pushResult state value nextStack next) := by
  have stored := X86WriteWords.storeBytes_frame 8 state nextStack value
  have updated := (X86StateFrame.registerOnly (put_frame (X86WriteWords.storeBytes 8 state nextStack value) 4 (nextStack.signExtend 64))).trans
    (X86StateFrame.registerOnly (pointer_frame _ next))
  simpa [pushResult, key] using stored.trans updated

def pushLength (source : Fin 16) : Nat := if source.val < 8 then 1 else 2
def pushPacket (source : Fin 16) : BitVec 52 :=
  X86PlainFetch.packet (pushOpcode source) (if source.val < 8 then (0#4) else (1#4))

theorem push_shape : ∀ source : Fin 16, X86PlainFetch.checkOpcode (pushOpcode source) = true := by decide
theorem push_packet_operand : ∀ source : Fin 16, Functions._get_prefixes_opr (pushPacket source) = (0#8) := by decide
theorem push_packet_address : ∀ source : Fin 16, Functions._get_prefixes_adr (pushPacket source) = (0#8) := by decide

theorem dispatch_push (other : OtherOpcodeHandlers) (source : Fin 16) (start next : BitVec 48) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next (pushPacket source) (pushRex source)
      (pushOpcode source) (0#8) (0#8) =
    Functions.x86_push_general_register .Mode_64bit start next (pushPacket source) (pushRex source)
      (pushOpcode source) (0#8) (0#8) := by
  fin_cases source <;> rfl

theorem push_fetch_to_handler (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (context : X86PlainFetch.Facts state)
    (start opcodeAddress next : BitVec 48)
    (opcodeLocation : opcodeAddress.toInt = start.toInt + (if source.val < 8 then 0 else 1))
    (advance : start.toInt + pushLength source = next.toInt)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (prefixByte : ¬source.val < 8 → state.mem.get? (start.signExtend 52).toNat = some (pushRex source))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (pushOpcode source)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.x86_push_general_register .Mode_64bit start next (pushPacket source) (pushRex source)
        (pushOpcode source) (0#8) (0#8)).run state := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape := (X86PlainFetch.checkOpcode_iff _).mp (push_shape source)
  by_cases low : source.val < 8
  · have same : opcodeAddress = start := BitVec.eq_of_toInt_eq (by simpa only [low, ite_true, Int.add_zero] using opcodeLocation)
    rw [same] at opcodeByte
    have step : start.toInt + 1 = next.toInt := by
      simp only [pushLength, low, ite_true] at advance
      omega
    rw [X86PlainFetch.fetch_to_dispatch (pushOpcode source) shape state start next context.control context.attributes
      step context.status context.fault context.msrs context.segments context.longMode context.codeMode
      context.application rip opcodeByte]
    have dispatched := congrArg (fun action : SailM Unit => action.run state) (dispatch_push other source start next)
    simpa only [pushPacket, pushRex, low, ite_true] using dispatched
  · have step : start.toInt + 1 = opcodeAddress.toInt := by simpa only [low, ite_false] using opcodeLocation.symm
    have finish : start.toInt + 2 = next.toInt := by
      simp only [pushLength, low, ite_false] at advance
      omega
    have byte : state.mem.get? (start.signExtend 52).toNat = some (X86RegisterEncoding.rex false 0 source) := by
      simpa only [pushRex, low, ite_false] using prefixByte low
    rw [X86PlainFetch.fetch_rex_to_dispatch (pushOpcode source) shape state start opcodeAddress next
      context.control context.attributes source step finish context.status context.fault context.msrs context.segments
      context.longMode context.codeMode context.application rip byte opcodeByte]
    have dispatched := congrArg (fun action : SailM Unit => action.run state) (dispatch_push other source start next)
    simpa only [pushPacket, pushRex, low, ite_false] using dispatched

theorem fetched_push (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (context : X86PlainFetch.Facts state)
    (start opcodeAddress next stack nextStack : BitVec 48) (value : Word)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (opcodeLocation : opcodeAddress.toInt = start.toInt + (if source.val < 8 then 0 else 1))
    (advance : start.toInt + pushLength source = next.toInt)
    (advanceStack : nextStack.toInt + 8 = stack.toInt)
    (stackUpper : nextStack.toInt + 8 ≤ (2 ^ 47 : Int))
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (stackKnown : lookup state 4 = some (stack.signExtend 64))
    (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) (quiet : state.regs.get? .log_register_writes = some false)
    (aligned : nextStack &&& (7#48) = (0#48))
    (prefixByte : ¬source.val < 8 → state.mem.get? (start.signExtend 52).toNat = some (pushRex source))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (pushOpcode source)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (pushResult state value nextStack next) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [push_fetch_to_handler other vector state source context start opcodeAddress next opcodeLocation advance rip prefixByte opcodeByte]
  apply push_handler state source start next stack nextStack (pushPacket source) value context.attributes visible controls
    flags (push_packet_operand source) (push_packet_address source) advanceStack
  · apply X86FrameLoad.length_from_distance _ _ (pushLength source)
    · unfold pushLength; split <;> decide
    · omega
  · exact stackUpper
  · exact context.segments
  · exact context.application
  · exact rip
  · exact stackKnown
  · exact sourceKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact aligned

theorem push_stack (state : State) (value : Word) (nextStack next : BitVec 48) :
    lookup (pushResult state value nextStack next) 4 = some (nextStack.signExtend 64) := by
  rw [pushResult, X86Move.lookup_putPointer, lookup_put_same]

theorem push_other (state : State) (value : Word) (nextStack next : BitVec 48)
    (observed : Fin 16) (apart : (4 : Fin 16) ≠ observed) :
    lookup (pushResult state value nextStack next) observed = lookup state observed := by
  rw [pushResult, X86Move.lookup_putPointer, lookup_put_other _ 4 observed _ apart]
  exact (X86WriteWords.storeBytes_frame 8 state nextStack value).lookup observed (by simp)

theorem push_memory (state : State) (value : Word) (nextStack next : BitVec 48) :
    (pushResult state value nextStack next).mem =
      (X86WriteWords.storeBytes 8 state nextStack value).mem := rfl

end Mettapedia.Machines.TIsa.X86Stack

#print axioms Mettapedia.Machines.TIsa.X86Stack.read_pointer
#print axioms Mettapedia.Machines.TIsa.X86Stack.add_pointer
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_pop
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_ret
#print axioms Mettapedia.Machines.TIsa.X86Stack.pop_frame
#print axioms Mettapedia.Machines.TIsa.X86Stack.ret_frame
#print axioms Mettapedia.Machines.TIsa.X86Stack.push_handler
#print axioms Mettapedia.Machines.TIsa.X86Stack.fetched_push
#print axioms Mettapedia.Machines.TIsa.X86Stack.push_frame
