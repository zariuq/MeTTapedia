import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86FuelPrefix

/-!
# Fetched zero-extended immediate writes to general registers

The six-byte REX/B8-BF form is checked through the original prefix scanner,
opcode dispatcher, little-endian immediate reader and MOV handler. It writes
all 64 destination bits with the zero-extended 32-bit immediate and advances
RIP, preserving flags, memory and every other register. No old destination
value is required. The separate five-byte EAX form is in X86OutcomeLoad.

The generic theorem covers all physical registers. A native leaf profile must
separately restrict destinations to its admitted register and scratch map.
Controls retain dirty upper bits, the actual R14 cap encoding, and an immediate
mutation. Entry checks, loops and ABI composition remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Immediate32
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86PrefixRead X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def opcode (destination : Fin 16) : BitVec 8 := BitVec.ofNat 8 (184 + destination.val % 8)
def packet (destination : Fin 16) : BitVec 52 := X86LegacyFetch.packet (opcode destination)

theorem encoded_register (destination : Fin 16) :
    Functions.reg_index (Sail.BitVec.truncate ((7#8) &&& opcode destination) 3) (rex false 0 destination) (0#2) =
      BitVec.ofNat 4 destination.val := by fin_cases destination <;> rfl

theorem handler (state : State) (destination : Fin 16) (start immediate finish : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32)
    (advance : immediate.toInt + 4 = finish.toInt)
    (length : Functions.check_instruction_length start finish (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4,
      state.mem.get? ((address immediate.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_oi .Mode_64bit start immediate (packet destination)
      (rex false 0 destination) (opcode destination) (0#8) (0#8)).run state =
        .ok () (X86Move.putPointer (put state destination (value.zeroExtend 64)) finish) := by
  have upper : immediate.toInt + 4 ≤ (2 ^ 47 : Int) := by have := BitVec.toInt_lt (x := finish); omega
  have notByte : (((176 : Int) ≤b Sail.BitVec.toNatInt (opcode destination)) &&
      ((Sail.BitVec.toNatInt (opcode destination) ≤b (183 : Int)) : Bool)) = false := by
    fin_cases destination <;> rfl
  have size : Functions.select_operand_size .Mode_64bit false (rex false 0 destination) false
      (packet destination) false false false = (pure 4 : SailM Int) := by fin_cases destination <;> rfl
  have addressSize : Functions.select_address_size .Mode_64bit (some (packet destination)) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,packet,X86LegacyFetch.packet_address]
  unfold Functions.x86_mov_op_en_oi
  dsimp only
  rw [notByte,size,run_bind,run_pure]
  dsimp only
  rw [addressSize]
  simp only [pure_bind,show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,Sail.BitVec.signExtend]
  rw [run_bind,X86FrameStore.read_dword state immediate pointer attributes value upper segments application rip present]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,run_bind,
    add_pointer_checked state immediate (4#48) finish (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [encoded_register]
  change (do
    Functions.wr32 (BitVec.ofNat 4 destination.val)
      (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32)
    Functions.write_iptr .Mode_64bit finish).run state = _
  rw [X86OutcomeLoad.narrowed,run_bind,wr32_exact state destination value quiet]
  exact X86Move.write_pointer64 _ finish ((put_other_register state destination (value.zeroExtend 64)
    .log_register_writes (by exact fun same => (key_ne_diagnostic destination) same)).trans quiet)

theorem opcode_scan (state : State) (destination : Fin 16) (start next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (advance : start.toInt + 1 = next.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (rip : state.regs.get? .rip = some pointer)
    (prefixByte : state.mem.get? (start.signExtend 52).toNat = some (rex false 0 destination))
    (byte : state.mem.get? (next.signExtend 52).toNat = some (opcode destination)) :
    (Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15).run state =
      .ok (packet destination,rex false 0 destination) state := by
  rw [rex_advances_scan state start next pointer attributes false (0 : Fin 16) destination (0#8) 14 advance
    (by decide) (by decide) segments application rip prefixByte]
  exact X86LegacyFetch.opcode_scan_stops (opcode destination) (by fin_cases destination <;> decide)
    (by fin_cases destination <;> decide) state next pointer attributes (rex false 0 destination) 13
    segments application rip byte

theorem fetch_to_handler [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (destination : Fin 16) (origin : X86LegacyFetch.Basis state)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex false 0 destination))
    (byte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (opcode destination)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.x86_mov_op_en_oi .Mode_64bit origin.address origin.modrmAddress
        (packet destination) (rex false 0 destination) (opcode destination) (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind,readRegister_exact,origin.status]
  dsimp only
  rw [run_bind,readRegister_exact,origin.fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind,X86InstructionFetch.operation_mode64 state origin.control origin.attributes origin.msrs origin.segments
    origin.longMode origin.codeMode]
  dsimp only
  rw [run_bind,X86InstructionFetch.read_pointer64 state origin.address origin.rip]
  dsimp only
  change (do let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15; _ : SailM Unit).run state = _
  rw [run_bind,opcode_scan state destination origin.address origin.opcodeAddress (origin.address.signExtend 64)
    origin.attributes origin.step1 origin.segments origin.application origin.rip prefixByte byte]
  dsimp only
  rw [show Functions._get_prefixes_num (Functions.Mk_prefixes (packet destination)) = (1#4) from
    X86LegacyFetch.packet_count (opcode destination)]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit origin.address (2#48); _ : SailM Unit).run state = _
  rw [run_bind,add_pointer_checked state origin.address (2#48) origin.modrmAddress (by simpa using origin.step2)]
  dsimp only
  simp only [pure_bind,Functions.Mk_modr_m,Functions.Mk_sib,bind_pure]
  rw [show Functions._get_prefixes_nxt (Functions.Mk_prefixes (packet destination)) = opcode destination from
    X86LegacyFetch.packet_opcode (opcode destination)]
  have noVex : ((opcode destination == (0xc5#8)) || (opcode destination == (0xc4#8))) = false := by fin_cases destination <;> decide
  have noEvex : (opcode destination == (0x62#8)) = false := by fin_cases destination <;> decide
  have noModrm : Functions.one_byte_opcode_modr_m_p .Mode_64bit (opcode destination) = false := by fin_cases destination <;> rfl
  have addressSize : Functions.select_address_size .Mode_64bit (some (Functions.Mk_prefixes (packet destination))) = (pure 8 : SailM Int) := by
    have ordinary : Functions._get_prefixes_adr (Functions.Mk_prefixes (packet destination)) = (0#8) :=
      X86LegacyFetch.packet_address (opcode destination)
    simp [Functions.select_address_size,Functions.in_64bit_mode,ordinary]
  simp only [noVex,noEvex,noModrm,Bool.false_eq_true,ite_false,Bool.false_and,Bool.false_or,pure_bind,addressSize]
  have dispatch := X86OpcodeDispatch.immediate_dword_guarded .Mode_64bit origin.address origin.modrmAddress
    (Functions.Mk_prefixes (packet destination)) (rex false 0 destination) (0#8) (0#8)
    (⟨destination.val % 8,Nat.mod_lt _ (by decide)⟩ : Fin 8)
  change Functions.one_byte_opcode_execute .Mode_64bit origin.address origin.modrmAddress
    (Functions.Mk_prefixes (packet destination)) (rex false 0 destination) (opcode destination) (0#8) (0#8) = _ at dispatch
  rw [dispatch]
  have ordinary : Functions._get_prefixes_lck (Functions.Mk_prefixes (packet destination)) = (0#8) :=
    X86LegacyFetch.packet_lock (opcode destination)
  rw [ordinary]
  rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48) (value : BitVec 32)
    (advance : origin.modrmAddress.toInt + 4 = finish.toInt)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex false 0 destination))
    (byte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (opcode destination))
    (present : ∀ index < 4,
      state.mem.get? ((address origin.modrmAddress.toInt index).signExtend 52).toNat = some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (X86Move.putPointer (put state destination (value.zeroExtend 64)) finish) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  simp only [Step]
  rw [fetch_to_handler state destination origin prefixByte byte]
  change (Functions.x86_mov_op_en_oi .Mode_64bit origin.address origin.modrmAddress
    (packet destination) (rex false 0 destination) (opcode destination) (0#8) (0#8)).run state = _
  apply handler state destination origin.address origin.modrmAddress finish origin.attributes (origin.address.signExtend 64) value advance
    _ origin.segments origin.application origin.rip quiet present
  apply X86FrameLoad.length_from_distance _ _ 6 (by decide)
  have := origin.step2
  omega

def code (destination : Fin 16) (value : BitVec 32) : List Nat :=
  [(rex false 0 destination).toNat,(opcode destination).toNat] ++
    (List.range 4).map (fun index => (value.extractLsb' (8 * index) 8).toNat)

theorem code_length (destination : Fin 16) (value : BitVec 32) : (code destination value).length = 6 := by
  simp [code]

def writes (destination : Fin 16) : Finset Register := {key destination,.rip}

theorem writes_data (destination : Fin 16) : writes destination ⊆ dataRegisters := by
  intro register member
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact data_key destination
  · decide

theorem result_frame (state : State) (destination : Fin 16) (value : BitVec 32) (finish : BitVec 48) :
    RegisterFrame (writes destination) state (X86Move.putPointer (put state destination (value.zeroExtend 64)) finish) := by
  exact ((put_frame state destination (value.zeroExtend 64)).trans (pointer_frame _ finish)).mono (by simp [writes])

structure Inputs (state : State) (destination : Fin 16) (value : BitVec 32) extends X86LegacyFetch.Basis state where
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 6 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (code destination value)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (value : BitVec 32) (input : Inputs state destination value) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧ lookup after destination = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some ((address input.address.toInt 6).signExtend 64) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let site := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let finish := address input.address.toInt 6
  have at2 : site.modrmAddress.toInt = input.address.toInt + 2 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 2 (by decide)
  have at6 : finish.toInt = input.address.toInt + 6 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 6 (by decide)
  have present : ∀ index < 4,
      state.mem.get? ((address site.modrmAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8) := by
    intro index within
    rw [at2]
    have shift : address (input.address.toInt + 2) index = address input.address.toInt (2 + index) := by
      simp [address,Int.add_assoc]
    rw [shift]
    have byte : (code destination value)[2 + index]? = some (value.extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.loaded _ _ byte
  have run := fetched other vector state destination site finish value (by omega) input.quiet
    (by simpa only [site,rebase,address,Int.add_zero,BitVec.ofInt_toInt,BitVec.ofNat_toNat,BitVec.setWidth_eq]
          using input.loaded 0 (rex false 0 destination).toNat (by simp [code]))
    (by simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq]
          using input.loaded 1 (opcode destination).toNat (by simp [code])) present
  let after := X86Move.putPointer (put state destination (value.zeroExtend 64)) finish
  refine ⟨after,X86FuelPrefix.fetches_one state after run,result_frame _ _ _ _,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    rfl

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells (destination : Fin 16) (value : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 6).map fun index => (4096 + index,BitVec.ofNat 8 (((code destination value)[index]?).getD 0))

private theorem distinct (destination : Fin 16) (value : BitVec 32) :
    (cells destination value).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells destination value).map Prod.fst).Nodup := by
    simp only [cells,List.map_map,Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map,beq_eq_false_iff_ne] using keys

private noncomputable def before (destination : Fin 16) (value : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert (key destination) (cast (key_word destination).symm (0xffffffffffffffff#64))
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells destination value),(),0,#[]⟩

private theorem image (destination : Fin 16) (value : BitVec 32) :
    codeLoaded (before destination value) 4096 (code destination value) := by
  intro index byte present
  have within : index < 6 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
  have point : ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide
  have member : (4096 + index,BitVec.ofNat 8 byte) ∈ cells destination value :=
    List.mem_map.mpr ⟨index,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct destination value) member

private def input (destination : Fin 16) (value : BitVec 32) : Inputs (before destination value) destination value where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  fault := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  msrs := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  segments := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  rip := by fin_cases destination <;> simp [before,key,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  loaded := image destination value

theorem all_registers (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (value : BitVec 32) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before destination value) = .ok () after ∧
      RegisterFrame (writes destination) (before destination value) after ∧
      lookup after destination = some (value.zeroExtend 64) ∧
      after.regs.get? .rip = some (4102#64) :=
  executes other vector _ destination value (input destination value)

theorem changed_immediate_rejected :
    ¬codeLoaded (before 14 (32#32)) 4096 (code 14 (33#32)) := by
  intro loaded
  have actual := image 14 (32#32) 2 32 (by decide)
  have changed := loaded 2 33 (by decide)
  rw [actual] at changed
  contradiction

example : code 14 (32#32) = [0x41,0xbe,0x20,0,0,0] := by decide
example : ((0xffffffff#32).zeroExtend 64) ≠ (0xffffffffffffffff#64) := by decide

end Controls

end Mettapedia.Machines.TIsa.X86Immediate32
