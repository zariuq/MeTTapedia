import Mettapedia.Machines.TIsa.X86LogicalWord
import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86Stack
import Mettapedia.Machines.TIsa.JsonImport

/-!
# Native U64 binary producer bodies for the sealed function registry

The source graph is the established modular word arithmetic. A 30-byte body
loads two input words through RDI, calculates into RAX, writes one output word
through RSI, sets RAX to one and returns normally. The six fetched steps use
the pinned original ISA definitions. Every register and byte outside the
declared footprint is preserved, including all callee-saved registers.

This matches the TcFn buffer/Boolean ABI. Constructive controls cover all five
operations and arbitrary words, arithmetic zero as a successful value, a false
Boolean return and a changed operation byte.

Deployment artifacts include a four-byte ENDBR64 prefix. Their exact bytes and
body slice are checked, but the execution theorem starts at body offset four.
The pinned Sail model rejects opcode0F1E, so a full registered-entry execution
theorem remains open. No landing-pad execution or CET enforcement is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BinaryCallbackBody
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Operation := Sum X86Arithmetic.DefinedOperation X86LogicalWord.Kind

def opcode : Operation → BitVec 8
  | .inl operation => X86Arithmetic.opcode operation
  | .inr operation => X86LogicalWord.opcode operation

def binary : Operation → Binary
  | .inl .add => .add
  | .inl .sub => .sub
  | .inr .or => .bor
  | .inr .and => .band
  | .inr .xor => .bxor

def evaluate (operation : Operation) (left right : Word) : Word := (binary operation).evaluate left right

def aluCode (operation : Operation) : List Nat := [0x48,(opcode operation).toNat,0xd0]

theorem alu_frame (state : State) (value : Word) (flags : BitVec 32) (next : BitVec 48) :
    RegisterFrame {.rax,.rflags,.rip} state
      (X86Move.putPointer (X86Flags.putFlags (put state 0 value) flags) next) :=
  (((put_frame state 0 value).trans (flags_frame _ flags)).trans (pointer_frame _ next)).mono (by simp [key])

theorem alu_fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State)
    (window : X86LegacyFetch.Window state (opcode operation) true 2 0)
    (left right : Word) (flags : BitVec 32)
    (leftKnown : lookup state 0 = some left) (rightKnown : lookup state 2 = some right)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after resultFlags, Step state after ∧ RegisterFrame {.rax,.rflags,.rip} state after ∧
      lookup after 0 = some (evaluate operation left right) ∧ after.regs.get? .rflags = some resultFlags ∧
      after.regs.get? .rip = some (window.next.signExtend 64) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  cases operation with
  | inl operation =>
    obtain ⟨output,run⟩ := X86Arithmetic.fetched_register64 other vector operation state 2 0 window
      left right flags rightKnown leftKnown flagsKnown quiet
    have result : X86Arithmetic.result operation left right = evaluate (.inl operation) left right := by cases operation <;> rfl
    rw [result] at run
    let resultFlags := X86Flags.mergeFlags flags output
    let after := X86Move.putPointer (X86Flags.putFlags (put state 0 (evaluate (.inl operation) left right)) resultFlags) window.next
    refine ⟨after,resultFlags,run,alu_frame _ _ _ _,?_,?_,?_⟩
    · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
    · rw [(pointer_frame _ window.next).registers .rflags (by decide)]
      simp [X86Flags.putFlags]
    · simp [after,X86Move.putPointer]
  | inr operation =>
    obtain ⟨output,run⟩ := X86LogicalWord.fetched other vector operation state 2 0 window
      left right flags rightKnown leftKnown flagsKnown quiet
    have result : X86LogicalWord.result operation left right = evaluate (.inr operation) left right := by cases operation <;> rfl
    rw [result] at run
    let resultFlags := X86LogicalFlags.merged flags output (0#1)
    let after := X86Move.putPointer (X86Flags.putFlags (put state 0 (evaluate (.inr operation) left right)) resultFlags) window.next
    refine ⟨after,resultFlags,run,alu_frame _ _ _ _,?_,?_,?_⟩
    · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
    · rw [(pointer_frame _ window.next).registers .rflags (by decide)]
      simp [X86Flags.putFlags]
    · simp [after,X86Move.putPointer]

def code (operation : Operation) : List Nat :=
  X86QwordLoad.code 0 7 (0#32) ++ (X86QwordLoad.code 2 7 (8#32) ++ (aluCode operation ++
    (X86DataStore.code true 0 6 (0#32) ++ [0xb8,1,0,0,0,0xc3])))

theorem code_length (operation : Operation) : (code operation).length = 30 := by
  simp [code,X86QwordLoad.code_length,X86DataStore.code_length,aluCode]

abbrev handlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86Arithmetic.linkedHandlers (X86Stack.linkedHandlers
    (X86FrameStore.linkedHandlers (X86FrameLoad.linkedHandlers other)))

theorem left_byte (operation : Operation) (index byte : Nat)
    (present : (X86QwordLoad.code 0 7 (0#32))[index]? = some byte) : (code operation)[index]? = some byte := by
  rw [code,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem right_byte (operation : Operation) (index byte : Nat)
    (present : (X86QwordLoad.code 2 7 (8#32))[index]? = some byte) : (code operation)[7 + index]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86QwordLoad.code_length]; omega),X86QwordLoad.code_length,
    Nat.add_sub_cancel_left,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem alu_byte (operation : Operation) (index byte : Nat)
    (present : (aluCode operation)[index]? = some byte) : (code operation)[14 + index]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86QwordLoad.code_length]; omega),X86QwordLoad.code_length,
    show 14 + index - 7 = 7 + index by omega,
    List.getElem?_append_right (by rw [X86QwordLoad.code_length]; omega),X86QwordLoad.code_length,
    Nat.add_sub_cancel_left,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem loaded_slice (state : State) (base : Int) (whole part : List Nat) (offset : Nat)
    (loaded : codeLoaded state base whole)
    (inside : ∀ index byte, part[index]? = some byte → whole[offset + index]? = some byte) :
    codeLoaded state (base + offset) part := by
  intro index byte present
  simpa only [address,Int.natCast_add,Int.add_assoc] using loaded (offset + index) byte (inside index byte present)

structure ReadInputs (state : State) (operation : Operation) extends X86LegacyFetch.Basis state where
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  buffer : BitVec 48
  left : Word
  right : Word
  bufferKnown : lookup state 7 = some (buffer.signExtend 64)
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 30 < (2 ^ 47 : Int)
  bufferUpper : buffer.toInt + 16 ≤ (2 ^ 47 : Int)
  aligned : ∀ slot : Fin 2, X86Execution.address buffer.toInt (8 * slot.val) &&& (7#48) = (0#48)
  loaded : codeLoaded state address.toInt (code operation)
  present : ∀ slot : Fin 2, ∀ byte < 8,
    state.mem.get? (X86WriteWords.physicalAddress (X86Execution.address buffer.toInt (8 * slot.val)) byte) =
      some ((if slot.val = 0 then left else right).extractLsb' (8 * byte) 8)

theorem read_and_calculate (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State) (input : ReadInputs state operation) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after resultFlags, (X86FuelPrefix.fetches 3).run state = .ok () after ∧
      RegisterFrame {.rax,.rdx,.rflags,.rip} state after ∧
      lookup after 0 = some (evaluate operation input.left input.right) ∧
      after.regs.get? .rflags = some resultFlags ∧
      after.regs.get? .rip = some ((address input.address.toInt 17).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  let first : X86QwordLoad.Inputs state 0 7 (0#32) := {
    input.toBasis with
    noSib := by decide
    noStack := by decide
    visible := input.visible
    controls := input.controls
    baseValue := input.buffer.signExtend 64
    value := input.left
    flags := input.flags
    dataAddress := input.buffer
    baseKnown := input.bufferKnown
    controlKnown := input.controlKnown
    flagsKnown := input.flagsKnown
    visibleKnown := input.visibleKnown
    quiet := input.quiet
    upper := by have := input.upper; omega
    dataUpper := by have := input.bufferUpper; omega
    effective := by simp
    aligned := by simpa [address] using input.aligned 0
    loaded := by intro index byte present; exact input.loaded index byte (left_byte operation index byte present)
    dataPresent := by
      intro byte within
      simpa only [Fin.val_zero,Nat.mul_zero,ite_true,X86WriteWords.physicalAddress,address,
        Int.natCast_zero,Int.add_zero,BitVec.ofInt_toInt] using input.present 0 byte within }
  obtain ⟨one,oneRun,oneFrame,leftKnown,oneRip⟩ := X86QwordLoad.executes (handlers other) vector state 0 7 (0#32) first
  have oneData : RegisterFrame dataRegisters state one := oneFrame.mono (by decide)
  let secondOrigin := rebase state one input.toBasis oneData input.upper 7 (by decide) oneRip
  have secondAddress : secondOrigin.address.toInt = input.address.toInt + 7 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 7 (by decide)
  have nextInput : (address input.buffer.toInt 8).toInt = input.buffer.toInt + 8 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.buffer) (extent := 8)
      (by have := input.bufferUpper; omega) 8 (by decide)
  let second : X86QwordLoad.Inputs one 2 7 (8#32) := {
    secondOrigin with
    noSib := by decide
    noStack := by decide
    visible := input.visible
    controls := input.controls
    baseValue := input.buffer.signExtend 64
    value := input.right
    flags := input.flags
    dataAddress := address input.buffer.toInt 8
    baseKnown := (oneFrame.lookup 7 (by decide)).trans input.bufferKnown
    controlKnown := (oneFrame.registers .ctrs (by decide)).trans input.controlKnown
    flagsKnown := (oneFrame.registers .rflags (by decide)).trans input.flagsKnown
    visibleKnown := (oneFrame.registers .seg_visibles (by decide)).trans input.visibleKnown
    quiet := (oneFrame.registers .log_register_writes (by decide)).trans input.quiet
    upper := by rw [secondAddress]; have := input.upper; omega
    dataUpper := by rw [nextInput]; have := input.bufferUpper; omega
    effective := by
      rw [show ((8#32).signExtend 64) = (8#64) from rfl]
      have coordinate : (input.buffer.signExtend 64 + (8#64)) = (address input.buffer.toInt 8).signExtend 64 := by
        apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_add,BitVec.toInt_signExtend_of_le (by decide),
          show (8#64).toInt = (8 : Int) from rfl,BitVec.toInt_signExtend_of_le (by decide),nextInput]
        apply Int.bmod_eq_of_le
        · have lower := BitVec.le_toInt input.buffer
          norm_num at lower ⊢
          omega
        · have upper := input.bufferUpper
          norm_num at upper ⊢
          omega
      exact coordinate
    aligned := by simpa only [show (8 : Nat) * (1 : Fin 2).val = 8 from rfl] using input.aligned 1
    loaded := by
      rw [secondAddress]
      apply loaded_slice one input.address.toInt (code operation) _ 7
        (by intro index byte present; rw [oneFrame.memory]; exact input.loaded index byte present)
      exact right_byte operation
    dataPresent := by
      intro byte within
      rw [oneFrame.memory]
      simpa [X86WriteWords.physicalAddress] using input.present (1 : Fin 2) byte within }
  obtain ⟨two,twoRun,twoFrame,rightKnown,twoRip⟩ := X86QwordLoad.executes (handlers other) vector one 2 7 (8#32) second
  have prefixFrame : RegisterFrame {.rax,.rdx,.rflags,.rip} state two :=
    (oneFrame.trans twoFrame).mono (by decide)
  have rip14 : two.regs.get? .rip = some ((address input.address.toInt 14).signExtend 64) := by
    simpa [second,secondAddress,address,Int.add_assoc] using twoRip
  let origin := rebase state two input.toBasis (prefixFrame.mono (by decide)) input.upper 14 (by decide) rip14
  have at14 : origin.address.toInt = input.address.toInt + 14 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 14 (by decide)
  let site : X86LegacyFetch.Window two (opcode operation) true 2 0 := {
    origin with
    prefixByte := by
      rw [prefixFrame.memory]
      exact input.loaded 14 0x48 (alu_byte operation 0 0x48 rfl)
    opcodeByte := by
      rw [prefixFrame.memory]
      simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.loaded 15 (opcode operation).toNat
        (alu_byte operation 1 _ rfl)
    modrmByte := by
      rw [prefixFrame.memory]
      exact input.loaded 16 0xd0 (alu_byte operation 2 0xd0 rfl) }
  obtain ⟨after,resultFlags,aluRun,aluFrame,result,flags,rip⟩ := alu_fetched (handlers other) vector operation two site
    input.left input.right input.flags ((twoFrame.lookup 0 (by decide)).trans leftKnown) rightKnown
    ((twoFrame.registers .rflags (by decide)).trans ((oneFrame.registers .rflags (by decide)).trans input.flagsKnown))
    ((prefixFrame.registers .log_register_writes (by decide)).trans input.quiet)
  refine ⟨after,resultFlags,X86FuelPrefix.fetches_then 1 2 state one after oneRun ?_,
    (prefixFrame.trans aluFrame).mono (by simp),result,flags,?_⟩
  · exact X86FuelPrefix.fetches_then 1 1 one two after twoRun (X86FuelPrefix.fetches_one two after aluRun)
  · simpa only [site,origin,rebase,address,Int.add_assoc] using rip

theorem store_byte (operation : Operation) (index byte : Nat)
    (present : (X86DataStore.code true 0 6 (0#32))[index]? = some byte) :
    (code operation)[17 + index]? = some byte := by
  have within : index < 7 := (List.getElem?_eq_some_iff.mp present).1
  interval_cases index <;> exact present

theorem tail_byte (operation : Operation) (index byte : Nat)
    (present : ([0xb8,1,0,0,0,0xc3] : List Nat)[index]? = some byte) :
    (code operation)[24 + index]? = some byte := by
  have within : index < 6 := (List.getElem?_eq_some_iff.mp present).1
  interval_cases index <;> exact present

def clobbers : Finset Register := {.rax,.rdx,.rflags,.rsp,.rip}
def outputWrites (output : BitVec 48) : Finset Nat := X86DataStore.writes true output

structure Inputs (state : State) (operation : Operation) extends ReadInputs state operation where
  output : BitVec 48
  stack : BitVec 48
  target : BitVec 48
  outputKnown : lookup state 6 = some (output.signExtend 64)
  stackKnown : lookup state 4 = some (stack.signExtend 64)
  outputUpper : output.toInt + 8 ≤ (2 ^ 47 : Int)
  stackUpper : stack.toInt + 8 < (2 ^ 47 : Int)
  outputAligned : output &&& (7#48) = (0#48)
  stackAligned : stack &&& (7#48) = (0#48)
  returnPresent : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress stack byte) =
    some ((target.signExtend 64).extractLsb' (8 * byte) 8)
  codeApart : ∀ offset byte, (code operation)[offset]? = some byte →
    ((X86Execution.address address.toInt offset).signExtend 52).toNat ∉ outputWrites output
  stackApart : ∀ byte < 8, X86WriteWords.physicalAddress stack byte ∉ outputWrites output

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State) (input : Inputs state operation) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame clobbers (outputWrites input.output) state after ∧
      lookup after 0 = some (1#64) ∧
      lookup after 4 = some ((address input.stack.toInt 8).signExtend 64) ∧
      after.regs.get? .rip = some (input.target.signExtend 64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress input.output byte) =
        some ((evaluate operation input.left input.right).extractLsb' (8 * byte) 8)) ∧
      codeLoaded after input.address.toInt (code operation) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  let point := fun offset => address input.address.toInt offset
  have pointInt (offset : Nat) (within : offset ≤ 30) : (point offset).toInt = input.address.toInt + offset :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within
  obtain ⟨three,flags,readRun,readFrame,value,flagsKnown,rip17⟩ :=
    read_and_calculate (handlers other) vector operation state input.toReadInputs
  let storeOrigin := rebase state three input.toBasis (readFrame.mono (by decide)) input.upper 17 (by decide) rip17
  have storeAddress : storeOrigin.address.toInt = input.address.toInt + 17 := pointInt 17 (by decide)
  let store : X86DataStore.Inputs three true 0 6 (0#32) := {
    storeOrigin with
    noSib := by decide
    noStack := by decide
    visible := input.visible
    controls := input.controls
    baseValue := input.output.signExtend 64
    value := evaluate operation input.left input.right
    flags := flags
    dataAddress := input.output
    baseKnown := (readFrame.lookup 6 (by decide)).trans input.outputKnown
    sourceKnown := value
    controlKnown := (readFrame.registers .ctrs (by decide)).trans input.controlKnown
    flagsKnown := flagsKnown
    visibleKnown := (readFrame.registers .seg_visibles (by decide)).trans input.visibleKnown
    quiet := (readFrame.registers .log_register_writes (by decide)).trans input.quiet
    upper := by rw [storeAddress]; have := input.upper; omega
    dataUpper := input.outputUpper
    effective := by simp
    aligned := input.outputAligned
    loaded := by
      rw [storeAddress]
      apply loaded_slice three input.address.toInt (code operation) _ 17
        (by intro index byte present; rw [readFrame.memory]; exact input.loaded index byte present)
      exact store_byte operation }
  let four := X86DataStore.result true three input.output (point 24) (evaluate operation input.left input.right)
  obtain ⟨storeRun,storeFrame⟩ := X86DataStore.executes (handlers other) vector three true 0 6 (0#32) store
  have storeNext : address store.address.toInt 7 = point 24 := by
    simp only [store,storeAddress,point,address,Int.add_assoc]
    rfl
  rw [storeNext] at storeRun storeFrame
  have prefixFrame : X86StateFrame.Frame {.rax,.rdx,.rflags,.rip} (outputWrites input.output) state four :=
    ((X86StateFrame.registerOnly readFrame).trans storeFrame).mono (by decide) (by simp [outputWrites,store])
  have fourRip : four.regs.get? .rip = some ((point 24).signExtend 64) := by
    simp [four,X86DataStore.result,X86Move.putPointer]
  let immediateOrigin := X86StateFrame.rebase state four input.toBasis prefixFrame (by decide) input.upper 24 (by decide) fourRip
  have immediateAddress : immediateOrigin.address.toInt = input.address.toInt + 24 := pointInt 24 (by decide)
  have immediateNext : immediateOrigin.opcodeAddress.toInt = input.address.toInt + 25 := pointInt 25 (by decide)
  have fourCode : codeLoaded four input.address.toInt (code operation) :=
    prefixFrame.codeLoaded _ _ input.loaded input.codeApart
  have immediateOpcode : four.mem.get? (immediateOrigin.address.signExtend 52).toNat = some (0xb8#8) :=
    fourCode 24 0xb8 (tail_byte operation 0 0xb8 rfl)
  have immediatePresent : ∀ byte < 4,
      four.mem.get? ((address immediateOrigin.opcodeAddress.toInt byte).signExtend 52).toNat =
        some ((1#32).extractLsb' (8 * byte) 8) := by
    intro byte within
    rw [immediateNext]
    have shift : address (input.address.toInt + 25) byte = address input.address.toInt (25 + byte) := by
      simp [address,Int.add_assoc]
    rw [shift]
    have present : (code operation)[25 + byte]? = some ((1#32).extractLsb' (8 * byte) 8).toNat := by
      interval_cases byte
      · exact tail_byte operation 1 1 rfl
      · exact tail_byte operation 2 0 rfl
      · exact tail_byte operation 3 0 rfl
      · exact tail_byte operation 4 0 rfl
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using fourCode _ _ present
  let five := X86Move.putPointer (put four 0 (1#64)) (point 29)
  have immediateRun : (X86FuelPrefix.fetches 1).run four = .ok () five := by
    apply X86FuelPrefix.fetches_one
    exact X86OutcomeLoad.fetched_eax (handlers other) vector four immediateOrigin (point 29) (1#32)
      (by rw [immediateNext,pointInt 29 (by decide)]; omega)
      ((prefixFrame.registers .log_register_writes (by decide)).trans input.quiet) immediateOpcode immediatePresent
  have immediateFrame : RegisterFrame {.rax,.rip} four five := by
    exact ((put_frame four 0 (1#64)).trans (pointer_frame _ (point 29))).mono (by simp [key])
  have allFrame : X86StateFrame.Frame {.rax,.rdx,.rflags,.rip} (outputWrites input.output) state five :=
    (prefixFrame.trans (X86StateFrame.registerOnly immediateFrame)).mono (by decide) (by simp)
  let facts : X86PlainFetch.Facts five := {
    control := input.control
    attributes := input.attributes
    status := (allFrame.registers .ms_reg (by decide)).trans input.status
    fault := (allFrame.registers .fault_reg (by decide)).trans input.fault
    msrs := (allFrame.registers .msrs (by decide)).trans input.msrs
    segments := (allFrame.registers .seg_hidden_attrs (by decide)).trans input.segments
    longMode := input.longMode
    codeMode := input.codeMode
    application := (allFrame.registers .app_view (by decide)).trans input.application }
  let nextStack := address input.stack.toInt 8
  have nextStackInt : nextStack.toInt = input.stack.toInt + 8 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.stack) input.stackUpper 8 (by decide)
  let after := X86Stack.retResult five nextStack input.target
  have returnRun : (X86FuelPrefix.fetches 1).run five = .ok () after := by
    apply X86FuelPrefix.fetches_one
    apply X86Stack.fetched_ret (handlers other) vector five facts (point 29) (point 30) input.stack nextStack input.target
      input.visible input.controls flags
    · rw [pointInt 29 (by decide),pointInt 30 (by decide)]; omega
    · exact nextStackInt.symm
    · exact le_of_lt input.stackUpper
    · simp [five,X86Move.putPointer]
    · exact (allFrame.lookup 4 (by decide)).trans input.stackKnown
    · exact (allFrame.registers .ctrs (by decide)).trans input.controlKnown
    · exact (immediateFrame.registers .rflags (by decide)).trans
        ((storeFrame.registers .rflags (by decide)).trans flagsKnown)
    · exact (allFrame.registers .seg_visibles (by decide)).trans input.visibleKnown
    · exact (allFrame.registers .log_register_writes (by decide)).trans input.quiet
    · exact input.stackAligned
    · exact allFrame.codeLoaded _ _ input.loaded input.codeApart 29 0xc3 (tail_byte operation 5 0xc3 rfl)
    · intro byte within
      rw [allFrame.memory _ (input.stackApart byte within)]
      exact input.returnPresent byte within
  have frame : X86StateFrame.Frame clobbers (outputWrites input.output) state after :=
    (allFrame.trans (X86StateFrame.registerOnly (X86Stack.ret_frame five nextStack input.target))).mono (by decide) (by simp)
  refine ⟨after,X86FuelPrefix.fetches_then 3 3 state three after readRun ?_,frame,?_,X86Stack.ret_stack _ _ _,?_,?_,?_⟩
  · exact X86FuelPrefix.fetches_then 1 2 three four after storeRun
      (X86FuelPrefix.fetches_then 1 1 four five after immediateRun returnRun)
  · rw [X86Stack.ret_other _ 0 _ _ (by decide),X86Move.lookup_putPointer,lookup_put_same]
  · simp [after,X86Stack.retResult,X86Move.putPointer]
  · intro byte within
    rw [(X86Stack.ret_frame five nextStack input.target).memory,immediateFrame.memory]
    exact X86DataStore.byte_readback three true input.output (point 24) (evaluate operation input.left input.right)
      input.outputUpper byte within
  · exact frame.codeLoaded _ _ input.loaded input.codeApart

theorem false_return_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State) (input : Inputs state operation) (after : State) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () after → lookup after 0 ≠ some (0#64) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,_,accepted,_⟩ := executes other vector operation state input
  intro observed rejected
  have same := X86FuelPrefix.fetches_deterministic 6 state proved after run observed
  rw [same,rejected] at accepted
  contradiction

def entryCode (operation : Operation) : List Nat := [0xf3,0x0f,0x1e,0xfa] ++ code operation

theorem entry_length (operation : Operation) : (entryCode operation).length = 34 := by
  simp [entryCode,code_length]

noncomputable def captured : List Nat × List NativeImage.TemplateSample :=
  tisa_template_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/BinaryCallbacks.json"

def operationAt (index : Fin 5) : Operation := match index.val with
  | 0 => .inl .add
  | 1 => .inl .sub
  | 2 => .inr .and
  | 3 => .inr .or
  | _ => .inr .xor

theorem artifact_bytes_exact (index : Fin 5) :
    (captured.2[index.val]?).map NativeImage.TemplateSample.bytes = some (entryCode (operationAt index)) := by
  fin_cases index <;> decide

theorem artifact_body_exact (index : Fin 5) :
    (captured.2[index.val]?).bind (fun sample => sample.body "BINARY_CALLBACK_BODY") =
      some (code (operationAt index)) := by
  fin_cases index <;> decide

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0
private def inputByte (left right : Word) (offset : Nat) : BitVec 8 :=
  (if offset < 8 then left else right).extractLsb' (8 * (offset % 8)) 8
private def cells (operation : Operation) (left right : Word) : List (Nat × BitVec 8) :=
  (List.range 30).map (fun offset => (X86WriteWords.physicalAddress (4096#48) offset,
    BitVec.ofNat 8 (((code operation)[offset]?).getD 0))) ++
  ((List.range 16).map (fun offset => (X86WriteWords.physicalAddress (12288#48) offset,inputByte left right offset)) ++
  ((List.range 8).map (fun offset => (X86WriteWords.physicalAddress (16384#48) offset,0xa5#8)) ++
  (List.range 8).map (fun offset => (X86WriteWords.physicalAddress (32768#48) offset,
    (0x9000#64).extractLsb' (8 * offset) 8))))
private def keys : List Nat :=
  (List.range 30).map (X86WriteWords.physicalAddress (4096#48)) ++
    ((List.range 16).map (X86WriteWords.physicalAddress (12288#48)) ++
      ((List.range 8).map (X86WriteWords.physicalAddress (16384#48)) ++
        (List.range 8).map (X86WriteWords.physicalAddress (32768#48))))
private theorem distinct (operation : Operation) (left right : Word) :
    (cells operation left right).Pairwise (fun a b => (a.1 == b.1) = false) := by
  have mapped : ((cells operation left right).map Prod.fst).Pairwise (fun a b => (a == b) = false) := by
    have same : (cells operation left right).map Prod.fst = keys := by
      simp [cells,keys,List.map_map,Function.comp_def]
    rw [same]
    decide
  exact List.pairwise_map.mp mapped

private def before (operation : Operation) (left right : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (12288#64)
  let registers := registers.insert .rsi (16384#64)
  let registers := registers.insert .rsp (32768#64)
  let registers := registers.insert .rax (123#64)
  let registers := registers.insert .rdx (456#64)
  let registers := registers.insert .rbx (1003#64)
  let registers := registers.insert .rbp (1005#64)
  let registers := registers.insert .r12 (1012#64)
  let registers := registers.insert .r13 (1013#64)
  let registers := registers.insert .r14 (1014#64)
  let registers := registers.insert .r15 (1015#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells operation left right),(),0,#[]⟩
private theorem cell (operation : Operation) (left right : Word) (key : Nat) (byte : BitVec 8)
    (present : (key,byte) ∈ cells operation left right) :
    (before operation left right).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct operation left right) present

private theorem inputCell (operation : Operation) (left right : Word) (index : Fin 16) :
    (before operation left right).mem.get? (X86WriteWords.physicalAddress (12288#48) index.val) =
      some (inputByte left right index.val) := by
  apply cell
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨index.val,List.mem_range.mpr index.isLt,rfl⟩

private def input (operation : Operation) (left right : Word) : Inputs (before operation left right) operation where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
  visible := visible
  controls := controls
  flags := 0x246#32
  buffer := 12288#48
  left := left
  right := right
  bufferKnown := by simp [before,lookup,key,Std.ExtDHashMap.get?_insert]; rfl
  controlKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  bufferUpper := by decide
  aligned := by intro slot; fin_cases slot <;> decide
  loaded := by
    intro offset byte present
    have within : offset < 30 := by have bound := (List.getElem?_eq_some_iff.mp present).1; rwa [code_length] at bound
    apply cell
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨offset,List.mem_range.mpr within,?_⟩
    simp only [present,Option.getD_some,X86WriteWords.physicalAddress]
  present := by
    intro slot byte within
    let index : Fin 16 := ⟨8 * slot.val + byte,by have := slot.isLt; omega⟩
    have known := inputCell operation left right index
    fin_cases slot <;> interval_cases byte <;>
      simpa [index,inputByte,X86WriteWords.physicalAddress,address] using known
  output := 16384#48
  stack := 32768#48
  target := 0x9000#48
  outputKnown := by simp [before,lookup,key,Std.ExtDHashMap.get?_insert]; rfl
  stackKnown := by simp [before,lookup,key,Std.ExtDHashMap.get?_insert]; rfl
  outputUpper := by decide
  stackUpper := by decide
  outputAligned := by decide
  stackAligned := by decide
  returnPresent := by
    intro byte within
    apply cell
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩
  codeApart := by
    intro offset byte present
    have within : offset < 30 := by have bound := (List.getElem?_eq_some_iff.mp present).1; rwa [code_length] at bound
    interval_cases offset <;> decide
  stackApart := by intro byte within; interval_cases byte <;> decide

theorem input_witness (operation : Operation) (left right : Word) :
    ∃ (state : State) (facts : Inputs state operation),
      facts.buffer = (12288#48) ∧ facts.output = (16384#48) ∧
      facts.stack = (32768#48) ∧ facts.target = (0x9000#48) ∧
      facts.left = left ∧ facts.right = right := by
  exact ⟨before operation left right, input operation left right,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem all_operations (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (left right : Word) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame clobbers (outputWrites (16384#48)) state after ∧
      lookup after 0 = some (1#64) ∧ lookup after 4 = some (32776#64) ∧
      after.regs.get? .rip = some (0x9000#64) ∧
      ∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (16384#48) byte) =
        some ((evaluate operation left right).extractLsb' (8 * byte) 8) := by
  obtain ⟨after,run,frame,accepted,stack,target,output,_⟩ := executes other vector operation
    (before operation left right) (input operation left right)
  exact ⟨before operation left right,after,run,frame,accepted,stack,target,output⟩

theorem zero_result_is_value (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      lookup after 0 = some (1#64) ∧
      ∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (16384#48) byte) = some (0#8) := by
  obtain ⟨state,after,run,_,accepted,_,_,output⟩ := all_operations other vector (.inl .add) (-1) 1
  refine ⟨state,after,run,accepted,?_⟩
  intro byte within
  simpa [evaluate,binary,Binary.evaluate] using output byte within

theorem changed_operation_rejected (left right : Word) :
    let changed : State := {(before (.inl .add) left right) with
      mem := (before (.inl .add) left right).mem.insert 4111 (0x31#8)}
    ¬codeLoaded changed 4096 (code (.inl .add)) := by
  let changed : State := {(before (.inl .add) left right) with
    mem := (before (.inl .add) left right).mem.insert 4111 (0x31#8)}
  change ¬codeLoaded changed 4096 (code (.inl .add))
  intro loaded
  have expected := loaded 15 0x01 (alu_byte (.inl .add) 1 0x01 rfl)
  change changed.mem.get? 4111 = some (0x01#8) at expected
  have actual : changed.mem.get? 4111 = some (0x31#8) := Std.ExtHashMap.getElem?_insert_self
  rw [actual] at expected
  contradiction
end Controls

#print axioms alu_fetched
#print axioms code_length
#print axioms read_and_calculate
#print axioms executes
#print axioms Controls.all_operations
#print axioms Controls.zero_result_is_value
#print axioms Controls.changed_operation_rejected
#print axioms artifact_bytes_exact
#print axioms artifact_body_exact
#print axioms false_return_refused
end Mettapedia.Machines.TIsa.X86BinaryCallbackBody
