import Mettapedia.Machines.TIsa.X86LogicalWord
import Mettapedia.Machines.TIsa.X86WordLibrary

/-!
# U64 logical components in the common source/WP native compiler

Each component is an existing resource firing and an actual three-byte x86
instruction. The local certificate proves fetched execution, source/readback
correspondence, readiness and frames for every instruction prefix. It then
instantiates the established block compiler for arbitrary finite sequences.
The source effects agree with the p1 U64 operations, including operand aliases.

The constructive mask-then-toggle example composes dependent AND/XOR steps
into six loaded bytes, with the exact result and preserved stack, frame
pointer and memory. Wrong-result and changed-opcode controls are separate.
Public calls, non-word operations and sealed runtime admission remain separate
contracts. No new instruction interpreter or source execution layer is used.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LogicalLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

structure Instruction where
  operation : X86LogicalWord.Kind
  source : Fin 12
  destination : Fin 12
  unlocked : destination ≠ 0

abbrev World := X86WordLibrary.World
abbrev Program := X86BlockCompiler.Program Instruction

def binary : X86LogicalWord.Kind → Binary
  | .or => .bor
  | .and => .band
  | .xor => .bxor

def effect (instruction : Instruction) : Cells.Action (Fin 12) :=
  ⟨.binary (binary instruction.operation),[instruction.destination,instruction.source],instruction.destination⟩

def action (instruction : Instruction) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : Cells.Invocation (effect instruction), Cells.system.Enables world invocation
  Step world _ after := ∃ invocation : Cells.Invocation (effect instruction),
    Cells.system.Enables world invocation ∧ Cells.system.fire world invocation = after

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  rintro world ⟨invocation,enabled⟩
  exact ⟨(),Cells.system.fire world invocation,invocation,enabled,rfl⟩

def bytes (instruction : Instruction) : List Nat :=
  X86LogicalWord.code instruction.operation (X86CopyBlock.physical instruction.source)
    (X86CopyBlock.physical instruction.destination)

def registers : Finset Register := X86CopyBlock.registerWrites ∪ {.rflags}

def spec : X86BlockCompiler.Spec Instruction World where
  action := action
  represents := X86WordLibrary.represents
  ready := X86WordLibrary.ready
  bytes := bytes
  count := fun _ => 1
  registerWrites := registers
  byteWrites := ∅

theorem data_only : registers ⊆ dataRegisters := by decide
theorem stack_readonly : Register.rsp ∉ registers := by decide
theorem frame_readonly : Register.rdi ∉ registers := by decide

theorem local_writes (instruction : Instruction) :
    X86LogicalWord.writes (X86CopyBlock.physical instruction.destination) ⊆ registers := by
  intro register member
  simp only [X86LogicalWord.writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (X86CopyBlock.destination_written
      ⟨instruction.source,instruction.destination,instruction.unlocked⟩)
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))

theorem source_computes (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      some (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source)) := by
  rcases instruction with ⟨operation,source,destination,unlocked⟩
  cases operation <;> rfl

theorem source_step_iff (instruction : Instruction) (values : Fin 12 → Word) (following : World) :
    (action instruction).Step (Cells.encode Finset.univ values) () following ↔
      following = Cells.encode Finset.univ (Function.update values instruction.destination
        (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source))) := by
  constructor
  · rintro ⟨invocation,enabled,endpoint⟩
    obtain ⟨computed,fired⟩ := Cells.scalar_update_reflected (effect instruction) invocation Finset.univ values enabled
    rw [source_computes] at computed
    have same := (Option.some.inj computed).symm
    exact endpoint.symm.trans (same ▸ fired)
  · intro endpoint
    obtain ⟨invocation,enabled,fired⟩ := Cells.scalar_update_realized (effect instruction) Finset.univ values _
      (Finset.subset_univ _) (source_computes instruction values)
    exact ⟨invocation,enabled,fired.trans endpoint.symm⟩

theorem physical_injective : Function.Injective X86CopyBlock.physical := by
  intro left right same
  exact Registers.logicalSlot_injective
    (placed_injective (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) same)

theorem destination_only (instruction : Instruction) (index : Fin 12) (different : index ≠ instruction.destination) :
    key (X86CopyBlock.physical index) ∉ X86LogicalWord.writes (X86CopyBlock.physical instruction.destination) := by
  intro member
  simp only [X86LogicalWord.writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with same | same | same
  · exact different (physical_injective (key_injective same))
  · exact (by decide : ∀ i : Fin 16, key i ≠ .rflags) _ same
  · exact (by decide : ∀ i : Fin 16, key i ≠ .rip) _ same

theorem execute (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (source following : World) (native : State)
    (origin : X86LegacyFetch.Basis native)
    (step : (spec.action instruction).Step source () following)
    (represented : spec.represents source native) (prepared : spec.ready native)
    (upper : origin.address.toInt + (((spec.bytes instruction).length + 3 : Nat) : Int) < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (spec.bytes instruction)) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      spec.represents following after ∧ spec.ready after ∧
      after.regs.get? .rip = some ((address origin.address.toInt (spec.bytes instruction).length).signExtend 64) ∧
      ∀ count ≤ 1, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        X86StateFrame.Frame spec.registerWrites spec.byteWrites native observed := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨values,sourceEq,registersKnown⟩ := represented
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have three : (spec.bytes instruction).length = 3 := rfl
  have bounded : origin.address.toInt + 3 < (2 ^ 47 : Int) := by rw [three] at upper; omega
  let input : X86LogicalWord.Inputs native instruction.operation
      (X86CopyBlock.physical instruction.source) (X86CopyBlock.physical instruction.destination) :=
    { toBasis := origin
      left := values instruction.destination
      right := values instruction.source
      flags := flags
      sourceKnown := registersKnown instruction.source (Finset.mem_univ _)
      destinationKnown := registersKnown instruction.destination (Finset.mem_univ _)
      flagsKnown := flagsKnown
      quiet := quiet
      upper := bounded
      loaded := loaded }
  obtain ⟨after,newFlags,run,frame,value,flagsAfter,rip⟩ := X86LogicalWord.executes other vector instruction.operation
    native (X86CopyBlock.physical instruction.source) (X86CopyBlock.physical instruction.destination) input
  have followingEq := (source_step_iff instruction values following).mp (sourceEq ▸ step)
  have outputRegisters : X86CopyBlock.RegistersRepresented
      (Function.update values instruction.destination
        (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source))) after := by
    intro index _
    change lookup after (X86CopyBlock.physical index) = some (Function.update values instruction.destination
      (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source)) index)
    by_cases same : index = instruction.destination
    · subst index
      simpa only [Function.update_self,input] using value
    · rw [Function.update_of_ne same,frame.lookup _ (destination_only instruction index same)]
      exact registersKnown index (Finset.mem_univ _)
  have outputFrame := X86StateFrame.registerOnly (frame.mono (local_writes instruction))
  refine ⟨after,run,outputFrame,⟨_,followingEq,outputRegisters⟩,
    ⟨newFlags,flagsAfter,(frame.registers .log_register_writes (fun member =>
      (by decide : .log_register_writes ∉ dataRegisters)
        (X86LogicalWord.writes_data _ member))).trans quiet⟩,?_,?_⟩
  · simpa only [three] using rip
  · intro count within observed observedRun
    interval_cases count
    · have same := X86FuelPrefix.fetches_deterministic 0 native native observed
        (X86FuelPrefix.fetches_zero native) observedRun
      subst observed
      exact X86StateFrame.Frame.refl _ _ _
    · have same := X86FuelPrefix.fetches_deterministic 1 native after observed run observedRun
      subst observed
      exact outputFrame

theorem correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact ⟨data_only,fun instruction source following native origin _safe step represented prepared upper loaded _outside =>
    execute other vector instruction source following native origin step represented prepared upper loaded⟩

def p1 (instruction : Instruction) : P1Source.Instr :=
  .binary (binary instruction.operation) .u64 instruction.destination instruction.destination instruction.source

theorem source_evaluate_p1 (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) := by
  cases instruction.operation <;> rfl

theorem compile_wp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (source : World) (native : State)
    (input : X86BlockCompiler.At spec stop program source native)
    (post : Unit → World → Prop) (wp : program.wp action post source) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame registers ∅ native after ∧ X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other vector) progress stop program source native input post wp

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values instruction.destination
      (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source))))) :
    (Prog.prim instruction).wp action post (Cells.encode Finset.univ values) := by
  apply (wp_prim action instruction post _).mpr
  obtain ⟨invocation,enabled,_⟩ := Cells.scalar_update_realized (effect instruction) Finset.univ values _
    (Finset.subset_univ _) (source_computes instruction values)
  refine ⟨⟨invocation,enabled⟩,?_⟩
  rintro ⟨⟩ following step
  rw [(source_step_iff instruction values following).mp step]
  exact expected

namespace Controls
private def mask : Instruction := ⟨.and,5,6,by decide⟩
private def toggle : Instruction := ⟨.xor,5,6,by decide⟩
private def program : Program := Prog.bind (Prog.prim mask) fun _ => Prog.prim toggle
private def left : Word := 0x80000001000000ff#64
private def right : Word := 0xffffffff000000f0#64
private def values (register : Fin 12) : Word := if register = 6 then left else if register = 5 then right else 0
private def masked : Fin 12 → Word := Function.update values 6 (left &&& right)
private def finalValues : Fin 12 → Word := Function.update masked 6 ((left &&& right) ^^^ right)
private def raw : List Nat := [0x4d,0x21,0xca,0x4d,0x31,0xca]

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := rfl
theorem compiled_steps : X86BlockCompiler.steps spec program = 2 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  [(4096,0x4d#8),(4097,0x21#8),(4098,0xca#8),
    (4099,0x4d#8),(4100,0x31#8),(4101,0xca#8),(8192,42#8)]
private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values 0)
  let registers := registers.insert .rsi (values 1)
  let registers := registers.insert .rdx (values 2)
  let registers := registers.insert .rcx (values 3)
  let registers := registers.insert .r8 (values 4)
  let registers := registers.insert .r9 (values 5)
  let registers := registers.insert .r10 (values 6)
  let registers := registers.insert .r11 (values 7)
  let registers := registers.insert .rax (values 8)
  let registers := registers.insert .rbx (values 9)
  let registers := registers.insert .r12 (values 10)
  let registers := registers.insert .r13 (values 11)
  let registers := registers.insert .rsp (8192#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin : X86LegacyFetch.Basis before where
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

private theorem cell (address : Nat) (byte : BitVec 8) (present : (address,byte) ∈ cells) :
    before.mem.get? address = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def input : X86BlockCompiler.At spec 4102 program (Cells.encode Finset.univ values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := by
    refine ⟨values,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x246#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before]⟩
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 6 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  outside := by intros; simp [spec]

private theorem source_wp : program.wp action
    (fun _ world => world = Cells.encode Finset.univ finalValues) (Cells.encode Finset.univ values) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step mask values
  exact source_wp_step toggle masked _ rfl

theorem mask_then_toggle (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      lookup after (X86CopyBlock.physical 6) = some (0x7ffffffe00000000#64) ∧
      after.regs.get? .rip = some (4102#64) ∧
      lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,after,_,expected,run,frame,⟨outputValues,encoded,outputRegisters⟩,_,rip⟩ :=
    compile_wp other vector 4102 program _ before input _ source_wp
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues finalValues).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 6 (Finset.mem_univ _)
  rw [equalValues.2 6 (Finset.mem_univ _)] at read
  have expectedWord : finalValues 6 = (0x7ffffffe00000000#64) := by decide
  rw [expectedWord] at read
  refine ⟨before,after,run,read,rip,frame.lookup 4 stack_readonly,frame.lookup 7 frame_readonly,?_⟩
  intro address
  exact frame.memory address (by simp)

theorem wrong_result_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after (X86CopyBlock.physical 6) = some (0#64) →
      (X86FuelPrefix.fetches 2).run state ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state,proved,run,value,_⟩ := mask_then_toggle other vector
  refine ⟨state,?_⟩
  intro after wrong observed
  have same := X86FuelPrefix.fetches_deterministic 2 state proved after run observed
  rw [same,wrong] at value
  contradiction

theorem changed_opcode_rejected :
    let changed : State := {before with mem := before.mem.insert 4097 (0x09#8)}
    ¬Nonempty (X86BlockCompiler.At spec 4102 program (Cells.encode Finset.univ values) changed) := by
  let changed : State := {before with mem := before.mem.insert 4097 (0x09#8)}
  change ¬Nonempty (X86BlockCompiler.At spec 4102 program (Cells.encode Finset.univ values) changed)
  rintro ⟨candidate⟩
  have placement : candidate.origin.address.toInt = 4096 := by
    have place := candidate.placed
    rw [compiled_bytes] at place
    exact place
  have expected := candidate.loaded 1 0x21 (by rw [compiled_bytes]; rfl)
  rw [placement] at expected
  change changed.mem.get? 4097 = some (0x21#8) at expected
  have actual : changed.mem.get? 4097 = some (0x09#8) := by
    simp [changed]
  rw [actual] at expected
  contradiction
end Controls

#print axioms source_step_iff
#print axioms execute
#print axioms correct
#print axioms source_evaluate_p1
#print axioms compile_wp
#print axioms Controls.mask_then_toggle
#print axioms Controls.wrong_result_refused
#print axioms Controls.changed_opcode_rejected
end Mettapedia.Machines.TIsa.X86LogicalLibrary
