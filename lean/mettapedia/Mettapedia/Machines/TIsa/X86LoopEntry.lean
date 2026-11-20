import Mettapedia.Machines.TIsa.X86Immediate32
import Mettapedia.Machines.TIsa.X86Zero32
import Mettapedia.Machines.TIsa.X86CapGate
import Mettapedia.Machines.TIsa.X86Conditional
import Mettapedia.Machines.TIsa.Loop

/-!
# Native cap validation and initialization of the existing loop entry

The eighteen-byte REX form loads a 32-bit cap into R14, compares the retained
64-bit bound, branches on strict unsigned excess, and otherwise zeroes the
counter. Three fetched instructions reach the rejection target with the old
counter; four reach the header with counter zero. Memory, the bound and all
registers outside the declared scratch/counter/flags/RIP frame are preserved.

The source join fires the existing guarded control/counter recipe. Excess
bounds admit no such firing. This introduces no Boolean data resource or
independent control machine. REX-form layout, canonical addresses and physical
register separation are explicit premises. The rejection handler, metering,
whole loop and public wrapper remain separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LoopEntry
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86CapGate.handlers (X86FrameStore.linkedHandlers other) extra

def code (index bound : Fin 16) (cap displacement : BitVec 32) : List Nat :=
  X86Immediate32.code 14 cap ++ (X86CapGate.code bound 14 displacement ++ X86Zero32.code index)

theorem code_length (index bound : Fin 16) (cap displacement : BitVec 32) :
    (code index bound cap displacement).length = 18 := by
  simp [code,X86Immediate32.code_length,X86CapGate.code_length,X86Zero32.code]

def writes (index : Fin 16) : Finset Register := {key index,key 14,.rflags,.rip}

theorem writes_data (index : Fin 16) : writes index ⊆ dataRegisters := by
  intro register member
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact data_key index
  · exact data_key 14
  · decide
  · decide

theorem first_frame_subset (index : Fin 16) : X86Immediate32.writes 14 ∪ X86CapGate.writes ⊆ writes index := by
  intro register member
  simp only [X86Immediate32.writes,X86CapGate.writes,X86BranchGate.writes,writes,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at member ⊢
  tauto

theorem last_frame_subset (index : Fin 16) : writes index ∪ X86Zero32.writes index ⊆ writes index := by
  intro register member
  simp only [X86Zero32.writes,writes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at member ⊢
  tauto

theorem immediate_byte (index bound : Fin 16) (cap displacement : BitVec 32) (offset byte : Nat)
    (present : (X86Immediate32.code 14 cap)[offset]? = some byte) :
    (code index bound cap displacement)[offset]? = some byte := by
  rw [code,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem gate_byte (index bound : Fin 16) (cap displacement : BitVec 32) (offset byte : Nat)
    (present : (X86CapGate.code bound 14 displacement)[offset]? = some byte) :
    (code index bound cap displacement)[6 + offset]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86Immediate32.code_length]; omega),X86Immediate32.code_length,
    Nat.add_sub_cancel_left,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem zero_byte (index bound : Fin 16) (cap displacement : BitVec 32) (offset byte : Nat)
    (present : (X86Zero32.code index)[offset]? = some byte) :
    (code index bound cap displacement)[15 + offset]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86Immediate32.code_length]; omega),X86Immediate32.code_length]
  rw [show 15 + offset - 6 = 9 + offset by omega,
    List.getElem?_append_right (by rw [X86CapGate.code_length]; omega),X86CapGate.code_length,Nat.add_sub_cancel_left]
  exact present

structure Inputs (native : State) (index bound : Fin 16) extends X86LegacyFetch.Basis native where
  indexValue : Word
  boundValue : Word
  cap : BitVec 32
  flags : BitVec 32
  indexKnown : lookup native index = some indexValue
  boundKnown : lookup native bound = some boundValue
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  separateIndex : index ≠ 14
  separateBound : bound ≠ 14
  distinct : index ≠ bound
  upper : address.toInt + 18 < (2 ^ 47 : Int)
  displacement : BitVec 32
  target : BitVec 48
  jump : target.toInt = address.toInt + 15 + displacement.toInt
  loaded : codeLoaded native address.toInt (code index bound cap displacement)

def position {native : State} {index bound : Fin 16} (input : Inputs native index bound) (offset : Nat) : BitVec 48 :=
  address input.address.toInt offset

theorem position_exact {native : State} {index bound : Fin 16} (input : Inputs native index bound)
    (offset : Nat) (within : offset ≤ 18) :
    (position input offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem address_shift (base : Int) (first second : Nat) :
    address (base + first) second = address base (first + second) := by
  simp only [address,Int.natCast_add,Int.add_assoc]

theorem immediate_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run native = .ok () after ∧
      RegisterFrame (X86Immediate32.writes 14) native after ∧ lookup after 14 = some (input.cap.zeroExtend 64) ∧
      after.regs.get? .rip = some ((position input 6).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared : X86Immediate32.Inputs native 14 input.cap := {
    input.toBasis with
    quiet := input.quiet
    upper := by have := input.upper; omega
    loaded := fun offset byte present => input.loaded offset byte (immediate_byte index bound input.cap input.displacement offset byte present) }
  exact X86Immediate32.executes (handlers other extra) vector native 14 input.cap prepared

theorem gate_step_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (writes index) native after ∧ lookup after index = some input.indexValue ∧
      lookup after bound = some input.boundValue ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.cap.toNat < input.boundValue.toNat then input.target else position input 15).signExtend 64) ∧
      X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 3, ∃ reached, (X86FuelPrefix.fetches count).run native = .ok () reached ∧
        RegisterFrame (writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,first,firstFrame,capKnown,firstRip⟩ := immediate_step other extra vector native index bound input
  have firstData := firstFrame.mono (X86Immediate32.writes_data 14)
  have firstLoaded := firstFrame.code_preserved input.address.toInt _ input.loaded
  let gateOrigin := rebase native middle input.toBasis firstData input.upper 6 (by decide) firstRip
  have at6 : gateOrigin.address.toInt = input.address.toInt + 6 := position_exact input 6 (by decide)
  let gateInput : X86CapGate.Inputs middle bound 14 := {
    gateOrigin with
    indexValue := input.boundValue
    boundValue := input.cap.zeroExtend 64
    flags := input.flags
    indexKnown := (firstFrame.lookup bound (by
      simp only [X86Immediate32.writes,Finset.mem_insert,Finset.mem_singleton]
      exact not_or.mpr ⟨fun same => input.separateBound (key_injective same),by fin_cases bound <;> decide⟩)).trans input.boundKnown
    boundKnown := capKnown
    flagsKnown := (firstFrame.registers .rflags (by decide)).trans input.flagsKnown
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans input.quiet
    upper := by rw [at6]; have := input.upper; omega
    displacement := input.displacement
    target := input.target
    jump := by rw [at6]; have := input.jump; omega
    loaded := by
      rw [at6]
      exact X86Conditional.loaded_slice middle input.address.toInt (code index bound input.cap input.displacement)
        (X86CapGate.code bound 14 input.displacement) 6 firstLoaded (gate_byte index bound input.cap input.displacement) }
  obtain ⟨tested,testFlags,gateRun,gateFrame,_,boundKnown,flagsKnown,gateRip,gateControl⟩ :=
    X86CapGate.executes_control (X86FrameStore.linkedHandlers other) extra vector middle bound 14 gateInput
  have capNat : (input.cap.zeroExtend 64).toNat = input.cap.toNat := by
    simp
    have := input.cap.isLt
    omega
  change tested.regs.get? .rip = some ((if (input.cap.zeroExtend 64).toNat < input.boundValue.toNat
    then input.target else X86CapGate.position gateInput 9).signExtend 64) at gateRip
  rw [capNat] at gateRip
  have testedFrame : RegisterFrame (writes index) native tested :=
    (firstFrame.trans gateFrame).mono (first_frame_subset index)
  have indexKnown : lookup tested index = some input.indexValue := by
    rw [gateFrame.lookup index (by fin_cases index <;> decide),firstFrame.lookup index (by
      simp only [X86Immediate32.writes,Finset.mem_insert,Finset.mem_singleton]
      exact not_or.mpr ⟨fun same => input.separateIndex (key_injective same),by fin_cases index <;> decide⟩)]
    exact input.indexKnown
  have boundRead : lookup tested bound = some input.boundValue := by
    rw [gateFrame.lookup bound (by fin_cases bound <;> decide)]
    exact gateInput.indexKnown
  have fallthrough : X86CapGate.position gateInput 9 = position input 15 := by
    change address gateOrigin.address.toInt 9 = address input.address.toInt 15
    rw [at6]
    exact address_shift input.address.toInt 6 9
  rw [fallthrough] at gateRip
  have three := X86FuelPrefix.fetches_then 1 2 native middle tested first gateRun
  refine ⟨tested,testFlags,three,testedFrame,indexKnown,boundRead,flagsKnown,gateRip,
    (X86ControlFlags.of_register_frame firstFrame (by decide)).trans gateControl,?_⟩
  intro count within
  interval_cases count
  · exact ⟨native,X86FuelPrefix.fetches_zero native,RegisterFrame.refl _ _⟩
  · exact ⟨middle,first,firstFrame.mono (fun register member =>
      first_frame_subset index (Finset.mem_union_left _ member))⟩
  · obtain ⟨reached,run,frame⟩ := X86CapGate.prefix_frame (X86FrameStore.linkedHandlers other) extra vector
      middle bound 14 gateInput 1 (by decide)
    exact ⟨reached,X86FuelPrefix.fetches_then 1 1 native middle reached first run,
      (firstFrame.trans frame).mono (first_frame_subset index)⟩
  · exact ⟨tested,three,testedFrame⟩

theorem gate_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (writes index) native after ∧ lookup after index = some input.indexValue ∧
      lookup after bound = some input.boundValue ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.cap.toNat < input.boundValue.toNat then input.target else position input 15).signExtend 64) ∧
      ∀ count ≤ 3, ∃ reached, (X86FuelPrefix.fetches count).run native = .ok () reached ∧
        RegisterFrame (writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip,_control,prefixes⟩ := gate_step_control other extra vector native index bound input
  exact ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip,prefixes⟩


theorem executes_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (if input.boundValue.toNat ≤ input.cap.toNat then 4 else 3)).run native = .ok () after ∧
      RegisterFrame (writes index) native after ∧
      lookup after index = some (if input.boundValue.toNat ≤ input.cap.toNat then (0#64) else input.indexValue) ∧
      lookup after bound = some input.boundValue ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.boundValue.toNat ≤ input.cap.toNat then position input 18 else input.target).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨tested,testFlags,gateRun,testedFrame,indexKnown,boundRead,flagsKnown,gateRip,gateControl,_⟩ :=
    gate_step_control other extra vector native index bound input
  by_cases admitted : input.boundValue.toNat ≤ input.cap.toNat
  · have testedRip : tested.regs.get? .rip = some ((position input 15).signExtend 64) := by
      rw [if_neg (by omega : ¬input.cap.toNat < input.boundValue.toNat)] at gateRip
      exact gateRip
    let zeroOrigin := rebase native tested input.toBasis (testedFrame.mono (writes_data index)) input.upper 15 (by decide) testedRip
    have at15 : zeroOrigin.address.toInt = input.address.toInt + 15 := position_exact input 15 (by decide)
    let zeroInput : X86Zero32.Inputs tested index := {
      zeroOrigin with
      value := input.indexValue
      flags := testFlags
      valueKnown := indexKnown
      flagsKnown := flagsKnown
      quiet := (testedFrame.registers .log_register_writes (by fin_cases index <;> decide)).trans input.quiet
      upper := by rw [at15]; have := input.upper; omega
      loaded := by
        rw [at15]
        exact X86Conditional.loaded_slice tested input.address.toInt (code index bound input.cap input.displacement)
          (X86Zero32.code index) 15 (testedFrame.code_preserved _ _ input.loaded) (zero_byte index bound input.cap input.displacement) }
    obtain ⟨after,finalFlags,zeroRun,zeroFrame,zeroKnown,finalFlagsKnown,zeroRip,zeroControl⟩ :=
      X86Zero32.executes_control (handlers other extra) vector tested index zeroInput
    have finalFrame : RegisterFrame (writes index) native after :=
      (testedFrame.trans zeroFrame).mono (last_frame_subset index)
    refine ⟨after,finalFlags,?_,finalFrame,by simpa only [if_pos admitted] using zeroKnown,?_,finalFlagsKnown,?_,?_⟩
    · simp only [if_pos admitted]
      exact X86FuelPrefix.fetches_then 3 1 native tested after gateRun zeroRun
    · rw [zeroFrame.lookup bound (by
        simp only [X86Zero32.writes,Finset.mem_insert,Finset.mem_singleton]
        exact not_or.mpr ⟨fun same => input.distinct (key_injective same).symm,not_or.mpr ⟨by fin_cases bound <;> decide,by fin_cases bound <;> decide⟩⟩)]
      exact boundRead
    · have lastAddress : address zeroInput.address.toInt 3 = position input 18 := by
        change address zeroOrigin.address.toInt 3 = address input.address.toInt 18
        rw [at15]
        exact address_shift input.address.toInt 15 3
      simpa only [if_pos admitted,lastAddress] using zeroRip
    · exact gateControl.trans zeroControl
  · refine ⟨tested,testFlags,?_,testedFrame,by simpa only [if_neg admitted] using indexKnown,boundRead,flagsKnown,?_,gateControl⟩
    · simpa only [if_neg admitted] using gateRun
    · rw [if_pos (by omega : input.cap.toNat < input.boundValue.toNat)] at gateRip
      simpa only [if_neg admitted] using gateRip
theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (if input.boundValue.toNat ≤ input.cap.toNat then 4 else 3)).run native = .ok () after ∧
      RegisterFrame (writes index) native after ∧
      lookup after index = some (if input.boundValue.toNat ≤ input.cap.toNat then (0#64) else input.indexValue) ∧
      lookup after bound = some input.boundValue ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.boundValue.toNat ≤ input.cap.toNat then position input 18 else input.target).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip,_control⟩ := executes_control other extra vector native index bound input
  exact ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip⟩


theorem prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound)
    (count : Nat) (within : count ≤ (if input.boundValue.toNat ≤ input.cap.toNat then 4 else 3)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches count).run native = .ok () after ∧ RegisterFrame (writes index) native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases short : count ≤ 3
  · obtain ⟨_,_,_,_,_,_,_,_,prefixes⟩ := gate_step other extra vector native index bound input
    exact prefixes count short
  · have admitted : input.boundValue.toNat ≤ input.cap.toNat := by split_ifs at within <;> omega
    have four : count = 4 := by rw [if_pos admitted] at within; omega
    obtain ⟨after,_,run,frame,_⟩ := executes other extra vector native index bound input
    exact ⟨after,by simpa only [four,if_pos admitted] using run,frame⟩

theorem realizes_entry_cells {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound)
    (loop : Control.Loop Key) (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : loop.entry.support ⊆ keys) (checked : loop.check = true)
    (current : before (.inl loop.activation) = loop.entryPoint)
    (boundRead : before (.inr loop.bound) = input.boundValue)
    (maximum : loop.maximum = input.cap.toNat)
    (bounded : input.boundValue.toNat ≤ input.cap.toNat)
    (header : loop.headerPoint = (position input 18).signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ invocation : CellEffects.Invocation loop.entry,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation = Cells.encode keys (loop.entryValues before) ∧
      (X86FuelPrefix.fetches 4).run native = .ok () after ∧ RegisterFrame (writes index) native after ∧
      lookup after index = some (loop.entryValues before (.inr loop.index)) ∧
      lookup after bound = some (loop.entryValues before (.inr loop.bound)) ∧
      after.regs.get? .rip = some (loop.entryValues before (.inl loop.activation)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨invocation,enabled,fired⟩ := loop.entry_realized keys before included checked current
    (by simpa only [boundRead,maximum] using bounded)
  obtain ⟨after,_,run,framed,indexKnown,boundKnown,_,rip⟩ := executes other extra vector native index bound input
  have distinct : loop.bound ≠ loop.index := Ne.symm (of_decide_eq_true checked).1
  refine ⟨after,invocation,enabled,fired,by simpa only [if_pos bounded] using run,framed,?_,?_,?_⟩
  · simpa [bounded,Control.Loop.entryValues] using indexKnown
  · simpa [Control.Loop.entryValues,distinct,boundRead] using boundKnown
  · simpa [Control.Loop.entryValues,header,bounded] using rip

theorem rejects_entry_guard {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound)
    (loop : Control.Loop Key) (before : Control.Location Key → Word)
    (boundRead : before (.inr loop.bound) = input.boundValue) (maximum : loop.maximum = input.cap.toNat)
    (excess : input.cap.toNat < input.boundValue.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run native = .ok () after ∧ RegisterFrame (writes index) native after ∧
      lookup after index = some input.indexValue ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rip = some (input.target.signExtend 64) ∧
      ∀ sourceAfter, loop.entry.guard (loop.entry.inputs.map before) (loop.entry.outputs.map sourceAfter) ≠ true := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have refused : ¬input.boundValue.toNat ≤ input.cap.toNat := by omega
  obtain ⟨after,_,run,framed,indexKnown,boundKnown,_,rip⟩ := executes other extra vector native index bound input
  refine ⟨after,by simpa only [if_neg refused] using run,framed,
    by simpa only [if_neg refused] using indexKnown,boundKnown,by simpa only [if_neg refused] using rip,?_⟩
  intro sourceAfter
  exact loop.entry_refuses_excess before sourceAfter (by simpa only [maximum,boundRead] using excess)

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 18).map fun offset => (4096 + offset,BitVec.ofNat 8 (((code 10 9 (32#32) (788#32))[offset]?).getD 0))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private noncomputable def before (index bound : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 index
  let registers := registers.insert .r9 bound
  let registers := registers.insert .r14 (0xdeadbeefbadcaffe#64)
  let registers := registers.insert .rsp (8192#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private theorem image (index bound : Word) : codeLoaded (before index bound) 4096 (code 10 9 (32#32) (788#32)) := by
  intro offset byte present
  have within : offset < 18 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
  have point : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide
  have member : (4096 + offset,BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def input (index bound : Word) : Inputs (before index bound) 10 9 where
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
  indexValue := index
  boundValue := bound
  cap := 32#32
  flags := 0x246#32
  indexKnown := by simp [lookup,before,key,Std.ExtDHashMap.get?_insert]; rfl
  boundKnown := by simp [lookup,before,key,Std.ExtDHashMap.get?_insert]; rfl
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  separateIndex := by decide
  separateBound := by decide
  distinct := by decide
  upper := by decide
  displacement := 788#32
  target := 4899#48
  jump := by decide
  loaded := image index bound

theorem outcome (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index bound : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if bound.toNat ≤ 32 then 4 else 3)).run (before index bound) = .ok () after ∧
      RegisterFrame (writes 10) (before index bound) after ∧
      lookup after 10 = some (if bound.toNat ≤ 32 then (0#64) else index) ∧
      lookup after 9 = some bound ∧ after.regs.get? .rip = some (if bound.toNat ≤ 32 then (4114#64) else (4899#64)) := by
  obtain ⟨after,_,run,frame,indexRead,boundRead,_,rip⟩ := executes other extra vector _ 10 9 (input index bound)
  refine ⟨after,run,frame,indexRead,boundRead,?_⟩
  by_cases admitted : bound.toNat ≤ 32 <;> simpa [admitted,input,position,address] using rip

theorem every_prefix_preserves_stack_memory (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (index bound : Word) (count : Nat)
    (within : count ≤ (if bound.toNat ≤ 32 then 4 else 3)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches count).run (before index bound) = .ok () after ∧
      after.mem = (before index bound).mem ∧ after.regs.get? .rsp = some (8192#64) := by
  obtain ⟨after,run,frame⟩ := prefix_frame other extra vector _ 10 9 (input index bound) count within
  refine ⟨after,run,frame.memory,?_⟩
  rw [frame.registers .rsp (by decide)]
  simp [before,Std.ExtDHashMap.get?_insert]

private noncomputable def changed : State := { before 77 32 with mem := (before 77 32).mem.insert 4106 (0x83#8) }

theorem changed_condition_rejected : ¬codeLoaded changed 4096 (code 10 9 (32#32) (788#32)) := by
  intro loaded
  have wrong := loaded 10 0x87 (by decide)
  simp [changed,address] at wrong

example : code 10 9 (32#32) (788#32) =
    [0x41,0xbe,0x20,0,0,0,0x4d,0x39,0xf1,0x0f,0x87,0x14,3,0,0,0x45,0x31,0xd2] := by decide
example : (0#64).toNat ≤ 32 := by decide
example : (32#64).toNat ≤ 32 := by decide
example : ¬(33#64).toNat ≤ 32 := by decide
example : ¬(0x100000000#64).toNat ≤ 32 := by decide

end Controls
end Mettapedia.Machines.TIsa.X86LoopEntry
