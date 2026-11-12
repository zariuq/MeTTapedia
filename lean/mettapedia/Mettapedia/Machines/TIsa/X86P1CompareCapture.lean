import Mettapedia.Machines.TIsa.X86P1TagCompare
import Mettapedia.Machines.TIsa.X86ConditionByte
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Actual p1 tag comparison composed through original fetched execution

The 15-byte CMP span in R_DERIVE_IS_PROP consists of CMP R10D,6661,
SETE R11B and MOVZX R11D,R11B. Three original fetched instructions produce
exactly the source comparison's canonical Boolean for every loaded U32
value and arbitrary old R11 contents. Memory and unrelated registers are
preserved; final flag availability is retained for later control joins.

The complete span is checked against the named p1 image and its source
instruction. Its scalar resource firing uses the existing recipe library.
The following IF, complete consumer, admission and ABI remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1CompareCapture

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def code : List Nat := [0x41,0x81,0xfa,5,0x1a,0,0,0x41,0x0f,0x94,0xc3,0x45,0x0f,0xb6,0xdb]
abbrev writes : Finset Register := {.rip,.rflags,.r11}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86ConditionByte.handlers

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 15 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 15) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by simp [position, address]

theorem position_shift (start : BitVec 48) (upper : start.toInt + 15 < (2 ^ 47 : Int))
    (offset index : Nat) (within : offset ≤ 15) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact start upper offset within]
  simp only [position, address, Nat.cast_add, Int.add_assoc]

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 15 < (2 ^ 47 : Int)
  value : BitVec 32
  old : Word
  flags : BitVec 32
  valueKnown : lookup state 10 = some (value.zeroExtend 64)
  oldKnown : lookup state 11 = some old
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends Facts state origin where
  loaded : codeLoaded state origin.address.toInt code

theorem compare_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step state after ∧ RegisterFrame {.rflags,.rip} state after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (input.value = (6661#32)) ∧
      after.regs.get? .rip = some ((position origin.address 7).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have rip : state.regs.get? .rip = some ((position origin.address 0).signExtend 64) := by
    simpa only [position_zero] using origin.rip
  let site := rebase state state origin (RegisterFrame.refl dataRegisters state) input.upper 0 (by decide) rip
  have advance : (position origin.address 3).toInt + 4 = (position origin.address 7).toInt := by
    rw [position_exact _ input.upper 3 (by decide), position_exact _ input.upper 7 (by decide)]
    omega
  have immediate : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some ((6661#32).extractLsb' (8 * index) 8) := by
    intro index within
    change state.mem.get? ((address (position origin.address 3).toInt index).signExtend 52).toNat = _
    rw [position_shift origin.address input.upper 3 index (by decide)]
    have byte : code[3 + index]? = some ((6661#32).extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded _ _ byte
  obtain ⟨output, executed, zero⟩ := X86P1TagCompare.fetched_cmp32 (handlers other extra) vector state site
    (position origin.address 7) input.value input.flags advance input.valueKnown input.flagsKnown input.quiet
    (by simpa only [site, rebase, position_zero] using input.loaded 0 0x41 (by rfl))
    (input.loaded 1 0x81 (by rfl)) (input.loaded 2 0xfa (by rfl)) immediate
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags state flags) (position origin.address 7)
  refine ⟨after, flags, executed, X86P1TagCompare.result_frame _ _ _ _, ?_,
    X86P1TagCompare.equal_sense _ _ zero, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags state flags) (position origin.address 7)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem sete_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags) (oldKnown : lookup current 11 = some input.old)
    (sense : X86BranchCondition.value .zero flags = decide (input.value = (6661#32)))
    (rip : current.regs.get? .rip = some ((position origin.address 7).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.r11,.rip} current after ∧
      lookup after 11 = some (X86ConditionByte.replaceByte input.old
        (X86ConditionByte.bitByte (decide (input.value = (6661#32))))) ∧
      after.regs.get? .rip = some ((position origin.address 11).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 7 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 10).toInt + 1 = (position origin.address 11).toInt := by
    rw [position_exact _ input.upper 10 (by decide), position_exact _ input.upper 11 (by decide)]
    omega
  have executed := X86ConditionByte.fetched_sete other extra vector current site (position origin.address 11)
    input.old flags advance oldKnown flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 7 0x41 (by rfl)) (loaded 8 0x0f (by rfl)) (loaded 9 0x94 (by rfl)) (loaded 10 0xc3 (by rfl))
  rw [sense] at executed
  let value := X86ConditionByte.replaceByte input.old (X86ConditionByte.bitByte (decide (input.value = (6661#32))))
  let after := X86Move.putPointer (put current 11 value) (position origin.address 11)
  refine ⟨after, executed, X86ConditionByte.byte_frame _ _ _, ?_, ?_⟩
  · rw [X86Move.lookup_putPointer, lookup_put_same]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem bitByte_word (condition : Bool) :
    (X86ConditionByte.bitByte condition).zeroExtend 64 = booleanWord condition := by cases condition <;> rfl

theorem movzx_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) (framed : RegisterFrame writes state current)
    (known : lookup current 11 = some (X86ConditionByte.replaceByte input.old
      (X86ConditionByte.bitByte (decide (input.value = (6661#32))))))
    (rip : current.regs.get? .rip = some ((position origin.address 11).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step current after ∧ RegisterFrame {.r11,.rip} current after ∧
      lookup after 11 = some (booleanWord (decide (input.value = (6661#32)))) ∧
      after.regs.get? .rip = some ((position origin.address 15).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 11 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 14).toInt + 1 = (position origin.address 15).toInt := by
    rw [position_exact _ input.upper 14 (by decide), position_exact _ input.upper 15 (by decide)]
    omega
  have executed := X86ConditionByte.fetched_movzx other extra vector current site (position origin.address 15)
    (X86ConditionByte.replaceByte input.old (X86ConditionByte.bitByte (decide (input.value = (6661#32)))))
    (X86ConditionByte.bitByte (decide (input.value = (6661#32)))) advance known
    (X86ConditionByte.replaceByte_low _ _) ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 11 0x45 (by rfl)) (loaded 12 0x0f (by rfl)) (loaded 13 0xb6 (by rfl)) (loaded 14 0xdb (by rfl))
  rw [bitByte_word] at executed
  let after := X86Move.putPointer (put current 11 (booleanWord (decide (input.value = (6661#32)))))
    (position origin.address 15)
  refine ⟨after, executed, X86ConditionByte.byte_frame _ _ _, ?_, ?_⟩
  · rw [X86Move.lookup_putPointer, lookup_put_same]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem observes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 10 = some (input.value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (input.value = (6661#32)))) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((position origin.address 15).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨s1, flags, step1, frame1, flags1, sense1, rip1⟩ := compare_step other extra vector state origin input
  have old1 := (frame1.lookup 11 (by decide)).trans input.oldKnown
  obtain ⟨s2, step2, frame2, byte2, rip2⟩ :=
    sete_step other extra vector state s1 origin input (frame1.mono (by decide)) flags flags1 old1 sense1 rip1
  have frame02 : RegisterFrame writes state s2 := (frame1.trans frame2).mono (by decide)
  obtain ⟨after, step3, frame3, bool3, rip3⟩ := movzx_step other extra vector state s2 origin input frame02 byte2 rip2
  have finalFrame : RegisterFrame writes state after := (frame02.trans frame3).mono (by decide)
  exact ⟨after, flags, X86FuelPrefix.fetches_cons 2 state s1 after step1
    (X86FuelPrefix.fetches_cons 1 s1 s2 after step2 (X86FuelPrefix.fetches_one s2 after step3)), finalFrame,
    (finalFrame.lookup 10 (by decide)).trans input.valueKnown, bool3,
    (frame3.registers .rflags (by decide)).trans ((frame2.registers .rflags (by decide)).trans flags1), rip3⟩

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 10 = some (input.value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (input.value = (6661#32)))) ∧
      after.regs.get? .rip = some ((position origin.address 15).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, valueRead, boolRead, _, rip⟩ := observes other extra vector state origin input
  exact ⟨after, executed, framed, valueRead, boolRead, rip⟩

def sourceInstruction : P1Source.Instr := .compare .equal .u32z 7 6 (.immediate 6661)

theorem source_instruction : X86P1LoadCapture.propImage.source.body.atPath [0, 1] =
    some (.instruction sourceInstruction) := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 52 && span.length == 15 && span.kind == "CMP" && span.path == some [0, 1]) = true := by
  kernel_reflexivity

theorem captured_bytes (index : Fin 15) :
    X86P1LoadCapture.propImage.view.read (52 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 52)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 15 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 15 at bounded
    exact bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (52 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (52 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 52) (offset : Nat) :
    position start offset = address base (52 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 52)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 10 = some (facts.value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (facts.value = (6661#32)))) ∧
      after.regs.get? .rip = some ((address base 67).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : Inputs state origin := ⟨facts, captured_loaded state base origin placed loaded⟩
  obtain ⟨after, executed, framed, valueRead, boolRead, rip⟩ := executes other extra vector state origin input
  refine ⟨after, executed, framed, valueRead, boolRead, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 15] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem source_value (value : BitVec 32) :
    P1Scalar.evaluate sourceInstruction [value.zeroExtend 64] =
      some (booleanWord (decide (value = (6661#32)))) := by
  have low : low32 (value.zeroExtend 64) = value := low32_extend32 false value
  change some (booleanWord (low32 (value.zeroExtend 64) == low32 (6661#64))) = _
  rw [low]
  change some (booleanWord (value == (6661#32))) = _
  by_cases same : value = (6661#32)
  · simp [same]
  · rw [show (value == (6661#32)) = false from beq_eq_false_iff_ne.mpr same]
    simp [same]

theorem resource_step (keys : Finset P1Source.Reg) (before : P1Source.Reg → Word) (value : BitVec 32)
    (included : (P1Scalar.recipe sourceInstruction 7).support ⊆ keys)
    (valueRead : before 6 = value.zeroExtend 64) :
    (CellEffects.profile [P1Scalar.recipe sourceInstruction 7]).theory.rewrites (Cells.encode keys before)
      (Cells.encode keys (Function.update before 7 (booleanWord (decide (value = (6661#32)))))) := by
  apply (P1Scalar.rewrite_iff sourceInstruction 7 keys before _).mpr
  refine ⟨_, included, ?_, rfl⟩
  change P1Scalar.evaluate sourceInstruction [before 6] = _
  rw [valueRead, source_value]

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 15).map (fun index => (4096 + index, BitVec.ofNat 8 ((code[index]?).getD 0)))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (value : BitVec 32) (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 (value.zeroExtend 64)
  let registers := registers.insert .r11 old
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 15) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
  interval_cases offset <;> decide

private theorem image (value : BitVec 32) (old : Word) : codeLoaded (before value old) 4096 code := by
  intro index byte present
  have within : index < 15 := by
    have within := (List.getElem?_eq_some_iff.mp present).1
    change index < 15 at within
    exact within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def origin (value : BitVec 32) (old : Word) : X86LegacyFetch.Basis (before value old) where
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

private def input (value : BitVec 32) (old : Word) : Inputs (before value old) (origin value old) where
  upper := by change (4096#48).toInt + 15 < (2 ^ 47 : Int); decide
  value := value
  old := old
  flags := 0x200#32
  valueKnown := by
    change ((before value old).regs.get? .r10).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  oldKnown := by
    change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  loaded := image value old

private theorem input_value (value : BitVec 32) (old : Word) : (input value old).value = value := rfl
private theorem origin_address (value : BitVec 32) (old : Word) : (origin value old).address = (4096#48) := rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : BitVec 32) (old : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before value old) = .ok () after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (value = (6661#32)))) ∧
      after.regs.get? .rip = some (4111#64) ∧ after.mem = (before value old).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, framed, valueRead, boolRead, rip⟩ := executes other extra vector _ _ (input value old)
  have next : ((position (origin value old).address 15).signExtend 64) = (4111#64) := by
    rw [origin_address]
    rfl
  rw [next] at rip
  refine ⟨after, executed, ?_, ?_, rip, framed.memory⟩
  · simpa only [input_value] using valueRead
  · have sameResult : booleanWord (decide ((input value old).value = (6661#32))) =
        booleanWord (decide (value = (6661#32))) := by
      apply congrArg booleanWord
      exact decide_eq_decide.mpr (by rw [input_value])
    exact boolRead.trans (congrArg some sameResult)

theorem matching_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before (6661#32) (0xfedcba9876543210#64)) = .ok () after ∧
      lookup after 10 = some (6661#64) ∧ lookup after 11 = some (1#64) ∧
      after.regs.get? .rip = some (4111#64) ∧ after.mem = (before (6661#32) (0xfedcba9876543210#64)).mem := by
  simpa [booleanWord] using control other extra vector (6661#32) (0xfedcba9876543210#64)

theorem different_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before (6660#32) (0xffffffffffffffff#64)) = .ok () after ∧
      lookup after 10 = some (6660#64) ∧ lookup after 11 = some (0#64) ∧
      after.regs.get? .rip = some (4111#64) ∧ after.mem = (before (6660#32) (0xffffffffffffffff#64)).mem := by
  simpa [booleanWord] using control other extra vector (6660#32) (0xffffffffffffffff#64)

end Controls

end Mettapedia.Machines.TIsa.X86P1CompareCapture
