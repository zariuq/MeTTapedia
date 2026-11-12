import Mettapedia.Machines.TIsa.X86P1CompareCapture

/-!
# Actual p1 IF and the joined LOAD/comparison/control prefix

Two original fetched instructions execute TEST R11,R11 and near JZ in the
nine-byte IF span at image offset 67. The zero case reaches offset 569;
the nonzero case falls through to 76. Source branch correctness requires
a canonical Boolean, supplied by the preceding comparison.

The actual-image five-instruction comparison/IF join retains its source
condition and frame. The thirteen-instruction prefix also joins the complete
first LOAD, exposing its flags rather than assuming a clobbered field exists.
Memory and the full image are preserved. This ends before either branch body;
the complete consumer, admission and ABI are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1IfCapture

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def code : List Nat := [0x4d,0x85,0xdb,0x0f,0x84,0xed,1,0,0]
abbrev writes : Finset Register := {.rflags,.rip}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86ConditionByte.handlers (X86Arithmetic.linkedHandlers other) extra

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 579 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 579) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by simp [position, address]

theorem position_shift (start : BitVec 48) (upper : start.toInt + 579 < (2 ^ 47 : Int))
    (offset index : Nat) (within : offset ≤ 579) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact start upper offset within]
  simp only [position, address, Nat.cast_add, Int.add_assoc]

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 579 < (2 ^ 47 : Int)
  value : Word
  flags : BitVec 32
  valueKnown : lookup state 11 = some value
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends Facts state origin where
  loaded : codeLoaded state origin.address.toInt code

theorem test_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step state after ∧ RegisterFrame writes state after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (input.value = (0#64)) ∧
      after.regs.get? .rip = some ((position origin.address 3).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have rip : state.regs.get? .rip = some ((position origin.address 0).signExtend 64) := by
    simpa only [position_zero] using origin.rip
  let site := windowAt state state origin (RegisterFrame.refl dataRegisters state) input.upper 0 (by decide) rip
    code input.loaded 11 11 (0x85#8) (by rfl) (by rfl) (by rfl)
  obtain ⟨output, executed, _, zero⟩ := X86Comparison.fetched_test64 (handlers other extra) vector state 11 11 site
    input.value input.value input.flags input.valueKnown input.valueKnown input.flagsKnown input.quiet
  let flags := X86LogicalFlags.merged input.flags output (0#1)
  let after := X86Move.putPointer (X86Flags.putFlags state flags) site.next
  refine ⟨after, flags, executed, X86Comparison.status_frame _ _ _, ?_, ?_, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags state flags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · have zeroFinal := (X86LogicalFlags.merged_zero input.flags output (0#1)).trans zero
    simp only [BitVec.and_self] at zeroFinal
    have zeroEq : input.value.toNat = 0 ↔ input.value = (0#64) := by
      change input.value.toNat = (0#64).toNat ↔ _
      exact BitVec.toNat_inj
    simp only [flags, X86BranchCondition.value, zeroFinal, X86BranchCondition.zero_sense, zeroEq]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 11 = some input.value ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if input.value = (0#64) then position origin.address 502
        else position origin.address 9).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, flagsRead, sense, middleRip⟩ := test_step other extra vector state origin input
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have step1 : (position origin.address 3).toInt + 1 = (position origin.address 4).toInt := by
    rw [position_exact _ input.upper 3 (by decide), position_exact _ input.upper 4 (by decide)]
    omega
  have step2 : (position origin.address 4).toInt + 1 = (position origin.address 5).toInt := by
    rw [position_exact _ input.upper 4 (by decide), position_exact _ input.upper 5 (by decide)]
    omega
  have advance : (position origin.address 5).toInt + 4 = (position origin.address 9).toInt := by
    rw [position_exact _ input.upper 5 (by decide), position_exact _ input.upper 9 (by decide)]
    omega
  have jump : (position origin.address 502).toInt = (position origin.address 9).toInt + (493#32).toInt := by
    rw [position_exact _ input.upper 502 (by decide), position_exact _ input.upper 9 (by decide)]
    change origin.address.toInt + 502 = origin.address.toInt + 9 + 493
    omega
  have displacement : ∀ index < 4,
      middle.mem.get? ((address (position origin.address 5).toInt index).signExtend 52).toNat =
        some ((493#32).extractLsb' (8 * index) 8) := by
    intro index within
    rw [position_shift _ input.upper 5 index (by decide)]
    have byte : code[5 + index]? = some ((493#32).extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ byte
  have last := X86EscapeFetch.fetched_branch (X86FrameIncrement.linkedHandlers (X86Arithmetic.linkedHandlers other))
    (X86ConditionByte.byteHandlers extra) vector .zero middle (position origin.address 3) (position origin.address 4)
    (position origin.address 5) (position origin.address 9) (position origin.address 502)
    origin.control origin.attributes flags (493#32) step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans origin.status)
    ((framed.registers .fault_reg (by decide)).trans origin.fault)
    ((framed.registers .msrs (by decide)).trans origin.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans origin.segments)
    origin.longMode origin.codeMode ((framed.registers .app_view (by decide)).trans origin.application)
    middleRip flagsRead ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 3 0x0f (by rfl)) (loaded 4 0x84 (by rfl)) displacement
  rw [sense] at last
  let target := if decide (input.value = (0#64)) then position origin.address 502 else position origin.address 9
  let after := X86Move.putPointer middle target
  have lastFrame := pointer_frame middle target
  refine ⟨after, flags, X86FuelPrefix.fetches_cons 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last), (framed.trans lastFrame).mono (by decide),
    (lastFrame.lookup 11 (by decide)).trans ((framed.lookup 11 (by decide)).trans input.valueKnown),
    (lastFrame.registers .rflags (by decide)).trans flagsRead, ?_⟩
  simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
  simp only [target, decide_eq_true_eq]

theorem source_condition :
    (X86P1LoadCapture.propImage.source.body.atPath [1]).bind (fun statement => match statement with
      | .branch condition _ _ => some condition
      | _ => none) = some 7 := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 67 && span.length == 9 && span.kind == "IF" && span.path == some [1]) = true := by
  kernel_reflexivity

theorem captured_bytes (index : Fin 9) :
    X86P1LoadCapture.propImage.view.read (67 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 67)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 9 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 9 at bounded
    exact bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (67 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (67 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 67) (offset : Nat) :
    position start offset = address base (67 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (facts : Facts state origin)
    (placed : origin.address.toInt = base + 67)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 11 = some facts.value ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if facts.value = (0#64) then address base 569 else address base 76).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : Inputs state origin := ⟨facts, captured_loaded state base origin placed loaded⟩
  obtain ⟨after, flags, executed, framed, valueRead, flagsRead, rip⟩ := executes other extra vector state origin input
  refine ⟨after, flags, executed, framed, valueRead, flagsRead, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 502, position_in_image origin.address base placed 9] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem compare_then_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1CompareCapture.Facts state origin) (placed : origin.address.toInt = base + 52)
    (imageUpper : base + 646 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      RegisterFrame X86P1CompareCapture.writes state after ∧
      lookup after 10 = some (facts.value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (facts.value = (6661#32)))) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if facts.value = (6661#32) then address base 76 else address base 569).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : X86P1CompareCapture.Inputs state origin :=
    ⟨facts, X86P1CompareCapture.captured_loaded state base origin placed loaded⟩
  obtain ⟨middle, firstFlags, first, firstFrame, _, boolRead, firstFlagsRead, firstRip⟩ :=
    X86P1CompareCapture.observes (X86Arithmetic.linkedHandlers other) extra vector state origin input
  have extent : origin.address.toInt + 594 < (2 ^ 47 : Int) := by omega
  let nextOrigin := rebase state middle origin (firstFrame.mono X86P1CompareCapture.writes_data)
    extent 15 (by decide) firstRip
  have nextPlaced : nextOrigin.address.toInt = base + 67 := by
    change (address origin.address.toInt 15).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) extent 15 (by decide)]
    omega
  have middleImage : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage middle base := by
    intro offset within
    rw [firstFrame.memory]
    exact loaded offset within
  let nextFacts : Facts middle nextOrigin := {
    upper := by rw [nextPlaced]; omega
    value := booleanWord (decide (facts.value = (6661#32)))
    flags := firstFlags
    valueKnown := boolRead
    flagsKnown := firstFlagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, flags, last, lastFrame, finalBool, finalFlags, rip, image⟩ :=
    captured_executes other extra vector middle base nextOrigin nextFacts nextPlaced middleImage
  have finalFrame : RegisterFrame X86P1CompareCapture.writes state after :=
    (firstFrame.trans lastFrame).mono (by decide)
  refine ⟨after, flags, X86FuelPrefix.fetches_then 3 2 state middle after first last, finalFrame,
    (finalFrame.lookup 10 (by decide)).trans facts.valueKnown, finalBool, finalFlags, ?_, image⟩
  change after.regs.get? .rip = some
    ((if booleanWord (decide (facts.value = (6661#32))) = (0#64) then address base 569
      else address base 76).signExtend 64) at rip
  by_cases same : facts.value = (6661#32)
  · have resultValue : booleanWord (decide (facts.value = (6661#32))) = (1#64) := by
      rw [show decide (facts.value = (6661#32)) = true from decide_eq_true same]
      rfl
    rw [resultValue] at rip
    simpa only [show (1#64) ≠ (0#64) from by decide, if_neg, ite_false, if_pos same] using rip
  · have resultValue : booleanWord (decide (facts.value = (6661#32))) = (0#64) := by
      rw [show decide (facts.value = (6661#32)) = false from decide_eq_false_iff_not.mpr same]
      rfl
    rw [resultValue, if_pos rfl] at rip
    simpa only [if_neg same] using rip

theorem common_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1LoadBounds.handlers other (X86ConditionByte.byteHandlers extra) =
      handlers (X86Funding.Placed.baseHandlers other) extra := by rfl

theorem load_compare_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin) (placed : origin.address.toInt = base + 9)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (old : Word) (oldKnown : lookup state 11 = some old) :
    letI : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 13).run state = .ok () after ∧
      RegisterFrame {.rip,.rflags,.r14,.r15,.r10,.r11} state after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (value = (6661#32)))) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if value = (6661#32) then address base 76 else address base 569).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  let input : X86P1LoadBounds.Inputs state origin :=
    ⟨facts, X86P1LoadCapture.span_loaded state base origin placed loaded⟩
  obtain ⟨middle, loadFlags, first, firstFrame, valueRead, loadFlagsRead, firstRip⟩ :=
    X86P1LoadBounds.load_observes other (X86ConditionByte.byteHandlers extra) vector state origin input value readable fits
  rw [common_handlers] at first
  have firstData : DataFrame state middle := firstFrame.mono (by decide)
  let cmpOrigin := rebase state middle origin firstData facts.upper 43 (by decide) firstRip
  have cmpPlaced : cmpOrigin.address.toInt = base + 52 := by
    change (address origin.address.toInt 43).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) facts.upper 43 (by decide)]
    omega
  have middleImage : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage middle base := by
    intro offset within
    rw [firstFrame.memory]
    exact loaded offset within
  let cmpFacts : X86P1CompareCapture.Facts middle cmpOrigin := {
    upper := by rw [cmpPlaced]; have := facts.upper; omega
    value := value
    old := old
    flags := loadFlags
    valueKnown := valueRead
    oldKnown := (firstFrame.lookup 11 (by decide)).trans oldKnown
    flagsKnown := loadFlagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, flags, last, lastFrame, finalValue, finalBool, finalFlags, rip, image⟩ :=
    compare_then_if (X86Funding.Placed.baseHandlers other) extra vector middle base cmpOrigin cmpFacts cmpPlaced
      (by have := facts.upper; omega) middleImage
  exact ⟨after, flags, X86FuelPrefix.fetches_then 8 5 state middle after first last,
    (firstFrame.trans lastFrame).mono (by decide), finalValue, finalBool, finalFlags, rip, image⟩

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map (fun index => (4096 + index, BitVec.ofNat 8 ((code[index]?).getD 0)))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r11 value
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 9) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide

private theorem image (value : Word) : codeLoaded (before value) 4096 code := by
  intro index byte present
  have within : index < 9 := by
    have within := (List.getElem?_eq_some_iff.mp present).1
    change index < 9 at within
    exact within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def origin (value : Word) : X86LegacyFetch.Basis (before value) where
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

private def input (value : Word) : Inputs (before value) (origin value) where
  upper := by change (4096#48).toInt + 579 < (2 ^ 47 : Int); decide
  value := value
  flags := 0x246#32
  valueKnown := by
    change ((before value).regs.get? .r11).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  loaded := image value

private theorem input_value (value : Word) : (input value).value = value := rfl
private theorem origin_address (value : Word) : (origin value).address = (4096#48) := rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before value) = .ok () after ∧ lookup after 11 = some value ∧
      after.regs.get? .rip = some (if value = (0#64) then (4598#64) else (4105#64)) ∧
      after.mem = (before value).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, valueRead, _, rip⟩ := executes other extra vector _ _ (input value)
  have thenTarget : (position (origin value).address 9).signExtend 64 = (4105#64) := by
    rw [origin_address]
    rfl
  have elseTarget : (position (origin value).address 502).signExtend 64 = (4598#64) := by
    rw [origin_address]
    rfl
  refine ⟨after, executed, by simpa only [input_value] using valueRead, ?_, framed.memory⟩
  by_cases zero : value = (0#64)
  · have inputZero : (input value).value = (0#64) := by rw [input_value]; exact zero
    simpa only [if_pos zero, if_pos inputZero, elseTarget] using rip
  · have inputNonzero : (input value).value ≠ (0#64) := by rw [input_value]; exact zero
    simpa only [if_neg zero, if_neg inputNonzero, thenTarget] using rip

theorem false_branches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before 0) = .ok () after ∧ lookup after 11 = some (0#64) ∧
      after.regs.get? .rip = some (4598#64) ∧ after.mem = (before 0).mem := by
  simpa using control other extra vector (0#64)

theorem true_falls_through (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before 1) = .ok () after ∧ lookup after 11 = some (1#64) ∧
      after.regs.get? .rip = some (4105#64) ∧ after.mem = (before 1).mem := by
  simpa using control other extra vector (1#64)

end Controls

namespace PrefixControls

private theorem byte_bounds : (List.range 646).all
    (fun index => decide (Lean.RArray.get X86P1LoadCapture.propImage.data index ≤ 255)) = true := by
  kernel_reflexivity

private theorem byte_bound (index : Nat) (within : index < 646) :
    Lean.RArray.get X86P1LoadCapture.propImage.data index ≤ 255 := by
  exact of_decide_eq_true (List.all_eq_true.mp byte_bounds index (List.mem_range.mpr within))

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)

private noncomputable def cells (value : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 646).map (fun index =>
    (4096 + index, BitVec.ofNat 8 (Lean.RArray.get X86P1LoadCapture.propImage.data index))) ++
  (List.range 8).map (fun index => (8192 + index, (12288#64).extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (8200 + index, (32#64).extractLsb' (8 * index) 8)) ++
  (List.range 4).map (fun index => (12288 + index, value.extractLsb' (8 * index) 8))

private def rangeKeys (base count : Nat) : List Nat := (List.range count).map (fun index => base + index)

private theorem range_nodup (base count : Nat) : (rangeKeys base count).Nodup := by
  change ((List.range count).map (fun index => base + index)).Nodup
  apply List.Nodup.map (f := fun index => base + index)
  · intro left right same
    dsimp only at same
    omega
  · exact List.nodup_range

private theorem range_apart (left size right count : Nat) (apart : left + size ≤ right) :
    ∀ x ∈ rangeKeys left size, ∀ y ∈ rangeKeys right count, x ≠ y := by
  intro x hx y hy same
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  have := List.mem_range.mp hi
  have := List.mem_range.mp hj
  omega

private theorem distinct (value : BitVec 32) :
    (cells value).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells value).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    change (rangeKeys 4096 646 ++ rangeKeys 8192 8 ++ rangeKeys 8200 8 ++ rangeKeys 12288 4).Nodup
    simp only [List.nodup_append, range_nodup, true_and, List.mem_append, or_imp, forall_and]
    repeat' constructor
    all_goals exact range_apart _ _ _ _ (by decide)
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (value : BitVec 32) (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4105#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi (12288#64)
  let registers := registers.insert .r10 (0xffffffffffffffff#64)
  let registers := registers.insert .r11 old
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells value), (), 0, #[]⟩

private theorem cell (value : BitVec 32) (old : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells value) : (before value old).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct value) present

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

private theorem image (value : BitVec 32) (old : Word) :
    X86P1LoadCapture.Loaded X86P1LoadCapture.propImage (before value old) 4096 := by
  intro index within
  have bounded : index < 646 := by simpa only [X86P1LoadCapture.byte_extent] using within
  have member : (4096 + index, BitVec.ofNat 8 (Lean.RArray.get X86P1LoadCapture.propImage.data index)) ∈ cells value := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩
  have place := positive_address 4096 index (by omega)
  change ((address 4096 index).signExtend 52).toNat = 4096 + index at place
  rw [place, cell value old _ _ member]
  simp only [P1Capture.Program.view, if_pos within]
  rw [show Nat.ble (Lean.RArray.get X86P1LoadCapture.propImage.data index) 255 = true from
    Nat.ble_eq.mpr (byte_bound index bounded)]
  rfl

private def origin (value : BitVec 32) (old : Word) : X86LegacyFetch.Basis (before value old) where
  address := 4105#48
  opcodeAddress := 4106#48
  modrmAddress := 4107#48
  next := 4108#48
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

private def facts (value : BitVec 32) (old : Word) : X86P1LoadBounds.Facts (before value old) (origin value old) where
  upper := by change (4105#48).toInt + 637 < (2 ^ 47 : Int); decide
  frame := 8192#64
  base := 12288#64
  pointer := 12288#64
  length := 32#64
  baseAddress := 8192#48
  lengthAddress := 8200#48
  controls := controls
  visible := visible
  flags := 0x200#32
  frameKnown := by
    change ((before value old).regs.get? .rdi).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  pointerKnown := by
    change ((before value old).regs.get? .rsi).map (fun word : Word => word) = _
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
    change (before value old).mem.get? ((address 8192 index).signExtend 52).toNat = _
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
    change (before value old).mem.get? ((address 8200 index).signExtend 52).toNat = _
    have place := positive_address 8200 index (by omega)
    change ((address 8200 index).signExtend 52).toNat = 8200 + index at place
    rw [place]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

private def readable (value : BitVec 32) (old : Word) :
    X86P1LoadBounds.Readable (before value old) (12288#64) value where
  dataAddress := 12288#48
  effective := by decide
  upper := by decide
  aligned := by decide
  bytes := by
    intro index within
    change (before value old).mem.get? ((address 12288 index).signExtend 52).toNat = _
    have place := positive_address 12288 index (by omega)
    change ((address 12288 index).signExtend 52).toNat = 12288 + index at place
    rw [place]
    apply cell
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

structure Fixture (value : BitVec 32) (old : Word) where
  state : State
  origin : X86LegacyFetch.Basis state
  facts : X86P1LoadBounds.Facts state origin
  readable : X86P1LoadBounds.Readable state facts.pointer value
  placed : origin.address.toInt = 4096 + 9
  image : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state 4096
  fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat
  oldKnown : lookup state 11 = some old
  frameValue : facts.frame = (8192#64)

noncomputable def fixture (value : BitVec 32) (old : Word) : Fixture value old where
  state := before value old
  origin := origin value old
  facts := facts value old
  readable := readable value old
  placed := by change (4105#48).toInt = 4096 + 9; decide
  image := image value old
  fits := by change (12288#64 - (12288#64)).toNat + 4 ≤ (32#64).toNat; decide
  oldKnown := by
    change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  frameValue := rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : BitVec 32) (old : Word) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 13).run (before value old) = .ok () after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧
      lookup after 11 = some (booleanWord (decide (value = (6661#32)))) ∧
      after.regs.get? .rip = some
        ((if value = (6661#32) then address 4096 76 else address 4096 569).signExtend 64) ∧
      after.mem = (before value old).mem := by
  let : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, valueRead, boolRead, _, rip, _⟩ :=
    X86P1IfCapture.load_compare_if other extra vector _ 4096 _ (facts value old)
      (by change (4105#48).toInt = 4096 + 9; decide) (image value old) value (readable value old)
      (by change (12288#64 - (12288#64)).toNat + 4 ≤ (32#64).toNat; decide)
      old (by change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
              simp [before, Std.ExtDHashMap.get?_insert])
  exact ⟨after, executed, valueRead, boolRead, rip, framed.memory⟩

theorem matching_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 13).run (before (6661#32) (0xfedcba9876543210#64)) = .ok () after ∧
      lookup after 10 = some (6661#64) ∧ lookup after 11 = some (1#64) ∧
      after.regs.get? .rip = some (4172#64) ∧ after.mem = (before (6661#32) (0xfedcba9876543210#64)).mem := by
  obtain ⟨after, executed, valueRead, boolRead, rip, memory⟩ :=
    control other extra vector (6661#32) (0xfedcba9876543210#64)
  rw [show (6661#32).zeroExtend 64 = (6661#64) from rfl] at valueRead
  rw [show booleanWord (decide ((6661#32) = (6661#32))) = (1#64) from rfl] at boolRead
  rw [if_pos rfl] at rip
  change after.regs.get? .rip = some (4172#64) at rip
  exact ⟨after, executed, valueRead, boolRead, rip, memory⟩

theorem different_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 13).run (before (6660#32) (0xffffffffffffffff#64)) = .ok () after ∧
      lookup after 10 = some (6660#64) ∧ lookup after 11 = some (0#64) ∧
      after.regs.get? .rip = some (4665#64) ∧ after.mem = (before (6660#32) (0xffffffffffffffff#64)).mem := by
  obtain ⟨after, executed, valueRead, boolRead, rip, memory⟩ :=
    control other extra vector (6660#32) (0xffffffffffffffff#64)
  rw [show (6660#32).zeroExtend 64 = (6660#64) from rfl] at valueRead
  rw [show booleanWord (decide ((6660#32) = (6661#32))) = (0#64) from rfl] at boolRead
  rw [if_neg (show (6660#32) ≠ (6661#32) from by decide)] at rip
  change after.regs.get? .rip = some (4665#64) at rip
  exact ⟨after, executed, valueRead, boolRead, rip, memory⟩

end PrefixControls

end Mettapedia.Machines.TIsa.X86P1IfCapture
