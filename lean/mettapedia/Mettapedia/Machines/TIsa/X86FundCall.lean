import Mettapedia.Machines.TIsa.X86Funding
import Mettapedia.Machines.TIsa.X86CallWrapper

/-!
# The captured funding image returns through the public ABI

The current 120-byte program pays source grade three and returns a full-width
argument, or returns exhaustion without changing the receipt. The proofs compose
the original five pushes, the actual FUND/return or failure body, and the original
five pops plus RET. Complete calls take twenty-one or nineteen fetched steps.

Entry facts describe loaded code, registers, word fields and their separation
from the saved stack. A PC-normalized view records those initial read facts;
proved state frames transport them across the actual prologue. No body execution
is supplied as an entry assumption. Both outcomes preserve the whole image,
restore caller registers, and establish exact output and receipt bytes.

The concrete controls exercise both outcomes, high-bit results and restoration,
a preserved suffix, and rejected unpaid receipts, scratch values and premature
epilogue-entry claims. This fixed captured program does not certify the emitter
function for other programs or the fifteen named source consumers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86FundCall
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def grade : Funding.Grade := ⟨3#32, by decide⟩
def view (state : State) (caller : X86CallWrapper.Inputs state) : State :=
  X86Move.putPointer state (X86Prologue.codeAt caller.prologue 9)

private theorem reverse_frame {registers : Finset Register} {bytes : Finset Nat} {before after : State}
    (frame : X86StateFrame.Frame registers bytes before after) :
    X86StateFrame.Frame registers bytes after before where
  registers register outside := (frame.registers register outside).symm
  memory key outside := (frame.memory key outside).symm
  choices := frame.choices.symm
  tags := frame.tags.symm
  cycles := frame.cycles.symm
  output := frame.output.symm

theorem view_frame (state : State) (caller : X86CallWrapper.Inputs state) :
    X86StateFrame.Frame {.rsp, .rip} (X86Prologue.writes caller.prologue.bottom)
      (view state caller) (X86Prologue.finished state caller.prologue) :=
  ((reverse_frame (X86StateFrame.registerOnly
    (pointer_frame state (X86Prologue.codeAt caller.prologue 9)))).trans
      (X86Prologue.finished_frame state caller.prologue)).mono (by decide) (by simp)

structure Inputs (state : State) (allowance receipt value : Word) where
  caller : X86CallWrapper.Inputs state
  origin : X86LegacyFetch.Basis (view state caller)
  start : origin.address = X86Prologue.codeAt caller.prologue 9
  fund : X86Funding.Placed.Inputs (view state caller) origin grade (53#32) allowance receipt
  facts : X86FailureHandler.FrameFacts (view state caller)
  upper : caller.prologue.code.toInt + 120 < (2 ^ 47 : Int)
  epilogue : caller.epilogue = address caller.prologue.code.toInt 110
  image : codeLoaded state caller.prologue.code.toInt X86Funding.Capture.image
  sourceKnown : lookup (view state caller) 6 = some value
  imageApartStack : ∀ index byte, X86Funding.Capture.image[index]? = some byte →
    ((address caller.prologue.code.toInt index).signExtend 52).toNat ∉ X86Prologue.writes caller.prologue.bottom
  budgetApartStack : ∀ index < 8,
    ((address fund.budgetAddress.toInt index).signExtend 52).toNat ∉ X86Prologue.writes caller.prologue.bottom
  receiptApartStack : ∀ index < 8,
    ((address fund.receiptAddress.toInt index).signExtend 52).toNat ∉ X86Prologue.writes caller.prologue.bottom
  imageApartBody : ∀ index byte, X86Funding.Capture.image[index]? = some byte →
    ((address caller.prologue.code.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written fund.receiptAddress (List.range 8) ∪ X86Funding.Return.writes facts
  receiptApartResult : ∀ index < 8,
    X86WriteWords.physicalAddress fund.receiptAddress index ∉ X86Funding.Return.writes facts
  stackApartBody : ∀ slot : Fin 6, ∀ byte < 8,
    X86WriteWords.physicalAddress (X86Prologue.stackAt caller.prologue slot.val) byte ∉
      X86WriteWords.written fund.receiptAddress (List.range 8) ∪ X86Funding.Return.writes facts

def bodyOrigin (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    X86LegacyFetch.Basis (X86Prologue.finished state input.caller.prologue) :=
  let frame := view_frame state input.caller
  { input.origin with
    status := (frame.registers .ms_reg (by decide)).trans input.origin.status
    fault := (frame.registers .fault_reg (by decide)).trans input.origin.fault
    msrs := (frame.registers .msrs (by decide)).trans input.origin.msrs
    segments := (frame.registers .seg_hidden_attrs (by decide)).trans input.origin.segments
    application := (frame.registers .app_view (by decide)).trans input.origin.application
    rip := (X86Prologue.finished_result state input.caller.prologue).pointer.trans
      (congrArg (fun pointer => some (pointer.signExtend 64)) input.start.symm) }

theorem origin_int (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    (bodyOrigin state input).address.toInt = input.caller.prologue.code.toInt + 9 := by
  change input.origin.address.toInt = _
  rw [input.start, X86Prologue.code_int _ 9 (by decide)]
  simp

theorem body_image (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    codeLoaded (X86Prologue.finished state input.caller.prologue) input.caller.prologue.code.toInt
      X86Funding.Capture.image :=
  (X86Prologue.finished_frame state input.caller.prologue).codeLoaded _ _ input.image input.imageApartStack

def bodyFund (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    X86Funding.Placed.Inputs (X86Prologue.finished state input.caller.prologue) (bodyOrigin state input)
      grade (53#32) allowance receipt :=
  let frame := view_frame state input.caller
  { input.fund with
    base := (frame.lookup 7 (by decide)).trans input.fund.base
    controlKnown := (frame.registers .ctrs (by decide)).trans input.fund.controlKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans input.fund.visibleKnown
    flagsKnown := (frame.registers .rflags (by decide)).trans input.fund.flagsKnown
    quiet := (frame.registers .log_register_writes (by decide)).trans input.fund.quiet
    loaded := by
      have captured := X86Funding.Placed.captured_window _ _ (body_image state input)
      rw [← origin_int state input] at captured
      exact captured
    budget := fun index within => (frame.memory _ (input.budgetApartStack index within)).trans (input.fund.budget index within)
    receipt := fun index within => (frame.memory _ (input.receiptApartStack index within)).trans (input.fund.receipt index within) }

def bodyFacts (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    X86FailureHandler.FrameFacts (X86Prologue.finished state input.caller.prologue) :=
  let frame := view_frame state input.caller
  { input.facts with
    frameKnown := (frame.lookup 7 (by decide)).trans input.facts.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans input.facts.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans input.facts.visibleKnown
    flagsKnown := (frame.registers .rflags (by decide)).trans input.facts.flagsKnown
    quiet := (frame.registers .log_register_writes (by decide)).trans input.facts.quiet }

def writes {state : State} {allowance receipt value : Word} (input : Inputs state allowance receipt value) : Finset Nat :=
  X86WriteWords.written input.fund.receiptAddress (List.range 8) ∪ X86Funding.Return.writes input.facts

theorem epilogue_apart (state : State) {allowance receipt value : Word} (input : Inputs state allowance receipt value) :
    ∀ index byte, X86Epilogue.expected[index]? = some byte →
      ((address input.caller.epilogue.toInt index).signExtend 52).toNat ∉ writes input := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := X86Funding.WrapperEncoding.epilogue_byte ⟨index, within⟩
  rw [same] at imageByte
  have known := input.imageApartBody (index + 110) byte imageByte
  have lower : -(2 ^ 47 : Int) ≤ input.caller.prologue.code.toInt := by
    simpa using BitVec.le_toInt input.caller.prologue.code
  have position : input.caller.epilogue.toInt = input.caller.prologue.code.toInt + 110 := by
    rw [input.epilogue]
    exact address_toInt _ lower input.upper 110 (by decide)
  rw [position]
  have place : address (input.caller.prologue.code.toInt + 110) index =
      address input.caller.prologue.code.toInt (index + 110) := by
    unfold address
    congr 1
    push_cast
    omega
  rw [place]
  exact known

theorem paid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (allowance receipt value : Word) (input : Inputs state allowance receipt value)
    (fits : receipt.toNat + 3 ≤ allowance.toNat) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches 21).run state = .ok () after ∧
      X86CallWrapper.Result state input.caller (writes input) body after ∧
      codeLoaded after input.caller.prologue.code.toInt X86Funding.Capture.image ∧
      lookup after 0 = some value ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.facts.statusAddress index) =
        some ((1#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.facts.resultAddress index) =
        some (value.extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.fund.receiptAddress index) =
        some ((receipt + grade.word).extractLsb' (8 * index) 8)) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  let middle := X86Prologue.finished state input.caller.prologue
  let origin := bodyOrigin state input
  let fund := bodyFund state input
  let facts := bodyFacts state input
  have source : lookup middle 6 = some value := (view_frame state input.caller).lookup 6 (by decide) |>.trans input.sourceKnown
  obtain ⟨body, flags, run, frame, code, result, statusBytes, resultBytes, receiptBytes, flagKnown, pointer⟩ :=
    X86Funding.Return.executes (X86Stack.linkedHandlers other) extra vector middle origin allowance receipt value
      fund facts input.caller.prologue.code.toInt (origin_int state input) input.upper (body_image state input) source
      (by
        intro index byte present member
        exact input.imageApartBody index byte present (Finset.mem_union_left _ member))
      (by
        intro index byte present member
        exact input.imageApartBody index byte present (Finset.mem_union_right _ member))
      input.receiptApartResult fits
  let exit : X86CallWrapper.BodyExit state input.caller (writes input) body := {
    frame := frame.mono (by decide) (Finset.Subset.refl _)
    flags := flags
    flagsKnown := flagKnown
    stackApart := input.stackApartBody
    epilogueApart := epilogue_apart state input
    pointer := pointer.trans (congrArg (fun location => some (location.signExtend 64)) input.epilogue.symm) }
  obtain ⟨after, fullRun, correct⟩ :=
    X86CallWrapper.executes (X86Funding.Return.handlers other extra) vector state input.caller (writes input) body 10 exit run
  refine ⟨body, after, fullRun, correct, ?_, correct.value.trans result, ?_, ?_, ?_⟩
  · intro index byte present
    rw [correct.memory]
    exact code index byte present
  · intro index within
    rw [correct.memory]
    exact statusBytes index within
  · intro index within
    rw [correct.memory]
    exact resultBytes index within
  · intro index within
    rw [correct.memory]
    exact receiptBytes index within


theorem exhausted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (allowance receipt value : Word) (input : Inputs state allowance receipt value)
    (valid : receipt.toNat ≤ allowance.toNat) (short : allowance.toNat < receipt.toNat + 3) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches 19).run state = .ok () after ∧
      X86CallWrapper.Result state input.caller (writes input) body after ∧
      codeLoaded after input.caller.prologue.code.toInt X86Funding.Capture.image ∧
      lookup after 0 = some (4#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.facts.statusAddress index) =
        some ((4#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.facts.resultAddress index) =
        some ((4#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.fund.receiptAddress index) =
        some (receipt.extractLsb' (8 * index) 8)) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  let middle := X86Prologue.finished state input.caller.prologue
  let origin := bodyOrigin state input
  let fund := bodyFund state input
  let facts := bodyFacts state input
  obtain ⟨body, flags, run, frame, code, result, statusBytes, resultBytes, receiptBytes, flagKnown, pointer⟩ :=
    X86Funding.Exhaustion.executes (X86ReturnPath.linkedHandlers (X86Stack.linkedHandlers other)) extra vector
      middle origin allowance receipt fund facts input.caller.prologue.code.toInt
      (origin_int state input) input.upper (body_image state input)
      (by
        intro index byte present member
        exact input.imageApartBody index byte present (Finset.mem_union_right _ member))
      input.receiptApartResult valid short
  let exit : X86CallWrapper.BodyExit state input.caller (writes input) body := {
    frame := frame.mono (by decide) Finset.subset_union_right
    flags := flags
    flagsKnown := flagKnown
    stackApart := input.stackApartBody
    epilogueApart := epilogue_apart state input
    pointer := pointer.trans (congrArg (fun location => some (location.signExtend 64)) input.epilogue.symm) }
  obtain ⟨after, fullRun, correct⟩ :=
    X86CallWrapper.executes (X86Funding.Return.handlers other extra) vector state input.caller (writes input) body 8 exit run
  refine ⟨body, after, fullRun, correct, ?_, correct.value.trans result, ?_, ?_, ?_⟩
  · intro index byte present
    rw [correct.memory]
    exact code index byte present
  · intro index within
    rw [correct.memory]
    exact statusBytes index within
  · intro index within
    rw [correct.memory]
    exact resultBytes index within
  · intro index within
    rw [correct.memory]
    exact receiptBytes index within


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

private theorem outside_written (location start count : Nat) (base : BitVec 48)
    (baseInt : base.toInt = (start : Int)) (upper : start + count < 2 ^ 47)
    (outside : location < start ∨ start + count ≤ location) :
    location ∉ X86WriteWords.written base (List.range count) := by
  intro present
  simp only [X86WriteWords.written, List.mem_toFinset, List.mem_map] at present
  obtain ⟨offset, inside, same⟩ := present
  have bounded := List.mem_range.mp inside
  have point : X86WriteWords.physicalAddress base offset = start + offset := by
    unfold X86WriteWords.physicalAddress
    rw [baseInt]
    exact positive_address start offset (by omega)
  rw [point] at same
  omega

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def saved (index : Fin 5) : Word :=
  #[7#64, 99#64, 42#64, 0x0123456789abcdef#64, 0xfedcba9876543210#64][index.val]'(by exact index.isLt)
private def frameAddress (slot : Fin 4) : Nat :=
  #[1048720, 1048728, 1048736, 1048744][slot.val]'(by exact slot.isLt)
private def frameValue (allowance receipt : Word) (slot : Fin 4) : Word :=
  #[99#64, 77#64, allowance, receipt][slot.val]'(by exact slot.isLt)
private noncomputable def cells (allowance receipt : Word) : List (Nat × BitVec 8) :=
  (List.range 120).map (fun index => (4087 + index, BitVec.ofNat 8 ((X86Funding.Capture.image[index]?).getD 0))) ++
  (List.finRange 4).flatMap (fun slot => (List.range 8).map (fun byte =>
    (frameAddress slot + byte, (frameValue allowance receipt slot).extractLsb' (8 * byte) 8))) ++
  (List.range 48).map (fun index => (8192 + index,
    if index < 40 then (0#8) else (0x3000#64).extractLsb' (8 * (index - 40)) 8)) ++ [(8240, 42#8)]

private theorem distinct (allowance receipt : Word) :
    (cells allowance receipt).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells allowance receipt).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, List.map_flatMap, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (allowance receipt : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4087#64)
  let registers := registers.insert .rsp (0x2028#64)
  let registers := registers.insert .rbx (saved 0)
  let registers := registers.insert .r12 (saved 1)
  let registers := registers.insert .r13 (saved 2)
  let registers := registers.insert .r14 (saved 3)
  let registers := registers.insert .r15 (saved 4)
  let registers := registers.insert .rdi (1048576#64)
  let registers := registers.insert .rsi (0xfedcba9876543210#64)
  let registers := registers.insert .rax (99#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (2#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells allowance receipt), (), 0, #[]⟩

private theorem cell (allowance receipt : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells allowance receipt) :
    (before allowance receipt).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct allowance receipt) present

private theorem image (allowance receipt : Word) :
    codeLoaded (before allowance receipt) 4087 X86Funding.Capture.image := by
  intro index byte present
  have within : index < 120 := by
    have size := (List.getElem?_eq_some_iff.mp present).choose
    simpa only [X86Funding.Capture.image_length] using size
  have member : (4087 + index, BitVec.ofNat 8 byte) ∈ cells allowance receipt := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨index, List.mem_range.mpr within, ?_⟩
    simp only [present, Option.getD_some]
  have place := positive_address 4087 index (by omega)
  change ((address 4087 index).signExtend 52).toNat = 4087 + index at place
  rw [place]
  exact cell allowance receipt _ _ member

private theorem frame_cell (allowance receipt : Word) (slot : Fin 4) (byte : Nat) (within : byte < 8) :
    (before allowance receipt).mem.get? (frameAddress slot + byte) =
      some ((frameValue allowance receipt slot).extractLsb' (8 * byte) 8) := by
  apply cell
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨slot, List.mem_finRange _, ?_⟩
  exact List.mem_map.mpr ⟨byte, List.mem_range.mpr within, rfl⟩

private noncomputable def prologue (allowance receipt : Word) : X86Prologue.Inputs (before allowance receipt) where
  bottom := 0x2000#48
  stackUpper := by decide
  stackKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  saved := saved
  savedKnown := by
    intro index
    fin_cases index <;> simp [before, lookup, X86Prologue.source, key, cast_eq, Std.ExtDHashMap.get?_insert] <;> rfl
  returnAddress := 0x3000#48
  returnBytes := by
    intro byte within
    have member : (8192 + (40 + byte), (0x3000#64).extractLsb' (8 * byte) 8) ∈ cells allowance receipt := by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨40 + byte, List.mem_range.mpr (by omega), ?_⟩
      simp [show ¬40 + byte < 40 from by omega]
    have got := cell allowance receipt _ _ member
    interval_cases byte <;> exact got
  visible := visible
  controls := controls
  flags := 2#32
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  aligned := by intro slot; fin_cases slot <;> decide
  context := {
    control := modeControl, attributes := attributes
    status := by simp [before, Std.ExtDHashMap.get?_insert]
    fault := by simp [before, Std.ExtDHashMap.get?_insert]
    msrs := by simp [before, Std.ExtDHashMap.get?_insert]
    segments := by simp [before, Std.ExtDHashMap.get?_insert]
    longMode := by decide
    codeMode := by decide
    application := by simp [before, Std.ExtDHashMap.get?_insert] }
  code := 4087#48
  codeUpper := by decide
  loaded := X86Funding.WrapperEncoding.prologue_window _ _ (image allowance receipt)
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  codeOutside := by
    intro index byte present
    have within : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
    change ((address 4087 index).signExtend 52).toNat ∉ X86Prologue.writes (8192#48)
    have place := positive_address 4087 index (by omega)
    change ((address 4087 index).signExtend 52).toNat = 4087 + index at place
    rw [place]
    exact outside_written _ 8192 40 _ rfl (by decide) (Or.inl (by omega))

private noncomputable def caller (allowance receipt : Word) : X86CallWrapper.Inputs (before allowance receipt) where
  prologue := prologue allowance receipt
  epilogue := 4197#48
  epilogueUpper := by decide
  epilogueLoaded := X86Funding.WrapperEncoding.epilogue_window (before allowance receipt) 4087 (image allowance receipt)
  epilogueStackApart := by
    intro index byte present
    have within : index < 10 := (List.getElem?_eq_some_iff.mp present).choose
    change ((address 4197 index).signExtend 52).toNat ∉ X86Prologue.writes (8192#48)
    have place := positive_address 4197 index (by omega)
    change ((address 4197 index).signExtend 52).toNat = 4197 + index at place
    rw [place]
    exact outside_written _ 8192 40 _ rfl (by decide) (Or.inl (by omega))


private theorem view_register (allowance receipt : Word) (register : Register) (outside : register ≠ .rip) :
    (view (before allowance receipt) (caller allowance receipt)).regs.get? register =
      (before allowance receipt).regs.get? register :=
  (pointer_frame _ _).registers register (by simpa using outside)

private noncomputable def origin (allowance receipt : Word) :
    X86LegacyFetch.Basis (view (before allowance receipt) (caller allowance receipt)) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := (view_register allowance receipt .ms_reg (by decide)).trans (prologue allowance receipt).context.status
  fault := (view_register allowance receipt .fault_reg (by decide)).trans (prologue allowance receipt).context.fault
  msrs := (view_register allowance receipt .msrs (by decide)).trans (prologue allowance receipt).context.msrs
  segments := (view_register allowance receipt .seg_hidden_attrs (by decide)).trans (prologue allowance receipt).context.segments
  longMode := by decide
  codeMode := by decide
  application := (view_register allowance receipt .app_view (by decide)).trans (prologue allowance receipt).context.application
  rip := X86FuelPrefix.pointer_rip _ _

private noncomputable def fund (allowance receipt : Word) :
    X86Funding.Placed.Inputs (view (before allowance receipt) (caller allowance receipt))
      (origin allowance receipt) grade (53#32) allowance receipt where
  upper := by change (4096#48).toInt + 36 < (2 ^ 47 : Int); decide
  frame := 1048576#64
  budgetAddress := 1048736#48
  receiptAddress := 1048744#48
  budgetUpper := by decide
  receiptUpper := by decide
  base := by
    rw [view, X86Move.lookup_putPointer]
    simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
    rfl
  budgetEffective := by decide
  receiptEffective := by decide
  budgetAligned := by decide
  receiptAligned := by decide
  controls := controls
  visible := visible
  flags := 2#32
  controlKnown := (view_register allowance receipt .ctrs (by decide)).trans (prologue allowance receipt).controlsKnown
  visibleKnown := (view_register allowance receipt .seg_visibles (by decide)).trans (prologue allowance receipt).visibleKnown
  flagsKnown := (view_register allowance receipt .rflags (by decide)).trans (prologue allowance receipt).flagsKnown
  quiet := (view_register allowance receipt .log_register_writes (by decide)).trans (prologue allowance receipt).quiet
  loaded := X86Funding.Placed.captured_window _ 4087 (image allowance receipt)
  budget := by
    intro index within
    have got := frame_cell allowance receipt 2 index within
    interval_cases index <;> exact got
  receipt := by
    intro index within
    have got := frame_cell allowance receipt 3 index within
    interval_cases index <;> exact got
  outsideCode := by
    intro index byte present
    have within : index < 36 := (List.getElem?_eq_some_iff.mp present).choose
    change ((address 4096 index).signExtend 52).toNat ∉ X86WriteWords.written (1048744#48) (List.range 8)
    have place := positive_address 4096 index (by omega)
    change ((address 4096 index).signExtend 52).toNat = 4096 + index at place
    rw [place]
    exact outside_written _ 1048744 8 _ rfl (by decide) (Or.inl (by omega))

private noncomputable def facts (allowance receipt : Word) :
    X86FailureHandler.FrameFacts (view (before allowance receipt) (caller allowance receipt)) where
  frame := 1048576#64
  statusAddress := 1048720#48
  resultAddress := 1048728#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := visible
  controls := controls
  flags := 2#32
  frameKnown := (fund allowance receipt).base
  controlsKnown := (fund allowance receipt).controlKnown
  visibleKnown := (fund allowance receipt).visibleKnown
  flagsKnown := (fund allowance receipt).flagsKnown
  quiet := (fund allowance receipt).quiet
  statusOutside := by intro index within; interval_cases index <;> decide


private def fieldWrites : Finset Nat :=
  X86WriteWords.written (1048744#48) (List.range 8) ∪
    (X86WriteWords.written (1048720#48) (List.range 8) ∪
      X86WriteWords.written (1048728#48) (List.range 8))

private theorem not_union {key : Nat} {left right : Finset Nat}
    (apart : key ∉ left ∧ key ∉ right) : key ∉ left ∪ right := by
  intro member
  exact (Finset.mem_union.mp member).elim apart.1 apart.2

private theorem below_fields (location : Nat) (below : location < 1048720) : location ∉ fieldWrites := by
  apply not_union
  refine ⟨outside_written _ 1048744 8 _ rfl (by decide) (Or.inl (by omega)), ?_⟩
  apply not_union
  exact ⟨outside_written _ 1048720 8 _ rfl (by decide) (Or.inl below),
    outside_written _ 1048728 8 _ rfl (by decide) (Or.inl (by omega))⟩

private noncomputable def input (allowance receipt : Word) :
    Inputs (before allowance receipt) allowance receipt (0xfedcba9876543210#64) where
  caller := caller allowance receipt
  origin := origin allowance receipt
  start := rfl
  fund := fund allowance receipt
  facts := facts allowance receipt
  upper := by change (4087#48).toInt + 120 < (2 ^ 47 : Int); decide
  epilogue := rfl
  image := image allowance receipt
  sourceKnown := by
    rw [view, X86Move.lookup_putPointer]
    simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
    rfl
  imageApartStack := by
    intro index byte present
    have within : index < 120 := by
      have size := (List.getElem?_eq_some_iff.mp present).choose
      simpa only [X86Funding.Capture.image_length] using size
    change ((address 4087 index).signExtend 52).toNat ∉ X86Prologue.writes (8192#48)
    have place := positive_address 4087 index (by omega)
    change ((address 4087 index).signExtend 52).toNat = 4087 + index at place
    rw [place]
    exact outside_written _ 8192 40 _ rfl (by decide) (Or.inl (by omega))
  budgetApartStack := by
    intro index within
    change ((address 1048736 index).signExtend 52).toNat ∉ X86Prologue.writes (8192#48)
    have place := positive_address 1048736 index (by omega)
    change ((address 1048736 index).signExtend 52).toNat = 1048736 + index at place
    rw [place]
    exact outside_written _ 8192 40 _ rfl (by decide) (Or.inr (by omega))
  receiptApartStack := by
    intro index within
    change ((address 1048744 index).signExtend 52).toNat ∉ X86Prologue.writes (8192#48)
    have place := positive_address 1048744 index (by omega)
    change ((address 1048744 index).signExtend 52).toNat = 1048744 + index at place
    rw [place]
    exact outside_written _ 8192 40 _ rfl (by decide) (Or.inr (by omega))
  imageApartBody := by
    intro index byte present
    have within : index < 120 := by
      have size := (List.getElem?_eq_some_iff.mp present).choose
      simpa only [X86Funding.Capture.image_length] using size
    change ((address 4087 index).signExtend 52).toNat ∉ fieldWrites
    have place := positive_address 4087 index (by omega)
    change ((address 4087 index).signExtend 52).toNat = 4087 + index at place
    rw [place]
    exact below_fields _ (by omega)
  receiptApartResult := by
    intro index within
    change X86WriteWords.physicalAddress (1048744#48) index ∉
      X86WriteWords.written (1048720#48) (List.range 8) ∪ X86WriteWords.written (1048728#48) (List.range 8)
    unfold X86WriteWords.physicalAddress
    change ((address 1048744 index).signExtend 52).toNat ∉
      X86WriteWords.written (1048720#48) (List.range 8) ∪ X86WriteWords.written (1048728#48) (List.range 8)
    have place := positive_address 1048744 index (by omega)
    change ((address 1048744 index).signExtend 52).toNat = 1048744 + index at place
    rw [place]
    exact not_union
      ⟨outside_written _ 1048720 8 _ rfl (by decide) (Or.inr (by omega)),
        outside_written _ 1048728 8 _ rfl (by decide) (Or.inr (by omega))⟩
  stackApartBody := by
    intro slot byte within
    change X86WriteWords.physicalAddress (X86Prologue.stackAt (prologue allowance receipt) slot.val) byte ∉ fieldWrites
    rw [X86Prologue.stack_byte (prologue allowance receipt) slot.val byte (by have := slot.isLt; omega)]
    change ((address 8192 (8 * slot.val + byte)).signExtend 52).toNat ∉ fieldWrites
    have place := positive_address 8192 (8 * slot.val + byte) (by have := slot.isLt; omega)
    change ((address 8192 (8 * slot.val + byte)).signExtend 52).toNat = 8192 + (8 * slot.val + byte) at place
    rw [place]
    exact below_fields _ (by have := slot.isLt; omega)

private theorem suffix_preserved (allowance receipt : Word) (body after : State)
    (correct : X86CallWrapper.Result (before allowance receipt) (caller allowance receipt)
      (writes (input allowance receipt)) body after) :
    after.mem.get? 8240 = some (42#8) := by
  rw [correct.frame.memory 8240 (not_union
    ⟨outside_written _ 8192 40 _ rfl (by decide) (Or.inr (by decide)), below_fields _ (by decide)⟩)]
  exact cell allowance receipt _ _ (List.mem_append_right _ (by simp))

theorem paid_returns (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 21).run (before 10 7) = .ok () after ∧
      after.regs.get? .rip = some (0x3000#64) ∧ lookup after 4 = some (0x2030#64) ∧
      lookup after 14 = some (0x0123456789abcdef#64) ∧ lookup after 15 = some (0xfedcba9876543210#64) ∧
      lookup after 0 = some (0xfedcba9876543210#64) ∧
      after.mem.get? 1048720 = some (1#8) ∧ after.mem.get? 1048728 = some (0x10#8) ∧
      after.mem.get? 1048744 = some (10#8) ∧ after.mem.get? 8240 = some (42#8) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  obtain ⟨body, after, run, correct, _, value, status, result, receipt⟩ :=
    paid other extra vector (before 10 7) (10#64) (7#64) _ (input 10 7) (by decide)
  exact ⟨after, run, correct.pointer, correct.stackPointer, correct.saved 3, correct.saved 4,
    value, status 0 (by decide), result 0 (by decide), receipt 0 (by decide), suffix_preserved 10 7 body after correct⟩

theorem exhausted_returns (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 19).run (before 9 7) = .ok () after ∧
      after.regs.get? .rip = some (0x3000#64) ∧ lookup after 4 = some (0x2030#64) ∧
      lookup after 14 = some (0x0123456789abcdef#64) ∧ lookup after 15 = some (0xfedcba9876543210#64) ∧
      lookup after 0 = some (4#64) ∧
      after.mem.get? 1048720 = some (4#8) ∧ after.mem.get? 1048728 = some (4#8) ∧
      after.mem.get? 1048744 = some (7#8) ∧ after.mem.get? 8240 = some (42#8) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  obtain ⟨body, after, run, correct, _, value, status, result, receipt⟩ :=
    exhausted other extra vector (before 9 7) (9#64) (7#64) _ (input 9 7) (by decide) (by decide)
  exact ⟨after, run, correct.pointer, correct.stackPointer, correct.saved 3, correct.saved 4,
    value, status 0 (by decide), result 0 (by decide), receipt 0 (by decide), suffix_preserved 9 7 body after correct⟩


theorem unpaid_receipt_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) (wrong : after.mem.get? 1048744 = some (10#8)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 19).run (before 9 7) ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨proved, run, _, _, _, _, _, _, _, receipt, _⟩ := exhausted_returns other extra vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at receipt
  contradiction

theorem scratch_value_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) (wrong : lookup after 14 = some (3#64)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 21).run (before 10 7) ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨proved, run, _, _, saved, _⟩ := paid_returns other extra vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at saved
  contradiction

theorem epilogue_entry_refused_as_return (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) (wrong : after.regs.get? .rip = some (4197#64)) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 21).run (before 10 7) ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers (X86Funding.Return.handlers other extra)
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨proved, run, returned, _⟩ := paid_returns other extra vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at returned
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86FundCall

#print axioms Mettapedia.Machines.TIsa.X86FundCall.bodyFund
#print axioms Mettapedia.Machines.TIsa.X86FundCall.paid
#print axioms Mettapedia.Machines.TIsa.X86FundCall.exhausted
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.paid_returns
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.exhausted_returns
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.unpaid_receipt_refused
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.scratch_value_refused
#print axioms Mettapedia.Machines.TIsa.X86FundCall.Controls.epilogue_entry_refused_as_return
