import Mettapedia.Machines.TIsa.X86P1OutputCapture
import Mettapedia.Machines.TIsa.X86P1QwordGuardCapture
import Mettapedia.Machines.TIsa.X86P1RefusedCapture

/-!
# The successful R_DERIVE_IS_PROP call through its public ABI

The actual two-guard prefix composes with output construction and successful
completion in 88 fetched instructions. The public theorem starts from entry
observations, proves their preservation across the six saves and the allowance
setup, executes the body, and composes the receipt block and the six restores.
It restores all saved registers, republishes the unchanged receipt and carries
all output and image observations to the caller.

The theorem covers the successful path with explicit read/write separation.
Other outcomes, actual source/admission and generic emitter correspondence
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1SuccessCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
noncomputable abbrev image := X86P1LoadCapture.propImage
abbrev guardWrites : Finset Register := {.rip,.rflags,.r14,.r15,.r10}
abbrev clobbers : Finset Register := insert .rax X86P1OutputCapture.clobbers
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86P1OutputCapture.completeHandlers other (X86ConditionByte.byteHandlers extra)
theorem guard_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1QwordGuardCapture.handlers (X86Funding.Placed.baseHandlers (X86FailureHandler.linkedHandlers other)) extra =
      handlers other extra := (X86P1QwordGuardCapture.common_handlers (X86FailureHandler.linkedHandlers other) extra).symm

def guardFacts (state : State) (origin : X86LegacyFetch.Basis state)
    (input : X86P1OutputCapture.DataFacts state) (placed : origin.address.toInt = input.base + 24) :
    X86P1LoadBounds.Facts state origin 623 :=
  X86P1LoadCapture.located rfl rfl input.premiseFacts origin (by rw [placed]; have := input.upper; omega)

def receiptAt {before after : State} (facts : X86FailureHandler.FrameFacts before)
    (frame : RegisterFrame guardWrites before after) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags) : X86FailureHandler.FrameFacts after := {
  facts with
  flags := flags
  frameKnown := (frame.lookup 7 (by decide)).trans facts.frameKnown
  controlsKnown := (frame.registers .ctrs (by decide)).trans facts.controlsKnown
  visibleKnown := (frame.registers .seg_visibles (by decide)).trans facts.visibleKnown
  flagsKnown := flagsKnown
  quiet := (frame.registers .log_register_writes (by decide)).trans facts.quiet }

def dataAt {before after : State} (input : X86P1OutputCapture.DataFacts before)
    (frame : RegisterFrame guardWrites before after) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags) : X86P1OutputCapture.DataFacts after :=
  input.transport (X86StateFrame.registerOnly frame) (by decide) (by decide) (by decide) (by decide) flags flagsKnown
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

def writes {state : State} (input : X86P1OutputCapture.DataFacts state) (receipt : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86P1OutputCapture.outputWrites input.output ∪ X86P1OutputCapture.receiptWrites receipt

theorem body_fires (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : X86P1OutputCapture.DataFacts state)
    (placed : origin.address.toInt = input.base + 24) (receipt : X86FailureHandler.FrameFacts state)
    (tag : X86P1LoadBounds.Readable state input.premiseFacts.pointer (6661#32))
    (zero : X86P1QwordBounds.Readable state input.premiseFacts.pointer (0#64))
    (fits : (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (codeApart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ X86P1OutputCapture.receiptWrites receipt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 88).run state = .ok () after ∧
      X86StateFrame.Frame clobbers (writes input receipt) state after ∧
      after.regs.get? .rflags = some flags ∧ lookup after 0 = some (1#64) ∧
      after.regs.get? .rip = some ((address input.base 619).signExtend 64) ∧
      X86P1OutputCapture.Prefix after input.output input.field 32 ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let facts := guardFacts state origin input placed
  have tagFits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat := by
    change (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 4 ≤ input.premiseFacts.length.toNat
    omega
  obtain ⟨middle,firstFlags,first,firstFrame,_,firstFlagsKnown,firstRip,_⟩ :=
    X86P1QwordGuardCapture.two_guard_prefix (X86FailureHandler.linkedHandlers other) extra vector state input.base origin facts
      placed input.loaded (6661#32) tag tagFits (0#64) (fun _ => zero) (fun _ => fits)
  rw [guard_handlers] at first
  have guardRun : (X86FuelPrefix.fetches 22).run state = .ok () middle := by simpa only [if_pos rfl,ite_true] using first
  have guardRip : middle.regs.get? .rip = some ((address input.base 149).signExtend 64) := by
    simpa only [if_pos rfl,ite_true] using firstRip
  let here := X86StateFrame.basisAt state middle origin (X86StateFrame.registerOnly firstFrame) (by decide)
    (address input.base 149)
    (by rw [address_toInt input.base (extent := 647) input.lower input.upper 149 (by decide)]; have := input.upper; omega) guardRip
  let next : X86P1OutputCapture.Inputs middle here := {
    toDataFacts := dataAt input firstFrame firstFlags firstFlagsKnown
    placed := address_toInt input.base (extent := 647) input.lower input.upper 149 (by decide) }
  let nextReceipt := receiptAt receipt firstFrame firstFlags firstFlagsKnown
  obtain ⟨after,flags,last,lastFrame,flagsKnown,rax,rip,bytes,status,result,image⟩ :=
    X86P1OutputCapture.completes other (X86ConditionByte.byteHandlers extra) vector middle here next nextReceipt codeApart outputApart
  have footprints : X86P1OutputCapture.outputWrites next.output ∪ X86P1OutputCapture.receiptWrites nextReceipt = writes input receipt := rfl
  rw [footprints] at lastFrame
  exact ⟨after,flags,X86FuelPrefix.fetches_then 22 66 state middle after guardRun last,
    ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono (by decide) (by simp),
    flagsKnown,rax,rip,bytes,status,result,image⟩

structure ReadProtection {state : State} (input : X86P1OutputCapture.DataFacts state) (written : Finset Nat) : Prop where
  code : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ written
  outputBase : ∀ byte < 8, X86WriteWords.physicalAddress input.outputFacts.baseAddress byte ∉ written
  outputLength : ∀ byte < 8, X86WriteWords.physicalAddress input.outputFacts.lengthAddress byte ∉ written
  premiseBase : ∀ byte < 8, X86WriteWords.physicalAddress input.premiseFacts.baseAddress byte ∉ written
  premiseLength : ∀ byte < 8, X86WriteWords.physicalAddress input.premiseFacts.lengthAddress byte ∉ written
  field : ∀ byte < 8, X86WriteWords.physicalAddress input.fieldAddress byte ∉ written

/-- Separation of the published receipt word and the saved stack from everything the body writes
or the caller reads back. -/
structure FuelProtection {state : State} (call : X86AllowanceCall.Inputs state)
    (input : X86P1OutputCapture.DataFacts state) (written : Finset Nat) : Prop where
  budget : ∀ byte < 8, X86WriteWords.physicalAddress call.fuel.budgetAddress byte ∉ written
  code : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉
    X86AllowanceCall.receiptBytes call.fuel.receiptAddress
  output : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉
    X86AllowanceCall.receiptBytes call.fuel.receiptAddress
  bottom : ∀ byte < 8, X86WriteWords.physicalAddress call.bottom byte ∉
    written ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress
  saved : ∀ slot : Fin 6, ∀ byte < 8,
    X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) byte ∉
      written ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress

noncomputable abbrev callHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  handlers (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra
theorem enter_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Stack.linkedHandlers (X86P1Sub1Fuel.handlers (callHandlers other extra)) = callHandlers other extra := rfl
theorem exit_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86AllowanceCall.Inputs.exitDispatch (callHandlers other extra) = callHandlers other extra := rfl

theorem public_fires (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (input : X86P1OutputCapture.DataFacts state)
    (entryAt : call.prologue.code.toInt = input.base) (exitAt : call.exit = address input.base 619)
    (receipt : X86FailureHandler.FrameFacts state)
    (tag : X86P1LoadBounds.Readable state input.premiseFacts.pointer (6661#32))
    (zero : X86P1QwordBounds.Readable state input.premiseFacts.pointer (0#64))
    (fits : (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (preserved : ReadProtection input (X86AllowanceCall.spillBytes call.prologue.bottom call.bottom))
    (tagApart : ∀ byte < 4, X86WriteWords.physicalAddress tag.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (zeroApart : ∀ byte < 8, X86WriteWords.physicalAddress zero.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (codeApart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ X86P1OutputCapture.receiptWrites receipt)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (fuel : FuelProtection call input (writes input receipt)) :
    letI : OtherOpcodeHandlers := callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches 106).run state = .ok () after ∧
      X86AllowanceCall.Result call (writes input receipt) (call.fuel.budget - call.fuel.receipt) body after ∧
      lookup after 0 = some (1#64) ∧
      X86P1OutputCapture.Prefix after input.output input.field 32 ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress byte) =
        some (call.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := callHandlers other extra
  let : VectorOpcodeHandlers := vector
  have codeUpper : call.prologue.code.toInt + 647 < (2 ^ 47 : Int) := by rw [entryAt]; exact input.upper
  have entry := call.enters (callHandlers other extra) vector
  rw [enter_dispatch] at entry
  obtain ⟨output, entered⟩ := entry
  let middle := call.entered output
  have frame := call.entered_frame output
  let nextData := input.transport frame (by decide) (by decide) (by decide) (by decide)
    (X86Flags.mergeFlags call.fuel.flags output) (call.entered_flags output) preserved.code preserved.outputBase
      preserved.outputLength preserved.premiseBase preserved.premiseLength preserved.field
  let here := X86AllowanceCall.basisAt call.prologue.code 24 codeUpper (by decide) (call.enteredMode output)
    (call.entered_rip output)
  have placed : here.address.toInt = nextData.base + 24 := by
    change (address call.prologue.code.toInt 24).toInt = input.base + 24
    rw [X86AllowanceCall.offset_int call.prologue.code codeUpper 24 (by decide), entryAt]
    rfl
  let nextTag : X86P1LoadBounds.Readable middle nextData.premiseFacts.pointer (6661#32) := {
    tag with bytes := fun byte within => (frame.memory _ (tagApart byte within)).trans (tag.bytes byte within) }
  let nextZero : X86P1QwordBounds.Readable middle nextData.premiseFacts.pointer (0#64) := {
    zero with bytes := fun byte within => (frame.memory _ (zeroApart byte within)).trans (zero.bytes byte within) }
  let nextReceipt : X86FailureHandler.FrameFacts middle := {
    receipt with
    flags := X86Flags.mergeFlags call.fuel.flags output
    frameKnown := (frame.lookup 7 (by decide)).trans receipt.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans receipt.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans receipt.visibleKnown
    flagsKnown := call.entered_flags output
    quiet := (frame.registers .log_register_writes (by decide)).trans receipt.quiet }
  obtain ⟨body,flags,bodyRun,bodyFrame,flagsKnown,rax,rip,bytes,status,result,bodyImage⟩ :=
    body_fires (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra vector middle here nextData
      placed nextReceipt nextTag nextZero fits codeApart outputApart
  have footprint : writes nextData nextReceipt = writes input receipt := rfl
  rw [footprint] at bodyFrame
  have lower : -(2 ^ 47 : Int) ≤ input.base := input.lower
  let exit : X86AllowanceCall.Exit call output (writes input receipt) body := {
    frame := bodyFrame.mono (by decide) (Finset.Subset.refl _)
    remaining := call.fuel.budget - call.fuel.receipt
    remainingKnown := (bodyFrame.lookup 5 (by decide)).trans (call.entered_allowance output)
    flags := flags
    flagsKnown := flagsKnown
    budgetSafe := fuel.budget
    bottomSafe := fuel.bottom
    savedSafe := fuel.saved
    exitSafe := by
      intro index byte present
      have bounded : index < 28 := (List.getElem?_eq_some_iff.mp present).1
      rw [X86P1RefusedCapture.exit_address input.base call.exit exitAt input.upper lower index]
      have within : 619 + index < image.size := by rw [X86P1LoadCapture.byte_extent]; omega
      intro member
      rcases Finset.mem_union.mp member with written | receiptWord
      · rcases Finset.mem_union.mp written with outputWord | resultWord
        · exact input.codeApart _ within outputWord
        · exact codeApart _ within resultWord
      · exact fuel.code _ within receiptWord
    pointer := by rw [exitAt]; exact rip }
  obtain ⟨after, run, correct⟩ :=
    call.executes (callHandlers other extra) vector output (writes input receipt) body 88 entered bodyRun exit
      (exit_dispatch other extra)
  refine ⟨body,after,run,correct,correct.value.trans rax,?_,?_,?_,?_,?_⟩
  · intro byte within
    rw [correct.tail.memory _ (fuel.output byte within)]
    exact bytes byte within
  · intro byte within
    rw [correct.tail.memory _ (statusReceiptApart byte within)]
    exact status byte within
  · intro byte within
    rw [correct.tail.memory _ (resultReceiptApart byte within)]
    exact result byte within
  · intro byte within
    have published := correct.receipt byte within
    change after.mem.get? _ = some (BitVec.extractLsb' (8 * byte) 8
      (call.fuel.budget - (call.fuel.budget - call.fuel.receipt))) at published
    rwa [X86P1RefusedCapture.restored_receipt] at published
  · intro byte within
    rw [correct.tail.memory _ (fuel.code byte within)]
    exact bodyImage byte within

namespace Controls
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
private noncomputable abbrev seed (field : Word) := X86P1OutputCapture.Controls.fixture field
private noncomputable def before (field : Word) : State := X86Move.putPointer (seed field).state (4096#48)
private theorem frame (field : Word) : RegisterFrame {.rip} (seed field).state (before field) := pointer_frame _ _
private noncomputable def data (field : Word) : X86P1OutputCapture.DataFacts (before field) :=
  (seed field).data.transport (X86StateFrame.registerOnly (frame field)) (by decide) (by decide) (by decide) (by decide)
    (seed field).data.outputFacts.flags ((frame field).registers .rflags (by decide) |>.trans (seed field).data.outputFacts.flagsKnown)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
private theorem base_value (field : Word) : (data field).base = 4096 := (seed field).baseValue
private theorem output_value (field : Word) : (data field).output = (16384#48) := (seed field).outputValue
private theorem field_value (field : Word) : (data field).field = field := (seed field).fieldValue
private noncomputable def context (field : Word) : X86PlainFetch.Facts (before field) :=
  let old := X86PlainFetch.Facts.ofBasis (seed field).origin
  { old with
    status := ((frame field).registers .ms_reg (by decide)).trans old.status
    fault := ((frame field).registers .fault_reg (by decide)).trans old.fault
    msrs := ((frame field).registers .msrs (by decide)).trans old.msrs
    segments := ((frame field).registers .seg_hidden_attrs (by decide)).trans old.segments
    application := ((frame field).registers .app_view (by decide)).trans old.application }
private theorem stack_lower (location : Nat) (member : location ∈ X86Prologue.writes (32728#48)) : 32728 ≤ location := by
  obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have bounded : byte < 40 := List.mem_range.mp within
  have point : X86WriteWords.physicalAddress (32728#48) byte = 32728 + byte :=
    X86P1OutputCapture.Controls.positive_address 32728 byte (by omega)
  rw [← same,point]
  omega
private theorem outside_stack (location : Nat) (below : location < 32728) : location ∉ X86Prologue.writes (32728#48) := by
  intro member
  have := stack_lower location member
  omega
private theorem spill_lower (location : Nat)
    (member : location ∈ X86AllowanceCall.spillBytes (32728#48) (32720#48)) : 32720 ≤ location := by
  rcases Finset.mem_union.mp member with five | sixth
  · have := stack_lower location five
    omega
  · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp sixth)
    have point : X86WriteWords.physicalAddress (32720#48) byte = 32720 + byte :=
      X86P1OutputCapture.Controls.positive_address 32720 byte (by have := List.mem_range.mp within; omega)
    rw [← same,point]
    omega
private theorem outside_spill (location : Nat) (below : location < 32720) :
    location ∉ X86AllowanceCall.spillBytes (32728#48) (32720#48) := by
  intro member
  have := spill_lower location member
  omega
private noncomputable def prologue (field : Word) : X86Prologue.Inputs (before field) where
  bottom := 32728#48
  stackUpper := by decide
  stackKnown := by
    have point : (address (32728#48).toInt 40).signExtend 64 = (32768#64) := by decide
    rw [point]
    exact ((frame field).lookup 4 (by decide)).trans (seed field).stackKnown
  saved := fun index => Classical.choose ((seed field).wordsKnown (X86Prologue.source index))
  savedKnown := by
    intro index
    rw [(frame field).lookup (X86Prologue.source index) (by fin_cases index <;> decide)]
    exact Classical.choose_spec ((seed field).wordsKnown (X86Prologue.source index))
  returnAddress := 0x9000#48
  returnBytes := by
    intro byte within
    have point : address (32728#48).toInt 40 = (32768#48) := by decide
    rw [point]
    change (seed field).state.mem.get? (X86WriteWords.physicalAddress (32768#48) byte) = _
    exact (seed field).returnBytes byte within
  visible := (data field).outputFacts.visible
  controls := (data field).outputFacts.controls
  flags := (data field).outputFacts.flags
  visibleKnown := (data field).outputFacts.visibleKnown
  controlsKnown := (data field).outputFacts.controlKnown
  flagsKnown := (data field).outputFacts.flagsKnown
  quiet := (data field).outputFacts.quiet
  aligned := by decide
  context := context field
  code := 4096#48
  codeUpper := by decide
  loaded := by
    intro byte encoded present
    have within : byte < 9 := (List.getElem?_eq_some_iff.mp present).1
    have capture := X86P1RefusedCapture.captured_entry ⟨byte,by omega⟩
    rw [show (X86Prologue.expected ++ X86AllowanceCall.entryCode)[byte]? = X86Prologue.expected[byte]? from
      List.getElem?_append_left within,present,Option.map_some] at capture
    have got := (data field).loaded byte (by rw [X86P1LoadCapture.byte_extent]; omega)
    rw [base_value] at got
    exact got.trans capture
  rip := by simp [before,X86Move.putPointer]
  codeOutside := by
    intro byte encoded present
    have within : byte < 9 := (List.getElem?_eq_some_iff.mp present).1
    have point := X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)
    change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
    change ((address 4096 byte).signExtend 52).toNat ∉ X86Prologue.writes (32728#48)
    rw [point]
    exact outside_stack _ (by omega)
private noncomputable def savedRbp (field : Word) : Word := Classical.choose ((seed field).wordsKnown 5)
private theorem fuel_point (byte : Nat) (within : byte < 16) :
    ((address 8352 byte).signExtend 52).toNat = 8352 + byte :=
  X86P1OutputCapture.Controls.positive_address 8352 byte (by omega)
private noncomputable def caller (field : Word) : X86AllowanceCall.Inputs (before field) where
  prologue := prologue field
  bottom := 32720#48
  savedRbp := savedRbp field
  rbpKnown := ((frame field).lookup 5 (by decide)).trans (Classical.choose_spec ((seed field).wordsKnown 5))
  step := by change (32720#48).toInt + 8 = (32728#48).toInt; decide
  aligned := by decide
  codeUpper := by change (4096#48).toInt + 24 < (2 ^ 47 : Int); decide
  entryLoaded := by
    intro byte encoded present
    have within : byte < 15 := (List.getElem?_eq_some_iff.mp present).1
    have capture := X86P1RefusedCapture.captured_entry ⟨9 + byte,by omega⟩
    have shift : (X86Prologue.expected ++ X86AllowanceCall.entryCode)[9 + byte]? = X86AllowanceCall.entryCode[byte]? := by
      rw [List.getElem?_append_right (by simp [X86Prologue.expected])]
      congr 1
      simp [X86Prologue.expected]
    change X86P1LoadCapture.propImage.view.read (9 + byte) = _ at capture
    rw [shift,present,Option.map_some] at capture
    change (before field).mem.get? ((address ((4096#48).toInt + 9) byte).signExtend 52).toNat = _
    have got := (data field).loaded (9 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega)
    rw [base_value] at got
    have point : address 4096 (9 + byte) = address ((4096#48).toInt + 9) byte := by
      change BitVec.ofInt 48 ((4096 : Int) + ((9 + byte : Nat) : Int)) = BitVec.ofInt 48 ((4096 : Int) + 9 + byte)
      exact congrArg (BitVec.ofInt 48) (by omega)
    rw [point] at got
    exact got.trans capture
  entrySafe := by
    intro byte encoded present
    have within : byte < 15 := (List.getElem?_eq_some_iff.mp present).1
    have point : ((address ((4096#48).toInt + 9) byte).signExtend 52).toNat = 4105 + byte := by
      have shifted : address ((4096#48).toInt + 9) byte = address 4105 byte := by
        change BitVec.ofInt 48 ((4096 : Int) + 9 + byte) = BitVec.ofInt 48 ((4105 : Int) + byte)
        exact congrArg (BitVec.ofInt 48) (by omega)
      rw [shifted]
      exact X86P1OutputCapture.Controls.positive_address 4105 byte (by omega)
    change ((address ((4096#48).toInt + 9) byte).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes (32728#48) (32720#48)
    rw [point]
    exact outside_spill _ (by omega)
  fuel := {
    frame := 8192#64
    frameKnown := (data field).outputFacts.frameKnown
    budgetAddress := 8352#48
    budgetUpper := by decide
    budgetEffective := by decide
    budgetAligned := by decide
    budget := 0x1000#64
    budgetPresent := by
      intro byte within
      rw [(frame field).memory]
      exact (seed field).budgetBytes byte within
    receiptAddress := 8360#48
    receiptUpper := by decide
    receiptEffective := by decide
    receiptAligned := by decide
    receipt := 0x10#64
    receiptPresent := by
      intro byte within
      rw [(frame field).memory]
      exact (seed field).receiptBytes byte within
    visible := (data field).outputFacts.visible
    controls := (data field).outputFacts.controls
    flags := (data field).outputFacts.flags
    visibleKnown := (data field).outputFacts.visibleKnown
    controlsKnown := (data field).outputFacts.controlKnown
    flagsKnown := (data field).outputFacts.flagsKnown
    quiet := (data field).outputFacts.quiet }
  budgetSafe := by
    intro byte within
    change ((address 8352 byte).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes (32728#48) (32720#48)
    rw [fuel_point byte (by omega)]
    exact outside_spill _ (by omega)
  receiptSafe := by
    intro byte within
    change ((address 8360 byte).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes (32728#48) (32720#48)
    have point : ((address 8360 byte).signExtend 52).toNat = 8360 + byte :=
      X86P1OutputCapture.Controls.positive_address 8360 byte (by omega)
    rw [point]
    exact outside_spill _ (by omega)
  exit := 4715#48
  exitUpper := by decide
  exitLoaded := by
    intro byte encoded present
    have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
    have capture := X86P1RefusedCapture.captured_exit ⟨byte,within⟩
    rw [present,Option.map_some] at capture
    have got := (data field).loaded (619 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega)
    rw [base_value] at got
    have point : address 4096 (619 + byte) = address (4715#48).toInt byte := by
      change BitVec.ofInt 48 ((4096 : Int) + ((619 + byte : Nat) : Int)) = BitVec.ofInt 48 ((4715 : Int) + byte)
      exact congrArg (BitVec.ofInt 48) (by omega)
    rw [point] at got
    exact got.trans capture
  exitSafe := by
    intro byte encoded present
    have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
    have point : ((address (4715#48).toInt byte).signExtend 52).toNat = 4715 + byte :=
      X86P1OutputCapture.Controls.positive_address 4715 byte (by omega)
    rw [point]
    exact outside_spill _ (by omega)
private noncomputable def receipt (field : Word) : X86FailureHandler.FrameFacts (before field) :=
  let old := (seed field).receipt
  { old with
    frameKnown := ((frame field).lookup 7 (by decide)).trans old.frameKnown
    controlsKnown := ((frame field).registers .ctrs (by decide)).trans old.controlsKnown
    visibleKnown := ((frame field).registers .seg_visibles (by decide)).trans old.visibleKnown
    flagsKnown := ((frame field).registers .rflags (by decide)).trans old.flagsKnown
    quiet := ((frame field).registers .log_register_writes (by decide)).trans old.quiet }
private theorem reads_protected (field : Word) :
    X86P1SuccessCapture.ReadProtection (data field) (X86AllowanceCall.spillBytes (32728#48) (32720#48)) where
  code := by
    intro byte within
    rw [base_value]
    have bounded : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
    have point := X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)
    change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
    rw [point]
    exact outside_spill _ (by omega)
  outputBase := by
    intro byte within
    have coordinate : (data field).outputFacts.baseAddress = (8208#48) := (seed field).outputBaseValue
    rw [coordinate,show X86WriteWords.physicalAddress (8208#48) byte = 8208 + byte from X86P1OutputCapture.Controls.positive_address 8208 byte (by omega)]
    exact outside_spill _ (by omega)
  outputLength := by
    intro byte within
    have coordinate : (data field).outputFacts.lengthAddress = (8216#48) := (seed field).outputLengthValue
    rw [coordinate,show X86WriteWords.physicalAddress (8216#48) byte = 8216 + byte from X86P1OutputCapture.Controls.positive_address 8216 byte (by omega)]
    exact outside_spill _ (by omega)
  premiseBase := by
    intro byte within
    have coordinate : (data field).premiseFacts.baseAddress = (8192#48) := (seed field).premiseBaseValue
    rw [coordinate,show X86WriteWords.physicalAddress (8192#48) byte = 8192 + byte from X86P1OutputCapture.Controls.positive_address 8192 byte (by omega)]
    exact outside_spill _ (by omega)
  premiseLength := by
    intro byte within
    have coordinate : (data field).premiseFacts.lengthAddress = (8200#48) := (seed field).premiseLengthValue
    rw [coordinate,show X86WriteWords.physicalAddress (8200#48) byte = 8200 + byte from X86P1OutputCapture.Controls.positive_address 8200 byte (by omega)]
    exact outside_spill _ (by omega)
  field := by
    intro byte within
    have coordinate : (data field).fieldAddress = (12296#48) := (seed field).fieldAddressValue
    rw [coordinate,show X86WriteWords.physicalAddress (12296#48) byte = 12296 + byte from X86P1OutputCapture.Controls.positive_address 12296 byte (by omega)]
    exact outside_spill _ (by omega)
private theorem writes_below (field : Word) (location : Nat) (member : location ∈ X86P1SuccessCapture.writes (data field) (receipt field)) :
    location < 16416 := by
  change location ∈ X86P1OutputCapture.outputWrites (data field).output ∪
    (X86WriteWords.written (receipt field).statusAddress (List.range 8) ∪ X86WriteWords.written (receipt field).resultAddress (List.range 8)) at member
  have statusAddress : (receipt field).statusAddress = (8336#48) := (seed field).statusAddressValue
  have resultAddress : (receipt field).resultAddress = (8344#48) := (seed field).resultAddressValue
  rw [output_value,statusAddress,resultAddress] at member
  rcases Finset.mem_union.mp member with output | result
  · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp output)
    have bounded : byte < 32 := List.mem_range.mp within
    have point : X86WriteWords.physicalAddress (16384#48) byte = 16384 + byte := X86P1OutputCapture.Controls.positive_address 16384 byte (by omega)
    rw [point] at same
    omega
  · rcases Finset.mem_union.mp result with status | result
    · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp status)
      have bounded : byte < 8 := List.mem_range.mp within
      have point : X86WriteWords.physicalAddress (8336#48) byte = 8336 + byte := X86P1OutputCapture.Controls.positive_address 8336 byte (by omega)
      rw [point] at same
      omega
    · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp result)
      have bounded : byte < 8 := List.mem_range.mp within
      have point : X86WriteWords.physicalAddress (8344#48) byte = 8344 + byte := X86P1OutputCapture.Controls.positive_address 8344 byte (by omega)
      rw [point] at same
      omega

structure EntryFixture where
  state : State
  caller : X86AllowanceCall.Inputs state
  data : X86P1OutputCapture.DataFacts state
  receipt : X86FailureHandler.FrameFacts state
  endUnmapped : state.mem.get? 12320 = none

noncomputable def entryFixture (field : Word) : EntryFixture :=
  ⟨before field,caller field,data field,receipt field,by
    rw [(frame field).memory]
    exact X86P1OutputCapture.Controls.fixture_end_unmapped field⟩

private theorem receipt_word_below (location : Nat)
    (member : location ∈ X86AllowanceCall.receiptBytes (8360#48)) : 8360 ≤ location ∧ location < 8368 := by
  obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have bounded : byte < 8 := List.mem_range.mp within
  have point : X86WriteWords.physicalAddress (8360#48) byte = 8360 + byte :=
    X86P1OutputCapture.Controls.positive_address 8360 byte (by omega)
  rw [← same,point]
  omega

/-- Input observations at the public caller, including unobserved capacity bytes. -/
structure EntryObservations (field : Word) (entry : EntryFixture) where
  baseValue : entry.data.base = 4096
  fieldValue : entry.data.field = field
  outputValue : entry.data.output = (16384#48)
  premisePointer : entry.data.premiseFacts.pointer = (12288#64)
  premiseBase : entry.data.premiseFacts.base = (12288#64)
  premiseLength : entry.data.premiseFacts.length = (32#64)
  outputPointer : entry.data.outputFacts.pointer = (16384#64)
  outputLength : entry.data.outputFacts.length = (32#64)
  fieldAddress : entry.data.fieldAddress = (12296#48)
  entryAt : entry.caller.prologue.code.toInt = entry.data.base
  exitAt : entry.caller.exit = address entry.data.base 619
  budget : entry.caller.fuel.budget = (0x1000#64)
  receiptWord : entry.caller.fuel.receipt = (0x10#64)
  tag : X86P1LoadBounds.Readable entry.state entry.data.premiseFacts.pointer (6661#32)
  level : X86P1QwordBounds.Readable entry.state entry.data.premiseFacts.pointer (0#64)
  fits : (entry.data.premiseFacts.pointer - entry.data.premiseFacts.base).toNat + 24 ≤ entry.data.premiseFacts.length.toNat
  oldKnown : lookup entry.state 11 = some (0#64)
  preserved : ReadProtection entry.data (X86AllowanceCall.spillBytes entry.caller.prologue.bottom entry.caller.bottom)
  tagApart : ∀ byte < 4, X86WriteWords.physicalAddress tag.dataAddress byte ∉
    X86AllowanceCall.spillBytes entry.caller.prologue.bottom entry.caller.bottom
  levelApart : ∀ byte < 8, X86WriteWords.physicalAddress level.dataAddress byte ∉
    X86AllowanceCall.spillBytes entry.caller.prologue.bottom entry.caller.bottom
  codeApart : ∀ byte < image.size, ((address entry.data.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites entry.receipt
  outputApart : ∀ byte < 32, X86WriteWords.physicalAddress entry.data.output byte ∉ X86P1OutputCapture.receiptWrites entry.receipt
  statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress entry.receipt.statusAddress byte ∉
    X86AllowanceCall.receiptBytes entry.caller.fuel.receiptAddress
  resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress entry.receipt.resultAddress byte ∉
    X86AllowanceCall.receiptBytes entry.caller.fuel.receiptAddress
  fuel : FuelProtection entry.caller entry.data (writes entry.data entry.receipt)
  premiseBytes : ∀ byte : Fin 24, entry.state.mem.get? (12288 + byte.val) =
    some (X86P1OutputCapture.Controls.fixturePremiseByte field byte)
  premiseSuffixUnobserved : ∀ byte : Fin 8, entry.state.mem.get? (12312 + byte.val) = none
  outputUnobserved : ∀ byte : Fin 32, entry.state.mem.get? (16384 + byte.val) = none

noncomputable def entryObservations (field : Word) : EntryObservations field (entryFixture field) := by
  let nextTag : X86P1LoadBounds.Readable (before field) (data field).premiseFacts.pointer (6661#32) := {
    (seed field).tag with bytes := fun byte within => by rw [(frame field).memory]; exact (seed field).tag.bytes byte within }
  let nextZero : X86P1QwordBounds.Readable (before field) (data field).premiseFacts.pointer (0#64) := {
    (seed field).zero with bytes := fun byte within => by rw [(frame field).memory]; exact (seed field).zero.bytes byte within }
  have tagApart : ∀ byte < 4, X86WriteWords.physicalAddress nextTag.dataAddress byte ∉
      X86AllowanceCall.spillBytes (32728#48) (32720#48) := by
    intro byte within
    change X86WriteWords.physicalAddress (seed field).tag.dataAddress byte ∉ _
    rw [(seed field).tagAddress,show X86WriteWords.physicalAddress (12288#48) byte = 12288 + byte from X86P1OutputCapture.Controls.positive_address 12288 byte (by omega)]
    exact outside_spill _ (by omega)
  have zeroApart : ∀ byte < 8, X86WriteWords.physicalAddress nextZero.dataAddress byte ∉
      X86AllowanceCall.spillBytes (32728#48) (32720#48) := by
    intro byte within
    change X86WriteWords.physicalAddress (seed field).zero.dataAddress byte ∉ _
    rw [(seed field).zeroAddress,show X86WriteWords.physicalAddress (12304#48) byte = 12304 + byte from X86P1OutputCapture.Controls.positive_address 12304 byte (by omega)]
    exact outside_spill _ (by omega)
  have statusAddress : (receipt field).statusAddress = (8336#48) := (seed field).statusAddressValue
  have resultAddress : (receipt field).resultAddress = (8344#48) := (seed field).resultAddressValue
  have stackAbove (location : Nat) (big : 32720 ≤ location) :
      location ∉ writes (data field) (receipt field) ∪ X86AllowanceCall.receiptBytes (8360#48) := by
    intro member
    rcases Finset.mem_union.mp member with written | receiptWord
    · have := writes_below field location written
      omega
    · have := receipt_word_below location receiptWord
      omega
  have fuel : FuelProtection (caller field) (data field) (writes (data field) (receipt field)) := {
    budget := by
      intro byte within member
      change ((address 8352 byte).signExtend 52).toNat ∈ X86P1OutputCapture.outputWrites (data field).output ∪
        (X86WriteWords.written (receipt field).statusAddress (List.range 8) ∪
          X86WriteWords.written (receipt field).resultAddress (List.range 8)) at member
      rw [fuel_point byte (by omega)] at member
      rw [output_value,statusAddress,resultAddress] at member
      rcases Finset.mem_union.mp member with output | result
      · obtain ⟨index,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp output)
        have point : X86WriteWords.physicalAddress (16384#48) index = 16384 + index :=
          X86P1OutputCapture.Controls.positive_address 16384 index (by have := List.mem_range.mp inside; omega)
        rw [point] at same
        omega
      · rcases Finset.mem_union.mp result with status | result
        · obtain ⟨index,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp status)
          have point : X86WriteWords.physicalAddress (8336#48) index = 8336 + index :=
            X86P1OutputCapture.Controls.positive_address 8336 index (by have := List.mem_range.mp inside; omega)
          rw [point] at same
          have := List.mem_range.mp inside
          omega
        · obtain ⟨index,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp result)
          have point : X86WriteWords.physicalAddress (8344#48) index = 8344 + index :=
            X86P1OutputCapture.Controls.positive_address 8344 index (by have := List.mem_range.mp inside; omega)
          rw [point] at same
          have := List.mem_range.mp inside
          omega
    code := by
      intro byte within member
      rw [base_value] at member
      have bounded : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
      have point := X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)
      change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
      rw [point] at member
      have := receipt_word_below _ member
      omega
    output := by
      intro byte within member
      rw [output_value,show X86WriteWords.physicalAddress (16384#48) byte = 16384 + byte from
        X86P1OutputCapture.Controls.positive_address 16384 byte (by omega)] at member
      have := receipt_word_below _ member
      omega
    bottom := by
      intro byte within
      change X86WriteWords.physicalAddress (32720#48) byte ∉ _
      rw [show X86WriteWords.physicalAddress (32720#48) byte = 32720 + byte from
        X86P1OutputCapture.Controls.positive_address 32720 byte (by omega)]
      exact stackAbove _ (by omega)
    saved := by
      intro slot byte within
      change X86WriteWords.physicalAddress (address (32728#48).toInt (8 * slot.val)) byte ∉ _
      have point : X86WriteWords.physicalAddress (address (32728#48).toInt (8 * slot.val)) byte =
          32728 + (8 * slot.val + byte) := by
        change X86WriteWords.physicalAddress (X86Prologue.stackAt (prologue field) slot.val) byte = _
        rw [X86Prologue.stack_byte (prologue field) slot.val byte (by have := slot.isLt; omega)]
        exact X86P1OutputCapture.Controls.positive_address 32728 _ (by have := slot.isLt; omega)
      rw [point]
      exact stackAbove _ (by omega) }
  exact {
    baseValue := base_value field
    fieldValue := field_value field
    outputValue := output_value field
    premisePointer := rfl
    premiseBase := rfl
    premiseLength := rfl
    outputPointer := rfl
    outputLength := rfl
    fieldAddress := (seed field).fieldAddressValue
    entryAt := by change 4096 = (data field).base; exact (base_value field).symm
    exitAt := by change (4715#48) = address (data field).base 619; rw [base_value]; rfl
    budget := rfl
    receiptWord := rfl
    tag := nextTag
    level := nextZero
    fits := (seed field).fits
    oldKnown := ((frame field).lookup 11 (by decide)).trans (seed field).oldKnown
    preserved := reads_protected field
    tagApart := tagApart
    levelApart := zeroApart
    codeApart := (seed field).codeApart
    outputApart := (seed field).outputApart
    statusReceiptApart := by
      intro byte within member
      change X86WriteWords.physicalAddress (receipt field).statusAddress byte ∈ X86AllowanceCall.receiptBytes (8360#48) at member
      rw [statusAddress,show X86WriteWords.physicalAddress (8336#48) byte = 8336 + byte from
        X86P1OutputCapture.Controls.positive_address 8336 byte (by omega)] at member
      have := receipt_word_below _ member
      omega
    resultReceiptApart := by
      intro byte within member
      change X86WriteWords.physicalAddress (receipt field).resultAddress byte ∈ X86AllowanceCall.receiptBytes (8360#48) at member
      rw [resultAddress,show X86WriteWords.physicalAddress (8344#48) byte = 8344 + byte from
        X86P1OutputCapture.Controls.positive_address 8344 byte (by omega)] at member
      have := receipt_word_below _ member
      omega
    fuel := fuel
    premiseBytes := fun byte => by
      change (before field).mem.get? (12288 + byte.val) = _
      rw [(frame field).memory]
      exact X86P1OutputCapture.Controls.fixture_premise_byte field byte
    premiseSuffixUnobserved := fun byte => by
      change (before field).mem.get? (12312 + byte.val) = none
      rw [(frame field).memory]
      exact X86P1OutputCapture.Controls.fixture_premise_suffix_unobserved field byte
    outputUnobserved := fun byte => by
      change (before field).mem.get? (16384 + byte.val) = none
      rw [(frame field).memory]
      exact X86P1OutputCapture.Controls.fixture_output_unobserved field byte }

theorem premise_capacity_not_full_backing (field : Word) :
    ¬ ∀ byte : Fin 32, ∃ value : BitVec 8, (entryFixture field).state.mem.get? (12288 + byte.val) = some value := by
  intro readable
  obtain ⟨value,present⟩ := readable ⟨24,by decide⟩
  have absent := (entryObservations field).premiseSuffixUnobserved 0
  change (entryFixture field).state.mem.get? 12312 = none at absent
  change (entryFixture field).state.mem.get? 12312 = some value at present
  have bad : (none : Option (BitVec 8)) = some value := absent.symm.trans present
  cases bad

theorem output_not_initially_readable (field : Word) :
    ¬ ∀ byte : Fin 32, ∃ value : BitVec 8, (entryFixture field).state.mem.get? (16384 + byte.val) = some value := by
  intro readable
  obtain ⟨value,present⟩ := readable 0
  have absent := (entryObservations field).outputUnobserved 0
  change (entryFixture field).state.mem.get? 16384 = none at absent
  change (entryFixture field).state.mem.get? 16384 = some value at present
  have bad : (none : Option (BitVec 8)) = some value := absent.symm.trans present
  cases bad

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) (field : Word) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 106).run (before field) = .ok () after ∧
      lookup after 0 = some (1#64) ∧ after.regs.get? .rip = some (0x9000#64) ∧ lookup after 4 = some (32776#64) ∧
      lookup after 5 = lookup (before field) 5 ∧
      (∀ index : Fin 5, lookup after (X86Prologue.source index) = lookup (before field) (X86Prologue.source index)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (8360#48) byte) =
        some ((0x10#64).extractLsb' (8 * byte) 8)) ∧
      X86P1OutputCapture.Prefix after (16384#48) field 32 := by
  let observed := entryObservations field
  obtain ⟨body,after,run,correct,rax,bytes,_,_,receiptWord,_⟩ := X86P1SuccessCapture.public_fires other extra vector
    (before field) (caller field) (data field) observed.entryAt observed.exitAt (receipt field) observed.tag observed.level
    observed.fits observed.preserved observed.tagApart observed.levelApart observed.codeApart observed.outputApart
    observed.statusReceiptApart observed.resultReceiptApart observed.fuel
  refine ⟨after,run,rax,correct.pointer,?_,correct.frame.lookup 5 (by decide),?_,receiptWord,?_⟩
  · have point : (address (32720#48).toInt 56).signExtend 64 = (32776#64) := by decide
    exact correct.stackPointer.trans (congrArg some point)
  · intro index
    exact correct.frame.lookup (X86Prologue.source index) (by fin_cases index <;> decide)
  · simpa only [output_value,field_value] using bytes

theorem wrong_zero_return_rejected (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) (field : Word) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∀ after, lookup after 0 = some (0#64) → (X86FuelPrefix.fetches 106).run (before field) ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,value,_⟩ := control other extra vector field
  intro after zero observed
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  have different : (1#64) ≠ (0#64) := by decide
  exact different (Option.some.inj (value.symm.trans (by simpa only [same] using zero)))

#print axioms control
#print axioms wrong_zero_return_rejected

end Controls

#print axioms body_fires
#print axioms public_fires
end Mettapedia.Machines.TIsa.X86P1SuccessCapture
