import Mettapedia.Machines.TIsa.X86P1SuccessCapture

/-!
# Both guard-refusal paths of the actual p1 image

One captured failure-handler contract covers the two refusal blocks at 524 and
552. Guard composition establishes the 14/26-instruction bodies and the
32/44-instruction public allowance calls. Refusal writes both zero outcome
words, republishes the unchanged receipt, restores the ABI, preserves the
input image and retains the previous output under explicit separation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1RejectionCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
noncomputable abbrev image := X86P1LoadCapture.propImage
noncomputable abbrev handlers := X86P1SuccessCapture.handlers
def site : Fin 2 → Nat | ⟨0,_⟩ => 524 | ⟨1,_⟩ => 552
def displacement : Fin 2 → BitVec 32 | ⟨0,_⟩ => 67 | ⟨1,_⟩ => 39
def code (index : Fin 2) : List Nat := X86FailureHandler.expected (0#32) (displacement index)
theorem site_bound : ∀ index : Fin 2, site index ≤ 552 := by decide
theorem fixup : ∀ index : Fin 2, (site index : Int) + 28 + (displacement index).toInt = 619 := by decide
theorem bytes (index : Fin 2) (byte : Fin 28) :
    image.view.read (site index + byte.val) = ((code index)[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> fin_cases byte <;> kernel_reflexivity
theorem loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 2)
    (placed : origin.address.toInt = base + site index) (imageLoaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (code index) := by
  intro byte value present
  have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
  have capture := bytes index ⟨byte,within⟩
  rw [present,Option.map_some] at capture
  have shift : address base (site index + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have bounded : site index + byte < image.size := by
    rw [X86P1LoadCapture.byte_extent]
    have sites : ∀ i : Fin 2, site i ≤ 552 := by decide
    have := sites index
    omega
  simpa only [shift] using (imageLoaded (site index + byte) bounded).trans capture

def handlerInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 2)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + site index)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 647 < (2 ^ 47 : Int))
    (imageLoaded : X86P1LoadCapture.Loaded image state base)
    (apart : ∀ byte < image.size, ((address base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites facts) :
    X86FailureHandler.Inputs state (0#32) where
  toBasis := origin
  toFrameFacts := facts
  displacement := displacement index
  epilogue := address base 619
  upper := by
    rw [placed]
    have := site_bound index
    omega
  jump := by
    rw [address_toInt base (extent := 647) lower upper 619 (by decide),placed]
    have := fixup index
    omega
  loaded := loaded state base origin index placed imageLoaded
  codeOutside := by
    intro byte value present
    have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
    have shift : address origin.address.toInt byte = address base (site index + byte) := by
      unfold address
      rw [placed]
      congr 1
      omega
    rw [shift]
    have bounded : site index + byte < image.size := by
      rw [X86P1LoadCapture.byte_extent]
      have sites : ∀ i : Fin 2, site i ≤ 552 := by decide
      have := sites index
      omega
    exact apart (site index + byte) bounded

theorem handler_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 2)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + site index)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 647 < (2 ^ 47 : Int))
    (imageLoaded : X86P1LoadCapture.Loaded image state base)
    (apart : ∀ byte < image.size, ((address base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites facts) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      X86StateFrame.Frame {.rax,.rip} (X86P1OutputCapture.receiptWrites facts) state after ∧
      after.regs.get? .rflags = some facts.flags ∧ lookup after 0 = some (0#64) ∧
      after.regs.get? .rip = some ((address base 619).signExtend 64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress byte) = some (0#8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress byte) = some (0#8)) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := handlerInput state base origin index facts placed lower upper imageLoaded apart
  have run := X86FailureHandler.executes (handlers other extra) vector state (0#32) input
  have installed : X86FailureHandler.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [installed] at run
  let after := X86FailureHandler.finished state input
  have correct := X86FailureHandler.finished_result state (0#32) input
  refine ⟨after,run,correct.frame,correct.flags,correct.rax,correct.pointer,?_,?_,?_⟩
  · intro byte within
    have observed := correct.status byte within
    have coordinate : input.statusAddress = facts.statusAddress := rfl
    rw [coordinate] at observed
    simpa only [after,show (0#32).signExtend 64 = (0#64) from rfl,BitVec.extractLsb'_zero] using observed
  · intro byte within
    have observed := correct.result byte within
    have coordinate : input.resultAddress = facts.resultAddress := rfl
    rw [coordinate] at observed
    simpa only [after,show (0#32).zeroExtend 64 = (0#64) from rfl,BitVec.extractLsb'_zero] using observed
  · intro byte within
    exact (correct.frame.memory _ (apart byte within)).trans (imageLoaded byte within)

def rejectedSite (tag : BitVec 32) : Fin 2 := if tag = (6661#32) then 0 else 1
def guardSteps (tag : BitVec 32) : Nat := if tag = (6661#32) then 22 else 10

theorem body_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : X86P1OutputCapture.DataFacts state)
    (placed : origin.address.toInt = input.base + 24) (receipt : X86FailureHandler.FrameFacts state)
    (tag : BitVec 32) (tagReadable : X86P1LoadBounds.Readable state input.premiseFacts.pointer tag)
    (level : Word) (levelReadable : tag = (6661#32) → X86P1QwordBounds.Readable state input.premiseFacts.pointer level)
    (fits : tag = (6661#32) → (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (tagFits : (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 4 ≤ input.premiseFacts.length.toNat)
    (rejected : tag ≠ (6661#32) ∨ level ≠ (0#64))
    (codeApart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (guardSteps tag + 4)).run state = .ok () after ∧
      X86StateFrame.Frame X86P1SuccessCapture.clobbers (X86P1OutputCapture.receiptWrites receipt) state after ∧
      after.regs.get? .rflags = some flags ∧ lookup after 0 = some (0#64) ∧
      after.regs.get? .rip = some ((address input.base 619).signExtend 64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some (0#8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some (0#8)) ∧
      X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let facts := X86P1SuccessCapture.guardFacts state origin input placed
  obtain ⟨middle,flags,first,firstFrame,_,flagsKnown,firstRip,middleImage⟩ :=
    X86P1QwordGuardCapture.two_guard_prefix (X86FailureHandler.linkedHandlers other) extra vector state input.base origin facts
      placed input.loaded tag tagReadable tagFits level levelReadable fits
  rw [X86P1SuccessCapture.guard_handlers] at first
  have rejectedRip : middle.regs.get? .rip = some ((address input.base (site (rejectedSite tag))).signExtend 64) := by
    by_cases same : tag = (6661#32)
    · have nonzero : level ≠ (0#64) := rejected.resolve_left (by simpa using same)
      simpa only [if_pos same,if_neg nonzero,rejectedSite,site] using firstRip
    · simpa only [if_neg same,rejectedSite,site] using firstRip
  have small := site_bound (rejectedSite tag)
  let here := X86StateFrame.basisAt state middle origin (X86StateFrame.registerOnly firstFrame)
    (by decide) (address input.base (site (rejectedSite tag)))
    (by rw [address_toInt input.base (extent := 647) input.lower input.upper _ (by omega)]; have := input.upper; omega) rejectedRip
  have nextPlaced : here.address.toInt = input.base + site (rejectedSite tag) :=
    address_toInt input.base (extent := 647) input.lower input.upper _ (by omega)
  let nextReceipt := X86P1SuccessCapture.receiptAt receipt firstFrame flags flagsKnown
  obtain ⟨after,last,lastFrame,lastFlags,rax,rip,status,result,image⟩ :=
    handler_executes other extra vector middle input.base here (rejectedSite tag) nextReceipt nextPlaced input.lower input.upper middleImage codeApart
  have footprint : X86P1OutputCapture.receiptWrites nextReceipt = X86P1OutputCapture.receiptWrites receipt := rfl
  rw [footprint] at lastFrame
  exact ⟨after,flags,X86FuelPrefix.fetches_then (guardSteps tag) 4 state middle after first last,
    ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono (by decide) (by simp),
    lastFlags,rax,rip,status,result,image⟩

theorem public_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (input : X86P1OutputCapture.DataFacts state)
    (entry : call.prologue.code.toInt = input.base) (exitAt : call.exit = address input.base 619)
    (receipt : X86FailureHandler.FrameFacts state)
    (tag : BitVec 32) (tagReadable : X86P1LoadBounds.Readable state input.premiseFacts.pointer tag)
    (level : Word) (levelReadable : tag = (6661#32) → X86P1QwordBounds.Readable state input.premiseFacts.pointer level)
    (fits : tag = (6661#32) → (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (tagFits : (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 4 ≤ input.premiseFacts.length.toNat)
    (rejected : tag ≠ (6661#32) ∨ level ≠ (0#64))
    (preserved : X86P1SuccessCapture.ReadProtection input (X86AllowanceCall.spillBytes call.prologue.bottom call.bottom))
    (tagApart : ∀ byte < 4, X86WriteWords.physicalAddress tagReadable.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (levelApart : ∀ same : tag = (6661#32), ∀ byte < 8,
      X86WriteWords.physicalAddress (levelReadable same).dataAddress byte ∉
        X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (codeApart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputSpillApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (fuel : X86P1SuccessCapture.FuelProtection call input (X86P1OutputCapture.receiptWrites receipt)) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches (guardSteps tag + 22)).run state = .ok () after ∧
      X86AllowanceCall.Result call (X86P1OutputCapture.receiptWrites receipt) (call.fuel.budget - call.fuel.receipt)
        body after ∧ lookup after 0 = some (0#64) ∧
      (∀ byte < 32, after.mem.get? (X86WriteWords.physicalAddress input.output byte) = state.mem.get? (X86WriteWords.physicalAddress input.output byte)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some (0#8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some (0#8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress byte) =
        some (call.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  have codeUpper : call.prologue.code.toInt + 647 < (2 ^ 47 : Int) := by rw [entry]; exact input.upper
  have enter := call.enters (X86P1SuccessCapture.callHandlers other extra) vector
  rw [X86P1SuccessCapture.enter_dispatch] at enter
  obtain ⟨output, entered⟩ := enter
  let middle := call.entered output
  have frame := call.entered_frame output
  let nextData := input.transport frame (by decide) (by decide) (by decide) (by decide)
    (X86Flags.mergeFlags call.fuel.flags output) (call.entered_flags output) preserved.code preserved.outputBase
      preserved.outputLength preserved.premiseBase preserved.premiseLength preserved.field
  let here := X86AllowanceCall.basisAt call.prologue.code 24 codeUpper (by decide) (call.enteredMode output)
    (call.entered_rip output)
  have placed : here.address.toInt = nextData.base + 24 := by
    change (address call.prologue.code.toInt 24).toInt = input.base + 24
    rw [X86AllowanceCall.offset_int call.prologue.code codeUpper 24 (by decide), entry]
    rfl
  let nextTag : X86P1LoadBounds.Readable middle nextData.premiseFacts.pointer tag := {
    tagReadable with bytes := fun byte within => (frame.memory _ (tagApart byte within)).trans (tagReadable.bytes byte within) }
  let nextLevel (same : tag = (6661#32)) : X86P1QwordBounds.Readable middle nextData.premiseFacts.pointer level := {
    levelReadable same with bytes := fun byte within =>
      (frame.memory _ (levelApart same byte within)).trans ((levelReadable same).bytes byte within) }
  let nextReceipt : X86FailureHandler.FrameFacts middle := {
    receipt with
    flags := X86Flags.mergeFlags call.fuel.flags output
    frameKnown := (frame.lookup 7 (by decide)).trans receipt.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans receipt.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans receipt.visibleKnown
    flagsKnown := call.entered_flags output
    quiet := (frame.registers .log_register_writes (by decide)).trans receipt.quiet }
  obtain ⟨body,flags,run,bodyFrame,flagsKnown,rax,rip,status,result,bodyImage⟩ :=
    body_refuses (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra vector middle here nextData
      placed nextReceipt tag nextTag level nextLevel fits tagFits rejected codeApart
  have footprint : X86P1OutputCapture.receiptWrites nextReceipt = X86P1OutputCapture.receiptWrites receipt := rfl
  rw [footprint] at bodyFrame
  let exit : X86AllowanceCall.Exit call output (X86P1OutputCapture.receiptWrites receipt) body := {
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
      rw [X86P1RefusedCapture.exit_address input.base call.exit exitAt input.upper input.lower index]
      have within : 619 + index < image.size := by rw [X86P1LoadCapture.byte_extent]; omega
      intro member
      rcases Finset.mem_union.mp member with written | receiptWord
      · exact codeApart _ within written
      · exact fuel.code _ within receiptWord
    pointer := by rw [exitAt]; exact rip }
  obtain ⟨after, whole, correct⟩ :=
    call.executes (X86P1SuccessCapture.callHandlers other extra) vector output (X86P1OutputCapture.receiptWrites receipt)
      body (guardSteps tag + 4) entered run exit (X86P1SuccessCapture.exit_dispatch other extra)
  have count : 8 + (guardSteps tag + 4) + 10 = guardSteps tag + 22 := by omega
  rw [count] at whole
  refine ⟨body,after,whole,correct,correct.value.trans rax,?_,?_,?_,?_,?_⟩
  · intro byte within
    apply correct.frame.memory
    intro member
    rcases Finset.mem_union.mp member with spillOrWritten | receiptWord
    · rcases Finset.mem_union.mp spillOrWritten with spill | written
      · exact outputSpillApart byte within spill
      · exact outputApart byte within written
    · exact fuel.output byte within receiptWord
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

#print axioms handler_executes
#print axioms body_refuses
#print axioms public_refuses
end Mettapedia.Machines.TIsa.X86P1RejectionCapture
