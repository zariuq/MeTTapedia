import Mettapedia.Machines.TIsa.X86P1Sub1Output
import Mettapedia.Machines.TIsa.X86FailureHandler

/-!
# Returns in the allowance-bearing Micromath sub1 image

The nine source returns publish status and payload through the concrete
frame and branch to the common fuel-receipt block.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Exit

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86P1Sub1Allowance (sub1 code_int)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Site where
  immediate : P1Capture.Span
  terminal : P1Capture.Span
  outcome : ExitStatus

def Site.decode? (program : P1Capture.Program) (terminal : P1Capture.Span) : Option Site := do
  let .ret outcome 8 ← program.source.body.atPath (← terminal.path) | none
  let immediate ← program.spans.find? (fun span => span.kind == "IMM" && span.offset + span.length == terminal.offset)
  if program.source.body.atPath (← immediate.path) =
      some (.instruction (.immediate .u64 8 outcome.word)) then
    some ⟨immediate, terminal, outcome⟩
  else none

noncomputable def returns : List P1Capture.Span := sub1.spans.filter (fun span => span.kind == "RETURN")

noncomputable def sites : List Site := (returns.mapM (Site.decode? sub1)).getD []

theorem decoded : returns.mapM (Site.decode? sub1) = some sites := by kernel_reflexivity

theorem site_count : sites.length = 9 := by kernel_reflexivity

noncomputable def site (i : Fin 9) : Site := sites[i.val]'(by rw [site_count]; exact i.isLt)

def Site.start (s : Site) : Nat := s.immediate.offset

def Site.delta (s : Site) : Int := (1568 : Int) - s.start - 28

def Site.displacement (s : Site) : BitVec 32 := BitVec.ofInt 32 s.delta

def Site.bytes (s : Site) : List Nat :=
  X86FailureHandler.expected (s.outcome.word.extractLsb' 0 32) s.displacement

theorem geometry (i : Fin 9) :
    (site i).start + 28 ≤ 1568 ∧ (site i).displacement.toInt = (site i).delta := by
  fin_cases i <;> exact ⟨of_decide_eq_true (by kernel_reflexivity), by kernel_reflexivity⟩

theorem exact_bytes (i : Fin 9) :
    NativeImage.readRange? sub1.view (site i).start (site i).bytes.length =
      some ((site i).bytes.map (BitVec.ofNat 8)) := by
  fin_cases i <;> kernel_reflexivity

theorem success : (site 0).start = 1277 ∧ (site 0).outcome = .completed := by
  exact ⟨by kernel_reflexivity, by kernel_reflexivity⟩

theorem capacity : (site 1).start = 1305 ∧ (site 1).outcome = .unsupported := by
  exact ⟨by kernel_reflexivity, by kernel_reflexivity⟩

theorem premise_exit (i : Fin 7) :
    ∃ exit : Fin 9, (site exit).start = (X86P1Sub1Guards.site (X86P1Sub1Guards.PremiseGuards.guardIndex i)).no ∧
      (site exit).outcome = .refused := by
  fin_cases i <;> first
    | exact ⟨2, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨3, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨4, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨5, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨6, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨7, by kernel_reflexivity, by kernel_reflexivity⟩
    | exact ⟨8, by kernel_reflexivity, by kernel_reflexivity⟩

theorem changed_status :
    NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 1289) (site 0).start (site 0).bytes.length ≠
      some ((site 0).bytes.map (BitVec.ofNat 8)) :=
  of_decide_eq_true (by kernel_reflexivity)

abbrev frameWrites {state : State} (frame : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written frame.statusAddress (List.range 8) ∪ X86WriteWords.written frame.resultAddress (List.range 8)

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86P1Sub1Guards.handlers (X86FailureHandler.linkedHandlers (X86Stack.linkedHandlers other)) extra

theorem return_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FailureHandler.linkedHandlers (handlers other extra) = handlers other extra := rfl

theorem receipt_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1Sub1Fuel.Receipt.handlers (handlers other extra) = handlers other extra := rfl

theorem restores_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Stack.linkedHandlers (handlers other extra) = handlers other extra := rfl

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (i : Fin 9) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (site i).start).signExtend 64))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view)
    (frame : X86FailureHandler.FrameFacts state)
    (codeApart : ∀ offset byte, sub1.view.read offset = some byte →
      ((address base.toInt offset).signExtend 52).toNat ∉ frameWrites frame) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt 1568).signExtend 64) ∧
      X86StateFrame.Frame {.rax, .rip} (frameWrites frame) state after ∧
      lookup after 0 = some (site i).outcome.word ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress frame.statusAddress index) =
        some ((site i).outcome.word.extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress frame.resultAddress index) =
        some ((site i).outcome.word.extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rflags = some frame.flags ∧ X86CodePlacement.Placed after base.toInt sub1.view := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let s := site i
  have size := X86P1Sub1Allowance.exported_identity.2.2
  obtain ⟨fits, delta⟩ := geometry i
  have bound : s.start + 3 ≤ sub1.size := by change (site i).start + 3 ≤ sub1.size; omega
  let origin := X86P1Sub1Fuel.basis base s.start upper bound mode rip
  have position : origin.address.toInt = base.toInt + s.start := code_int base upper _ (by omega)
  have receiptPosition : (address base.toInt 1568).toInt = base.toInt + 1568 := code_int base upper _ (by omega)
  let input : X86FailureHandler.Inputs state (s.outcome.word.extractLsb' 0 32) :=
    { toBasis := origin
      toFrameFacts := frame
      displacement := s.displacement
      epilogue := address base.toInt 1568
      upper := by
        rw [position]
        change base.toInt + (site i).start + 28 < (2 ^ 47 : Int)
        omega
      jump := by
        change (address base.toInt 1568).toInt = origin.address.toInt + 28 + (site i).displacement.toInt
        rw [receiptPosition, position, delta, Site.delta]
        change base.toInt + 1568 = base.toInt + (site i).start + 28 + (1568 - (site i).start - 28 : Int)
        omega
      loaded := X86CodePlacement.code_of_read_range state base.toInt sub1.view _ _ s.bytes position placed (exact_bytes i)
      codeOutside := by
        intro index byte present
        change (site i).bytes[index]? = some byte at present
        have range := X86CodePlacement.read_range_byte sub1.view s.start s.bytes.length _ (exact_bytes i)
          index (BitVec.ofNat 8 byte) (List.getElem?_eq_some_iff.mp present).1
          (by simp only [List.getElem?_map, present, Option.map_some])
        have shifted : address origin.address.toInt index = address base.toInt (s.start + index) := by
          rw [position]
          simp only [address, Nat.cast_add, Int.add_assoc]
        rw [shifted]
        exact codeApart _ _ range }
  let after := X86FailureHandler.finished state input
  have run := X86FailureHandler.executes (handlers other extra) vector state _ input
  rw [return_dispatch] at run
  have result := X86FailureHandler.finished_result state _ input
  obtain ⟨rax, status, payload⟩ := X86FailureHandler.outcome_words state after s.outcome input result
  exact ⟨after, run, result.pointer, result.frame, rax, status, payload, result.flags,
    result.image_preserved base.toInt sub1.view placed codeApart⟩

open X86P1Sub1Fuel.Receipt (Facts)

abbrev receiptWrites {state : State} (fuel : Facts state) : Finset Nat :=
  X86WriteWords.written fuel.receiptAddress (List.range 8)

abbrev receiptRegisters : Finset Register := {.rax, .r14, .rflags, .rip}

theorem writes_receipt (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (i : Fin 9) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (site i).start).signExtend 64))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view)
    (frame : X86FailureHandler.FrameFacts state) (fuel : Facts state)
    (budgetSafe : ∀ index < 8, X86WriteWords.physicalAddress fuel.budgetAddress index ∉ frameWrites frame)
    (statusSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.statusAddress index ∉ receiptWrites fuel)
    (resultSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.resultAddress index ∉ receiptWrites fuel)
    (codeSafe : ∀ offset byte, sub1.view.read offset = some byte →
      ((address base.toInt offset).signExtend 52).toNat ∉ frameWrites frame ∪ receiptWrites fuel) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 7).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt X86P1Sub1Allowance.restoreOffset).signExtend 64) ∧
      X86StateFrame.Frame receiptRegisters (frameWrites frame ∪ receiptWrites fuel) state after ∧
      lookup after 0 = some (site i).outcome.word ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress frame.statusAddress n) =
        some ((site i).outcome.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress frame.resultAddress n) =
        some ((site i).outcome.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress fuel.receiptAddress n) =
        some ((fuel.budget - fuel.remaining).extractLsb' (8 * n) 8)) ∧
      after.regs.get? .rflags = some flags ∧ X86CodePlacement.Placed after base.toInt sub1.view := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, returned, atReceipt, returnedFrame, rax, status, result, knownFlags, stillPlaced⟩ :=
    executes other extra vector i state base upper mode rip placed frame
      (fun offset byte observed written => codeSafe offset byte observed (Finset.mem_union_left _ written))
  have firstData : ({.rax, .rip} : Finset Register) ⊆ dataRegisters := by decide
  let receipt : X86P1Sub1Fuel.Receipt.Inputs middle :=
    { fuel.transport returnedFrame firstData (by decide) (by decide) budgetSafe frame.flags knownFlags with
      mode := X86P1Sub1Guards.PremiseGuards.modeAfterRegisters mode
        (fun r outside => returnedFrame.registers r (fun ins => outside (firstData ins)))
      base := base
      codeUpper := upper
      placed := stillPlaced
      rip := atReceipt }
  have publishes := X86P1Sub1Fuel.Receipt.publishes (handlers other extra) vector middle receipt
  rw [receipt_dispatch] at publishes
  obtain ⟨flags, written, next, wroteFrame, bytes⟩ := publishes
  let after := X86P1Sub1Fuel.Receipt.afterWrite receipt flags
  have joined : X86StateFrame.Frame receiptRegisters (frameWrites frame ∪ receiptWrites fuel) state after :=
    (returnedFrame.trans wroteFrame).mono (by decide) (Finset.Subset.refl _)
  refine ⟨after, X86Flags.mergeFlags frame.flags flags,
    X86FuelPrefix.fetches_then 4 3 state middle after returned written, next, joined,
    (wroteFrame.lookup 0 (by decide)).trans rax,
    fun n inside => (wroteFrame.memory _ (statusSafe n inside)).trans (status n inside),
    fun n inside => (wroteFrame.memory _ (resultSafe n inside)).trans (result n inside),
    bytes, X86P1Sub1Fuel.Receipt.flags_after_write receipt flags, ?_⟩
  exact X86CodePlacement.Placed.preserved _ _ placed joined codeSafe

structure SavedStack (state : State) where
  bottom : BitVec 48
  stack : BitVec 48
  step : bottom.toInt + 8 = stack.toInt
  upper : stack.toInt + 48 < (2 ^ 47 : Int)
  current : lookup state 4 = some (bottom.signExtend 64)
  rbp : Word
  saved : Fin 5 → Word
  returnAddress : BitVec 48
  bottomAligned : bottom &&& (7#48) = 0#48
  bottomBytes : ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress bottom index) =
    some (rbp.extractLsb' (8 * index) 8)
  aligned : ∀ slot : Fin 6, address stack.toInt (8 * slot.val) &&& (7#48) = 0#48
  present : ∀ slot : Fin 6, ∀ byte < 8,
    state.mem.get? (X86WriteWords.physicalAddress (address stack.toInt (8 * slot.val)) byte) =
      some ((if within : slot.val < 5 then saved ⟨slot.val, within⟩ else returnAddress.signExtend 64).extractLsb' (8 * byte) 8)

abbrev tailWrites {state : State} (frame : X86FailureHandler.FrameFacts state) (fuel : Facts state) : Finset Nat :=
  frameWrites frame ∪ receiptWrites fuel

abbrev tailRegisters : Finset Register := insert .rbp (receiptRegisters ∪ X86Epilogue.clobbers)

noncomputable def SavedStack.restoreInputs {state after : State} {written : Finset Nat}
    (stack : SavedStack state) (fuel : Facts state)
    (framed : X86StateFrame.Frame receiptRegisters written state after)
    (mode : X86PlainFetch.Facts state) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed after base.toInt sub1.view)
    (rip : after.regs.get? .rip = some ((address base.toInt X86P1Sub1Allowance.restoreOffset).signExtend 64))
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags)
    (bottomSafe : ∀ index < 8, X86WriteWords.physicalAddress stack.bottom index ∉ written)
    (savedSafe : ∀ slot : Fin 6, ∀ index < 8,
      X86WriteWords.physicalAddress (address stack.stack.toInt (8 * slot.val)) index ∉ written) :
    X86P1Sub1Allowance.RestoreInputs after := by
  have visible := (framed.registers .seg_visibles (by decide)).trans fuel.visibleKnown
  have controls := (framed.registers .ctrs (by decide)).trans fuel.controlsKnown
  have quiet := (framed.registers .log_register_writes (by decide)).trans fuel.quiet
  let code := address base.toInt (X86P1Sub1Allowance.restoreOffset + 1)
  let popped := X86Stack.pop_frame after 5 stack.rbp stack.stack code
  have data : receiptRegisters ⊆ dataRegisters := by decide
  have context := X86P1Sub1Guards.PremiseGuards.modeAfterRegisters mode
    (fun r outside => framed.registers r (fun ins => outside (data ins)))
  exact {
    context := context
    base := base
    bottom := stack.bottom
    stack := stack.stack
    rbp := stack.rbp
    codeUpper := upper
    placed := placed
    stackStep := stack.step
    stackUpper := by have := stack.step; have := stack.upper; omega
    rip := rip
    stackKnown := (framed.lookup 4 (by decide)).trans stack.current
    visible := fuel.visible
    controls := fuel.controls
    flags := flags
    controlsKnown := controls
    flagsKnown := flagsKnown
    visibleKnown := visible
    quiet := quiet
    aligned := stack.bottomAligned
    present := fun index within => (framed.memory _ (bottomSafe index within)).trans (stack.bottomBytes index within)
    remaining :=
      { stack := stack.stack
        stackUpper := stack.upper
        stackKnown := X86Stack.pop_stack after 5 stack.rbp stack.stack code (by decide)
        saved := stack.saved
        returnAddress := stack.returnAddress
        visible := fuel.visible
        controls := fuel.controls
        flags := flags
        visibleKnown := (popped.registers .seg_visibles (by decide)).trans visible
        controlsKnown := (popped.registers .ctrs (by decide)).trans controls
        flagsKnown := (popped.registers .rflags (by decide)).trans flagsKnown
        quiet := (popped.registers .log_register_writes (by decide)).trans quiet
        aligned := stack.aligned
        present := by
          intro slot index within
          rw [show (X86P1Sub1Allowance.afterRbp after base stack.stack stack.rbp).mem = after.mem from popped.memory]
          exact (framed.memory _ (savedSafe slot index within)).trans (stack.present slot index within) }
    remainingStack := rfl }

theorem returns_to_caller (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (i : Fin 9) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (site i).start).signExtend 64))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view)
    (frame : X86FailureHandler.FrameFacts state) (fuel : Facts state) (stack : SavedStack state)
    (budgetSafe : ∀ index < 8, X86WriteWords.physicalAddress fuel.budgetAddress index ∉ frameWrites frame)
    (statusSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.statusAddress index ∉ receiptWrites fuel)
    (resultSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.resultAddress index ∉ receiptWrites fuel)
    (codeSafe : ∀ offset byte, sub1.view.read offset = some byte →
      ((address base.toInt offset).signExtend 52).toNat ∉ tailWrites frame fuel)
    (bottomSafe : ∀ index < 8, X86WriteWords.physicalAddress stack.bottom index ∉ tailWrites frame fuel)
    (savedSafe : ∀ slot : Fin 6, ∀ index < 8,
      X86WriteWords.physicalAddress (address stack.stack.toInt (8 * slot.val)) index ∉ tailWrites frame fuel) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 14).run state = .ok () after ∧
      after.regs.get? .rip = some (stack.returnAddress.signExtend 64) ∧
      lookup after 4 = some ((address stack.bottom.toInt 56).signExtend 64) ∧
      lookup after 5 = some stack.rbp ∧
      (∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (stack.saved slot)) ∧
      X86StateFrame.Frame tailRegisters (tailWrites frame fuel) state after ∧
      lookup after 0 = some (site i).outcome.word ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress frame.statusAddress n) =
        some ((site i).outcome.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress frame.resultAddress n) =
        some ((site i).outcome.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress fuel.receiptAddress n) =
        some ((fuel.budget - fuel.remaining).extractLsb' (8 * n) 8)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, receipt, beforeRestore, written, rax, status, value, spent, known, placedMiddle⟩ :=
    writes_receipt other extra vector i state base upper mode rip placed frame fuel budgetSafe statusSafe resultSafe codeSafe
  let ready := stack.restoreInputs fuel written mode base upper placedMiddle beforeRestore flags known bottomSafe savedSafe
  have restores := X86P1Sub1Allowance.six_restores (handlers other extra) vector middle ready
  rw [restores_dispatch] at restores
  let after := X86P1Sub1Allowance.afterRestores ready
  obtain ⟨rbp, saved, caller, rsp, memory, valueKnown, _⟩ := X86P1Sub1Allowance.restore_result ready
  let popped := X86P1Sub1Allowance.afterRbp middle ready.base ready.stack ready.rbp
  have firstFrame := X86Stack.pop_frame middle 5 ready.rbp ready.stack
    (address ready.base.toInt (X86P1Sub1Allowance.restoreOffset + 1))
  have lastFrame := (X86Epilogue.finished_result popped (X86P1Sub1Allowance.lastRestores ready)).frame
  have joined : X86StateFrame.Frame tailRegisters (tailWrites frame fuel) state after :=
    ((written.trans (X86StateFrame.registerOnly firstFrame)).trans
      (X86StateFrame.registerOnly lastFrame)).mono (by decide) (by simp)
  refine ⟨after, X86FuelPrefix.fetches_then 7 7 state middle after receipt restores,
    caller, rsp, rbp, saved, joined, valueKnown.trans rax, ?_, ?_, ?_⟩
  · intro n inside
    rw [memory]
    exact status n inside
  · intro n inside
    rw [memory]
    exact value n inside
  · intro n inside
    rw [memory]
    exact spent n inside

structure TailFacts (base : BitVec 48) (state : State) where
  frame : X86FailureHandler.FrameFacts state
  fuel : Facts state
  stack : SavedStack state
  budgetSafe : ∀ index < 8, X86WriteWords.physicalAddress fuel.budgetAddress index ∉ frameWrites frame
  statusSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.statusAddress index ∉ receiptWrites fuel
  resultSafe : ∀ index < 8, X86WriteWords.physicalAddress frame.resultAddress index ∉ receiptWrites fuel
  codeSafe : ∀ offset byte, sub1.view.read offset = some byte →
    ((address base.toInt offset).signExtend 52).toNat ∉ tailWrites frame fuel
  bottomSafe : ∀ index < 8, X86WriteWords.physicalAddress stack.bottom index ∉ tailWrites frame fuel
  savedSafe : ∀ slot : Fin 6, ∀ index < 8,
    X86WriteWords.physicalAddress (address stack.stack.toInt (8 * slot.val)) index ∉ tailWrites frame fuel

structure TailFacts.ReadsOutside {base : BitVec 48} {state : State} (tail : TailFacts base state)
    (written : Finset Nat) : Prop where
  budget : ∀ index < 8, X86WriteWords.physicalAddress tail.fuel.budgetAddress index ∉ written
  bottom : ∀ index < 8, X86WriteWords.physicalAddress tail.stack.bottom index ∉ written
  saved : ∀ slot : Fin 6, ∀ index < 8,
    X86WriteWords.physicalAddress (address tail.stack.stack.toInt (8 * slot.val)) index ∉ written

def TailFacts.transport {base : BitVec 48} {before after : State} {regWrites : Finset Register}
    {byteWrites : Finset Nat} (tail : TailFacts base before)
    (framed : X86StateFrame.Frame regWrites byteWrites before after)
    (dataOnly : regWrites ⊆ dataRegisters) (stackFixed : key 4 ∉ regWrites)
    (allowanceFixed : key 5 ∉ regWrites) (frameFixed : key 7 ∉ regWrites)
    (reads : tail.ReadsOutside byteWrites) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags) : TailFacts base after :=
  let preserves (reg : Register) (outside : reg ∉ dataRegisters) :=
    framed.registers reg (fun written => outside (dataOnly written))
  { tail with
    frame :=
      { tail.frame with
        frameKnown := (framed.lookup 7 frameFixed).trans tail.frame.frameKnown
        controlsKnown := (preserves .ctrs (by decide)).trans tail.frame.controlsKnown
        visibleKnown := (preserves .seg_visibles (by decide)).trans tail.frame.visibleKnown
        flags := flags
        flagsKnown := flagsKnown
        quiet := (preserves .log_register_writes (by decide)).trans tail.frame.quiet }
    fuel := tail.fuel.transport framed dataOnly frameFixed allowanceFixed reads.budget flags flagsKnown
    stack :=
      { tail.stack with
        current := (framed.lookup 4 stackFixed).trans tail.stack.current
        bottomBytes := fun n h => (framed.memory _ (reads.bottom n h)).trans (tail.stack.bottomBytes n h)
        present := fun slot n h => (framed.memory _ (reads.saved slot n h)).trans (tail.stack.present slot n h) } }

open X86P1Sub1Guards
open X86P1Sub1Guards.PremiseGuards (leftLoad rightLoad entryOffset prefixCount)
open X86P1Sub1Output (loadIndex outputPrefixCount outputWrites)
open X86P1Sub1Output.Stores (Destination instructionAt fieldWrites rowWrites prefixStoreCount)

set_option maxHeartbeats 1600000 in
theorem completed_after_checks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, OperandLoads.Request (OperandLoads.instructionAt (leftLoad i)) state)
    (right : ∀ i, OperandLoads.Request (OperandLoads.instructionAt (rightLoad i)) state)
    (agrees : ∀ i : Fin 7, (left i).value == (right i).value)
    (space : Capacity.Inputs state) (room : (space.value false).toNat < (space.value true).toNat)
    (request : ∀ i, OperandLoads.Request (OperandLoads.instructionAt (loadIndex i)) state)
    (dest : ∀ i, Destination (instructionAt i) state)
    (separate : Pairwise fun i j =>
      Disjoint (fieldWrites (fun i => (dest i).data) i) (fieldWrites (fun i => (dest i).data) j))
    (baseSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).baseAddress index ∉
      rowWrites (fun i => (dest i).data))
    (lengthSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).lengthAddress index ∉
      rowWrites (fun i => (dest i).data))
    (codeSafe : ∀ index byte, sub1.view.read index = some byte →
      ((address base.toInt index).signExtend 52).toNat ∉ rowWrites (fun i => (dest i).data))
    (tail : TailFacts base state) (tailSafe : tail.ReadsOutside (rowWrites (fun i => (dest i).data)))
    (retainOutput : Disjoint (rowWrites (fun i => (dest i).data)) (tailWrites tail.frame tail.fuel)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches (prefixCount 7 + 4 + outputPrefixCount 4 + prefixStoreCount 4 + 14)).run state = .ok () after ∧
      after.regs.get? .rip = some (tail.stack.returnAddress.signExtend 64) ∧
      lookup after 4 = some ((address tail.stack.bottom.toInt 56).signExtend 64) ∧
      lookup after 5 = some tail.stack.rbp ∧
      (∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (tail.stack.saved slot)) ∧
      X86StateFrame.Frame (outputWrites ∪ tailRegisters)
        (rowWrites (fun i => (dest i).data) ∪ tailWrites tail.frame tail.fuel) state after ∧
      lookup after 0 = some ExitStatus.completed.word ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.statusAddress n) =
        some (ExitStatus.completed.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.resultAddress n) =
        some (ExitStatus.completed.word.extractLsb' (8 * n) 8)) ∧
      (∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.fuel.receiptAddress n) =
        some ((tail.fuel.budget - tail.fuel.remaining).extractLsb' (8 * n) 8)) ∧
      (∀ i : Fin 4, ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress (dest i).data n) =
        some ((request i).value.extractLsb' (8 * n) 8)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let core := X86FailureHandler.linkedHandlers (X86Stack.linkedHandlers other)
  obtain ⟨middle, flags, body, returned, bodyFrame, _, known, _, fields⟩ :=
    X86P1Sub1Output.Stores.stores_after_checks core extra vector state base upper placed mode rip left right agrees space room
      request dest separate baseSafe lengthSafe codeSafe
  have data : outputWrites ⊆ dataRegisters := by decide
  let current : TailFacts base middle :=
    tail.transport bodyFrame data (by decide) (by decide) (by decide) tailSafe flags known
  have code : X86CodePlacement.Placed middle base.toInt sub1.view :=
    X86CodePlacement.Placed.preserved _ _ placed bodyFrame codeSafe
  have modeNow := X86P1Sub1Guards.PremiseGuards.modeAfterRegisters mode
    (fun r outside => bodyFrame.registers r (fun ins => outside (data ins)))
  obtain ⟨after, final, caller, rsp, rbp, saved, lastFrame, rax, status, result, spent⟩ :=
    returns_to_caller other extra vector 0 middle base upper modeNow
      (by simpa only [success.1] using returned) code current.frame current.fuel current.stack
      current.budgetSafe current.statusSafe current.resultSafe current.codeSafe current.bottomSafe current.savedSafe
  change X86StateFrame.Frame tailRegisters (tailWrites tail.frame tail.fuel) middle after at lastFrame
  refine ⟨after, ?_, caller, rsp, rbp, saved, ?_, ?_, ?_, ?_, spent, ?_⟩
  · let instructions := prefixCount 7 + 4 + outputPrefixCount 4 + prefixStoreCount 4
    change (@X86FuelPrefix.fetches (handlers other extra) vector (instructions + 14)).run state = .ok () after
    change (@X86FuelPrefix.fetches (handlers other extra) vector instructions).run state = .ok () middle at body
    change (@X86FuelPrefix.fetches (handlers other extra) vector 14).run middle = .ok () after at final
    exact @X86FuelPrefix.fetches_then (handlers other extra) vector instructions 14 state middle after body final
  · exact bodyFrame.trans lastFrame
  · simpa only [success.2] using rax
  · change ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.statusAddress n) =
      some ((site 0).outcome.word.extractLsb' (8 * n) 8) at status
    simpa only [success.2] using status
  · change ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.resultAddress n) =
      some ((site 0).outcome.word.extractLsb' (8 * n) 8) at result
    simpa only [success.2] using result
  · intro i n inside
    have inRow : X86WriteWords.physicalAddress (dest i).data n ∈ rowWrites (fun j => (dest j).data) :=
      X86P1Sub1Output.Stores.byte_in_row (fun j => (dest j).data) i n inside
    have outside : X86WriteWords.physicalAddress (dest i).data n ∉ tailWrites tail.frame tail.fuel :=
      fun overlap => Finset.disjoint_left.mp retainOutput inRow overlap
    exact (lastFrame.memory _ outside).trans (fields i n inside)

open X86P1Sub1Guards.PremiseGuards (pairCount prefixWrites)

structure RefusalResult {base : BitVec 48} {before : State}
    (tail : TailFacts base before) (outcome : ExitStatus) (after : State) : Prop where
  caller : after.regs.get? .rip = some (tail.stack.returnAddress.signExtend 64)
  stack : lookup after 4 = some ((address tail.stack.bottom.toInt 56).signExtend 64)
  rbp : lookup after 5 = some tail.stack.rbp
  saved : ∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (tail.stack.saved slot)
  frame : X86StateFrame.Frame (prefixWrites ∪ tailRegisters) (tailWrites tail.frame tail.fuel) before after
  rax : lookup after 0 = some outcome.word
  status : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.statusAddress n) =
    some (outcome.word.extractLsb' (8 * n) 8)
  result : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.frame.resultAddress n) =
    some (outcome.word.extractLsb' (8 * n) 8)
  receipt : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress tail.fuel.receiptAddress n) =
    some ((tail.fuel.budget - tail.fuel.remaining).extractLsb' (8 * n) 8)

private theorem finish_read_only (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state middle : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (tail : TailFacts base state) (i : Fin 9)
    (atExit : middle.regs.get? .rip = some ((address base.toInt (site i).start).signExtend 64))
    (framed : RegisterFrame prefixWrites state middle) (flags : BitVec 32)
    (known : middle.regs.get? .rflags = some flags) (n : Nat)
    (prefixRun : (@X86FuelPrefix.fetches (handlers other extra) vector n).run state = .ok () middle) :
    ∃ after, (@X86FuelPrefix.fetches (handlers other extra) vector (n + 14)).run state = .ok () after ∧
      RefusalResult tail (site i).outcome after := by
  have data : prefixWrites ⊆ dataRegisters := by decide
  have memory := X86StateFrame.registerOnly framed
  have safe : tail.ReadsOutside ∅ := by constructor <;> simp
  let current : TailFacts base middle :=
    tail.transport memory data (by decide) (by decide) (by decide) safe flags known
  have code := X86CodePlacement.Placed.preserved _ _ placed memory (by simp)
  obtain ⟨after, final, caller, rsp, rbp, saved, lastFrame, rax, status, result, spent⟩ :=
    returns_to_caller other extra vector i middle base upper (PremiseGuards.modeAfter mode framed data)
      atExit code current.frame current.fuel current.stack current.budgetSafe current.statusSafe current.resultSafe
      current.codeSafe current.bottomSafe current.savedSafe
  change X86StateFrame.Frame tailRegisters (tailWrites tail.frame tail.fuel) middle after at lastFrame
  have joined := (memory.trans lastFrame).mono (Finset.Subset.refl _)
    (Finset.union_subset (Finset.empty_subset _) (Finset.Subset.refl _))
  exact ⟨after, @X86FuelPrefix.fetches_then (handlers other extra) vector n 14 state middle after prefixRun final,
    ⟨caller, rsp, rbp, saved, joined, rax, status, result, spent⟩⟩

theorem capacity_stops_after_checks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, OperandLoads.Request (OperandLoads.instructionAt (leftLoad i)) state)
    (right : ∀ i, OperandLoads.Request (OperandLoads.instructionAt (rightLoad i)) state)
    (agrees : ∀ i : Fin 7, (left i).value == (right i).value)
    (space : Capacity.Inputs state) (full : ¬(space.value false).toNat < (space.value true).toNat)
    (tail : TailFacts base state) :
    ∃ after, (@X86FuelPrefix.fetches (handlers other extra) vector (prefixCount 7 + 4 + 14)).run state = .ok () after ∧
      RefusalResult tail .unsupported after := by
  let core := X86FailureHandler.linkedHandlers (X86Stack.linkedHandlers other)
  obtain ⟨middle, flags, body, pc, framed, _, known, _⟩ :=
    Capacity.executes_after_matches core extra vector state base upper placed mode rip left right agrees space
  have atExit : middle.regs.get? .rip = some ((address base.toInt (site 1).start).signExtend 64) := by
    simpa only [if_neg full, capacity.1] using pc
  obtain ⟨after, run, observed⟩ := finish_read_only other extra vector state middle base upper placed mode
    tail 1 atExit framed flags known (prefixCount 7 + 4) body
  exact ⟨after, run, by simpa only [capacity.2] using observed⟩

set_option maxHeartbeats 1700000 in
theorem premise_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (i : Fin 7) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ j, OperandLoads.Request (OperandLoads.instructionAt (leftLoad j)) state)
    (right : ∀ j, OperandLoads.Request (OperandLoads.instructionAt (rightLoad j)) state)
    (earlier : ∀ j : Fin 7, j.val < i.val → (left j).value == (right j).value)
    (mismatch : (left i).value ≠ (right i).value) (tail : TailFacts base state) :
    ∃ after,
      (@X86FuelPrefix.fetches (handlers other extra) vector (prefixCount i.val + pairCount i.val + 14)).run state =
        .ok () after ∧ RefusalResult tail .refused after := by
  let core := X86FailureHandler.linkedHandlers (X86Stack.linkedHandlers other)
  obtain ⟨middle, flags, prefixRun, atGuard, prefixFrame, known, control⟩ :=
    PremiseGuards.executes_matching_prefix core extra vector state base upper placed mode rip left right i.val
      (by have := i.isLt; omega) earlier
  have data : prefixWrites ⊆ dataRegisters := by decide
  obtain ⟨leftFixed, rightFixed⟩ := PremiseGuards.operand_pointers_fixed i
  let leftValue := (left i).transport prefixFrame leftFixed (by decide) data control flags known
  let rightValue := (right i).transport prefixFrame rightFixed (by decide) data control flags known
  have code := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly prefixFrame) (by simp)
  obtain ⟨refusal, flagsAfter, guardRun, pc, guardFrame, _, knownAfter, _⟩ :=
    PremiseGuards.executes core extra vector i middle base upper code (PremiseGuards.modeAfter mode prefixFrame data)
      (by simpa only [entryOffset, dif_pos i.isLt] using atGuard) leftValue rightValue
  obtain ⟨exit, target, outcome⟩ := premise_exit i
  have unequal : ¬(leftValue.value == rightValue.value) := by
    simpa only [beq_iff_eq, leftValue, rightValue, OperandLoads.Request.transport] using mismatch
  have atExit : refusal.regs.get? .rip = some ((address base.toInt (site exit).start).signExtend 64) := by
    simpa only [if_neg unequal, target] using pc
  have framed : RegisterFrame prefixWrites state refusal := by
    simpa only [Finset.union_self] using prefixFrame.trans (guardFrame.mono (PremiseGuards.pair_writes i))
  have step : (@X86FuelPrefix.fetches (handlers other extra) vector (pairCount i.val)).run middle = .ok () refusal := by
    simpa only [pairCount, dif_pos i.isLt] using guardRun
  have body := @X86FuelPrefix.fetches_then (handlers other extra) vector (prefixCount i.val)
    (pairCount i.val) state middle refusal prefixRun step
  obtain ⟨after, run, observed⟩ := finish_read_only other extra vector state refusal base upper placed mode tail exit
    atExit framed flagsAfter knownAfter (prefixCount i.val + pairCount i.val) body
  exact ⟨after, run, by simpa only [outcome] using observed⟩

end Mettapedia.Machines.TIsa.X86P1Sub1Exit

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.decoded
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.exact_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.premise_exit
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.changed_status
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.writes_receipt
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.returns_to_caller
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.completed_after_checks
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.capacity_stops_after_checks
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Exit.premise_refuses
