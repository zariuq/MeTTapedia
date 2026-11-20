import Mettapedia.Machines.TIsa.X86P1Sub1Exit

/-!
# Public entry and return for Micromath sub1

The six running pushes establish the saved-register bytes used on return.
The allowance setup preserves the caller's admitted arguments and leaves the
status, result and receipt destinations available to the body and exit.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Entry

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86P1Sub1Allowance (sub1 afterSaves)
open X86P1Sub1Exit (SavedStack handlers)
local instance : MemoryPrimitives := X86Memory.ordinary

private theorem outside_last_save {state : State} (five : X86Prologue.Inputs state) (bottom : BitVec 48)
    (step : bottom.toInt + 8 = five.bottom.toInt) (slot : Fin 6) (byte : Nat) (within : byte < 8) :
    X86WriteWords.physicalAddress (address five.bottom.toInt (8 * slot.val)) byte ∉
      X86WriteWords.written bottom (List.range 8) := by
  have point : (address five.bottom.toInt (8 * slot.val)).toInt = five.bottom.toInt + 8 * slot.val :=
    X86Prologue.stack_int five slot.val (by have := slot.isLt; omega)
  have relocated : X86WriteWords.physicalAddress (address five.bottom.toInt (8 * slot.val)) byte =
      X86WriteWords.physicalAddress bottom (8 + 8 * slot.val + byte) := by
    unfold X86WriteWords.physicalAddress
    rw [point, ← step]
    simp only [address, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.add_assoc]
  rw [relocated]
  intro present
  simp only [X86WriteWords.written, List.mem_toFinset, List.mem_map] at present
  obtain ⟨earlier, bound, same⟩ := present
  have first := List.mem_range.mp bound
  have last : 8 + 8 * slot.val + byte < 56 := by have := slot.isLt; omega
  have upper : bottom.toInt + 56 ≤ (2 ^ 47 : Int) := by have := five.stackUpper; omega
  have equal := X86WriteWords.physicalAddress_injective 56 bottom upper _ _ (by omega) last same
  omega

def savedStack (state : State) (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word)
    (step : bottom.toInt + 8 = five.bottom.toInt) (aligned : bottom &&& (7#48) = 0#48) :
    SavedStack (afterSaves state five bottom rbp) := by
  let previous := X86Prologue.epilogueStackFacts state five
  let next := address five.code.toInt (X86P1Sub1Allowance.saveOffset + 1)
  have sixth := X86Stack.push_frame (X86Prologue.finished state five) rbp bottom next
  refine {
    bottom := bottom
    stack := five.bottom
    step := step
    upper := five.stackUpper
    current := X86Stack.push_stack (X86Prologue.finished state five) rbp bottom next
    rbp := rbp
    saved := X86Prologue.epilogueSaved five
    returnAddress := five.returnAddress
    bottomAligned := aligned
    bottomBytes := ?_
    aligned := five.aligned
    present := ?_ }
  · intro index within
    rw [afterSaves, X86Stack.push_memory]
    exact X86WriteWords.store_word_byte _ bottom rbp (by have := five.stackUpper; omega) index within
  · intro slot index within
    change (X86Stack.pushResult (X86Prologue.finished state five) rbp bottom next).mem.get?
      (X86WriteWords.physicalAddress (address five.bottom.toInt (8 * slot.val)) index) = _
    exact (sixth.memory _ (outside_last_save five bottom step slot index within)).trans
      (previous.present slot index within)

def savedStackAtBody (state : State) (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word)
    (step : bottom.toInt + 8 = five.bottom.toInt) (aligned : bottom &&& (7#48) = 0#48)
    (input : X86P1Sub1Fuel.Inputs (afterSaves state five bottom rbp)) (output : BitVec 32) :
    SavedStack (X86P1Sub1Fuel.afterAllowance input output) :=
  let prior := savedStack state five bottom rbp step aligned
  let frame := X86P1Sub1Fuel.allowance_frame input output
  { prior with
    current := (frame.lookup 4 (by decide)).trans prior.current
    bottomBytes := fun index within => (frame.memory _ (by simp)).trans (prior.bottomBytes index within)
    present := fun slot index within => (frame.memory _ (by simp)).trans (prior.present slot index within) }

theorem prologue_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1Sub1Fuel.entryHandlers (handlers other extra) = handlers other extra := rfl

theorem enters_with_saved_stack (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State)
    (five : X86Prologue.Inputs state) (bottom : BitVec 48) (rbp : Word)
    (upper : five.code.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state five.code.toInt sub1.view)
    (outside : ∀ index byte, sub1.view.read index = some byte →
      ((address five.code.toInt index).signExtend 52).toNat ∉ X86Prologue.writes five.bottom)
    (step : bottom.toInt + 8 = five.bottom.toInt)
    (aligned : bottom &&& (7#48) = 0#48) (saved : lookup state 5 = some rbp)
    (input : X86P1Sub1Fuel.Inputs (afterSaves state five bottom rbp)) (base : input.base = five.code) :
    ∃ output, ∃ stack : SavedStack (X86P1Sub1Fuel.afterAllowance input output),
      (@X86FuelPrefix.fetches (handlers other extra) vector 8).run state =
        .ok () (X86P1Sub1Fuel.afterAllowance input output) ∧
      (X86P1Sub1Fuel.afterAllowance input output).regs.get? .rip =
        some ((address five.code.toInt 24).signExtend 64) ∧
      lookup (X86P1Sub1Fuel.afterAllowance input output) 5 = some (input.budget - input.receipt) ∧
      stack.bottom = bottom ∧ stack.stack = five.bottom ∧ stack.rbp = rbp ∧
      stack.saved = X86Prologue.epilogueSaved five ∧ stack.returnAddress = five.returnAddress := by
  have entry := X86P1Sub1Fuel.enters_body (handlers other extra) vector state five bottom rbp upper placed outside
    step aligned saved input base
  rw [prologue_dispatch] at entry
  obtain ⟨output, run, pointer, allowance, _⟩ := entry
  exact ⟨output, savedStackAtBody state five bottom rbp step aligned input output,
    run, pointer, allowance, rfl, rfl, rfl, rfl, rfl⟩

abbrev spillBytes (fiveBottom bottom : BitVec 48) : Finset Nat :=
  X86Prologue.writes fiveBottom ∪ X86WriteWords.written bottom (List.range 8)

abbrev entryRegisters : Finset Register := {.rsp, .rip, .rbp, .rflags}

structure CallerInputs (state : State) where
  prologue : X86Prologue.Inputs state
  bottom : BitVec 48
  savedRbp : Word
  rbpKnown : lookup state 5 = some savedRbp
  step : bottom.toInt + 8 = prologue.bottom.toInt
  aligned : bottom &&& (7#48) = 0#48
  upper : prologue.code.toInt + sub1.size < (2 ^ 47 : Int)
  placed : X86CodePlacement.Placed state prologue.code.toInt sub1.view
  codeSafe : ∀ index byte, sub1.view.read index = some byte →
    ((address prologue.code.toInt index).signExtend 52).toNat ∉ spillBytes prologue.bottom bottom
  fuel : X86P1Sub1Fuel.SetupFacts state
  budgetSafe : ∀ n < 8, X86WriteWords.physicalAddress fuel.budgetAddress n ∉ spillBytes prologue.bottom bottom
  receiptSafe : ∀ n < 8, X86WriteWords.physicalAddress fuel.receiptAddress n ∉ spillBytes prologue.bottom bottom

noncomputable def CallerInputs.setup {state : State} (caller : CallerInputs state) :
    X86P1Sub1Fuel.Inputs (afterSaves state caller.prologue caller.bottom caller.savedRbp) := by
  let framed := X86P1Sub1Allowance.six_saves_frame state caller.prologue caller.bottom caller.savedRbp
  let data : ({.rsp, .rip} : Finset Register) ⊆ dataRegisters := by decide
  refine {
    toSetupFacts :=
      { caller.fuel with
        frameKnown := (framed.lookup 7 (by decide)).trans caller.fuel.frameKnown
        budgetPresent := fun n h => (framed.memory _ (caller.budgetSafe n h)).trans (caller.fuel.budgetPresent n h)
        receiptPresent := fun n h => (framed.memory _ (caller.receiptSafe n h)).trans (caller.fuel.receiptPresent n h)
        visibleKnown := (framed.registers .seg_visibles (by decide)).trans caller.fuel.visibleKnown
        controlsKnown := (framed.registers .ctrs (by decide)).trans caller.fuel.controlsKnown
        flagsKnown := (framed.registers .rflags (by decide)).trans caller.fuel.flagsKnown
        quiet := (framed.registers .log_register_writes (by decide)).trans caller.fuel.quiet }
    mode := X86P1Sub1Guards.PremiseGuards.modeAfterRegisters caller.prologue.context
      (fun r outside => framed.registers r (fun h => outside (data h)))
    base := caller.prologue.code
    codeUpper := caller.upper
    placed := X86CodePlacement.Placed.preserved _ _ caller.placed framed caller.codeSafe
    rip := ?_ }
  rw [afterSaves, X86Stack.pushResult, X86FuelPrefix.pointer_rip, X86P1Sub1Allowance.save_offset]

noncomputable def CallerInputs.body {state : State} (caller : CallerInputs state) (output : BitVec 32) : State :=
  X86P1Sub1Fuel.afterAllowance caller.setup output

theorem CallerInputs.frame {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    X86StateFrame.Frame entryRegisters (spillBytes caller.prologue.bottom caller.bottom)
      state (caller.body output) :=
  ((X86P1Sub1Allowance.six_saves_frame state caller.prologue caller.bottom caller.savedRbp).trans
    (X86P1Sub1Fuel.allowance_frame caller.setup output)).mono (by decide) (by simp)

theorem CallerInputs.control {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    X86ControlFlags.Preserved state (caller.body output) := by
  have pushes := X86P1Sub1Allowance.six_saves_frame state caller.prologue caller.bottom caller.savedRbp
  have saved : X86ControlFlags.Preserved state (afterSaves state caller.prologue caller.bottom caller.savedRbp) := by
    unfold X86ControlFlags.Preserved
    rw [pushes.registers .rflags (by decide)]
  exact saved.trans (X86P1Sub1Fuel.allowance_control caller.setup output)

theorem CallerInputs.enters (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state) :
    ∃ output, (@X86FuelPrefix.fetches (handlers other extra) vector 8).run state = .ok () (caller.body output) ∧
      (caller.body output).regs.get? .rip = some ((address caller.prologue.code.toInt 24).signExtend 64) ∧
      lookup (caller.body output) 5 = some (caller.fuel.budget - caller.fuel.receipt) := by
  have entered := X86P1Sub1Fuel.enters_body (handlers other extra) vector state caller.prologue caller.bottom
    caller.savedRbp caller.upper caller.placed
    (fun index byte observed member => caller.codeSafe index byte observed (Finset.mem_union_left _ member))
    caller.step caller.aligned caller.rbpKnown caller.setup rfl
  rw [prologue_dispatch] at entered
  obtain ⟨output, run, pc, remaining, _⟩ := entered
  exact ⟨output, run, pc, remaining⟩

theorem CallerInputs.flags {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    (caller.body output).regs.get? .rflags = some (X86Flags.mergeFlags caller.fuel.flags output) :=
  X86P1Sub1Fuel.allowance_flags caller.setup output

structure Arguments (state : State) where
  loads : ∀ i : Fin 18, X86P1Sub1Guards.OperandLoads.Request (X86P1Sub1Guards.OperandLoads.instructionAt i) state
  capacity : X86P1Sub1Guards.Capacity.Inputs state
  stores : ∀ i : Fin 4, X86P1Sub1Output.Stores.Destination (X86P1Sub1Output.Stores.instructionAt i) state

structure Arguments.Apart {state : State} (args : Arguments state) (spills : Finset Nat) : Prop where
  loadBase : ∀ i : Fin 18, ∀ n < 8, X86WriteWords.physicalAddress (args.loads i).baseAddress n ∉ spills
  loadLength : ∀ i : Fin 18, ∀ n < 8, X86WriteWords.physicalAddress (args.loads i).lengthAddress n ∉ spills
  loadData : ∀ i : Fin 18, ∀ n < X86DataLoad.byteCount (X86P1Sub1Guards.OperandLoads.instructionAt i).wide,
    X86WriteWords.physicalAddress (args.loads i).dataAddress n ∉ spills
  capacity : ∀ limit : Bool, ∀ n < 8, X86WriteWords.physicalAddress (args.capacity.data limit) n ∉ spills
  storeBase : ∀ i : Fin 4, ∀ n < 8, X86WriteWords.physicalAddress (args.stores i).baseAddress n ∉ spills
  storeLength : ∀ i : Fin 4, ∀ n < 8, X86WriteWords.physicalAddress (args.stores i).lengthAddress n ∉ spills

private theorem load_pointer (i : Fin 18) :
    key (X86BoundedLoad.physical (X86P1Sub1Guards.OperandLoads.instructionAt i).base) ∉ entryRegisters := by
  fin_cases i <;> exact of_decide_eq_true (by kernel_reflexivity)

private theorem store_pointer (i : Fin 4) :
    key (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt i)).pointer ∉ entryRegisters := by
  fin_cases i <;> exact of_decide_eq_true (by kernel_reflexivity)

noncomputable def CallerInputs.arguments {state : State} (caller : CallerInputs state) (args : Arguments state)
    (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom)) (output : BitVec 32) :
    Arguments (caller.body output) := by
  let frame := caller.frame output
  let flags := X86Flags.mergeFlags caller.fuel.flags output
  have known : (caller.body output).regs.get? .rflags = some flags := caller.flags output
  refine {
    loads := ?_
    capacity := ?_
    stores := fun i => (args.stores i).transport frame (by decide) (by decide) (store_pointer i)
      (apart.storeBase i) (apart.storeLength i) (caller.control output) flags known }
  · intro i
    let req := args.loads i
    have ac := X86ControlFlags.ac_preserved (caller.control output) req.flags flags req.flagsKnown known
    exact {
      req with
      frameKnown := (frame.lookup 7 (by decide)).trans req.frameKnown
      pointerKnown := (frame.lookup _ (load_pointer i)).trans req.pointerKnown
      controlKnown := (frame.registers .ctrs (by decide)).trans req.controlKnown
      visibleKnown := (frame.registers .seg_visibles (by decide)).trans req.visibleKnown
      quiet := (frame.registers .log_register_writes (by decide)).trans req.quiet
      flags := flags
      flagsKnown := known
      alignment := by simpa only [X86FrameLoad.alignmentEnabled, ac] using req.alignment
      baseBytes := fun n h => (frame.memory _ (apart.loadBase i n h)).trans (req.baseBytes n h)
      lengthBytes := fun n h => (frame.memory _ (apart.loadLength i n h)).trans (req.lengthBytes n h)
      dataBytes := fun n h => (frame.memory _ (apart.loadData i n h)).trans (req.dataBytes n h) }
  · let cap := args.capacity
    exact {
      cap with
      frameKnown := (frame.lookup 7 (by decide)).trans cap.frameKnown
      controlsKnown := (frame.registers .ctrs (by decide)).trans cap.controlsKnown
      visibleKnown := (frame.registers .seg_visibles (by decide)).trans cap.visibleKnown
      quiet := (frame.registers .log_register_writes (by decide)).trans cap.quiet
      flags := flags
      flagsKnown := known
      present := fun limit n h => (frame.memory _ (apart.capacity limit n h)).trans (cap.present limit n h) }

theorem enters_with_arguments (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom)) :
    ∃ output, ∃ live : Arguments (caller.body output),
      (@X86FuelPrefix.fetches (handlers other extra) vector 8).run state = .ok () (caller.body output) ∧
      (caller.body output).regs.get? .rip = some ((address caller.prologue.code.toInt 24).signExtend 64) ∧
      lookup (caller.body output) 5 = some (caller.fuel.budget - caller.fuel.receipt) ∧
      (∀ i, (live.loads i).value = (args.loads i).value) ∧
      (∀ limit, live.capacity.value limit = args.capacity.value limit) ∧
      (∀ i, (live.stores i).data = (args.stores i).data) := by
  obtain ⟨output, run, pc, allowance⟩ := caller.enters other extra vector state
  exact ⟨output, caller.arguments args apart output, run, pc, allowance, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

open X86P1Sub1Exit (TailFacts RefusalResult frameWrites tailRegisters)
open X86P1Sub1Guards.PremiseGuards (leftLoad rightLoad entryOffset prefixCount pairCount prefixWrites)

noncomputable def CallerInputs.bodyMode {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    X86PlainFetch.Facts (caller.body output) :=
  X86P1Sub1Guards.PremiseGuards.modeAfterRegisters caller.prologue.context
    (fun r outside => (caller.frame output).registers r (fun h => outside ((show entryRegisters ⊆ dataRegisters from by decide) h)))

theorem CallerInputs.bodyPlacement {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    X86CodePlacement.Placed (caller.body output) caller.prologue.code.toInt sub1.view :=
  X86CodePlacement.Placed.preserved _ _ caller.placed (caller.frame output) caller.codeSafe

abbrev receiptBytes (address : BitVec 48) : Finset Nat :=
  X86WriteWords.written address (List.range 8)

structure ReturnInputs {state : State} (caller : CallerInputs state) where
  frame : X86FailureHandler.FrameFacts state
  budgetSafe : ∀ n < 8, X86WriteWords.physicalAddress caller.fuel.budgetAddress n ∉ frameWrites frame
  statusSafe : ∀ n < 8, X86WriteWords.physicalAddress frame.statusAddress n ∉ receiptBytes caller.fuel.receiptAddress
  resultSafe : ∀ n < 8, X86WriteWords.physicalAddress frame.resultAddress n ∉ receiptBytes caller.fuel.receiptAddress
  codeSafe : ∀ offset byte, sub1.view.read offset = some byte →
    ((address caller.prologue.code.toInt offset).signExtend 52).toNat ∉
      frameWrites frame ∪ receiptBytes caller.fuel.receiptAddress
  bottomSafe : ∀ n < 8, X86WriteWords.physicalAddress caller.bottom n ∉
    frameWrites frame ∪ receiptBytes caller.fuel.receiptAddress
  savedSafe : ∀ slot : Fin 6, ∀ n < 8,
    X86WriteWords.physicalAddress (address caller.prologue.bottom.toInt (8 * slot.val)) n ∉
      frameWrites frame ∪ receiptBytes caller.fuel.receiptAddress

abbrev ReturnInputs.writes {state : State} {caller : CallerInputs state} (ret : ReturnInputs caller) : Finset Nat :=
  frameWrites ret.frame ∪ receiptBytes caller.fuel.receiptAddress

def CallerInputs.returnFuel {state : State} (caller : CallerInputs state) (output : BitVec 32) :
    X86P1Sub1Fuel.Receipt.Facts (caller.body output) :=
  let fuel := caller.fuel
  let frame := caller.frame output
  { frame := fuel.frame
    frameKnown := (frame.lookup 7 (by decide)).trans fuel.frameKnown
    budgetAddress := fuel.budgetAddress
    budgetUpper := fuel.budgetUpper
    budgetEffective := fuel.budgetEffective
    budgetAligned := fuel.budgetAligned
    budget := fuel.budget
    budgetPresent := fun n h => (frame.memory _ (caller.budgetSafe n h)).trans (fuel.budgetPresent n h)
    receiptAddress := fuel.receiptAddress
    receiptUpper := fuel.receiptUpper
    receiptEffective := fuel.receiptEffective
    receiptAligned := fuel.receiptAligned
    remaining := fuel.budget - fuel.receipt
    remainingKnown := X86P1Sub1Fuel.initialized_allowance caller.setup output
    visible := fuel.visible
    controls := fuel.controls
    flags := X86Flags.mergeFlags fuel.flags output
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans fuel.visibleKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans fuel.controlsKnown
    flagsKnown := caller.flags output
    quiet := (frame.registers .log_register_writes (by decide)).trans fuel.quiet }

noncomputable def CallerInputs.tail {state : State} (caller : CallerInputs state)
    (ret : ReturnInputs caller) (output : BitVec 32) : TailFacts caller.prologue.code (caller.body output) :=
  let frame := caller.frame output
  { frame :=
      { ret.frame with
        frameKnown := (frame.lookup 7 (by decide)).trans ret.frame.frameKnown
        controlsKnown := (frame.registers .ctrs (by decide)).trans ret.frame.controlsKnown
        visibleKnown := (frame.registers .seg_visibles (by decide)).trans ret.frame.visibleKnown
        flags := X86Flags.mergeFlags caller.fuel.flags output
        flagsKnown := caller.flags output
        quiet := (frame.registers .log_register_writes (by decide)).trans ret.frame.quiet }
    fuel := caller.returnFuel output
    stack := savedStackAtBody state caller.prologue caller.bottom caller.savedRbp caller.step caller.aligned caller.setup output
    budgetSafe := ret.budgetSafe
    statusSafe := ret.statusSafe
    resultSafe := ret.resultSafe
    codeSafe := ret.codeSafe
    bottomSafe := ret.bottomSafe
    savedSafe := ret.savedSafe }

structure ReturnObservation {state : State} {caller : CallerInputs state} (ret : ReturnInputs caller)
    (registerWrites : Finset Register) (published : Finset Nat) (outcome : ExitStatus) (after : State) : Prop where
  rip : after.regs.get? .rip = some (caller.prologue.returnAddress.signExtend 64)
  rsp : lookup after 4 = some ((address caller.bottom.toInt 56).signExtend 64)
  rbp : lookup after 5 = some caller.savedRbp
  saved : ∀ slot : Fin 5, lookup after (X86Epilogue.target slot) = some (X86Prologue.epilogueSaved caller.prologue slot)
  frame : X86StateFrame.Frame (entryRegisters ∪ registerWrites)
    (spillBytes caller.prologue.bottom caller.bottom ∪ published) state after
  statusReg : lookup after 0 = some outcome.word
  status : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress ret.frame.statusAddress n) =
    some (outcome.word.extractLsb' (8 * n) 8)
  result : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress ret.frame.resultAddress n) =
    some (outcome.word.extractLsb' (8 * n) 8)
  receipt : ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress caller.fuel.receiptAddress n) =
    some (caller.fuel.receipt.extractLsb' (8 * n) 8)

private theorem entryOffset_zero : entryOffset 0 = 24 := by kernel_reflexivity

private theorem restored_receipt (budget prior : Word) : budget - (budget - prior) = prior :=
  BitVec.sub_eq_iff_eq_add.mpr (by rw [BitVec.add_comm, BitVec.sub_add_cancel])

private theorem CallerInputs.observes_refusal {state : State} (caller : CallerInputs state) (ret : ReturnInputs caller)
    (output : BitVec 32) {outcome : ExitStatus} {after : State}
    (returned : RefusalResult (caller.tail ret output) outcome after) :
    ReturnObservation ret (prefixWrites ∪ tailRegisters) ret.writes outcome after := by
  refine ⟨returned.caller, returned.stack, returned.rbp, returned.saved, (caller.frame output).trans returned.frame,
    returned.rax, returned.status, returned.result, ?_⟩
  intro index present
  simpa only [CallerInputs.tail, CallerInputs.returnFuel, restored_receipt] using returned.receipt index present

theorem refuses_from_caller (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (index : Fin 7) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom))
    (ret : ReturnInputs caller)
    (earlier : ∀ j : Fin 7, j.val < index.val → (args.loads (leftLoad j)).value == (args.loads (rightLoad j)).value)
    (unequal : (args.loads (leftLoad index)).value ≠ (args.loads (rightLoad index)).value) :
    ∃ after,
      (@X86FuelPrefix.fetches (handlers other extra) vector (8 + (prefixCount index.val + pairCount index.val + 14))).run
        state = .ok () after ∧ ReturnObservation ret (prefixWrites ∪ tailRegisters) ret.writes .refused after := by
  obtain ⟨output, entered, pc, _⟩ := caller.enters other extra vector state
  let live := caller.arguments args apart output
  obtain ⟨after, body, refused⟩ := X86P1Sub1Exit.premise_refuses other extra vector index (caller.body output)
    caller.prologue.code caller.upper (caller.bodyPlacement output) (caller.bodyMode output)
    (by simpa only [entryOffset_zero] using pc) (fun i => live.loads (leftLoad i)) (fun i => live.loads (rightLoad i))
    earlier unequal (caller.tail ret output)
  exact ⟨after, @X86FuelPrefix.fetches_then (handlers other extra) vector 8 _ state (caller.body output) after entered body,
    caller.observes_refusal ret output refused⟩

theorem capacity_stop_from_caller (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom))
    (ret : ReturnInputs caller)
    (agrees : ∀ j : Fin 7, (args.loads (leftLoad j)).value == (args.loads (rightLoad j)).value)
    (full : ¬(args.capacity.value false).toNat < (args.capacity.value true).toNat) :
    ∃ after,
      (@X86FuelPrefix.fetches (handlers other extra) vector (8 + (prefixCount 7 + 4 + 14))).run state = .ok () after ∧
      ReturnObservation ret (prefixWrites ∪ tailRegisters) ret.writes .unsupported after := by
  obtain ⟨output, entered, pc, _⟩ := caller.enters other extra vector state
  let live := caller.arguments args apart output
  obtain ⟨after, body, stopped⟩ := X86P1Sub1Exit.capacity_stops_after_checks other extra vector (caller.body output)
    caller.prologue.code caller.upper (caller.bodyPlacement output) (caller.bodyMode output)
    (by simpa only [entryOffset_zero] using pc) (fun i => live.loads (leftLoad i)) (fun i => live.loads (rightLoad i))
    agrees live.capacity full (caller.tail ret output)
  exact ⟨after, @X86FuelPrefix.fetches_then (handlers other extra) vector 8 _ state (caller.body output) after entered body,
    caller.observes_refusal ret output stopped⟩

open X86P1Sub1Output (loadIndex outputPrefixCount outputWrites)
open X86P1Sub1Output.Stores (fieldWrites rowWrites prefixStoreCount)

abbrev Arguments.outputBytes {state : State} (args : Arguments state) : Finset Nat :=
  rowWrites (fun i => (args.stores i).data)

structure OutputApart {state : State} {caller : CallerInputs state} (args : Arguments state)
    (ret : ReturnInputs caller) : Prop where
  fields : Pairwise fun i j =>
    Disjoint (fieldWrites (fun i => (args.stores i).data) i) (fieldWrites (fun i => (args.stores i).data) j)
  base : ∀ i n, n < 8 → X86WriteWords.physicalAddress (args.stores i).baseAddress n ∉ args.outputBytes
  length : ∀ i n, n < 8 → X86WriteWords.physicalAddress (args.stores i).lengthAddress n ∉ args.outputBytes
  code : ∀ index byte, sub1.view.read index = some byte →
    ((address caller.prologue.code.toInt index).signExtend 52).toNat ∉ args.outputBytes
  budget : ∀ n < 8, X86WriteWords.physicalAddress caller.fuel.budgetAddress n ∉ args.outputBytes
  bottom : ∀ n < 8, X86WriteWords.physicalAddress caller.bottom n ∉ args.outputBytes
  saved : ∀ slot : Fin 6, ∀ n < 8,
    X86WriteWords.physicalAddress (address caller.prologue.bottom.toInt (8 * slot.val)) n ∉ args.outputBytes
  retain : Disjoint args.outputBytes ret.writes

set_option maxHeartbeats 1600000 in
theorem completes_from_caller (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom))
    (ret : ReturnInputs caller) (outputApart : OutputApart args ret)
    (agrees : ∀ j : Fin 7, (args.loads (leftLoad j)).value == (args.loads (rightLoad j)).value)
    (room : (args.capacity.value false).toNat < (args.capacity.value true).toNat) :
    ∃ after,
      (@X86FuelPrefix.fetches (handlers other extra) vector
        (8 + (prefixCount 7 + 4 + outputPrefixCount 4 + prefixStoreCount 4 + 14))).run state = .ok () after ∧
      ReturnObservation ret (outputWrites ∪ tailRegisters) (args.outputBytes ∪ ret.writes) .completed after ∧
      (∀ i : Fin 4, ∀ n < 8, after.mem.get? (X86WriteWords.physicalAddress (args.stores i).data n) =
        some ((args.loads (loadIndex i)).value.extractLsb' (8 * n) 8)) := by
  obtain ⟨output, entered, pc, _⟩ := caller.enters other extra vector state
  let live := caller.arguments args apart output
  let tail := caller.tail ret output
  have protects : tail.ReadsOutside args.outputBytes := ⟨outputApart.budget, outputApart.bottom, outputApart.saved⟩
  obtain ⟨after, body, returned, rsp, rbp, saved, frame, statusReg, status, result, receipt, written⟩ :=
    X86P1Sub1Exit.completed_after_checks other extra vector (caller.body output)
      caller.prologue.code caller.upper (caller.bodyPlacement output) (caller.bodyMode output)
      (by simpa only [entryOffset_zero] using pc) (fun i => live.loads (leftLoad i)) (fun i => live.loads (rightLoad i))
      agrees live.capacity room (fun i => live.loads (loadIndex i)) live.stores outputApart.fields
      outputApart.base outputApart.length outputApart.code tail protects outputApart.retain
  refine ⟨after, @X86FuelPrefix.fetches_then (handlers other extra) vector 8 _ state (caller.body output) after entered body,
    ⟨returned, rsp, rbp, saved, (caller.frame output).trans frame, statusReg, status, result, ?_⟩, written⟩
  intro n present
  simpa only [tail, CallerInputs.tail, CallerInputs.returnFuel, restored_receipt] using receipt n present

noncomputable def Arguments.expectedExit {state : State} (args : Arguments state) : ExitStatus := by
  classical
  exact if ∀ j : Fin 7, (args.loads (leftLoad j)).value = (args.loads (rightLoad j)).value then
    if (args.capacity.value false).toNat < (args.capacity.value true).toNat then .completed else .unsupported
  else .refused

theorem returns_from_caller (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom))
    (ret : ReturnInputs caller) (outputApart : OutputApart args ret) :
    ∃ steps after,
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret
        ((if args.expectedExit = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if args.expectedExit = .completed then args.outputBytes ∪ ret.writes else ret.writes)
        args.expectedExit after ∧
      (args.expectedExit = .completed → ∀ i : Fin 4, ∀ n < 8,
        after.mem.get? (X86WriteWords.physicalAddress (args.stores i).data n) =
          some ((args.loads (loadIndex i)).value.extractLsb' (8 * n) 8)) := by
  classical
  by_cases agrees : ∀ j : Fin 7, (args.loads (leftLoad j)).value = (args.loads (rightLoad j)).value
  · have agreeWords : ∀ j : Fin 7, (args.loads (leftLoad j)).value == (args.loads (rightLoad j)).value := by
      simpa using agrees
    by_cases room : (args.capacity.value false).toNat < (args.capacity.value true).toNat
    · obtain ⟨after, ran, returned, written⟩ :=
        completes_from_caller other extra vector state caller args apart ret outputApart agreeWords room
      exact ⟨_, after, ran, by simpa [Arguments.expectedExit, agrees, room] using returned,
        fun _ => written⟩
    · obtain ⟨after, ran, returned⟩ :=
        capacity_stop_from_caller other extra vector state caller args apart ret agreeWords room
      exact ⟨_, after, ran, by simpa [Arguments.expectedExit, agrees, room] using returned,
        by simp [Arguments.expectedExit, agrees, room]⟩
  · let mismatch (n : Nat) := ∃ i : Fin 7, i.val = n ∧
      (args.loads (leftLoad i)).value ≠ (args.loads (rightLoad i)).value
    have someMismatch : ∃ n, mismatch n := by
      obtain ⟨i, bad⟩ := not_forall.mp agrees
      exact ⟨i.val, i, rfl, bad⟩
    obtain ⟨index, least, unequal⟩ := Nat.find_spec someMismatch
    have earlier (j : Fin 7) (before : j.val < index.val) :
        (args.loads (leftLoad j)).value == (args.loads (rightLoad j)).value := by
      by_contra bad
      apply Nat.find_min someMismatch (least ▸ before)
      exact ⟨j, rfl, fun eq => bad (by simp [eq])⟩
    obtain ⟨after, ran, returned⟩ :=
      refuses_from_caller other extra vector index state caller args apart ret earlier unequal
    exact ⟨_, after, ran, by simpa [Arguments.expectedExit, agrees] using returned,
      by simp [Arguments.expectedExit, agrees]⟩

end Mettapedia.Machines.TIsa.X86P1Sub1Entry

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.savedStack
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.savedStackAtBody
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.enters_with_saved_stack
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.CallerInputs.enters
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.CallerInputs.control
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.enters_with_arguments
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.refuses_from_caller
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.capacity_stop_from_caller
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.completes_from_caller
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Entry.returns_from_caller
