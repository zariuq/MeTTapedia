import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86BinBlock
import Mettapedia.Machines.TIsa.X86CodePlacement

/-!
# Complete U64 ADD/SUB template with native fuel accounting

The existing fetched fuel-prefix and three-instruction arithmetic contracts
compose into the forty-nine-byte instruction template. The result retains
logical register representation, counter bytes, code-exclusion conditions and
an exact register/byte frame. Exhaustion reaches the declared failure boundary
without running the data body. Counted execution is deterministic.

Captured C helper outputs supply only the nine-byte BIN body. Their unpatched
fuel displacement is never used as a final linked failure target. Raw image
placement, actual failure-handler results, source admission and whole-program
ABI composition remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86FueledBin
open _root_.X86Registers X86RegisterRefinement X86Execution X86Arithmetic
open X86BinCapture (physical scratch expected)

local instance : MemoryPrimitives := X86Memory.ordinary

structure Inputs (state : State) (operation : DefinedOperation) (destination left right : Fin 12)
    extends X86FuelPrefix.Inputs state where
  wholeUpper : address.toInt + 49 < (2 ^ 47 : Int)
  bodyLoaded : codeLoaded state (address.toInt + 40) (expected operation destination left right)
  bodyOutside : ∀ index byte, (expected operation destination left right)[index]? = some byte →
    ((X86Execution.address (address.toInt + 40) index).signExtend 52).toNat ∉
      X86WriteWords.written usedAddress (List.range 8)

def instructionCount {state : State} {operation : DefinedOperation} {destination left right : Fin 12}
    (input : Inputs state operation destination left right) : Nat :=
  X86FuelPrefix.instructionCount input.toInputs + if fuelAvailable input.budget input.used then 3 else 0

def clobbers (destination : Fin 12) : Finset Register :=
  {.r14, .r15, key (physical destination), .rflags, .rip}

theorem logical_outside : ∀ register : Fin 12,
    key (physical register) ∉ ({.r14, .r15, .rflags, .rip} : Finset Register) := by decide

theorem prefix_data : ({.r14, .r15, .rflags, .rip} : Finset Register) ⊆ dataRegisters := by
  decide

theorem prefix_preserves_representation (state after : State)
    (input : X86FuelPrefix.Inputs state) (correct : X86FuelPrefix.Result state input after)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state) :
    RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys values after := by
  intro register member
  change lookup after (physical register) = some (values register)
  rw [correct.frame.lookup (physical register) (logical_outside register)]
  exact represented register member

theorem body_after_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state after : State) (input : Inputs state operation destination left right)
    (correct : X86FuelPrefix.Result state input.toInputs after)
    (available : fuelAvailable input.budget input.used = true)
    (leftValue rightValue : Word)
    (leftKnown : lookup state (physical left) = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ flags output,
      (X86FuelPrefix.fetches 3).run after = .ok ()
        (X86BinBlock.finished after (input.address.toInt + 40) operation destination leftValue rightValue flags output) := by
  let : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  have pointer : after.regs.get? .rip = some ((address input.address.toInt 40).signExtend 64) := by
    simpa only [available, ite_true] using correct.pointer
  let origin := X86StateFrame.rebase state after input.toInputs.toBasis correct.frame prefix_data
    (extent := 49) input.wholeUpper 40 (by decide) pointer
  have originValue : origin.address.toInt = input.address.toInt + 40 := by
    exact address_toInt _ (by simpa using BitVec.le_toInt input.address) input.wholeUpper 40 (by decide)
  have loaded : codeLoaded after origin.address.toInt (expected operation destination left right) := by
    rw [originValue]
    apply correct.frame.codeLoaded _ _ input.bodyLoaded
    intro index byte present
    simpa only [X86FuelPrefix.writes, available, ite_true] using input.bodyOutside index byte present
  obtain ⟨flags, flagsKnown⟩ := correct.flags
  have lhs := (correct.frame.lookup (physical left) (logical_outside left)).trans leftKnown
  have rhs := (correct.frame.lookup (physical right) (logical_outside right)).trans rightKnown
  have quiet := (correct.frame.registers .log_register_writes (by decide)).trans input.quiet
  have body := X86BinBlock.expected_executes (X86FuelPrefix.linkedHandlers other extra) vector operation
    destination left right after origin (by rw [originValue]; have := input.wholeUpper; omega)
    loaded leftValue rightValue flags lhs rhs flagsKnown quiet
  rw [X86FuelPrefix.arithmetic_installed] at body
  obtain ⟨output, ⟨first, second, one, two, three⟩, _⟩ := body
  refine ⟨flags, output, ?_⟩
  have run := X86FuelPrefix.fetches_cons 2 after first _ one
    (X86FuelPrefix.fetches_cons 1 first second _ two (X86FuelPrefix.fetches_one _ _ three))
  simpa only [originValue] using run

def outputValues {state : State} {operation : DefinedOperation} {destination left right : Fin 12}
    (input : Inputs state operation destination left right) (values : Fin 12 → Word) : Fin 12 → Word :=
  if fuelAvailable input.budget input.used then
    Function.update values destination (result operation (values left) (values right)) else values

structure Result (state : State) {operation : DefinedOperation} {destination left right : Fin 12}
    (input : Inputs state operation destination left right) (keys : Finset (Fin 12))
    (values : Fin 12 → Word) (after : State) : Prop where
  pointer : after.regs.get? .rip = some ((if fuelAvailable input.budget input.used then
    address input.address.toInt 49 else input.exhausted).signExtend 64)
  represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
    keys (outputValues input values) after
  frame : X86StateFrame.Frame (clobbers destination) (X86FuelPrefix.writes input.toInputs) state after
  flags : ∃ value, after.regs.get? .rflags = some value
  counter : fuelAvailable input.budget input.used = true → ∀ index < 8,
    after.mem.get? (X86WriteWords.physicalAddress input.usedAddress index) =
      some ((input.used + (1#64)).extractLsb' (8 * index) 8)
  exhausted : fuelAvailable input.budget input.used = false → after.mem = state.mem

theorem finished_pointer (state : State) (base : Int) (operation : DefinedOperation)
    (destination : Fin 12) (left right : Word) (flags output : BitVec 32) :
    (X86BinBlock.finished state base operation destination left right flags output).regs.get? .rip =
      some ((address base 9).signExtend 64) := by
  simp [X86BinBlock.finished, X86BinBlock.copied, X86Move.putPointer]

theorem finished_flags (state : State) (base : Int) (operation : DefinedOperation)
    (destination : Fin 12) (left right : Word) (flags output : BitVec 32) :
    (X86BinBlock.finished state base operation destination left right flags output).regs.get? .rflags =
      some (X86Flags.mergeFlags flags output) := by
  unfold X86BinBlock.finished
  rw [X86BinBlock.copied_flags]
  simp [X86BinBlock.calculated, X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state : State) (input : Inputs state operation destination left right)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (instructionCount input)).run state = .ok () after ∧
      Result state input keys values after := by
  let : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨fueled, fuelRun, fuelResult⟩ := X86FuelPrefix.executes other extra vector state input.toInputs
  have fuelRepresentation := prefix_preserves_representation state fueled input.toInputs fuelResult keys values represented
  by_cases available : fuelAvailable input.budget input.used = true
  · obtain ⟨flags, output, bodyRun⟩ := body_after_prefix other extra vector operation destination left right
      state fueled input fuelResult available (values left) (values right)
      (represented left leftPresent) (represented right rightPresent)
    let finish := X86BinBlock.finished fueled (input.address.toInt + 40) operation destination
      (values left) (values right) flags output
    have bodyFrame := X86BinBlock.finished_frame fueled (input.address.toInt + 40) operation destination
      (values left) (values right) flags output
    refine ⟨finish, ?_, ?_⟩
    · simpa only [instructionCount, available, ite_true] using
        X86FuelPrefix.fetches_then _ 3 state fueled finish fuelRun bodyRun
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have position : address (input.address.toInt + 40) 9 = address input.address.toInt 49 := by
          simp only [address]
          congr 1
          omega
        simpa only [available, ite_true, position] using
          finished_pointer fueled (input.address.toInt + 40) operation destination (values left) (values right) flags output
      · simpa only [outputValues, available, ite_true] using
          X86BinBlock.finished_represents keys values fueled fuelRepresentation (input.address.toInt + 40)
            operation destination (values left) (values right) flags output
      · have combined := fuelResult.frame.trans (X86StateFrame.registerOnly bodyFrame)
        apply combined.mono
        · intro register member
          simp only [clobbers, X86BinBlock.clobbers, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, show scratch = (14 : Fin 16) from by decide, key] at member ⊢
          tauto
        · simp
      · exact ⟨_, finished_flags fueled (input.address.toInt + 40) operation destination
          (values left) (values right) flags output⟩
      · intro _ index within
        rw [bodyFrame.memory]
        exact fuelResult.counter available index within
      · intro unavailable
        rw [available] at unavailable
        cases unavailable
  · have unavailable : fuelAvailable input.budget input.used = false := by
      cases found : fuelAvailable input.budget input.used with
      | false => rfl
      | true => exact False.elim (available found)
    refine ⟨fueled, ?_, ?_⟩
    · simpa only [instructionCount, unavailable, Bool.false_eq_true, ite_false, Nat.add_zero] using fuelRun
    · refine ⟨?_, ?_, ?_, fuelResult.flags, ?_, fuelResult.exhausted⟩
      · simpa only [unavailable, Bool.false_eq_true, ite_false] using fuelResult.pointer
      · simpa only [outputValues, unavailable, Bool.false_eq_true, ite_false] using fuelRepresentation
      · apply fuelResult.frame.mono
        · intro register member
          simp only [clobbers, Finset.mem_insert, Finset.mem_singleton] at member ⊢
          tauto
        · exact Finset.Subset.refl _
      · intro possible
        rw [unavailable] at possible
        cases possible

theorem any_run_refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state : State) (input : Inputs state operation destination left right)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state) (after : State) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (instructionCount input)).run state = .ok () after →
      Result state input keys values after := by
  intro observed
  obtain ⟨proved, executed, correct⟩ := executes other extra vector operation destination left right
    state input keys values leftPresent rightPresent represented
  have same := (EStateM.Result.ok.inj (executed.symm.trans observed)).2
  simpa only [same] using correct

theorem source_refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state : State) (input : Inputs state operation destination left right)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys) (destinationPresent : destination ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state) (available : fuelAvailable input.budget input.used = true) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ invocation : Cells.Invocation (X86BinBlock.sourceAction operation left right destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (result operation (values left) (values right))) ∧
      ∃ after, (X86FuelPrefix.fetches (instructionCount input)).run state = .ok () after ∧
        Result state input keys values after ∧
        RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys
          (Function.update values destination (result operation (values left) (values right))) after := by
  obtain ⟨invocation, enabled, fired⟩ := X86BinBlock.source_realized operation keys values left right destination
    leftPresent rightPresent destinationPresent
  obtain ⟨after, executed, correct⟩ := executes other extra vector operation destination left right
    state input keys values leftPresent rightPresent represented
  refine ⟨invocation, enabled, fired, after, executed, correct, ?_⟩
  simpa only [outputValues, available, ite_true] using correct.represented

theorem source_answer_unique (operation : DefinedOperation) (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (left right destination : Fin 12)
    (invocation : Cells.Invocation (X86BinBlock.sourceAction operation left right destination))
    (enabled : Cells.system.Enables (Cells.encode keys values) invocation) :
    invocation.result = result operation (values left) (values right) :=
  (X86BinBlock.source_reflected operation keys values left right destination invocation enabled).1

theorem Result.image_preserved {state after : State} {operation : DefinedOperation}
    {destination left right : Fin 12} {input : Inputs state operation destination left right}
    {keys : Finset (Fin 12)} {values : Fin 12 → Word}
    (correct : Result state input keys values after) (base : Int) (view : NativeImage.View)
    (placed : X86CodePlacement.Placed state base view)
    (outside : ∀ index byte, view.read index = some byte →
      ((address base index).signExtend 52).toNat ∉ X86FuelPrefix.writes input.toInputs) :
    X86CodePlacement.Placed after base view := placed.preserved base view correct.frame outside

def inputsOfCapturedBody (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ X86BinCapture.captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (fuel : X86FuelPrefix.Inputs state)
    (upper : fuel.address.toInt + 49 < (2 ^ 47 : Int))
    (loaded : codeLoaded state (fuel.address.toInt + 40) body)
    (outside : ∀ index byte, body[index]? = some byte →
      ((address (fuel.address.toInt + 40) index).signExtend 52).toNat ∉
        X86WriteWords.written fuel.usedAddress (List.range 8)) :
    Inputs state (X86BinCapture.decodeOperation operation.val) destination left right where
  toInputs := fuel
  wholeUpper := upper
  bodyLoaded := by
    have same := Option.some.inj (output.symm.trans
      (X86BinCapture.checked_body operation destination left right sample member inputs))
    rw [← same]
    exact loaded
  bodyOutside := by
    have same := Option.some.inj (output.symm.trans
      (X86BinCapture.checked_body operation destination left right sample member inputs))
    rw [← same]
    exact outside

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ X86BinCapture.captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (fuel : X86FuelPrefix.Inputs state)
    (upper : fuel.address.toInt + 49 < (2 ^ 47 : Int))
    (loaded : codeLoaded state (fuel.address.toInt + 40) body)
    (outside : ∀ index byte, body[index]? = some byte →
      ((address (fuel.address.toInt + 40) index).signExtend 52).toNat ∉
        X86WriteWords.written fuel.usedAddress (List.range 8))
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state) :
    let input := inputsOfCapturedBody operation destination left right sample member inputs body output
      state fuel upper loaded outside
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (instructionCount input)).run state = .ok () after ∧
      Result state input keys values after :=
  executes other extra vector (X86BinCapture.decodeOperation operation.val) destination left right state
    (inputsOfCapturedBody operation destination left right sample member inputs body output state fuel upper loaded outside)
    keys values leftPresent rightPresent represented

namespace Controls

private def code (operation : DefinedOperation) : List Nat :=
  X86FuelPrefix.expected (0x1e0#32) ++ expected operation 4 4 5

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)

private def cells (operation : DefinedOperation) (budget used : Word) : List (Nat × BitVec 8) :=
  (List.range 49).map (fun index => (4096 + index, BitVec.ofNat 8 (((code operation)[index]?).getD 0))) ++
  (List.range 8).map (fun index => (8352 + index, budget.extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (8360 + index, used.extractLsb' (8 * index) 8)) ++ [(8368, 42#8)]

private theorem cells_distinct (operation : DefinedOperation) (budget used : Word) :
    (cells operation budget used).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells operation budget used).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private def mapped (operation : DefinedOperation) (budget used : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rdi (0x2000#64)
  let registers := registers.insert .r8 (7#64)
  let registers := registers.insert .r9 (11#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells operation budget used), (), 0, #[]⟩

private theorem mapped_known (operation : DefinedOperation) (budget used : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells operation budget used) :
    (mapped operation budget used).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (cells_distinct operation budget used) present

private theorem mapped_code (operation : DefinedOperation) (budget used : Word) (index : Nat) (within : index < 49) :
    (mapped operation budget used).mem.get? (4096 + index) =
      some (BitVec.ofNat 8 (((code operation)[index]?).getD 0)) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl ⟨index, List.mem_range.mpr within, rfl⟩))

private theorem mapped_budget (operation : DefinedOperation) (budget used : Word) (index : Nat) (within : index < 8) :
    (mapped operation budget used).mem.get? (8352 + index) = some (budget.extractLsb' (8 * index) 8) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨index, List.mem_range.mpr within, rfl⟩))

private theorem mapped_used (operation : DefinedOperation) (budget used : Word) (index : Nat) (within : index < 8) :
    (mapped operation budget used).mem.get? (8360 + index) = some (used.extractLsb' (8 * index) 8) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨index, List.mem_range.mpr within, rfl⟩)

private def input (operation : DefinedOperation) (budget used : Word) :
    Inputs (mapped operation budget used) operation 4 4 5 where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [mapped, Std.ExtDHashMap.get?_insert]
  fault := by simp [mapped, Std.ExtDHashMap.get?_insert]
  msrs := by simp [mapped, Std.ExtDHashMap.get?_insert]
  segments := by simp [mapped, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [mapped, Std.ExtDHashMap.get?_insert]
  rip := by simp [mapped, Std.ExtDHashMap.get?_insert]
  displacement := 0x1e0#32
  exhausted := 0x1200#48
  upper := by decide
  jump := by decide
  loaded := by
    intro index byte present
    have within : index < 40 := by
      have bound := (List.getElem?_eq_some_iff.mp present).choose
      simpa only [X86FuelPrefix.expected_length] using bound
    have place : ((address (0x1000#48).toInt index).signExtend 52).toNat = 4096 + index := by
      interval_cases index <;> rfl
    have codeAt : (code operation)[index]? = some byte := by
      rw [code, List.getElem?_append_left (by simpa only [X86FuelPrefix.expected_length] using within)]
      exact present
    rw [place, mapped_code operation budget used index (by omega), codeAt]
    rfl
  frame := 0x2000#64
  budget := budget
  used := used
  budgetAddress := 0x20a0#48
  usedAddress := 0x20a8#48
  budgetUpper := by decide
  usedUpper := by decide
  budgetEffective := by decide
  usedEffective := by decide
  budgetAligned := by decide
  usedAligned := by decide
  visible := visible
  controls := controls
  flags := 0#32
  frameKnown := by
    change ((mapped operation budget used).regs.get? .rdi).map (fun value : Word => value) = _
    simp [mapped, Std.ExtDHashMap.get?_insert]
  controlsKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  quiet := by simp [mapped]
  budgetPresent := by
    intro index within
    have place : ((address (0x20a0#48).toInt index).signExtend 52).toNat = 8352 + index := by
      interval_cases index <;> rfl
    rw [place]
    exact mapped_budget operation budget used index within
  usedPresent := by
    intro index within
    have place : ((address (0x20a8#48).toInt index).signExtend 52).toNat = 8360 + index := by
      interval_cases index <;> rfl
    rw [place]
    exact mapped_used operation budget used index within
  wholeUpper := by decide
  bodyLoaded := by
    intro index byte present
    have within : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
    have place : ((address ((0x1000#48).toInt + 40) index).signExtend 52).toNat = 4096 + (40 + index) := by
      interval_cases index <;> rfl
    have codeAt : (code operation)[40 + index]? = some byte := by
      rw [code, List.getElem?_append_right (by rw [X86FuelPrefix.expected_length]; omega)]
      simpa only [X86FuelPrefix.expected_length, Nat.add_sub_cancel_left] using present
    rw [place, mapped_code operation budget used (40 + index) (by omega), codeAt]
    rfl
  bodyOutside := by
    intro index byte present
    have within : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
    interval_cases index <;> decide

private def keys : Finset (Fin 12) := {4, 5}
private def values (register : Fin 12) : Word := if register = 4 then (7#64) else (11#64)

private theorem represented (operation : DefinedOperation) (budget used : Word) :
    RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values (mapped operation budget used) := by
  intro register member
  simp only [keys, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · change lookup (mapped operation budget used) (physical 4) = _
    rw [show physical 4 = (8 : Fin 16) from by decide]
    change ((mapped operation budget used).regs.get? .r8).map (fun value : Word => value) = _
    simp [mapped, values, Std.ExtDHashMap.get?_insert]
  · change lookup (mapped operation budget used) (physical 5) = _
    rw [show physical 5 = (9 : Fin 16) from by decide]
    change ((mapped operation budget used).regs.get? .r9).map (fun value : Word => value) = _
    simp [mapped, values, Std.ExtDHashMap.get?_insert]

private theorem run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (budget used : Word) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (instructionCount (input operation budget used))).run
        (mapped operation budget used) = .ok () after ∧
      Result (mapped operation budget used) (input operation budget used) keys values after :=
  executes other extra vector operation 4 4 5 (mapped operation budget used) (input operation budget used)
    keys values (by decide) (by decide) (represented operation budget used)

theorem add_alias (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (mapped .add (3#64) (2#64)) = .ok () after ∧
      lookup after 8 = some (18#64) ∧ after.mem.get? 8360 = some (3#8) ∧
      after.regs.get? .rip = some (0x1031#64) := by
  obtain ⟨after, executed, correct⟩ := run other extra vector .add (3#64) (2#64)
  refine ⟨after, executed, ?_, ?_, correct.pointer⟩
  · have value := correct.represented 4 (by decide)
    change lookup after (physical 4) = _ at value
    rw [show physical 4 = (8 : Fin 16) from by decide] at value
    exact value
  · exact correct.counter (by decide) 0 (by decide)

theorem sub_alias (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (mapped .sub (3#64) (2#64)) = .ok () after ∧
      lookup after 8 = some (0xfffffffffffffffc#64) ∧ after.mem.get? 8360 = some (3#8) := by
  obtain ⟨after, executed, correct⟩ := run other extra vector .sub (3#64) (2#64)
  refine ⟨after, executed, ?_, correct.counter (by decide) 0 (by decide)⟩
  have value := correct.represented 4 (by decide)
  change lookup after (physical 4) = _ at value
  rw [show physical 4 = (8 : Fin 16) from by decide] at value
  exact value

theorem exhausted_preserves (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run (mapped .add (3#64) (3#64)) = .ok () after ∧
      lookup after 8 = some (7#64) ∧ after.mem = (mapped .add (3#64) (3#64)).mem ∧
      after.regs.get? .rip = some (0x1200#64) := by
  obtain ⟨after, executed, correct⟩ := run other extra vector .add (3#64) (3#64)
  refine ⟨after, executed, ?_, correct.exhausted (by decide), correct.pointer⟩
  have value := correct.represented 4 (by decide)
  change lookup after (physical 4) = _ at value
  rw [show physical 4 = (8 : Fin 16) from by decide] at value
  exact value

theorem unlimited_wraps (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run (mapped .add (0#64) (0xffffffffffffffff#64)) = .ok () after ∧
      lookup after 8 = some (18#64) ∧ after.mem.get? 8360 = some (0#8) := by
  obtain ⟨after, executed, correct⟩ := run other extra vector .add (0#64) (0xffffffffffffffff#64)
  refine ⟨after, executed, ?_, correct.counter (by decide) 0 (by decide)⟩
  have value := correct.represented 4 (by decide)
  change lookup after (physical 4) = _ at value
  rw [show physical 4 = (8 : Fin 16) from by decide] at value
  exact value

theorem exhausted_execution_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (X86FuelPrefix.fetches 6).run (mapped .add (3#64) (3#64)) = .ok () after ∧
      lookup after 8 = some (18#64) := by
  obtain ⟨after, executed, old, _, _⟩ := exhausted_preserves other extra vector
  rintro ⟨claimed, run, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans run)).2
  rw [← same, old] at wrong
  exact (by decide : some (7#64) ≠ some (18#64)) wrong

theorem changed_opcode_refuses_add (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (X86FuelPrefix.fetches 10).run (mapped .sub (3#64) (2#64)) = .ok () after ∧
      lookup after 8 = some (18#64) := by
  obtain ⟨after, executed, difference, _⟩ := sub_alias other extra vector
  rintro ⟨claimed, run, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans run)).2
  rw [← same, difference] at wrong
  exact (by decide : some (0xfffffffffffffffc#64) ≠ some (18#64)) wrong

end Controls
end Mettapedia.Machines.TIsa.X86FueledBin

#print axioms Mettapedia.Machines.TIsa.X86FueledBin.executes
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.source_refines
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Result.image_preserved
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.add_alias
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.sub_alias
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.exhausted_preserves
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.unlimited_wraps
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.exhausted_execution_refused
#print axioms Mettapedia.Machines.TIsa.X86FueledBin.Controls.changed_opcode_refuses_add
