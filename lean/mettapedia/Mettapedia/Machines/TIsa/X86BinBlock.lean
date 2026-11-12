import Mettapedia.Machines.TIsa.X86Execution
import Mettapedia.Machines.TIsa.X86BinCapture
import Mettapedia.Machines.TIsa.X86ResourceCopy
import Mettapedia.Machines.TIsa.X86ResourceBinary

/-!
# The captured U64 ADD/SUB data span as three fetched instructions

The original Sail model executes the captured copy/arithmetic/copy body.
Address rebasing and a concrete state frame carry code and decode inputs
through all three steps. The result joins one existing TAKE/KEEP/MAKE scalar
update; source reflection and native three-step determinism exclude invented
answers. The final frame permits only the destination, scratch register,
arithmetic flags and RIP to change.

The proof is uniform over the captured operand tuples and all represented
word values, including aliases. Controls load actual captured bytes, run
high-register ADD with an aliased destination, and refuse its answer after
changing the arithmetic opcode to SUB. Fuel-prefix execution, whole compiler
buffer behavior, ABI and complete program refinement remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BinBlock

open _root_.X86Registers X86RegisterRefinement X86Execution X86Arithmetic
open X86BinCapture (physical scratch expected)

def copied (state : State) (destination : Fin 16) (value : Word) (pointer : BitVec 48) : State :=
  X86Move.putPointer (put state destination value) pointer

def calculated (state : State) (value : Word) (flags : BitVec 32) (pointer : BitVec 48) : State :=
  X86Move.putPointer (X86Flags.putFlags (put state scratch value) flags) pointer

def finished (state : State) (base : Int) (operation : DefinedOperation) (destination : Fin 12)
    (left right : Word) (flags output : BitVec 32) : State :=
  let first := copied state scratch left (address base 3)
  let second := calculated first (result operation left right) (X86Flags.mergeFlags flags output) (address base 6)
  copied second (physical destination) (result operation left right) (address base 9)

theorem scratch_ne_physical (register : Fin 12) : scratch ≠ physical register := by
  intro same
  exact Registers.scratch_apart .x86_64 (Registers.canonical .x86_64)
    (Registers.canonical_admitted .x86_64) 0 register (congrArg Fin.val same)

theorem copied_frame (state : State) (destination : Fin 16) (value : Word) (pointer : BitVec 48) :
    DataFrame state (copied state destination value pointer) :=
  data_trans (data_put state destination value) (data_pointer _ pointer)

theorem calculated_frame (state : State) (value : Word) (flags : BitVec 32) (pointer : BitVec 48) :
    DataFrame state (calculated state value flags pointer) :=
  data_trans (data_put state scratch value) (data_trans (data_flags _ flags) (data_pointer _ pointer))

theorem copied_rip (state : State) (destination : Fin 16) (value : Word) (pointer : BitVec 48) :
    (copied state destination value pointer).regs.get? .rip = some (pointer.signExtend 64) := by
  simp [copied, X86Move.putPointer]

theorem calculated_rip (state : State) (value : Word) (flags : BitVec 32) (pointer : BitVec 48) :
    (calculated state value flags pointer).regs.get? .rip = some (pointer.signExtend 64) := by
  simp [calculated, X86Move.putPointer]

theorem copied_flags (state : State) (destination : Fin 16) (value : Word) (pointer : BitVec 48) :
    (copied state destination value pointer).regs.get? .rflags = state.regs.get? .rflags := by
  unfold copied
  rw [(pointer_frame _ pointer).registers .rflags (by decide), put_flags]

def clobbers (destination : Fin 12) : Finset Register :=
  {key scratch, key (physical destination), .rflags, .rip}

theorem finished_frame (state : State) (base : Int) (operation : DefinedOperation)
    (destination : Fin 12) (left right : Word) (flags output : BitVec 32) :
    RegisterFrame (clobbers destination) state (finished state base operation destination left right flags output) := by
  let first := copied state scratch left (address base 3)
  let second := calculated first (result operation left right)
    (X86Flags.mergeFlags flags output) (address base 6)
  have one : RegisterFrame ({key scratch} ∪ {.rip}) state first :=
    (put_frame state scratch left).trans (pointer_frame _ _)
  have two : RegisterFrame ({key scratch} ∪ ({.rflags} ∪ {.rip})) first second :=
    (put_frame first scratch _).trans ((flags_frame _ _).trans (pointer_frame _ _))
  have three : RegisterFrame ({key (physical destination)} ∪ {.rip}) second
      (finished state base operation destination left right flags output) :=
    (put_frame second (physical destination) _).trans (pointer_frame _ _)
  apply (one.trans (two.trans three)).mono
  intro register member
  simp only [clobbers, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
  tauto

theorem clobbers_data (destination : Fin 12) : clobbers destination ⊆ dataRegisters := by
  revert destination
  decide

theorem copied_local_frame (state : State) (destination : Fin 16) (value : Word) (pointer : BitVec 48) :
    RegisterFrame {key destination, .rip} state (copied state destination value pointer) := by
  simpa only [copied, Finset.singleton_union] using
    (put_frame state destination value).trans (pointer_frame _ pointer)

theorem calculated_local_frame (state : State) (value : Word) (flags : BitVec 32) (pointer : BitVec 48) :
    RegisterFrame {key scratch, .rflags, .rip} state (calculated state value flags pointer) := by
  simpa only [calculated, Finset.singleton_union] using
    (put_frame state scratch value).trans ((flags_frame _ flags).trans (pointer_frame _ pointer))

theorem finished_flags (state : State) (base : Int) (operation : DefinedOperation)
    (destination : Fin 12) (left right : Word) (flags output : BitVec 32) :
    (finished state base operation destination left right flags output).regs.get? .rflags =
      some (X86Flags.mergeFlags flags output) := by
  unfold finished
  rw [copied_flags]
  unfold calculated
  rw [(pointer_frame _ _).registers .rflags (by decide)]
  simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]

local instance : MemoryPrimitives := X86Memory.ordinary

theorem expected_trace (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state : State) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 9 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt (expected operation destination left right))
    (leftValue rightValue : Word) (flags : BitVec 32)
    (leftKnown : lookup state (physical left) = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output first second, Step state first ∧ Step first second ∧
      Step second (finished state origin.address.toInt operation destination leftValue rightValue flags output) ∧
      RegisterFrame (clobbers destination) state first ∧
      RegisterFrame (clobbers destination) state second ∧
      RegisterFrame (clobbers destination) state
        (finished state origin.address.toInt operation destination leftValue rightValue flags output) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let first := copied state scratch leftValue (address origin.address.toInt 3)
  let firstWindow := windowAt state state origin (RegisterFrame.refl dataRegisters state) upper 0 (by decide)
    (by simpa [address] using origin.rip) (expected operation destination left right) loaded
    (physical left) scratch (0x89#8) rfl rfl rfl
  have firstRun : Step state first :=
    X86ResourceCopy.Window.executes state (physical left) scratch firstWindow leftValue leftKnown quiet
  have firstFrame : DataFrame state first := copied_frame state scratch leftValue _
  have scratchKnown : lookup first scratch = some leftValue := by
    dsimp only [first, copied]
    rw [X86Move.lookup_putPointer, lookup_put_same]
  have rightAfter : lookup first (physical right) = some rightValue := by
    dsimp only [first, copied]
    rw [X86Move.lookup_putPointer, lookup_put_other _ _ _ _ (scratch_ne_physical right)]
    exact rightKnown
  have flagsAfter : first.regs.get? .rflags = some flags := by
    rw [copied_flags]
    exact flagsKnown
  have quietAfter : first.regs.get? .log_register_writes = some false :=
    (firstFrame.registers .log_register_writes (by decide)).trans quiet
  let secondWindow := windowAt state first origin firstFrame upper 3 (by decide)
    (copied_rip _ _ _ _) (expected operation destination left right)
    (firstFrame.code_preserved _ _ loaded) (physical right) scratch (opcode operation) rfl rfl rfl
  obtain ⟨output, secondRun⟩ := fetched_register64 other vector operation first (physical right) scratch
    secondWindow leftValue rightValue flags rightAfter scratchKnown flagsAfter quietAfter
  let second := calculated first (result operation leftValue rightValue)
    (X86Flags.mergeFlags flags output) (address origin.address.toInt 6)
  have secondStep : Step first second := secondRun
  have secondFrame : DataFrame state second := data_trans firstFrame (calculated_frame first _ _ _)
  have computed : lookup second scratch = some (result operation leftValue rightValue) := by
    dsimp only [second, calculated]
    rw [X86Move.lookup_putPointer, X86Flags.putFlags_gpr, lookup_put_same]
  have quietSecond : second.regs.get? .log_register_writes = some false :=
    (secondFrame.registers .log_register_writes (by decide)).trans quiet
  let finalWindow := windowAt state second origin secondFrame upper 6 (by decide)
    (calculated_rip _ _ _ _) (expected operation destination left right)
    (secondFrame.code_preserved _ _ loaded) scratch (physical destination) (0x89#8) rfl rfl rfl
  have finalRun : Step second
      (finished state origin.address.toInt operation destination leftValue rightValue flags output) :=
    X86ResourceCopy.Window.executes second scratch (physical destination) finalWindow
      (result operation leftValue rightValue) computed quietSecond
  have firstLocal : RegisterFrame (clobbers destination) state first :=
    (copied_local_frame state scratch leftValue _).mono (by simp [clobbers])
  have secondLocal : RegisterFrame (clobbers destination) state second := by
    apply (firstLocal.trans (calculated_local_frame first _ _ _)).mono
    simp [clobbers]
  exact ⟨output, first, second, firstRun, secondStep, finalRun, firstLocal, secondLocal,
    finished_frame state origin.address.toInt operation destination leftValue rightValue flags output⟩

theorem expected_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination left right : Fin 12)
    (state : State) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 9 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt (expected operation destination left right))
    (leftValue rightValue : Word) (flags : BitVec 32)
    (leftKnown : lookup state (physical left) = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      (∃ first second, Step state first ∧ Step first second ∧
        Step second (finished state origin.address.toInt operation destination leftValue rightValue flags output)) ∧
      DataFrame state (finished state origin.address.toInt operation destination leftValue rightValue flags output) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, first, second, one, two, three, _, _, framed⟩ :=
    expected_trace other vector operation destination left right state origin upper loaded
      leftValue rightValue flags leftKnown rightKnown flagsKnown quiet
  exact ⟨output, ⟨first, second, one, two, three⟩, framed.mono (clobbers_data destination)⟩

theorem finished_destination (state : State) (base : Int) (operation : DefinedOperation)
    (destination : Fin 12) (left right : Word) (flags output : BitVec 32) :
    lookup (finished state base operation destination left right flags output) (physical destination) =
      some (result operation left right) := by
  unfold finished copied
  rw [X86Move.lookup_putPointer, lookup_put_same]

theorem finished_represents (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (state : State) (represented : RepresentsOn (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) keys values state)
    (base : Int) (operation : DefinedOperation) (destination : Fin 12)
    (left right : Word) (flags output : BitVec 32) :
    RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys
      (Function.update values destination (result operation left right))
      (finished state base operation destination left right flags output) := by
  have one : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values (copied state scratch left (address base 3)) := by
    apply X86ResourceCopy.pointer_preserves_representation
    exact put_scratch_represents _ _ keys values state represented 0 left
  have two : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values (calculated (copied state scratch left (address base 3)) (result operation left right)
        (X86Flags.mergeFlags flags output) (address base 6)) := by
    apply X86ResourceCopy.pointer_preserves_representation
    apply X86Flags.putFlags_represents
    exact put_scratch_represents _ _ keys values _ one 0 _
  apply X86ResourceCopy.pointer_preserves_representation
  apply put_logical_represents
  intro register member
  exact two register (Finset.mem_of_mem_erase member)

theorem captured_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ X86BinCapture.captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 9 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt body)
    (leftValue rightValue : Word) (flags : BitVec 32)
    (leftKnown : lookup state (physical left) = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ resultFlags,
      (∃ first second, Step state first ∧ Step first second ∧
        Step second (finished state origin.address.toInt (X86BinCapture.decodeOperation operation.val)
          destination leftValue rightValue flags resultFlags)) ∧
      DataFrame state (finished state origin.address.toInt (X86BinCapture.decodeOperation operation.val)
        destination leftValue rightValue flags resultFlags) := by
  have same := Option.some.inj (output.symm.trans
    (X86BinCapture.checked_body operation destination left right sample member inputs))
  subst body
  exact expected_executes other vector (X86BinCapture.decodeOperation operation.val) destination left right
    state origin upper loaded leftValue rightValue flags leftKnown rightKnown flagsKnown quiet

def sourceAction {Key : Type} (operation : DefinedOperation) (left right destination : Key) : Cells.Action Key :=
  ⟨.binary (X86ResourceBinary.binary operation), [left, right], destination⟩

theorem source_computes {Key : Type} (operation : DefinedOperation) (values : Key → Word)
    (left right destination : Key) :
    (sourceAction operation left right destination).scalar.evaluate
      ((sourceAction operation left right destination).inputs.map values) =
      some (result operation (values left) (values right)) := by
  cases operation <;> rfl

theorem source_realized {Key : Type} [DecidableEq Key] (operation : DefinedOperation)
    (keys : Finset Key) (values : Key → Word) (left right destination : Key)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys) (destinationPresent : destination ∈ keys) :
    ∃ invocation : Cells.Invocation (sourceAction operation left right destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (result operation (values left) (values right))) := by
  apply Cells.scalar_update_realized _ keys values _
  · intro register member
    simp [sourceAction, Cells.Action.support] at member
    rcases member with rfl | rfl | rfl
    · exact destinationPresent
    · exact leftPresent
    · exact rightPresent
  · exact source_computes operation values left right destination

theorem source_reflected {Key : Type} [DecidableEq Key] (operation : DefinedOperation)
    (keys : Finset Key) (values : Key → Word) (left right destination : Key)
    (invocation : Cells.Invocation (sourceAction operation left right destination))
    (enabled : Cells.system.Enables (Cells.encode keys values) invocation) :
    invocation.result = result operation (values left) (values right) ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (result operation (values left) (values right))) := by
  obtain ⟨computed, fired⟩ := Cells.scalar_update_reflected _ invocation keys values enabled
  rw [source_computes] at computed
  have same := (Option.some.inj computed).symm
  exact ⟨same, same ▸ fired⟩

theorem captured_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ X86BinCapture.captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 9 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt body)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (leftPresent : left ∈ keys) (rightPresent : right ∈ keys) (destinationPresent : destination ∈ keys)
    (represented : RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
      keys values state)
    (flags : BitVec 32) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ invocation : Cells.Invocation
        (sourceAction (X86BinCapture.decodeOperation operation.val) left right destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination
          (result (X86BinCapture.decodeOperation operation.val) (values left) (values right))) ∧
      ∃ after, Steps state after ∧
        RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) keys
          (Function.update values destination
            (result (X86BinCapture.decodeOperation operation.val) (values left) (values right))) after ∧
        RegisterFrame (clobbers destination) state after := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨invocation, enabled, fired⟩ := source_realized (X86BinCapture.decodeOperation operation.val)
    keys values left right destination leftPresent rightPresent destinationPresent
  obtain ⟨resultFlags, path, _⟩ := captured_executes other vector operation destination left right sample member
    inputs body output state origin upper loaded (values left) (values right) flags
    (represented left leftPresent) (represented right rightPresent) flagsKnown quiet
  obtain ⟨first, second, one, two, three⟩ := path
  exact ⟨invocation, enabled, fired, _, three_steps one two three,
    finished_represents keys values state represented origin.address.toInt
      (X86BinCapture.decodeOperation operation.val) destination (values left) (values right) flags resultFlags,
    finished_frame state origin.address.toInt (X86BinCapture.decodeOperation operation.val)
      destination (values left) (values right) flags resultFlags⟩

theorem captured_wrong_answer_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12)
    (sample : NativeImage.TemplateSample) (member : sample ∈ X86BinCapture.captured.2)
    (inputs : sample.inputs = [operation.val, destination.val, left.val, right.val])
    (body : List Nat) (output : sample.body "BIN" = some body)
    (state : State) (origin : X86LegacyFetch.Basis state)
    (upper : origin.address.toInt + 9 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt body)
    (leftValue rightValue : Word) (flags : BitVec 32)
    (leftKnown : lookup state (physical left) = some leftValue)
    (rightKnown : lookup state (physical right) = some rightValue)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (answer : Word) (wrongAnswer : result (X86BinCapture.decodeOperation operation.val) leftValue rightValue ≠ answer) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (∃ first second, Step state first ∧ Step first second ∧ Step second after) ∧
      lookup after (physical destination) = some answer := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨resultFlags, expectedPath, _⟩ := captured_executes other vector operation destination left right
    sample member inputs body output state origin upper loaded leftValue rightValue flags
    leftKnown rightKnown flagsKnown quiet
  rintro ⟨after, suppliedPath, answerKnown⟩
  have same := three_steps_deterministic expectedPath suppliedPath
  rw [← same, finished_destination] at answerKnown
  exact wrongAnswer (Option.some.inj answerKnown)

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped (operation : DefinedOperation) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .r8 (7#64)
  let registers := registers.insert .r9 (11#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x4d#8)
  let memory := memory.insert 4097 (0x89#8)
  let memory := memory.insert 4098 (0xc6#8)
  let memory := memory.insert 4099 (0x4d#8)
  let memory := memory.insert 4100 (opcode operation)
  let memory := memory.insert 4101 (0xce#8)
  let memory := memory.insert 4102 (0x4d#8)
  let memory := memory.insert 4103 (0x89#8)
  let memory := memory.insert 4104 (0xf0#8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (operation : DefinedOperation) : X86LegacyFetch.Basis (mapped operation) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := control
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

private theorem loaded (operation : DefinedOperation) :
    codeLoaded (mapped operation) 4096 (expected operation 4 4 5) := by
  change codeLoaded (mapped operation) 4096 [77, 137, 198, 77, (opcode operation).toNat, 206, 77, 137, 240]
  intro index byte present
  have bounded : index < 9 := (List.getElem?_eq_some_iff.mp present).choose
  interval_cases index <;> simp_all [mapped, address, Std.ExtHashMap.getElem_insert]
  all_goals rw [← present, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem leftKnown (operation : DefinedOperation) : lookup (mapped operation) (physical 4) = some (7#64) := by
  change ((mapped operation).regs.get? .r8).map (fun value : Word => value) = _
  simp [mapped, Std.ExtDHashMap.get?_insert]

private theorem rightKnown (operation : DefinedOperation) : lookup (mapped operation) (physical 5) = some (11#64) := by
  change ((mapped operation).regs.get? .r9).map (fun value : Word => value) = _
  simp [mapped]

private theorem actual_capture_run (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ flags, ∃ first second,
      Step (mapped (X86BinCapture.decodeOperation operation.val)) first ∧ Step first second ∧
      Step second (finished (mapped (X86BinCapture.decodeOperation operation.val)) 4096
        (X86BinCapture.decodeOperation operation.val) 4 (7#64) (11#64) (0x200#32) flags) := by
  obtain ⟨sample, member, inputs, bytes⟩ := X86BinCapture.every_output_exact operation 4 4 5
  obtain ⟨flags, path, _⟩ := captured_executes other vector operation 4 4 5 sample member inputs _ bytes
    (mapped (X86BinCapture.decodeOperation operation.val)) (origin _)
    (by change (4096 : Int) + 9 < 2 ^ 47; decide) (loaded _)
    (7#64) (11#64) (0x200#32) (leftKnown _) (rightKnown _)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
  exact ⟨flags, path⟩

theorem captured_add_three_steps (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (∃ first second, Step (mapped .add) first ∧ Step first second ∧ Step second after) ∧
      lookup after (physical 4) = some (18#64) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨flags, path⟩ := actual_capture_run other vector 0
  exact ⟨_, path, finished_destination (mapped .add) 4096 .add 4 (7#64) (11#64) (0x200#32) flags⟩

theorem changed_opcode_refuses_add_answer (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (∃ first second, Step (mapped .sub) first ∧ Step first second ∧ Step second after) ∧
      lookup after (physical 4) = some (18#64) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨flags, path⟩ := actual_capture_run other vector 1
  rintro ⟨after, supplied, wrong⟩
  have same := three_steps_deterministic path supplied
  rw [← same, finished_destination] at wrong
  exact (by decide : result .sub (7#64) (11#64) ≠ (18#64)) (Option.some.inj wrong)

theorem alias_has_no_duplicate_read :
    (sourceAction .add (0 : Fin 1) 0 0).readKeys = ∅ := by decide

theorem wrong_aliased_result_refused
    (invocation : Cells.Invocation (sourceAction .add (0 : Fin 1) 0 0))
    (enabled : Cells.system.Enables (Cells.encode {0} (fun _ => (7#64))) invocation) :
    invocation.result ≠ (13#64) := by
  have same := (source_reflected .add {0} (fun _ => (7#64)) 0 0 0 invocation enabled).1
  rw [same]
  decide

end Controls
end Mettapedia.Machines.TIsa.X86BinBlock

#print axioms Mettapedia.Machines.TIsa.X86BinBlock.expected_executes
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.finished_frame
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.captured_refines
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.captured_wrong_answer_refused
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.Controls.captured_add_three_steps
#print axioms Mettapedia.Machines.TIsa.X86BinBlock.Controls.changed_opcode_refuses_add_answer
