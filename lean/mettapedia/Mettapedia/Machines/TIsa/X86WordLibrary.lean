import Mettapedia.Machines.TIsa.X86BlockCompiler
import Mettapedia.Machines.TIsa.X86CopyBlock
import Mettapedia.Machines.TIsa.X86BinBlock

/-!
# Captured MOV/ADD/SUB templates in the common native block compiler

Source operations are guarded cell-resource firings. Their interpretation
agrees with the existing p1 U64 scalar recipes. Complete captured inventories
supply MOV and all 3456 ADD/SUB operand tuples, with proved-present lookups.

The library constructs local certificates for X86BlockCompiler. Copies reuse
their existing proved block instance; arithmetic uses the original three fetched
instructions and their intermediate frames. Flags availability and quiet logging
are preserved as readiness. The frame permits only non-frame logical registers,
R14, arithmetic flags and RIP; every fetched prefix preserves memory and RSP.

The mixed control checks dependent copies, an aliased destination, arithmetic
wraparound, self-elision, exact counts and a changed arithmetic opcode. Native
control/loops, full typed admission/hosting and public ABI composition remain
separate obligations. No new runtime or instruction-model definitions are used.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86WordLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Instruction where
  | copy (instruction : X86CopyBlock.Copy)
  | binary (operation : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0)

abbrev World := X86CopyBlock.World

def effect : Instruction → Cells.Action (Fin 12)
  | .copy instruction => instruction.effect
  | .binary operation destination left right _ =>
      X86BinBlock.sourceAction (X86BinCapture.decodeOperation operation.val) left right destination

def action (instruction : Instruction) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : Cells.Invocation (effect instruction), Cells.system.Enables world invocation
  Step world _ after := ∃ invocation : Cells.Invocation (effect instruction),
    Cells.system.Enables world invocation ∧ Cells.system.fire world invocation = after

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  rintro world ⟨invocation, enabled⟩
  exact ⟨(), Cells.system.fire world invocation, invocation, enabled, rfl⟩

def represents (world : World) (native : State) : Prop :=
  ∃ values : Fin 12 → Word, world = Cells.encode Finset.univ values ∧ X86CopyBlock.RegistersRepresented values native

def ready (native : State) : Prop :=
  ∃ flags : BitVec 32, native.regs.get? .rflags = some flags ∧ native.regs.get? .log_register_writes = some false

noncomputable def binSample? (operation : Fin 2) (destination left right : Fin 12) : Option NativeImage.TemplateSample :=
  X86BinCapture.captured.2.find? (fun sample => sample.inputs == [operation.val,destination.val,left.val,right.val])

theorem binSample_present (operation : Fin 2) (destination left right : Fin 12) :
    (binSample? operation destination left right).isSome := by
  apply List.find?_isSome.mpr
  obtain ⟨sample, member, inputs⟩ := X86BinCapture.sample_present operation destination left right
  exact ⟨sample, member, by simp [inputs]⟩

noncomputable def binSample (operation : Fin 2) (destination left right : Fin 12) : NativeImage.TemplateSample :=
  (binSample? operation destination left right).get (binSample_present operation destination left right)

theorem binSample_found (operation : Fin 2) (destination left right : Fin 12) :
    binSample? operation destination left right = some (binSample operation destination left right) :=
  (Option.some_get (binSample_present operation destination left right)).symm

theorem binSample_member (operation : Fin 2) (destination left right : Fin 12) :
    binSample operation destination left right ∈ X86BinCapture.captured.2 :=
  List.mem_of_find?_eq_some (binSample_found operation destination left right)

theorem binSample_inputs (operation : Fin 2) (destination left right : Fin 12) :
    (binSample operation destination left right).inputs = [operation.val,destination.val,left.val,right.val] := by
  have checked := List.find?_some (binSample_found operation destination left right)
  simpa only [beq_iff_eq] using checked

theorem binSample_body (operation : Fin 2) (destination left right : Fin 12) :
    (binSample operation destination left right).body "BIN" =
      some (X86BinCapture.expected (X86BinCapture.decodeOperation operation.val) destination left right) :=
  X86BinCapture.checked_body operation destination left right _ (binSample_member operation destination left right)
    (binSample_inputs operation destination left right)

noncomputable def binaryBytes (operation : Fin 2) (destination left right : Fin 12) : List Nat :=
  ((binSample operation destination left right).body "BIN").get
    (by rw [binSample_body]; rfl)

theorem binaryBytes_exact (operation : Fin 2) (destination left right : Fin 12) :
    binaryBytes operation destination left right =
      X86BinCapture.expected (X86BinCapture.decodeOperation operation.val) destination left right := by
  simp only [binaryBytes, binSample_body, Option.get_some]

noncomputable def bytes : Instruction → List Nat
  | .copy instruction => X86CopyBlock.emit instruction
  | .binary operation destination left right _ => binaryBytes operation destination left right

def count : Instruction → Nat
  | .copy instruction => if instruction.destination = instruction.source then 0 else 1
  | .binary .. => 3

def registers : Finset Register := X86CopyBlock.registerWrites ∪ {.r14,.rflags}

noncomputable def spec : X86BlockCompiler.Spec Instruction World where
  action := action
  represents := represents
  ready := ready
  bytes := bytes
  count := count
  registerWrites := registers
  byteWrites := ∅

theorem data_only : registers ⊆ dataRegisters := by decide
theorem stack_readonly : Register.rsp ∉ registers := by decide
theorem frame_readonly : Register.rdi ∉ registers := by decide

theorem copy_execute [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (instruction : X86CopyBlock.Copy) (source following : World) (native : State)
    (origin : X86LegacyFetch.Basis native)
    (safe : (spec.action (.copy instruction)).Safe source)
    (step : (spec.action (.copy instruction)).Step source () following)
    (represented : spec.represents source native) (prepared : spec.ready native)
    (upper : origin.address.toInt + (((spec.bytes (.copy instruction)).length + 3 : Nat) : Int) < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (spec.bytes (.copy instruction))) :
    ∃ after, (X86FuelPrefix.fetches (spec.count (.copy instruction))).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      spec.represents following after ∧ spec.ready after ∧
      after.regs.get? .rip = some ((address origin.address.toInt (spec.bytes (.copy instruction)).length).signExtend 64) ∧
      ∀ prefixCount ≤ spec.count (.copy instruction), ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          X86StateFrame.Frame spec.registerWrites spec.byteWrites native observed := by
  obtain ⟨values, sourceEq, registersKnown⟩ := represented
  obtain ⟨flags, flagsKnown, quiet⟩ := prepared
  change origin.address.toInt + (((X86CopyBlock.emit instruction).length + 3 : Nat) : Int) < (2 ^ 47 : Int) at upper
  change codeLoaded native origin.address.toInt (X86CopyBlock.emit instruction) at loaded
  let one : X86CopyBlock.Program := .call instruction fun _ => .ret ()
  let stop : Int := origin.address.toInt + (X86CopyBlock.emit instruction).length
  let input : X86CopyBlock.At stop one source native := {
    origin := origin
    placed := by simp only [one, X86CopyBlock.code, List.append_nil]; dsimp only [stop]; omega
    upper := by dsimp only [stop]; omega
    values := values
    source := sourceEq
    registers := registersKnown
    loaded := by simpa only [one, X86CopyBlock.code, List.append_nil] using loaded
    quiet := quiet }
  have oneSafe : one.Safe X86CopyBlock.action source := ⟨safe, by intros; trivial⟩
  have oneRun : one.Runs X86CopyBlock.action source () following := ⟨(), following, step, rfl, rfl⟩
  obtain ⟨after, executed, framed, outputValues, encoded, outputRegisters, pointer⟩ :=
    (X86CopyBlock.counted_boundary stop).realizes one source following native () oneSafe ⟨input⟩ oneRun
  change (X86FuelPrefix.fetches (X86CopyBlock.steps one)).run native = .ok () after at executed
  have outputFrame : X86StateFrame.Frame spec.registerWrites spec.byteWrites native after :=
    framed.mono Finset.subset_union_left (Finset.Subset.refl _)
  refine ⟨after, ?_, outputFrame, ⟨outputValues, encoded, outputRegisters⟩,
    ⟨flags, (framed.registers .rflags (by decide)).trans flagsKnown,
      (framed.registers .log_register_writes (by decide)).trans quiet⟩, ?_, ?_⟩
  · simpa only [one, X86CopyBlock.steps, spec, count, Nat.add_zero] using executed
  · exact pointer
  · intro prefixCount within observed observedRun
    have oldWithin : prefixCount ≤ X86CopyBlock.steps one := by
      simpa only [one, X86CopyBlock.steps, spec, count, Nat.add_zero] using within
    exact (X86CopyBlock.prefix_frame stop one source native observed input prefixCount oldWithin observedRun).mono
      Finset.subset_union_left (Finset.Subset.refl _)

theorem prefix_from_three [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (before first second after : State) (writes : Finset Register)
    (one : Step before first) (two : Step first second) (three : Step second after)
    (firstFrame : RegisterFrame writes before first) (secondFrame : RegisterFrame writes before second)
    (lastFrame : RegisterFrame writes before after)
    (count : Nat) (within : count ≤ 3) (observed : State)
    (run : (X86FuelPrefix.fetches count).run before = .ok () observed) :
    RegisterFrame writes before observed := by
  have known : ∃ proved, (X86FuelPrefix.fetches count).run before = .ok () proved ∧ RegisterFrame writes before proved := by
    interval_cases count
    · exact ⟨before, X86FuelPrefix.fetches_zero before, RegisterFrame.refl _ _⟩
    · exact ⟨first, X86FuelPrefix.fetches_one before first one, firstFrame⟩
    · exact ⟨second, X86FuelPrefix.fetches_then 1 1 before first second
        (X86FuelPrefix.fetches_one before first one) (X86FuelPrefix.fetches_one first second two), secondFrame⟩
    · exact ⟨after, X86FuelPrefix.fetches_cons 2 before first after one
        (X86FuelPrefix.fetches_cons 1 first second after two (X86FuelPrefix.fetches_one second after three)), lastFrame⟩
  obtain ⟨proved, executed, framed⟩ := known
  have same := X86FuelPrefix.fetches_deterministic count before proved observed executed run
  subst observed
  exact framed

theorem binary_clobbers (destination : Fin 12) (unlocked : destination ≠ 0) :
    X86BinBlock.clobbers destination ⊆ registers := by
  intro register member
  simp only [X86BinBlock.clobbers, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Finset.mem_union_right _ (by decide)
  · exact Finset.mem_union_left _ (X86CopyBlock.destination_written ⟨0,destination,unlocked⟩)
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))

theorem binary_execute (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0)
    (source following : World) (native : State) (origin : X86LegacyFetch.Basis native)
    (step : (spec.action (.binary operation destination left right unlocked)).Step source () following)
    (represented : spec.represents source native) (prepared : spec.ready native)
    (upper : origin.address.toInt + (((spec.bytes (.binary operation destination left right unlocked)).length + 3 : Nat) : Int) < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (spec.bytes (.binary operation destination left right unlocked))) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      spec.represents following after ∧ spec.ready after ∧
      after.regs.get? .rip = some ((address origin.address.toInt (spec.bytes (.binary operation destination left right unlocked)).length).signExtend 64) ∧
      ∀ prefixCount ≤ 3, ∀ observed, (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
        X86StateFrame.Frame spec.registerWrites spec.byteWrites native observed := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨values, sourceEq, registersKnown⟩ := represented
  obtain ⟨flags, flagsKnown, quiet⟩ := prepared
  change codeLoaded native origin.address.toInt (binaryBytes operation destination left right) at loaded
  rw [binaryBytes_exact] at loaded
  have byteLength : (spec.bytes (.binary operation destination left right unlocked)).length = 9 := by
    change (binaryBytes operation destination left right).length = 9
    rw [binaryBytes_exact]
    rfl
  rw [byteLength] at upper
  have bounded : origin.address.toInt + 9 < (2 ^ 47 : Int) := by omega
  obtain ⟨output, first, second, one, two, three, firstFrame, secondFrame, lastFrame⟩ :=
    X86BinBlock.expected_trace other vector (X86BinCapture.decodeOperation operation.val) destination left right
      native origin bounded loaded (values left) (values right) flags
      (registersKnown left (Finset.mem_univ _)) (registersKnown right (Finset.mem_univ _)) flagsKnown quiet
  let after := X86BinBlock.finished native origin.address.toInt (X86BinCapture.decodeOperation operation.val)
    destination (values left) (values right) flags output
  obtain ⟨invocation, enabled, endpoint⟩ := step
  rw [sourceEq] at enabled endpoint
  have sourceAfter := (X86BinBlock.source_reflected (X86BinCapture.decodeOperation operation.val)
    Finset.univ values left right destination invocation enabled).2
  have followingEq : following = Cells.encode Finset.univ (Function.update values destination
      (X86Arithmetic.result (X86BinCapture.decodeOperation operation.val) (values left) (values right))) :=
    endpoint.symm.trans sourceAfter
  refine ⟨after, X86FuelPrefix.fetches_cons 2 native first after one
      (X86FuelPrefix.fetches_cons 1 first second after two (X86FuelPrefix.fetches_one second after three)),
    X86StateFrame.registerOnly (lastFrame.mono (binary_clobbers destination unlocked)),
    ⟨_, followingEq, X86BinBlock.finished_represents _ _ _ registersKnown _ _ _ _ _ _ _⟩,
    ⟨_, X86BinBlock.finished_flags _ _ _ _ _ _ _ _,
      ((lastFrame.mono (X86BinBlock.clobbers_data destination)).registers .log_register_writes
        (by decide : .log_register_writes ∉ dataRegisters)).trans quiet⟩,
    ?_, ?_⟩
  · rw [byteLength]
    exact X86BinBlock.copied_rip _ _ _ _
  · intro prefixCount within observed observedRun
    exact X86StateFrame.registerOnly ((prefix_from_three native first second after _ one two three firstFrame
      secondFrame lastFrame prefixCount within observed observedRun).mono (binary_clobbers destination unlocked))

theorem correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  refine { dataOnly := data_only, execute := ?_ }
  intro instruction source following native origin safe step represented prepared upper loaded _
  cases instruction with
  | copy instruction => exact copy_execute instruction source following native origin safe step represented prepared upper loaded
  | binary operation destination left right unlocked =>
      exact binary_execute other vector operation destination left right unlocked source following native origin
        step represented prepared upper loaded

theorem source_step_iff (instruction : Instruction) (values : Fin 12 → Word) (following : World) :
    (action instruction).Step (Cells.encode Finset.univ values) () following ↔
      ∃ result, (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) = some result ∧
        following = Cells.encode Finset.univ (Function.update values (effect instruction).destination result) := by
  constructor
  · rintro ⟨invocation, enabled, endpoint⟩
    obtain ⟨computed, resource⟩ := Cells.scalar_update_reflected (effect instruction) invocation Finset.univ values enabled
    exact ⟨invocation.result, computed, endpoint.symm.trans resource⟩
  · rintro ⟨result, computed, endpoint⟩
    obtain ⟨invocation, enabled, resource⟩ := Cells.scalar_update_realized (effect instruction) Finset.univ values result
      (Finset.subset_univ _) computed
    exact ⟨invocation, enabled, resource.trans endpoint.symm⟩

def p1 : Instruction → P1Source.Instr
  | .copy instruction => .move .u64 instruction.destination instruction.source
  | .binary operation destination left right _ =>
      .binary (X86ResourceBinary.binary (X86BinCapture.decodeOperation operation.val)) .u64 destination left right

theorem source_evaluate_p1 (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) := by
  cases instruction with
  | copy instruction => rfl
  | binary operation destination left right unlocked => fin_cases operation <;> rfl

theorem p1_iff (instruction : Instruction) (values : Fin 12 → Word) (following : World) :
    (action instruction).Step (Cells.encode Finset.univ values) () following ↔
      (CellEffects.profile [P1Scalar.recipe (p1 instruction) (effect instruction).destination]).theory.rewrites
        (Cells.encode Finset.univ values) following := by
  rw [source_step_iff, P1Scalar.rewrite_iff, source_evaluate_p1]
  simp only [Finset.subset_univ, true_and]

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word) (result : Word)
    (computed : (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) = some result)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values (effect instruction).destination result))) :
    (Prog.prim instruction).wp action post (Cells.encode Finset.univ values) := by
  apply (wp_prim action instruction post _).mpr
  obtain ⟨invocation, enabled, _⟩ := Cells.scalar_update_realized (effect instruction) Finset.univ values result
    (Finset.subset_univ _) computed
  refine ⟨⟨invocation, enabled⟩, ?_⟩
  rintro ⟨⟩ following step
  obtain ⟨actual, actualComputed, endpoint⟩ := (source_step_iff instruction values following).mp step
  have same : actual = result := Option.some.inj (actualComputed.symm.trans computed)
  simpa only [endpoint, same] using expected

theorem prefix_preserves (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : X86BlockCompiler.Program Instruction) (source : World) (native after : State)
    (input : X86BlockCompiler.At spec stop program source native) (safe : program.Safe action source)
    (prefixCount : Nat) (within : prefixCount ≤ X86BlockCompiler.steps spec program) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches prefixCount).run native = .ok () after →
      lookup after 4 = lookup native 4 ∧ lookup after 7 = lookup native 7 ∧
        ∀ address, after.mem.get? address = native.mem.get? address := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro run
  have framed := X86BlockCompiler.prefix_frame spec (correct other vector) progress stop program source native after
    input safe prefixCount within run
  exact ⟨framed.lookup 4 stack_readonly, framed.lookup 7 frame_readonly,
    fun address => framed.memory address (by simp [spec])⟩

namespace Controls

private def move : Instruction := .copy ⟨1,2,by decide⟩
private def add : Instruction := .binary 0 2 2 1 (by decide)
private def sub : Instruction := .binary 1 3 2 1 (by decide)
private def selfCopy : Instruction := .copy ⟨3,3,by decide⟩
private def program : Prog Instruction (fun _ => Unit) Unit :=
  Prog.bind (Prog.prim move) fun _ =>
    Prog.bind (Prog.prim add) fun _ =>
      Prog.bind (Prog.prim sub) fun _ => Prog.prim selfCopy

private def value : Word := 0xffffffffffffffff#64
private def values (register : Fin 12) : Word :=
  if register = 0 then (8192#64) else if register = 1 then value else 0
private def moved : Fin 12 → Word := Function.update values 2 value
private def added : Fin 12 → Word := Function.update moved 2 (value + value)
private def subtracted : Fin 12 → Word := Function.update added 3 ((value + value) - value)
private def finalValues : Fin 12 → Word := Function.update subtracted 3 (subtracted 3)

private def raw : List Nat :=
  [0x48,0x89,0xf2,0x49,0x89,0xd6,0x49,0x01,0xf6,0x4c,0x89,0xf2,
    0x49,0x89,0xd6,0x49,0x29,0xf6,0x4c,0x89,0xf1]

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind, X86BlockCompiler.code_bind, X86BlockCompiler.code_bind,
    X86BlockCompiler.code_prim, X86BlockCompiler.code_prim, X86BlockCompiler.code_prim, X86BlockCompiler.code_prim]
  simp only [spec, bytes, move, add, sub, selfCopy]
  rw [X86CopyBlock.emit_distinct _ (by decide), binaryBytes_exact, binaryBytes_exact,
    X86CopyBlock.emit_self _ rfl]
  rfl

theorem compiled_steps : X86BlockCompiler.steps spec program = 7 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 21).map fun index => (4096 + index, BitVec.ofNat 8 ((raw[index]?).getD 0))

private noncomputable def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values 0)
  let registers := registers.insert .rsi (values 1)
  let registers := registers.insert .rdx (values 2)
  let registers := registers.insert .rcx (values 3)
  let registers := registers.insert .r8 (values 4)
  let registers := registers.insert .r9 (values 5)
  let registers := registers.insert .r10 (values 6)
  let registers := registers.insert .r11 (values 7)
  let registers := registers.insert .rax (values 8)
  let registers := registers.insert .rbx (values 9)
  let registers := registers.insert .r12 (values 10)
  let registers := registers.insert .r13 (values 11)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private def origin : X86LegacyFetch.Basis before where
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

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private theorem cell (address : Nat) (byte : BitVec 8) (present : (address, byte) ∈ cells) :
    before.mem.get? address = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private def input : X86BlockCompiler.At spec 4117 program (Cells.encode Finset.univ values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := by
    refine ⟨values, rfl, ?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup, placed, Registers.canonical, Registers.Placement.resolve, Registers.logicalSlot,
        key, before, Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x246#32, by simp [before, Std.ExtDHashMap.get?_insert], by simp [before]⟩
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 21 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  outside := by intros; simp [spec]

private theorem source_wp : program.wp action
    (fun _ world => world = Cells.encode Finset.univ finalValues) (Cells.encode Finset.univ values) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step move values value rfl
  rw [wp_bind]
  apply source_wp_step add moved (value + value) rfl
  rw [wp_bind]
  apply source_wp_step sub added ((value + value) - value) rfl
  exact source_wp_step selfCopy subtracted (subtracted 3) rfl _ rfl

theorem mixed_wraparound (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 7).run state = .ok () after ∧
      lookup after (X86CopyBlock.physical 3) = some value ∧ after.regs.get? .rip = some (4117#64) ∧
      lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following, after, _, expected, run, framed, ⟨outputValues, encoded, outputRegisters⟩, _, pointer⟩ :=
    X86BlockCompiler.compile_wp spec (correct other vector) progress 4117 program _ before input _ source_wp
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues finalValues).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 3 (Finset.mem_univ _)
  rw [equalValues.2 3 (Finset.mem_univ _)] at read
  have result : finalValues 3 = value := by decide
  rw [result] at read
  refine ⟨before, after, ?_, read, pointer, framed.lookup 4 stack_readonly, framed.lookup 7 frame_readonly,
    fun address => framed.memory address (by simp [spec])⟩
  simpa only [compiled_steps] using run

theorem wrong_result_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after (X86CopyBlock.physical 3) = some (0#64) →
      (X86FuelPrefix.fetches 7).run state ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state, proved, run, valueRead, _⟩ := mixed_wraparound other vector
  refine ⟨state, ?_⟩
  intro after wrong observed
  have same := X86FuelPrefix.fetches_deterministic 7 state proved after run observed
  rw [same, wrong] at valueRead
  contradiction

theorem changed_byte_rejected :
    let changed : State := { before with mem := before.mem.insert 4103 (0x29#8) }
    ¬ Nonempty (X86BlockCompiler.At spec 4117 program (Cells.encode Finset.univ values) changed) := by
  let changed : State := { before with mem := before.mem.insert 4103 (0x29#8) }
  change ¬ Nonempty (X86BlockCompiler.At spec 4117 program (Cells.encode Finset.univ values) changed)
  rintro ⟨candidate⟩
  have place : candidate.origin.address.toInt = 4096 := by
    have placed := candidate.placed
    rw [compiled_bytes] at placed
    simpa [raw] using placed
  have read := candidate.loaded 7 0x01 (by rw [compiled_bytes]; rfl)
  rw [place] at read
  change changed.mem.get? 4103 = some (0x01#8) at read
  have actual : changed.mem.get? 4103 = some (0x29#8) := Std.ExtHashMap.getElem?_insert_self
  rw [actual] at read
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86WordLibrary
