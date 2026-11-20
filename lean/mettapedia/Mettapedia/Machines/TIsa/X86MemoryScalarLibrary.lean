import Mettapedia.Machines.TIsa.X86MemoryView
import Mettapedia.Machines.TIsa.X86Readiness

/-!
# Existing scalar native certificates over the memory-cell source carrier

Scalar actions are genuine firings over the existing register/byte/capability
cells. Their evaluation agrees with p1 and projects to the original scalar
source step. The local native certificate reuses the proved fetched scalar
library and derives preservation of every nonregister readback from its frame.

The established block compiler then gives source/WP refinement for arbitrary
finite scalar sequences, with unchanged bytes/counts and the actual control,
segment and AC profile. No additional instruction model or runtime is used.

The twelve-byte control performs aliased wrapping ADD followed by XOR in four
fetches beside actual descriptor words and data bytes. Controls reject wrong
native results, changed or missing descriptors, a noncanonical byte alias and
changed code. Native memory operations, writable-view aliasing, ABI, actual
admission/hosting and complete emitter/frontend refinement remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryScalarLibrary

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView

local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := X86ScalarLibrary.Instruction

def effect (instruction : Instruction) : Cells.Action Key where
  scalar := (X86ScalarLibrary.effect instruction).scalar
  inputs := (X86ScalarLibrary.effect instruction).inputs.map Memory.Key.register
  destination := .register (X86ScalarLibrary.effect instruction).destination

def action (instruction : Instruction) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : Cells.Invocation (effect instruction), Cells.system.Enables world invocation
  Step world _ following := ∃ invocation : Cells.Invocation (effect instruction),
    Cells.system.Enables world invocation ∧ Cells.system.fire world invocation = following

theorem evaluate_p1 (instruction : Instruction) (values : Key → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      P1Scalar.evaluate (X86ScalarLibrary.p1 instruction)
        ((X86ScalarLibrary.p1 instruction).reads.map (fun register => values (.register register))) := by
  simp only [effect, List.map_map, Function.comp_def]
  exact X86ScalarLibrary.source_evaluate_p1 instruction (fun register => values (.register register))

theorem support_included (instruction : Instruction) (keys : Finset Key)
    (registers : ∀ register, Memory.Key.register register ∈ keys) : (effect instruction).support ⊆ keys := by
  intro key member
  simp only [Cells.Action.support, effect, Finset.mem_insert, List.mem_toFinset, List.mem_map] at member
  rcases member with rfl | ⟨register, _, rfl⟩
  · exact registers _
  · exact registers _

theorem step_iff (instruction : Instruction) (keys : Finset Key) (values : Key → Word)
    (registers : ∀ register, Memory.Key.register register ∈ keys) (following : World) :
    (action instruction).Step (Cells.encode keys values) () following ↔
      ∃ result,
        P1Scalar.evaluate (X86ScalarLibrary.p1 instruction)
          ((X86ScalarLibrary.p1 instruction).reads.map (fun register => values (.register register))) = some result ∧
        following = Cells.encode keys
          (Function.update values (.register (X86ScalarLibrary.effect instruction).destination) result) := by
  constructor
  · rintro ⟨invocation, enabled, fired⟩
    obtain ⟨computed, updated⟩ := Cells.scalar_update_reflected (effect instruction) invocation keys values enabled
    rw [evaluate_p1] at computed
    exact ⟨invocation.result, computed, fired.symm.trans updated⟩
  · rintro ⟨result, computed, rfl⟩
    rw [← evaluate_p1] at computed
    obtain ⟨invocation, enabled, fired⟩ := Cells.scalar_update_realized (effect instruction) keys values result
      (support_included instruction keys registers) computed
    exact ⟨invocation, enabled, fired⟩

theorem readonly_readback (instruction : Instruction) (keys : Finset Key) (values : Key → Word)
    (registers : ∀ register, Memory.Key.register register ∈ keys) (following : World)
    (step : (action instruction).Step (Cells.encode keys values) () following)
    (key : Key) (readonly : ∀ register, key ≠ Memory.Key.register register) (value : Word) :
    Cells.Cell.mk key value ∈ following ↔ key ∈ keys ∧ values key = value := by
  obtain ⟨result, _computed, rfl⟩ := (step_iff instruction keys values registers following).mp step
  simp only [Cells.mem_encode, Function.update_of_ne (readonly _)]

theorem original_step_iff (instruction : Instruction) (before following : X86ScalarLibrary.World) :
    (X86ScalarLibrary.spec.action instruction).Step before () following ↔
      ∃ invocation : Cells.Invocation (X86ScalarLibrary.effect instruction),
        Cells.system.Enables before invocation ∧ Cells.system.fire before invocation = following := by
  cases instruction <;> rfl

theorem projects_original (instruction : Instruction) (keys : Finset Key) (values : Key → Word)
    (registers : ∀ register, Memory.Key.register register ∈ keys) (following : World)
    (step : (action instruction).Step (Cells.encode keys values) () following) :
    ∃ result,
      (X86ScalarLibrary.spec.action instruction).Step
        (Cells.encode Finset.univ (fun register => values (.register register))) ()
        (Cells.encode Finset.univ (Function.update (fun register => values (.register register))
          (X86ScalarLibrary.effect instruction).destination result)) ∧
      following = Cells.encode keys
        (Function.update values (.register (X86ScalarLibrary.effect instruction).destination) result) := by
  obtain ⟨result, computed, updated⟩ := (step_iff instruction keys values registers following).mp step
  rw [← X86ScalarLibrary.source_evaluate_p1] at computed
  obtain ⟨invocation, enabled, fired⟩ := Cells.scalar_update_realized (X86ScalarLibrary.effect instruction)
    Finset.univ (fun register => values (.register register)) result (Finset.subset_univ _) computed
  exact ⟨result, (original_step_iff instruction _ _).mpr ⟨invocation, enabled, fired⟩, updated⟩

theorem scalar_bytes_readonly : X86ScalarLibrary.spec.byteWrites = ∅ := by
  change (∅ : Finset Nat) ∪ ∅ = ∅
  exact Finset.union_self _

theorem readback_framed (modes : Fin 9 → Word) (before after : State)
    (frame : X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites before after)
    (key : Key) (readonly : ∀ register, key ≠ Memory.Key.register register) :
    readback modes after key = readback modes before key := by
  have sameMemory : memory after = memory before := by
    funext address
    exact frame.memory address (by rw [scalar_bytes_readonly]; simp)
  exact readback_nonregister modes before after sameMemory
    (frame.lookup 7 X86ScalarLibrary.frame_readonly) key readonly

noncomputable def spec (view : View) (profile : X86Readiness.Profile) :
    X86BlockCompiler.Spec Instruction World where
  action := action
  represents := represents view
  ready := (X86Readiness.strengthen X86ScalarLibrary.spec profile.Holds).ready
  bytes := X86ScalarLibrary.spec.bytes
  count := X86ScalarLibrary.spec.count
  registerWrites := X86ScalarLibrary.spec.registerWrites
  byteWrites := X86ScalarLibrary.spec.byteWrites

theorem original_safe_iff (instruction : Instruction) (before : X86ScalarLibrary.World) :
    (X86ScalarLibrary.spec.action instruction).Safe before ↔
      ∃ invocation : Cells.Invocation (X86ScalarLibrary.effect instruction), Cells.system.Enables before invocation := by
  cases instruction <;> rfl

theorem register_update (values : Key → Word) (destination register : Fin 12) (result : Word) :
    Function.update values (.register destination) result (.register register) =
      Function.update (fun name => values (.register name)) destination result register := by
  simp only [Function.update_apply, Memory.Key.register.injEq]

theorem correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (profile : X86Readiness.Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct (spec view profile) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have original := X86Readiness.scalar_correct other vector profile
  refine ⟨original.dataOnly, ?_⟩
  intro instruction source following native origin _safe step represented ready upper loaded outside
  obtain ⟨values, rfl, known⟩ := represented
  obtain ⟨result, sourceStep, followingEq⟩ := projects_original instruction view.keys values view.registers following step
  have sourceSafe := (original_safe_iff instruction _).mpr
    (let ⟨invocation, enabled, _⟩ := (original_step_iff instruction _ _).mp sourceStep; ⟨invocation, enabled⟩)
  have originalRepresented : X86ScalarLibrary.spec.represents
      (Cells.encode Finset.univ (fun register => values (.register register))) native := by
    refine ⟨_, rfl, ?_⟩
    intro register _member
    exact known (.register register) (view.registers register)
  obtain ⟨after, run, frame, representedAfter, readyAfter, rip, prefixes⟩ :=
    original.execute instruction _ _ native origin sourceSafe sourceStep originalRepresented ready upper loaded outside
  obtain ⟨afterValues, encoded, registersAfter⟩ := representedAfter
  have afterValuesEq (register : Fin 12) :
      afterValues register = Function.update (fun name => values (.register name))
        (X86ScalarLibrary.effect instruction).destination result register := by
    exact ((Cells.encode_le_iff Finset.univ Finset.univ afterValues _).mp (le_of_eq encoded.symm)).2
      register (Finset.mem_univ _)
  refine ⟨after, run, frame, ?_, readyAfter, rip, prefixes⟩
  refine ⟨Function.update values (.register (X86ScalarLibrary.effect instruction).destination) result, followingEq, ?_⟩
  intro key member
  by_cases mutable : ∃ register, key = Memory.Key.register register
  · obtain ⟨register, rfl⟩ := mutable
    change lookup after (X86CopyBlock.physical register) = _
    have read : lookup after (X86CopyBlock.physical register) = some (afterValues register) :=
      registersAfter register (Finset.mem_univ _)
    rw [read, afterValuesEq, register_update]
  · have readonly : ∀ register, key ≠ Memory.Key.register register := by
      intro register same
      exact mutable ⟨register, same⟩
    rw [readback_framed view.modes native after frame key readonly, known key member]
    rw [Function.update_of_ne (readonly _)]

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  rintro world ⟨invocation, enabled⟩
  exact ⟨(), Cells.system.fire world invocation, invocation, enabled, rfl⟩

theorem source_wp_step (view : View) (profile : X86Readiness.Profile) (instruction : Instruction)
    (values : Key → Word) (result : Word)
    (computed : P1Scalar.evaluate (X86ScalarLibrary.p1 instruction)
      ((X86ScalarLibrary.p1 instruction).reads.map (fun register => values (.register register))) = some result)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode view.keys
      (Function.update values (.register (X86ScalarLibrary.effect instruction).destination) result))) :
    (Prog.prim instruction).wp (spec view profile).action post (Cells.encode view.keys values) := by
  apply (wp_prim (spec view profile).action instruction post _).mpr
  have computation := computed
  rw [← evaluate_p1] at computation
  obtain ⟨invocation, enabled, _⟩ := Cells.scalar_update_realized (effect instruction) view.keys values result
    (support_included instruction view.keys view.registers) computation
  refine ⟨⟨invocation, enabled⟩, ?_⟩
  rintro ⟨⟩ following step
  obtain ⟨actual, actualComputed, endpoint⟩ := (step_iff instruction view.keys values view.registers following).mp step
  have same : actual = result := Option.some.inj (actualComputed.symm.trans computed)
  simpa only [endpoint, same] using expected

theorem compile_wp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (profile : X86Readiness.Profile) (stop : Int)
    (program : X86BlockCompiler.Program Instruction) (source : World) (native : State)
    (input : X86BlockCompiler.At (spec view profile) stop program source native)
    (post : Unit → World → Prop) (wp : program.wp (spec view profile).action post source) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs (spec view profile).action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps (spec view profile) program)).run native = .ok () after ∧
      X86StateFrame.Frame (spec view profile).registerWrites (spec view profile).byteWrites native after ∧
      X86BlockCompiler.Observed (spec view profile) stop () following after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp (spec view profile) (correct other vector view profile)
    progress stop program source native input post wp

namespace Controls

private def double : Instruction := .inl (.binary 0 2 2 2 (by decide))
private def keys : Finset Key :=
  (Finset.univ.image Memory.Key.register) ∪
    {.byte 900, .capabilityBase 0, .capabilityLength 0, .capabilityMode 0}
private def values : Key → Word
  | .register _ => 7
  | .byte _ => 0xa5
  | .capabilityBase _ => 900
  | .capabilityLength _ => 8
  | .capabilityMode _ => 2

private theorem registers : ∀ register, Memory.Key.register register ∈ keys := by
  intro register
  simp [keys]

theorem double_with_bytes :
    ∃ following, (action double).Step (Cells.encode keys values) () following ∧
      Cells.Cell.mk (.register 2 : Key) 14 ∈ following ∧
      Cells.Cell.mk (.byte 900 : Key) 0xa5 ∈ following ∧
      Cells.Cell.mk (.capabilityBase 0 : Key) 900 ∈ following ∧
      Cells.Cell.mk (.capabilityLength 0 : Key) 8 ∈ following ∧
      Cells.Cell.mk (.capabilityMode 0 : Key) 2 ∈ following := by
  let following := Cells.encode keys (Function.update values (.register 2) 14)
  refine ⟨following, ?_, ?_⟩
  · exact (step_iff double keys values registers following).mpr ⟨14, by decide, rfl⟩
  · simp [following, Cells.mem_encode, keys, values]

theorem wrong_result_refused (following : World)
    (step : (action double).Step (Cells.encode keys values) () following) :
    Cells.Cell.mk (.register 2 : Key) 15 ∉ following := by
  obtain ⟨result, computed, updated⟩ := (step_iff double keys values registers following).mp step
  have expected : P1Scalar.evaluate (X86ScalarLibrary.p1 double)
      ((X86ScalarLibrary.p1 double).reads.map (fun register => values (.register register))) = some 14 := by decide
  have same : result = 14 := Option.some.inj (computed.symm.trans expected)
  subst result
  rw [updated]
  simp [Cells.mem_encode, double, X86ScalarLibrary.effect, X86WordLibrary.effect,
    X86BinBlock.sourceAction]

end Controls

namespace NativeControls

private def double : Instruction := .inl (.binary 0 2 2 2 (by decide))
private def toggle : Instruction := .inr ⟨.xor,2,3,by decide⟩
private def program : X86BlockCompiler.Program Instruction :=
  Prog.bind (Prog.prim double) fun _ => Prog.prim toggle

private def keys : Finset Key := (Finset.univ.image Memory.Key.register) ∪
  {.capabilityBase 0,.capabilityLength 0,.capabilityMode 0,
   .capabilityBase 255,.capabilityLength 255,.capabilityMode 255,
   .byte 36864,.byte 36865,.byte 36866,.byte 36867,.byte 36868,.byte 36869,.byte 36870,.byte 36871}

private def view : View where
  keys := keys
  registers := by intro register; simp [keys]
  modes := fun region => if region.val = 0 then 2 else 0

private def profile : X86Readiness.Profile where
  controls := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
  visible := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)
  ac := 1#1

private def dataWord : Word := 0xa5b6c7d8e9f00123#64
private def values : Key → Word
  | .register register => if register = 0 then 32768 else if register = 1 then 36864
      else if register = 2 then 0x8000000000000007 else if register = 3 then 0xf0 else 0
  | .byte address => (dataWord.extractLsb' (8 * (address - 36864)) 8).zeroExtend 64
  | .capabilityBase region => if region = 0 then 36864 else if region = 255 then 32768 else 0
  | .capabilityLength region => if region = 0 then 8 else if region = 255 then 192 else 0
  | .capabilityMode region => if region = 0 then 2 else if region = 255 then 1 else 0

private def doubled : Key → Word := Function.update values (.register 2) 14
private def finalValues : Key → Word := Function.update doubled (.register 3) 0xfe
private def raw : List Nat :=
  [0x49,0x89,0xd6,0x49,0x01,0xd6,0x4c,0x89,0xf2,0x48,0x31,0xd1]

theorem compiled_bytes : X86BlockCompiler.code (spec view profile) program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind,X86BlockCompiler.code_prim,X86BlockCompiler.code_prim]
  simp only [spec,X86ScalarLibrary.spec,X86LibrarySum.combine,double,toggle,
    X86WordLibrary.spec,X86LogicalLibrary.spec,Sum.elim_inl,Sum.elim_inr,X86WordLibrary.bytes]
  rw [X86WordLibrary.binaryBytes_exact]
  rfl

theorem compiled_steps : X86BlockCompiler.steps (spec view profile) program = 4 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def cells : List (Nat × BitVec 8) :=
  (List.range 12).map (fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0))) ++
  (List.range 8).map (fun index => (32768 + index,(36864#64).extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (32776 + index,(8#64).extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (36864 + index,dataWord.extractLsb' (8 * index) 8))

private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values (.register 0))
  let registers := registers.insert .rsi (values (.register 1))
  let registers := registers.insert .rdx (values (.register 2))
  let registers := registers.insert .rcx (values (.register 3))
  let registers := registers.insert .r8 (values (.register 4))
  let registers := registers.insert .r9 (values (.register 5))
  let registers := registers.insert .r10 (values (.register 6))
  let registers := registers.insert .r11 (values (.register 7))
  let registers := registers.insert .rax (values (.register 8))
  let registers := registers.insert .rbx (values (.register 9))
  let registers := registers.insert .r12 (values (.register 10))
  let registers := registers.insert .r13 (values (.register 11))
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs profile.controls
  let registers := registers.insert .seg_visibles profile.visible
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

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
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]

private theorem cell (address : Nat) (byte : BitVec 8) (present : (address,byte) ∈ cells) :
    before.mem.get? address = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private theorem frame_pointer : lookup before 7 = some (32768#64) := by
  simp [lookup,key,before,values,Std.ExtDHashMap.get?_insert]
  rfl

private theorem base_word : wordAt? (memory before) (32768#64) = some (36864#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  interval_cases offset <;> apply cell <;> decide

private theorem length_word : wordAt? (memory before) (32776#64) = some (8#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  interval_cases offset <;> apply cell <;> decide

private theorem data_byte (offset : Fin 8) : memory before (36864 + offset.val) =
    some (dataWord.extractLsb' (8 * offset.val) 8) := by
  apply cell
  fin_cases offset <;> decide

private theorem readback_known : ∀ key ∈ keys, readback view.modes before key = some (values key) := by
  intro key member
  rcases Finset.mem_union.mp member with register | other
  · obtain ⟨register, _member, rfl⟩ := Finset.mem_image.mp register
    fin_cases register <;>
      simp [readback,Registers.logicalSlot,
        lookup,placed,Registers.canonical,Registers.Placement.resolve,key,before,values,Std.ExtDHashMap.get?_insert] <;> rfl
  · simp only [Finset.mem_insert,Finset.mem_singleton] at other
    rcases other with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [readback,field?,frame_pointer,values] using base_word
    · simpa [readback,field?,frame_pointer,values] using length_word
    · rfl
    · simp [readback,frame_pointer,values]
    · rfl
    · rfl
    all_goals
      apply readback_byte_known _ _ _ _ (by decide) (by decide)
      first
      | exact data_byte 0
      | exact data_byte 1
      | exact data_byte 2
      | exact data_byte 3
      | exact data_byte 4
      | exact data_byte 5
      | exact data_byte 6
      | exact data_byte 7

private theorem profile_before : profile.Holds before := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · decide

private def input : X86BlockCompiler.At (spec view profile) 4108 program
    (Cells.encode view.keys values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := ⟨values,rfl,readback_known⟩
  ready := ⟨⟨0x40246#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before]⟩,profile_before⟩
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 12 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  outside := by intros; rw [show (spec view profile).byteWrites = ∅ from scalar_bytes_readonly]; simp

private theorem source_wp : program.wp (spec view profile).action
    (fun _ world => world = Cells.encode view.keys finalValues) (Cells.encode view.keys values) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step view profile double values 14 (by decide)
  exact source_wp_step view profile toggle doubled 0xfe (by decide) _ rfl

theorem native_block (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following machine,
      program.Runs (spec view profile).action (Cells.encode view.keys values) () following ∧
      following = Cells.encode view.keys finalValues ∧
      (X86FuelPrefix.fetches 4).run before = .ok () machine ∧
      readback view.modes machine (.register 2) = some 14 ∧
      readback view.modes machine (.register 3) = some 0xfe ∧
      readback view.modes machine (.capabilityBase 0) = some 36864 ∧
      readback view.modes machine (.capabilityLength 0) = some 8 ∧
      readback view.modes machine (.capabilityMode 0) = some 2 ∧
      (∀ address, machine.mem.get? address = before.mem.get? address) ∧
      profile.Holds machine ∧ machine.regs.get? .rip = some (4108#64) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,machine,source,endpoint,executed,frame,observed⟩ :=
    compile_wp other vector view profile 4108 program _ before input _ source_wp
  obtain ⟨afterValues,encoded,known⟩ := observed.1
  have same (key : Key) (member : key ∈ view.keys) : afterValues key = finalValues key :=
    ((Cells.encode_le_iff view.keys view.keys afterValues finalValues).mp
      (le_of_eq (encoded.symm.trans endpoint))).2 key member
  have read (key : Key) (member : key ∈ view.keys) :
      readback view.modes machine key = some (finalValues key) := (known key member).trans (congrArg some (same key member))
  refine ⟨following,machine,source,endpoint,?_,?_,?_,?_,?_,?_,?_,observed.2.1.2,observed.2.2⟩
  · simpa only [compiled_steps] using executed
  · simpa [finalValues,doubled] using read (.register 2) (view.registers 2)
  · simpa [finalValues] using read (.register 3) (view.registers 3)
  · simpa [finalValues,doubled,values] using read (.capabilityBase 0) (by decide)
  · simpa [finalValues,doubled,values] using read (.capabilityLength 0) (by decide)
  · simpa [finalValues,doubled,values] using read (.capabilityMode 0) (by decide)
  · intro address
    exact frame.memory address (by rw [show (spec view profile).byteWrites = ∅ from scalar_bytes_readonly]; simp)

theorem wrong_native_result_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ initial, ∀ reached, readback view.modes reached (.register 2) = some 15 →
      (X86FuelPrefix.fetches 4).run initial ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨_following,proved,_source,_endpoint,run,read,_rest⟩ := native_block other vector
  refine ⟨before, ?_⟩
  intro reached wrong observed
  have same := X86FuelPrefix.fetches_deterministic 4 before proved reached run observed
  rw [same,wrong] at read
  exact (by decide : (some (15#64) : Option Word) ≠ some 14) read

private def changedDescriptor : State := { before with mem := before.mem.insert 32768 (1#8) }

private theorem unchanged_descriptor_byte (address : Nat) (value : BitVec 8) (different : address ≠ 32768)
    (original : memory before address = some value) : memory changedDescriptor address = some value := by
  change memory { before with mem := before.mem.insert 32768 (1#8) } address = some value
  rw [memory_insert]
  simpa only [beq_iff_eq,if_neg different,if_neg (Ne.symm different)] using original

private theorem changed_word : wordAt? (memory changedDescriptor) (32768#64) = some (36865#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  interval_cases offset
  · change changedDescriptor.mem.get? 32768 = some (1#8)
    simp [changedDescriptor]
  all_goals
    apply unchanged_descriptor_byte _ _ (by decide)
    apply cell
    decide

private theorem changed_readback : readback view.modes changedDescriptor (.capabilityBase 0) = some 36865 := by
  have pointer : lookup changedDescriptor 7 = some (32768#64) :=
    (lookup_memory_update before (before.mem.insert 32768 (1#8)) 7).trans frame_pointer
  change (lookup changedDescriptor 7 >>= fun pointer =>
    wordAt? (memory changedDescriptor) (pointer + (0#64))) = some (36865#64)
  rw [pointer]
  change wordAt? (memory changedDescriptor) ((32768#64) + (0#64)) = some (36865#64)
  rw [BitVec.add_zero]
  exact changed_word

theorem changed_descriptor_refused : ¬represents view (Cells.encode view.keys values) changedDescriptor := by
  rintro ⟨assigned,encoded,known⟩
  have member : Memory.Key.capabilityBase 0 ∈ view.keys := by decide
  have assignedValue := ((Cells.encode_le_iff view.keys view.keys assigned values).mp (le_of_eq encoded.symm)).2
    (.capabilityBase 0) member
  have observed := known (.capabilityBase 0) member
  rw [changed_readback,assignedValue] at observed
  exact (by decide : (some (36865#64) : Option Word) ≠ some (values (.capabilityBase 0))) observed

private def missingDescriptor : State := { before with mem := before.mem.erase 32775 }

private theorem missing_word : wordAt? (memory missingDescriptor) (32768#64) = none := by
  apply wordAt?_missing _ _ ⟨7,by decide⟩
  change missingDescriptor.mem.get? 32775 = none
  simp [missingDescriptor]

theorem missing_descriptor_refused (world : World) : ¬represents view world missingDescriptor := by
  rintro ⟨assigned,_encoded,known⟩
  have member : Memory.Key.capabilityBase 0 ∈ view.keys := by decide
  have observed := known (.capabilityBase 0) member
  have pointer : lookup missingDescriptor 7 = some (32768#64) := frame_pointer
  have missing : readback view.modes missingDescriptor (.capabilityBase 0) = none := by
    simpa [readback,field?,pointer] using missing_word
  rw [missing] at observed
  contradiction

theorem noncanonical_alias_refused :
    readback view.modes before (.byte (2 ^ 48 + 36864)) = none ∧
    memory before (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (2 ^ 48 + 36864))) = some (0x23#8) := by
  constructor
  · rw [readback,if_neg (by decide)]
  · exact data_byte 0

private def changedOpcode : State := { before with mem := before.mem.insert 4100 (0x29#8) }

theorem changed_opcode_refused : ¬codeLoaded changedOpcode 4096 raw := by
  intro loaded
  have wrong := loaded 4 1 (by decide)
  change changedOpcode.mem.get? 4100 = some (1#8) at wrong
  simp [changedOpcode] at wrong

end NativeControls

#print axioms step_iff
#print axioms readonly_readback
#print axioms projects_original
#print axioms Controls.double_with_bytes
#print axioms Controls.wrong_result_refused
#print axioms correct
#print axioms compile_wp
#print axioms NativeControls.native_block
#print axioms NativeControls.wrong_native_result_refused
#print axioms NativeControls.changed_descriptor_refused
#print axioms NativeControls.missing_descriptor_refused
#print axioms NativeControls.noncanonical_alias_refused
#print axioms NativeControls.changed_opcode_refused

end Mettapedia.Machines.TIsa.X86MemoryScalarLibrary
