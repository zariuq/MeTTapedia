import Mettapedia.Machines.TIsa.X86LibrarySum
import Mettapedia.Machines.TIsa.X86LogicalLibrary
import Mettapedia.Machines.TIsa.X86Conditional

/-!
# Mixed arithmetic and logical native components

The captured MOV/ADD/SUB library and the U64 OR/AND/XOR library share their
source representation and readiness. Their actual local certificates combine
through X86LibrarySum, so mixed programs reuse the common source/WP compiler.
Each source effect agrees with the corresponding p1 U64 operation.

The same interface reuses the conditional compiler, with exact path counts,
byte layout and every-prefix frames. Constructive controls copy, mask and add
high-bit words, then run that mixed block or a copy fallback through a Boolean
gate. Wrong results, changed opcodes and a non-Boolean condition have separate
controls. Nested control, bounded-loop integration, other widths and the
public ABI remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86ScalarLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := Sum X86WordLibrary.Instruction X86LogicalLibrary.Instruction
abbrev World := X86WordLibrary.World
abbrev Program := X86BlockCompiler.Program Instruction

noncomputable def spec : X86BlockCompiler.Spec Instruction World :=
  X86LibrarySum.combine X86WordLibrary.spec X86LogicalLibrary.spec

def effect : Instruction → Cells.Action (Fin 12)
  | .inl instruction => X86WordLibrary.effect instruction
  | .inr instruction => X86LogicalLibrary.effect instruction

def p1 : Instruction → P1Source.Instr
  | .inl instruction => X86WordLibrary.p1 instruction
  | .inr instruction => X86LogicalLibrary.p1 instruction

theorem source_evaluate_p1 (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) := by
  cases instruction with
  | inl instruction => exact X86WordLibrary.source_evaluate_p1 instruction values
  | inr instruction => exact X86LogicalLibrary.source_evaluate_p1 instruction values

theorem progress (instruction : Instruction) : (spec.action instruction).Progress :=
  X86LibrarySum.progress X86WordLibrary.spec X86LogicalLibrary.spec X86WordLibrary.progress X86LogicalLibrary.progress instruction

theorem correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86LibrarySum.correct X86WordLibrary.spec X86LogicalLibrary.spec
    (X86WordLibrary.correct other vector) (X86LogicalLibrary.correct other vector) rfl rfl

theorem stack_readonly : Register.rsp ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86WordLibrary.stack_readonly left
  · exact X86LogicalLibrary.stack_readonly right

theorem frame_readonly : Register.rdi ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86WordLibrary.frame_readonly left
  · exact X86LogicalLibrary.frame_readonly right

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word) (result : Word)
    (computed : (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) = some result)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values (effect instruction).destination result))) :
    (Prog.prim instruction).wp spec.action post (Cells.encode Finset.univ values) := by
  cases instruction with
  | inl instruction => exact X86WordLibrary.source_wp_step instruction values result computed post expected
  | inr instruction =>
    have actual := X86LogicalLibrary.source_computes instruction values
    have same := Option.some.inj (actual.symm.trans computed)
    apply X86LogicalLibrary.source_wp_step instruction values post
    rw [same]
    exact expected

theorem compile_wp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (source : World) (native : State)
    (input : X86BlockCompiler.At spec stop program source native)
    (post : Unit → World → Prop) (wp : program.wp spec.action post source) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other vector) progress stop program source native input post wp

def compatible (condition : Fin 12) : X86Conditional.Compatible spec where
  condition := (X86Conditional.wordCompatible condition).condition
  value := (X86Conditional.wordCompatible condition).value
  read := (X86Conditional.wordCompatible condition).read
  prepared := (X86Conditional.wordCompatible condition).prepared
  stable := (X86Conditional.wordCompatible condition).stable

theorem conditional_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (condition : Fin 12) (yes no : Program) (source : World) (native : State)
    (input : X86Conditional.At spec (compatible condition) yes no source native)
    (choice : Bool) (chosen : RegisterProfile.truth ((compatible condition).value source) = some choice)
    (post : Unit → World → Prop) (wp : (if choice then yes else no).wp spec.action post source) :
    letI : OtherOpcodeHandlers := X86Conditional.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after,
      (if choice then yes else no).Runs spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (2 + X86BlockCompiler.steps spec (if choice then yes else no) +
        (if choice then 1 else 0))).run native = .ok () after ∧
      X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec (input.layout.address.toInt +
        (X86Conditional.code (compatible condition).condition (X86BlockCompiler.code spec yes)
          (X86BlockCompiler.code spec no)).length) () following after ∧
      ∀ count ≤ 2 + X86BlockCompiler.steps spec (if choice then yes else no) + (if choice then 1 else 0),
        ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
          X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native observed := by
  let : OtherOpcodeHandlers := X86Conditional.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86Conditional.compile_wp other extra vector spec (compatible condition)
    (correct (X86Conditional.handlers other extra) vector) progress yes no source native input choice chosen post wp

namespace Controls
private def copy : Instruction := .inl (.copy ⟨1,2,by decide⟩)
private def mask : Instruction := .inr ⟨.and,3,2,by decide⟩
private def add : Instruction := .inl (.binary 0 4 2 3 (by decide))
private def program : Program := Prog.bind (Prog.prim copy) fun _ =>
  Prog.bind (Prog.prim mask) fun _ => Prog.prim add
private def value : Word := 0x80000001000000ff#64
private def maskWord : Word := 0xffffffff000000f0#64
private def values (register : Fin 12) : Word :=
  if register = 1 then value else if register = 3 then maskWord else 0
private def copied : Fin 12 → Word := Function.update values 2 value
private def masked : Fin 12 → Word := Function.update copied 2 (value &&& maskWord)
private def finalValues : Fin 12 → Word := Function.update masked 4 ((value &&& maskWord) + maskWord)
private def raw : List Nat :=
  [0x48,0x89,0xf2,0x48,0x21,0xca,0x49,0x89,0xd6,0x49,0x01,0xce,0x4d,0x89,0xf0]

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,X86BlockCompiler.code_prim,
    X86BlockCompiler.code_prim,X86BlockCompiler.code_prim]
  simp only [spec,X86LibrarySum.combine,copy,mask,add,Sum.elim_inl,Sum.elim_inr,
    X86WordLibrary.spec,X86LogicalLibrary.spec,X86WordLibrary.bytes]
  rw [X86CopyBlock.emit_distinct _ (by decide),X86WordLibrary.binaryBytes_exact]
  rfl

theorem compiled_steps : X86BlockCompiler.steps spec program = 5 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 15).map fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0))
private def before : State :=
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

private def input : X86BlockCompiler.At spec 4111 program (Cells.encode Finset.univ values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := by
    refine ⟨values,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x246#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before]⟩
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 15 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  outside := by intros; simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec]

private theorem source_wp : program.wp spec.action
    (fun _ world => world = Cells.encode Finset.univ finalValues) (Cells.encode Finset.univ values) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step copy values value rfl
  rw [wp_bind]
  apply source_wp_step mask copied (value &&& maskWord) rfl
  exact source_wp_step add masked ((value &&& maskWord) + maskWord) rfl _ rfl

theorem copy_mask_add (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      lookup after (X86CopyBlock.physical 4) = some (0x80000000000001e0#64) ∧
      after.regs.get? .rip = some (4111#64) ∧
      lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,after,_,expected,run,frame,⟨outputValues,encoded,outputRegisters⟩,_,rip⟩ :=
    compile_wp other vector 4111 program _ before input _ source_wp
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues finalValues).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 4 (Finset.mem_univ _)
  rw [equalValues.2 4 (Finset.mem_univ _)] at read
  have expectedWord : finalValues 4 = (0x80000000000001e0#64) := by decide
  rw [expectedWord] at read
  refine ⟨before,after,run,read,rip,frame.lookup 4 stack_readonly,frame.lookup 7 frame_readonly,?_⟩
  intro address
  exact frame.memory address (by simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec])

theorem wrong_result_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after (X86CopyBlock.physical 4) = some (0#64) →
      (X86FuelPrefix.fetches 5).run state ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state,proved,run,value,_⟩ := copy_mask_add other vector
  refine ⟨state,?_⟩
  intro after wrong observed
  have same := X86FuelPrefix.fetches_deterministic 5 state proved after run observed
  rw [same,wrong] at value
  contradiction

theorem changed_opcode_rejected :
    let changed : State := {before with mem := before.mem.insert 4100 (0x09#8)}
    ¬Nonempty (X86BlockCompiler.At spec 4111 program (Cells.encode Finset.univ values) changed) := by
  let changed : State := {before with mem := before.mem.insert 4100 (0x09#8)}
  change ¬Nonempty (X86BlockCompiler.At spec 4111 program (Cells.encode Finset.univ values) changed)
  rintro ⟨candidate⟩
  have placement : candidate.origin.address.toInt = 4096 := by
    have place := candidate.placed
    rw [compiled_bytes] at place
    exact place
  have expected := candidate.loaded 4 0x21 (by rw [compiled_bytes]; rfl)
  rw [placement] at expected
  change changed.mem.get? 4100 = some (0x21#8) at expected
  have actual : changed.mem.get? 4100 = some (0x09#8) := Std.ExtHashMap.getElem?_insert_self
  rw [actual] at expected
  contradiction

private def fallback : Program := Prog.prim (.inl (.copy ⟨1,4,by decide⟩))
private def branchValues (choice : Bool) (register : Fin 12) : Word :=
  if register = 7 then booleanWord choice else values register
private def branchFinal (choice : Bool) : Fin 12 → Word :=
  if choice then
    Function.update (Function.update (Function.update (branchValues choice) 2 value) 2 (value &&& maskWord))
      4 ((value &&& maskWord) + maskWord)
  else Function.update (branchValues choice) 4 value
private def branchRaw : List Nat :=
  [0x4d,0x85,0xdb,0x0f,0x84,20,0,0,0] ++ raw ++ [0xe9,3,0,0,0,0x49,0x89,0xf0]

theorem branch_compiled_bytes : X86Conditional.code (compatible 7).condition
    (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback) = branchRaw := by
  rw [compiled_bytes]
  have fallbackBytes : X86BlockCompiler.code spec fallback = [0x49,0x89,0xf0] := by
    rw [fallback,X86BlockCompiler.code_prim]
    change X86CopyBlock.emit ⟨1,4,by decide⟩ = _
    rw [X86CopyBlock.emit_distinct _ (by decide)]
    rfl
  rw [fallbackBytes]
  rfl

private def branchCells : List (Nat × BitVec 8) :=
  (List.range 32).map fun index => (4096 + index,BitVec.ofNat 8 ((branchRaw[index]?).getD 0))
private def branchBefore (choice : Bool) : State :=
  {before with regs := before.regs.insert .r11 (booleanWord choice),mem := Std.ExtHashMap.ofList branchCells}

private def branchOrigin (choice : Bool) : X86LegacyFetch.Basis (branchBefore choice) where
  address := origin.address
  opcodeAddress := origin.opcodeAddress
  modrmAddress := origin.modrmAddress
  next := origin.next
  control := origin.control
  attributes := origin.attributes
  step1 := origin.step1
  step2 := origin.step2
  step3 := origin.step3
  status := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.status
  fault := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.fault
  msrs := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.msrs
  segments := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.segments
  longMode := origin.longMode
  codeMode := origin.codeMode
  application := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.application
  rip := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.rip

private theorem branchCell (choice : Bool) (address : Nat) (byte : BitVec 8)
    (present : (address,byte) ∈ branchCells) : (branchBefore choice).mem.get? address = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def branchInput (choice : Bool) : X86Conditional.At spec (compatible 7) program fallback
    (Cells.encode Finset.univ (branchValues choice)) (branchBefore choice) where
  origin := branchOrigin choice
  yesFits := by rw [compiled_bytes]; decide
  noFits := by change (X86CopyBlock.emit ⟨1,4,by decide⟩).length < 2 ^ 31; rw [X86CopyBlock.emit_distinct _ (by decide)]; decide
  upper := by
    rw [branch_compiled_bytes]
    change (4096 : Int) + (branchRaw.length + 3 : Nat) < 2 ^ 47
    decide
  loaded := by
    rw [branch_compiled_bytes]
    change codeLoaded (branchBefore choice) 4096 branchRaw
    intro index byte present
    have within : index < 32 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [branchRaw,raw,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply branchCell <;> decide
  represented := by
    refine ⟨branchValues choice,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,branchBefore,before,branchValues,Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x246#32,by simp [branchBefore,before,Std.ExtDHashMap.get?_insert],
    by simp [branchBefore,before,Std.ExtDHashMap.get?_insert]⟩
  outside := by intros; simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec]

private theorem branch_source_wp (choice : Bool) : (if choice then program else fallback).wp spec.action
    (fun _ world => world = Cells.encode Finset.univ (branchFinal choice))
    (Cells.encode Finset.univ (branchValues choice)) := by
  cases choice with
  | false =>
    change (Prog.prim (.inl (.copy ⟨1,4,by decide⟩))).wp spec.action _ _
    exact source_wp_step _ (branchValues false) value rfl _ rfl
  | true =>
    change program.wp spec.action _ _
    unfold program
    rw [wp_bind]
    apply source_wp_step copy (branchValues true) value rfl
    rw [wp_bind]
    apply source_wp_step mask (Function.update (branchValues true) 2 value) (value &&& maskWord) rfl
    exact source_wp_step add _ ((value &&& maskWord) + maskWord) rfl _ rfl

theorem branch_copy_mask_add (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86Conditional.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches (if choice then 8 else 3)).run state = .ok () after ∧
      lookup after (X86CopyBlock.physical 4) = some (if choice then (0x80000000000001e0#64) else value) ∧
      after.regs.get? .rip = some (4128#64) ∧
      lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  let : OtherOpcodeHandlers := X86Conditional.handlers other extra
  let : VectorOpcodeHandlers := vector
  have chosen : RegisterProfile.truth ((compatible 7).value (Cells.encode Finset.univ (branchValues choice))) = some choice := by
    change RegisterProfile.truth (X86Conditional.wordValue 7 (Cells.encode Finset.univ (branchValues choice))) = some choice
    rw [X86Conditional.wordValue_encode]
    cases choice <;> rfl
  obtain ⟨following,after,_,expected,run,frame,⟨⟨outputValues,encoded,outputRegisters⟩,_,rip⟩,_⟩ :=
    conditional_wp other extra vector 7 program fallback _ (branchBefore choice) (branchInput choice) choice chosen _ (branch_source_wp choice)
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues (branchFinal choice)).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 4 (Finset.mem_univ _)
  rw [equalValues.2 4 (Finset.mem_univ _)] at read
  have expectedWord : branchFinal choice 4 = (if choice then (0x80000000000001e0#64) else value) := by
    cases choice <;> decide
  rw [expectedWord] at read
  refine ⟨branchBefore choice,after,?_,read,?_,?_,?_,?_⟩
  · cases choice <;> exact run
  · have length : (X86Conditional.code (compatible 7).condition
        (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback)).length = 32 := by
      rw [branch_compiled_bytes]; rfl
    have start : (branchInput choice).layout.address.toInt = 4096 := rfl
    rw [length,start] at rip
    exact rip
  · apply frame.lookup 4
    intro member
    rcases Finset.mem_union.mp member with library | gate
    · exact stack_readonly library
    · exact (by decide : key 4 ∉ X86BranchGate.writes) gate
  · apply frame.lookup 7
    intro member
    rcases Finset.mem_union.mp member with library | gate
    · exact frame_readonly library
    · exact (by decide : key 7 ∉ X86BranchGate.writes) gate
  · intro address
    exact frame.memory address (by simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec])

theorem nonboolean_condition_refused :
    RegisterProfile.truth ((compatible 7).value (Cells.encode Finset.univ
      (Function.update (branchValues false) 7 (2#64)))) = none := by
  change RegisterProfile.truth (X86Conditional.wordValue 7 (Cells.encode Finset.univ _)) = none
  rw [X86Conditional.wordValue_encode]
  rfl
end Controls

#print axioms correct
#print axioms compile_wp
#print axioms source_evaluate_p1
#print axioms conditional_wp
#print axioms Controls.copy_mask_add
#print axioms Controls.wrong_result_refused
#print axioms Controls.changed_opcode_rejected
#print axioms Controls.branch_copy_mask_add
#print axioms Controls.nonboolean_condition_refused
end Mettapedia.Machines.TIsa.X86ScalarLibrary
