import Mettapedia.Machines.TIsa.X86P1ScalarLibrary
import Mettapedia.Machines.TIsa.X86P1ScalarReadiness

/-! Current p1 aliasing cases and typed normalization in one compiled block. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86P1ScalarLibrary.Controls
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

private def distinct : Instruction := .inl ⟨⟨.add,3,1,2,by decide⟩,.u32z,by decide⟩
private def scratch : Instruction := .inl ⟨⟨.sub,1,3,1,by decide⟩,.i32s,by decide⟩
private def inplace : Instruction := .inl ⟨⟨.add,1,1,3,by decide⟩,.u64,by decide⟩
private def commute : Instruction := .inl ⟨⟨.add,3,1,3,by decide⟩,.u64,by decide⟩
private def shift : Instruction := .inr (.inr (.inl ⟨.rightSigned,4,1,63,by decide⟩))

private def program : Program :=
  Prog.bind (Prog.prim distinct) fun _ =>
    Prog.bind (Prog.prim scratch) fun _ =>
      Prog.bind (Prog.prim inplace) fun _ =>
        Prog.bind (Prog.prim commute) fun _ => Prog.prim shift

private def raw : List Nat :=
  [0x48,0x89,0xf1,0x48,0x01,0xd1,0x89,0xc9,
   0x49,0x89,0xce,0x49,0x29,0xf6,0x4c,0x89,0xf6,0x48,0x63,0xf6,
   0x48,0x01,0xce,0x48,0x01,0xf1,
   0x49,0x89,0xf0,0x49,0xc1,0xf8,0x3f]

private theorem distinct_bytes : spec.bytes distinct = [0x48,0x89,0xf1,0x48,0x01,0xd1,0x89,0xc9] := by rfl
private theorem scratch_bytes : spec.bytes scratch =
    [0x49,0x89,0xce,0x49,0x29,0xf6,0x4c,0x89,0xf6,0x48,0x63,0xf6] := by rfl
private theorem inplace_bytes : spec.bytes inplace = [0x48,0x01,0xce] := by rfl
private theorem commute_bytes : spec.bytes commute = [0x48,0x01,0xf1] := by rfl
private theorem shift_bytes : spec.bytes shift = [0x49,0x89,0xf0,0x49,0xc1,0xf8,0x3f] := by rfl

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,
    X86BlockCompiler.code_prim,X86BlockCompiler.code_prim,X86BlockCompiler.code_prim,
    X86BlockCompiler.code_prim,X86BlockCompiler.code_prim,distinct_bytes,scratch_bytes,inplace_bytes,commute_bytes,shift_bytes]
  rfl

theorem compiled_steps : X86BlockCompiler.steps spec program = 11 := rfl

theorem frame_destination_refused :
    (lower? (.binary .add .u64 0 1 2)).isNone = true := by decide

theorem boolean_arithmetic_refused :
    (lower? (.binary .sub .boolean 1 2 3)).isNone = true := by decide

theorem pointer_arithmetic_refused :
    (lower? (.binary .add .pointer 1 2 3)).isNone = true := by decide

theorem oversized_shift_refused :
    (lower? (.shift .rightSigned .u64 1 2 64)).isNone = true := by decide

private def values (choice : Bool) (register : Fin 12) : Word :=
  if register = 0 then 8192 else if register = 1 then (if choice then 1 else 0)
  else if register = 2 then (if choice then 0xffffffff else 1) else 0
private def sumValue (choice : Bool) : Word := if choice then 0 else 1
private def signedValue (choice : Bool) : Word := if choice then 0xffffffffffffffff else 1
private def addedValue (choice : Bool) : Word := if choice then 0xffffffffffffffff else 2
private def commuteValue (choice : Bool) : Word := if choice then 0xffffffffffffffff else 3
private def shiftValue (choice : Bool) : Word := if choice then 0xffffffffffffffff else 0
private def afterDistinct (choice : Bool) := Function.update (values choice) 3 (sumValue choice)
private def afterScratch (choice : Bool) := Function.update (afterDistinct choice) 1 (signedValue choice)
private def afterInplace (choice : Bool) := Function.update (afterScratch choice) 1 (addedValue choice)
private def afterCommute (choice : Bool) := Function.update (afterInplace choice) 3 (commuteValue choice)
private def finalValues (choice : Bool) := Function.update (afterCommute choice) 4 (shiftValue choice)

private theorem source_wp (choice : Bool) : program.wp spec.action
    (fun _ world => world = Cells.encode Finset.univ (finalValues choice))
    (Cells.encode Finset.univ (values choice)) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step distinct (values choice) (sumValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step scratch (afterDistinct choice) (signedValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step inplace (afterScratch choice) (addedValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step commute (afterInplace choice) (commuteValue choice) (by cases choice <;> decide)
  exact source_wp_step shift (afterCommute choice) (shiftValue choice) (by cases choice <;> decide) _ rfl

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def cells : List (Nat × BitVec 8) :=
  (List.range 33).map (fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0)))

private def profile : X86Readiness.Profile where
  controls := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
  visible := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)
  ac := 1#1

private def before (choice : Bool) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .ctrs profile.controls
  let registers := registers.insert .seg_visibles profile.visible
  let registers := registers.insert .rsp (12288#64)
  let registers := registers.insert .rdi (values choice 0)
  let registers := registers.insert .rsi (values choice 1)
  let registers := registers.insert .rdx (values choice 2)
  let registers := registers.insert .rcx (values choice 3)
  let registers := registers.insert .r8 (values choice 4)
  let registers := registers.insert .r9 (values choice 5)
  let registers := registers.insert .r10 (values choice 6)
  let registers := registers.insert .r11 (values choice 7)
  let registers := registers.insert .rax (values choice 8)
  let registers := registers.insert .rbx (values choice 9)
  let registers := registers.insert .r12 (values choice 10)
  let registers := registers.insert .r13 (values choice 11)
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private theorem cell (choice : Bool) (position : Nat) (byte : BitVec 8) (present : (position,byte) ∈ cells) :
    (before choice).mem.get? position = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def input (choice : Bool) : X86BlockCompiler.At spec 4129 program
    (Cells.encode Finset.univ (values choice)) (before choice) where
  origin := {
    address := 4096#48
    opcodeAddress := 4097#48
    modrmAddress := 4098#48
    next := 4099#48
    control := control
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
    rip := by simp [before,Std.ExtDHashMap.get?_insert] }
  placed := by rw [compiled_bytes];rfl
  upper := by decide
  represented := ⟨values choice,rfl,by
    intro register _
    fin_cases register <;> cases choice <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,before,values,Std.ExtDHashMap.get?_insert] <;> rfl⟩
  ready := ⟨0x40246#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before,Std.ExtDHashMap.get?_insert]⟩
  loaded := by
    rw [compiled_bytes]
    change codeLoaded (before choice) 4096 raw
    intro index byte present
    have within : index < 33 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell choice <;> decide
  outside := by
    intros
    simp [spec,X86LibrarySum.combine,X86P1ArithmeticLibrary.spec,X86TypedScalarLibrary.spec,
      X86ScalarLibrary.spec,X86ShiftLibrary.spec,X86WordLibrary.spec,X86LogicalLibrary.spec]

theorem compiled_aliasing_program (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 11).run (before choice) = .ok () after ∧
      lookup after (X86CopyBlock.physical 1) = some (addedValue choice) ∧
      lookup after (X86CopyBlock.physical 3) = some (commuteValue choice) ∧
      lookup after (X86CopyBlock.physical 4) = some (shiftValue choice) ∧
      after.regs.get? .rip = some (4129#64) ∧
      lookup after 4 = lookup (before choice) 4 ∧ lookup after 7 = lookup (before choice) 7 ∧
      ∀ position, after.mem.get? position = (before choice).mem.get? position := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,after,_,expected,run,frame,⟨⟨outputValues,encoded,outputRegisters⟩,_,rip⟩⟩ :=
    compile_wp other extra vector 4129 program _ (before choice) (input choice) _ (source_wp choice)
  have sameValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues (finalValues choice)).mp
    (le_of_eq (encoded.symm.trans expected))
  have observed (register : Fin 12) : lookup after (X86CopyBlock.physical register) =
      some (finalValues choice register) := by
    have read := outputRegisters register (Finset.mem_univ _)
    rw [sameValues.2 register (Finset.mem_univ _)] at read
    exact read
  refine ⟨after,?_,?_,?_,?_,rip,frame.lookup 4 stack_readonly,frame.lookup 7 frame_readonly,?_⟩
  · simpa only [compiled_steps] using run
  · simpa [finalValues,afterCommute,afterInplace] using observed 1
  · simpa [finalValues,afterCommute] using observed 3
  · simpa [finalValues] using observed 4
  · intro position
    exact frame.memory position (by simp [spec,X86LibrarySum.combine,X86P1ArithmeticLibrary.spec,
      X86TypedScalarLibrary.spec,X86ScalarLibrary.spec,X86ShiftLibrary.spec,
      X86WordLibrary.spec,X86LogicalLibrary.spec])

private theorem profile_before (choice : Bool) : profile.Holds (before choice) := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · decide

theorem alignment_enabled_at_entry (choice : Bool) :
    (Functions.alignment_checking_enabled_p ()).run (before choice) = .ok true (before choice) := by
  have observed := profile.alignment_exact (before choice) (profile_before choice)
  simpa only [show profile.enabled = true from by decide] using observed

theorem compiled_aliasing_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 11).run (before choice) = .ok () after ∧
      lookup after (X86CopyBlock.physical 1) = some (addedValue choice) ∧
      lookup after (X86CopyBlock.physical 3) = some (commuteValue choice) ∧
      lookup after (X86CopyBlock.physical 4) = some (shiftValue choice) ∧
      profile.Holds after ∧ after.regs.get? .rip = some (4129#64) := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := X86Readiness.strengthen_at spec profile.Holds 4129 program _ (before choice)
    (input choice) (profile_before choice)
  obtain ⟨following,after,_sourceRun,expected,run,_frame,observed⟩ :=
    X86P1ScalarReadiness.compile_wp other extra vector profile 4129 program _ (before choice)
      prepared _ (source_wp choice)
  obtain ⟨⟨outputValues,encoded,outputRegisters⟩,⟨_ready,holds⟩,rip⟩ := observed
  have sameValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues (finalValues choice)).mp
    (le_of_eq (encoded.symm.trans expected))
  have read (register : Fin 12) : lookup after (X86CopyBlock.physical register) =
      some (finalValues choice register) := by
    rw [← sameValues.2 register (Finset.mem_univ _)]
    exact outputRegisters register (Finset.mem_univ _)
  refine ⟨after,?_,?_,?_,?_,holds,rip⟩
  · simpa only [compiled_steps] using run
  · simpa [finalValues,afterCommute,afterInplace] using read 1
  · simpa [finalValues,afterCommute] using read 3
  · simpa [finalValues] using read 4

theorem cleared_ac_rejected (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ native, ∀ after, (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches 11).run native ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,_one,_three,_four,holds,_rip⟩ := compiled_aliasing_profile other extra vector choice
  obtain ⟨_controls,_visible,flags,known,ac⟩ := holds
  have retained : (proved.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
    rw [known]
    simpa only [Option.map_some,profile] using congrArg some ac
  refine ⟨before choice,?_⟩
  intro after cleared executed
  have same := X86FuelPrefix.fetches_deterministic 11 (before choice) proved after run executed
  rw [same,cleared] at retained
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some (1#1)) retained

#print axioms compiled_bytes
#print axioms compiled_steps
#print axioms source_wp
#print axioms compiled_aliasing_program
#print axioms alignment_enabled_at_entry
#print axioms compiled_aliasing_profile
#print axioms cleared_ac_rejected
end Mettapedia.Machines.TIsa.X86P1ScalarLibrary.Controls
