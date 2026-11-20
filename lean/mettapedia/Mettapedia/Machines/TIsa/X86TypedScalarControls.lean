import Mettapedia.Machines.TIsa.X86TypedScalarLibrary

/-! A compiled mixed-width bit-classification block and its concrete frame controls. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86TypedScalarLibrary.Controls
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

private def signedShift : Instruction := .inr (.inr ⟨.rightSigned,true,2,1,31,by decide⟩)
private def narrowShift : Instruction := .inr (.inr ⟨.left,false,5,2,1,by decide⟩)
private def wideShift : Instruction := .inr (.inl ⟨.rightUnsigned,3,5,31,by decide⟩)
private def sub : Instruction := .inl (.inl (.binary 1 4 3 4 (by decide)))
private def bor : Instruction := .inl (.inr ⟨.or,3,4,by decide⟩)

private def program : Program :=
  Prog.bind (Prog.prim signedShift) fun _ =>
    Prog.bind (Prog.prim narrowShift) fun _ =>
      Prog.bind (Prog.prim wideShift) fun _ =>
        Prog.bind (Prog.prim sub) fun _ => Prog.prim bor

private def raw : List Nat :=
  [0x48,0x89,0xf2,0xc1,0xfa,0x1f,0x48,0x63,0xd2,
   0x49,0x89,0xd1,0x41,0xc1,0xe1,0x01,0x45,0x89,0xc9,
   0x4c,0x89,0xc9,0x48,0xc1,0xe9,0x1f,
   0x49,0x89,0xce,0x4d,0x29,0xc6,0x4d,0x89,0xf0,
   0x49,0x09,0xc8]

private theorem signed_bytes : spec.bytes signedShift =
    [0x48,0x89,0xf2,0xc1,0xfa,0x1f,0x48,0x63,0xd2] := by rfl
private theorem narrow_bytes : spec.bytes narrowShift =
    [0x49,0x89,0xd1,0x41,0xc1,0xe1,0x01,0x45,0x89,0xc9] := by rfl
private theorem wide_bytes : spec.bytes wideShift =
    [0x4c,0x89,0xc9,0x48,0xc1,0xe9,0x1f] := by rfl
private theorem sub_bytes : spec.bytes sub =
    [0x49,0x89,0xce,0x4d,0x29,0xc6,0x4d,0x89,0xf0] := by
  dsimp only [spec,X86LibrarySum.combine,X86ScalarLibrary.spec,X86WordLibrary.spec,sub,Sum.elim,X86WordLibrary.bytes]
  rw [X86WordLibrary.binaryBytes_exact]
  rfl
private theorem or_bytes : spec.bytes bor = [0x49,0x09,0xc8] := by rfl

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,
    X86BlockCompiler.code_bind,X86BlockCompiler.code_prim,X86BlockCompiler.code_prim,
    X86BlockCompiler.code_prim,X86BlockCompiler.code_prim,X86BlockCompiler.code_prim]
  rw [signed_bytes,narrow_bytes,wide_bytes,sub_bytes,or_bytes]
  rfl

theorem compiled_steps : X86BlockCompiler.steps spec program = 12 := rfl

private def values (choice : Bool) (register : Fin 12) : Word :=
  if register = 0 then (8192#64) else if register = 1 then
    (if choice then (0xdeadbeef80000000#64) else (0xffffffff7fffffff#64))
  else if register = 4 then (0xfffffffffffffffe#64) else 0
private def signedValue (choice : Bool) : Word := if choice then (0xffffffffffffffff#64) else 0
private def narrowValue (choice : Bool) : Word := if choice then (0xfffffffe#64) else 0
private def bitValue (choice : Bool) : Word := if choice then 1 else 0
private def subValue (choice : Bool) : Word := if choice then 3 else 2
private def maskValue (choice : Bool) : Word := if choice then 3 else 2
private def afterSigned (choice : Bool) := Function.update (values choice) 2 (signedValue choice)
private def afterNarrow (choice : Bool) := Function.update (afterSigned choice) 5 (narrowValue choice)
private def afterWide (choice : Bool) := Function.update (afterNarrow choice) 3 (bitValue choice)
private def afterSub (choice : Bool) := Function.update (afterWide choice) 4 (subValue choice)
private def finalValues (choice : Bool) := Function.update (afterSub choice) 4 (maskValue choice)

private theorem source_wp (choice : Bool) : program.wp spec.action
    (fun _ world => world = Cells.encode Finset.univ (finalValues choice))
    (Cells.encode Finset.univ (values choice)) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step signedShift (values choice) (signedValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step narrowShift (afterSigned choice) (narrowValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step wideShift (afterNarrow choice) (bitValue choice) (by cases choice <;> decide)
  rw [wp_bind]
  apply source_wp_step sub (afterWide choice) (subValue choice) (by cases choice <;> decide)
  exact source_wp_step bor (afterSub choice) (maskValue choice) (by cases choice <;> decide) _ rfl

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def cells : List (Nat × BitVec 8) :=
  (List.range 38).map (fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0)))

private def before (choice : Bool) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (512#32)
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

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private theorem cell (choice : Bool) (position : Nat) (byte : BitVec 8) (present : (position,byte) ∈ cells) :
    (before choice).mem.get? position = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private def input (choice : Bool) : X86BlockCompiler.At spec 4134 program
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
  placed := by rw [compiled_bytes]; rfl
  upper := by decide
  represented := ⟨values choice,rfl,by
    intro register member
    fin_cases register <;> cases choice <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,before,values,Std.ExtDHashMap.get?_insert] <;> rfl⟩
  ready := ⟨512#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before,Std.ExtDHashMap.get?_insert]⟩
  loaded := by
    rw [compiled_bytes]
    change codeLoaded (before choice) 4096 raw
    intro index byte present
    have within : index < 38 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell choice <;> decide
  outside := by
    intros
    simp [spec,X86LibrarySum.combine,X86ScalarLibrary.spec,X86ShiftLibrary.spec,
      X86WordLibrary.spec,X86LogicalLibrary.spec]

theorem compiled_bit_mask (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 12).run (before choice) = .ok () after ∧
      lookup after (X86CopyBlock.physical 2) = some (signedValue choice) ∧
      lookup after (X86CopyBlock.physical 5) = some (narrowValue choice) ∧
      lookup after (X86CopyBlock.physical 4) = some (maskValue choice) ∧
      after.regs.get? .rip = some (4134#64) ∧
      lookup after 4 = lookup (before choice) 4 ∧ lookup after 7 = lookup (before choice) 7 ∧
      ∀ address, after.mem.get? address = (before choice).mem.get? address := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,after,_,expected,run,frame,⟨⟨outputValues,encoded,outputRegisters⟩,_,rip⟩⟩ :=
    compile_wp other extra vector 4134 program _ (before choice) (input choice) _ (source_wp choice)
  have sameValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues (finalValues choice)).mp
    (le_of_eq (encoded.symm.trans expected))
  have observed (register : Fin 12) : lookup after (X86CopyBlock.physical register) =
      some (finalValues choice register) := by
    have read := outputRegisters register (Finset.mem_univ _)
    rw [sameValues.2 register (Finset.mem_univ _)] at read
    exact read
  refine ⟨after,?_,?_,?_,?_,rip,frame.lookup 4 stack_readonly,frame.lookup 7 frame_readonly,?_⟩
  · simpa only [compiled_steps] using run
  · simpa [finalValues,afterSub,afterWide,afterNarrow,afterSigned] using observed 2
  · simpa [finalValues,afterSub,afterWide,afterNarrow,afterSigned] using observed 5
  · simpa [finalValues] using observed 4
  · intro address
    exact frame.memory address (by simp [spec,X86LibrarySum.combine,X86ScalarLibrary.spec,
      X86ShiftLibrary.spec,X86WordLibrary.spec,X86LogicalLibrary.spec])

theorem wrong_signed_carrier_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 12).run (before true) = .ok () after →
      lookup after (X86CopyBlock.physical 2) ≠ some (0xffffffff#64) := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨correct,run,signed,_⟩ := compiled_bit_mask other extra vector true
  intro candidate
  have same := X86FuelPrefix.fetches_deterministic 12 _ correct after run candidate
  subst after
  rw [signed]
  decide

theorem high64_is_not_bit31 (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 12).run (before false) = .ok () after →
      lookup after (X86CopyBlock.physical 4) ≠ some (3#64) := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨correct,run,_,_,mask,_⟩ := compiled_bit_mask other extra vector false
  intro candidate
  have same := X86FuelPrefix.fetches_deterministic 12 _ correct after run candidate
  subst after
  rw [mask]
  decide

#print axioms wrong_signed_carrier_refused
#print axioms high64_is_not_bit31
#print axioms compiled_bytes
#print axioms compiled_steps
#print axioms source_wp
#print axioms compiled_bit_mask
end Mettapedia.Machines.TIsa.X86TypedScalarLibrary.Controls
