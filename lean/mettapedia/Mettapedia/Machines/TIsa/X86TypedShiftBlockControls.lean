import Mettapedia.Machines.TIsa.X86TypedShiftBlock

/-! A signed typed shift initializes an absent destination and preserves its frame. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86TypedShiftBlock.Controls
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

private def instruction : Instruction := ⟨.rightSigned,true,2,1,31,by decide⟩
private def raw : List Nat := [0x48,0x89,0xf2,0xc1,0xfa,0x1f,0x48,0x63,0xd2]
private def values (value : Word) (register : Fin 12) : Word := if register = 1 then value else 0

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map (fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0)))

private def before (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (512#32)
  let registers := registers.insert .rsp (12288#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi value
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin (value : Word) : X86LegacyFetch.Basis (before value) where
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
  rip := by simp [before,Std.ExtDHashMap.get?_insert]

private theorem cell (value : Word) (position : Nat) (byte : BitVec 8) (present : (position,byte) ∈ cells) :
    (before value).mem.get? position = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private theorem loaded (value : Word) : codeLoaded (before value) 4096 raw := by
  intro index byte present
  have within : index < 9 := (List.getElem?_eq_some_iff.mp present).1
  interval_cases index <;>
    simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
    subst byte <;> apply cell value <;> decide

theorem bytes_exact : bytes instruction = raw := by rfl
theorem destination_absent (value : Word) : lookup (before value) (physical 2) = none := by
  simp [physical,X86WordPrimitive.physical,X86BinCapture.physical,lookup,placed,Registers.canonical,
    Registers.Placement.resolve,Registers.logicalSlot,key,before,Std.ExtDHashMap.get?_insert]

theorem initializes_destination (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before value) = .ok () after ∧
      lookup after (physical 2) = some (extend32 true ((low32 value).sshiftRight 31)) ∧
      after.regs.get? .rip = some (4105#64) ∧
      lookup after 4 = lookup (before value) 4 ∧ lookup after 7 = lookup (before value) 7 ∧
      (∀ position, after.mem.get? position = (before value).mem.get? position) ∧
      ∀ prefixCount ≤ 3, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run (before value) = .ok () observed →
          RegisterFrame (writes instruction) (before value) observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have known : lookup (before value) (physical 1) = some value := by
    change ((before value).regs.get? .rsi).map (fun x : Word => x) = some value
    simp [before]
  obtain ⟨after,_,run,frame,result,rip,_,_,_,prefixes⟩ := executes_block other extra vector instruction
    (values value) (before value) (origin value) known (512#32)
    (by simp [before,Std.ExtDHashMap.get?_insert]) (by simp [before,Std.ExtDHashMap.get?_insert])
    (by change (4096 : Int) + 9 < (2 ^ 47 : Int); decide)
    (by rw [bytes_exact];exact loaded value)
  refine ⟨after,run,result,rip,frame.lookup 4 (by decide),frame.lookup 7 (by decide),?_,prefixes⟩
  intro position
  rw [frame.memory]

theorem wrong_carrier_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 3).run (before (0xdeadbeef80000000#64)) = .ok () after →
      lookup after (physical 2) ≠ some (0xffffffff#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨correct,run,result,_⟩ := initializes_destination other extra vector (0xdeadbeef80000000#64)
  intro candidate
  have same := X86FuelPrefix.fetches_deterministic 3 _ correct after run candidate
  subst after
  rw [result]
  decide

theorem count32_refused : lower? (.shift .rightSigned .i32s 2 1 32) = none := by decide
theorem frame_destination_refused : lower? (.shift .left .u32z 0 1 1) = none := by decide

#print axioms destination_absent
#print axioms initializes_destination
#print axioms wrong_carrier_refused
#print axioms count32_refused
#print axioms frame_destination_refused
end Mettapedia.Machines.TIsa.X86TypedShiftBlock.Controls
