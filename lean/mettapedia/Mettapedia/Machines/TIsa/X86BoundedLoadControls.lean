import Mettapedia.Machines.TIsa.X86BoundedLoadSites

/-! A bounds refusal with absent destination and absent data memory. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedLoad.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

private def instruction : Instruction := ⟨true,6,1,0,⟨0,by decide⟩,256,by decide,by decide,by decide⟩
private def modeControl : Vector (BitVec 64) 7 := Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0
private def cells : List (Nat × BitVec 8) :=
  (List.range (bytes instruction).length).map (fun index =>
    (4096 + index,BitVec.ofNat 8 (((bytes instruction)[index]?).getD 0))) ++
  (List.range 16).map (fun index => (8192 + index,if index < 8 then (12288#64).extractLsb' (8 * index) 8 else 0))

private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (512#32)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi (12288#64)
  let registers := registers.insert .rsp (16384#64)
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private theorem cell (position : Nat) (byte : BitVec 8) (present : (position,byte) ∈ cells) :
    before.mem.get? position = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

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

private def input : Inputs instruction before origin where
  frame := 8192#64
  base := 12288#64
  pointer := 12288#64
  length := 0#64
  baseAddress := 8192#48
  lengthAddress := 8200#48
  controls := controls
  visible := visible
  flags := 512#32
  frameKnown := by simp [lookup,key,before,Std.ExtDHashMap.get?_insert];rfl
  pointerKnown := by
    change lookup before 6 = some (12288#64)
    simp [lookup,key,before,Std.ExtDHashMap.get?_insert]
    rfl
  baseEffective := by decide
  lengthEffective := by decide
  baseUpper := by decide
  lengthUpper := by decide
  baseAligned := by decide
  lengthAligned := by decide
  controlKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before,Std.ExtDHashMap.get?_insert]
  baseBytes := by intro index within;interval_cases index <;> apply cell <;> decide
  lengthBytes := by intro index within;interval_cases index <;> apply cell <;> decide
  geometry := {
    extent := 512
    upper := by decide
    codeWithin := by decide
    rejectWithin := by decide
    overflowDelta := by decide
    shortDelta := by decide
    rangeDelta := by decide }
  tailWithin := by decide
  loaded := by
    change codeLoaded before 4096 (bytes instruction)
    intro index byte present
    have within : index < 43 := by have := (List.getElem?_eq_some_iff.mp present).1;exact this
    have coordinates : ∀ index : Fin 43, ((address 4096 index.val).signExtend 52).toNat = 4096 + index.val := by decide
    rw [coordinates ⟨index,within⟩]
    apply cell
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨index,List.mem_range.mpr (by exact within),?_⟩
    rw [present]
    rfl

theorem destination_and_data_absent : lookup before 10 = none ∧ before.mem.get? 12288 = none := by
  constructor
  · simp [lookup,key,before,Std.ExtDHashMap.get?_insert]
  · exact Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (by decide)

theorem rejects_before_data_read (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
      after.regs.get? .rip = some (4352#64) ∧ lookup after 10 = none ∧
      after.mem.get? 12288 = none ∧ lookup after 4 = lookup before 4 ∧
      (∀ address, after.mem.get? address = before.mem.get? address) ∧
      ∀ prefixCount ≤ 5, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run before = .ok () observed → RegisterFrame X86Bounds.writes before observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,rip,_control,prefixes⟩ := rejects other extra vector instruction before origin input (by decide)
  refine ⟨after,run,?_,?_,?_,frame.lookup 4 (by decide),(fun _ => by rw [frame.memory]),prefixes⟩
  · exact rip
  · rw [frame.lookup 10 (by decide)]
    exact destination_and_data_absent.1
  · rw [frame.memory]
    exact destination_and_data_absent.2

#print axioms rejects_before_data_read
end Mettapedia.Machines.TIsa.X86BoundedLoad.Controls
