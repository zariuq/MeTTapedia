import Mettapedia.Machines.TIsa.X86BoundedStoreSites

/-! Unaligned checked writes, exact suffixes, and refusal without a payload. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedStore.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86StoreRepresentation
local instance : MemoryPrimitives := X86Memory.ordinary

private def instruction (wide : Bool) : Instruction := ⟨wide,6,1,0,⟨0,by decide⟩,256,by decide,by decide⟩
private def word : Word := 0x80000001800000ff
private def modeControl : Vector (BitVec 64) 7 := Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0
private def length (ready : Bool) : Word := if ready then 32 else 0

private def cells (wide ready : Bool) : List (Nat × BitVec 8) :=
  ((List.range (bytes (instruction wide)).length).map (fun index =>
    (4096 + index,BitVec.ofNat 8 (((bytes (instruction wide))[index]?).getD 0))) ++
    (List.range 16).map (fun index => (8192 + index,
      if index < 8 then (12288#64).extractLsb' (8 * index) 8 else (length ready).extractLsb' (8 * (index - 8)) 8))) ++
    (if ready then (List.range 32).map (fun index => (12288 + index,0xa5#8)) else [])

private def before (wide ready : Bool) : State :=
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
  let registers := registers.insert .rsi (12289#64)
  let registers := if ready then registers.insert .r10 word else registers
  let registers := registers.insert .rsp (16384#64)
  ⟨registers,(),Std.ExtHashMap.ofList (cells wide ready),(),0,#[]⟩

private theorem cell (wide ready : Bool) (position : Nat) (byte : BitVec 8)
    (present : (position,byte) ∈ cells wide ready) : (before wide ready).mem.get? position = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by cases wide <;> cases ready <;> decide) present

private def origin (wide ready : Bool) : X86LegacyFetch.Basis (before wide ready) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  fault := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  segments := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  rip := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]

private def input (wide ready : Bool) : Inputs (instruction wide) (before wide ready) (origin wide ready) where
  frame := 8192#64
  base := 12288#64
  pointer := 12289#64
  length := length ready
  baseAddress := 8192#48
  lengthAddress := 8200#48
  controls := controls
  visible := visible
  flags := 512#32
  frameKnown := by cases ready <;> simp [lookup,key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  pointerKnown := by
    change lookup (before wide ready) 6 = some (12289#64)
    cases ready <;> simp [lookup,key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  baseEffective := by cases wide <;> decide
  lengthEffective := by cases wide <;> decide
  baseUpper := by decide
  lengthUpper := by decide
  baseAligned := by decide
  lengthAligned := by decide
  controlKnown := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by cases ready <;> simp [before,Std.ExtDHashMap.get?_insert]
  baseBytes := by intro index within;interval_cases index <;> apply cell <;> cases wide <;> cases ready <;> decide
  lengthBytes := by intro index within;interval_cases index <;> apply cell <;> cases wide <;> cases ready <;> decide
  geometry := {
    extent := 512
    upper := by change (4096 : Int) + 512 < 2 ^ 47;decide
    codeWithin := by cases wide <;> decide
    rejectWithin := by cases wide <;> decide
    overflowDelta := by cases wide <;> decide
    shortDelta := by cases wide <;> decide
    rangeDelta := by cases wide <;> decide }
  tailWithin := by cases wide <;> cases ready <;> decide
  loaded := by
    change codeLoaded (before wide ready) 4096 (bytes (instruction wide))
    intro index byte present
    have within : index < 43 := by have := (List.getElem?_eq_some_iff.mp present).1;exact this
    have coordinates : ∀ index : Fin 43, ((address 4096 index.val).signExtend 52).toNat = 4096 + index.val := by decide
    rw [coordinates ⟨index,within⟩]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨index,List.mem_range.mpr within,?_⟩
    rw [present]
    rfl

private def writable (wide : Bool) : Writable (input wide true) where
  value := word
  sourceKnown := by change lookup (before wide true) 10 = some word;simp [lookup,key,before,Std.ExtDHashMap.get?_insert];rfl
  dataAddress := 12289#48
  upper := by cases wide <;> decide
  effective := by change (12289#64) + (0#32).signExtend 64 = (12289#48).signExtend 64;decide
  safe := Or.inl (by change X86FrameLoad.alignmentEnabled controls (512#32) visible = false;decide)

private theorem original_data (wide : Bool) (index : Fin 32) :
    (before wide true).mem.get? (12288 + index.val) = some (0xa5#8) := by
  apply cell
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨index.val,List.mem_range.mpr index.isLt,rfl⟩

private theorem untouched : ∀ wide : Bool, ∀ index : Fin 32,
    (index.val = 0 ∨ 1 + X86DataStore.byteCount wide ≤ index.val) →
      12288 + index.val ∉ X86DataStore.writes wide (12289#48) := by decide

theorem unaligned_prefix_and_suffix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (wide : Bool) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run (before wide true) = .ok () after ∧
      (∀ index < X86DataStore.byteCount wide, after.mem.get? (12289 + index) = some (word.extractLsb' (8 * index) 8)) ∧
      (∀ index : Fin 32, index.val = 0 ∨ 1 + X86DataStore.byteCount wide ≤ index.val →
        after.mem.get? (12288 + index.val) = some (0xa5#8)) ∧
      lookup after 4 = lookup (before wide true) 4 ∧ lookup after 7 = lookup (before wide true) 7 ∧
      ∀ prefixCount ≤ 8, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run (before wide true) = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes wide (12289#48)) (before wide true) observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,_flags,run,frame,stored,_rip,_flagsRead,_quiet,_control,prefixes⟩ :=
    succeeds other extra vector (instruction wide) (before wide true) (origin wide true) (input wide true)
      (by cases wide <;> decide) (writable wide)
  refine ⟨after,run,?_,?_,frame.lookup 4 (by decide),frame.lookup 7 (by decide),prefixes⟩
  · intro index within
    have bound : index < 8 := by cases wide <;> simp [X86DataStore.byteCount] at within <;> omega
    have coordinates : ∀ index : Fin 8, X86WriteWords.physicalAddress (12289#48) index.val = 12289 + index.val := by decide
    have observed := stored index within
    change after.mem.get? (X86WriteWords.physicalAddress (12289#48) index) =
      some ((X86DataStore.payload wide word).extractLsb' (8 * index) 8) at observed
    rw [coordinates ⟨index,bound⟩,payload_byte wide _ index within] at observed
    exact observed
  · intro index outside
    rw [frame.memory _ (untouched wide index outside)]
    exact original_data wide index

theorem rejection_without_payload (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (wide : Bool) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run (before wide false) = .ok () after ∧
      lookup after 10 = none ∧ after.mem.get? 12289 = none ∧
      after.regs.get? .rip = some (4352#64) ∧
      ∀ location, after.mem.get? location = (before wide false).mem.get? location := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,rip,_control,_prefixes⟩ :=
    rejects other extra vector (instruction wide) (before wide false) (origin wide false) (input wide false)
      (by cases wide <;> decide)
  have number : X86Bounds.boundsSteps (layout (instruction wide)) (input wide false).base
      (input wide false).pointer (input wide false).length = 5 := by cases wide <;> decide
  rw [number] at run
  have endpoint : after.regs.get? .rip = some (4352#64) := by
    change after.regs.get? .rip = some ((address 4096 256).signExtend 64) at rip
    have same : (address 4096 256).signExtend 64 = (4352#64) := by decide
    simpa only [same] using rip
  refine ⟨after,run,?_,?_,endpoint,fun _ => by rw [frame.memory]⟩
  · rw [frame.lookup 10 (by decide)]
    simp [lookup,key,before,Std.ExtDHashMap.get?_insert]
  · rw [frame.memory]
    exact Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (by cases wide <;> decide)

#print axioms unaligned_prefix_and_suffix
#print axioms rejection_without_payload
end Mettapedia.Machines.TIsa.X86BoundedStore.Controls
