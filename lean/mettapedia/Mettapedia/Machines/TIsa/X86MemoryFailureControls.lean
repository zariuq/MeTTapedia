import Mettapedia.Machines.TIsa.X86MemoryFailureSites

/-! Genuine source/error-control firings with absent native payload and data. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MemoryFailure.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView Cells CellEffects Control
local instance : MemoryPrimitives := X86Memory.ordinary

private def width (wide : Bool) : P1Source.Width := if wide then .word64 else .word32
private def layout (wide : Bool) : X86Bounds.Layout := ⟨6,0,⟨0,by decide⟩,if wide then 8 else 4,256⟩
private def pointer (fault : Fin 3) : Word := if fault.val = 1 then 12287 else if fault.val = 2 then 12321 else 12289
private def length (fault : Fin 3) : Word := if fault.val = 0 then 0 else 32
private def modes (write : Bool) : Fin 9 → Word := fun _ => if write then 2 else 1
private def keys : Finset Key := {.capabilityBase 0,.capabilityLength 0,.capabilityMode 0,.register 1}
private def values (write : Bool) (fault : Fin 3) : Key → Word
  | .register 0 => 8192
  | .register 1 => pointer fault
  | .capabilityBase 0 => 12288
  | .capabilityLength 0 => length fault
  | .capabilityMode 0 => if write then 2 else 1
  | _ => 0
private def modeControl : Vector (BitVec 64) 7 := Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0
private def profile : X86Readiness.Profile := ⟨controls,visible,0⟩
private def cells (wide : Bool) (fault : Fin 3) : List (Nat × BitVec 8) :=
  ((List.range (X86Bounds.code (layout wide)).length).map (fun index =>
    (4096 + index,BitVec.ofNat 8 (((X86Bounds.code (layout wide))[index]?).getD 0)))) ++
    (List.range 16).map (fun index => (8192 + index,
      if index < 8 then (12288#64).extractLsb' (8 * index) 8 else (length fault).extractLsb' (8 * (index - 8)) 8))
@[irreducible] private def native (wide : Bool) (fault : Fin 3) : State :=
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
  let registers := registers.insert .rsi (pointer fault)
  let registers := registers.insert .rsp (16384#64)
  ⟨registers,(),Std.ExtHashMap.ofList (cells wide fault),(),0,#[]⟩
private theorem native_memory (wide : Bool) (fault : Fin 3) :
    (native wide fault).mem = Std.ExtHashMap.ofList (cells wide fault) := by
  unfold native
  rfl
private theorem cell (wide : Bool) (fault : Fin 3) (position : Nat) (byte : BitVec 8)
    (present : (position,byte) ∈ cells wide fault) : (native wide fault).mem.get? position = some byte := by
  rw [native_memory]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by cases wide <;> fin_cases fault <;> decide) present
private theorem descriptor (wide : Bool) (fault : Fin 3) (slot : Fin 2) :
    wordAt? (memory (native wide fault)) (BitVec.ofNat 64 (8192 + 8 * slot.val)) =
      some (if slot.val = 0 then (12288#64) else length fault) := by
  apply wordAt?_known _ _ _ (by fin_cases slot <;> decide)
  intro index within
  fin_cases slot <;> interval_cases index <;> apply cell <;> cases wide <;> fin_cases fault <;> decide
private theorem frameKnown (wide : Bool) (fault : Fin 3) : lookup (native wide fault) 7 = some (8192#64) := by
  simp [native,lookup,key,Std.ExtDHashMap.get?_insert]
  rfl
private theorem observed (write wide : Bool) (fault : Fin 3) :
    ∀ observed ∈ keys, readback (modes write) (native wide fault) observed = some (values write fault observed) := by
  intro observed member
  simp only [keys,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · change field? (native wide fault) 0 = some (12288#64)
    unfold field?
    rw [frameKnown]
    change wordAt? (memory (native wide fault)) ((8192#64) + (0#64)) = some (12288#64)
    rw [BitVec.add_zero]
    exact descriptor wide fault 0
  · change field? (native wide fault) 8 = some (length fault)
    unfold field?
    rw [frameKnown]
    change wordAt? (memory (native wide fault)) ((8192#64) + (8#64)) = some (length fault)
    rw [show (8192#64) + (8#64) = (8200#64) from by decide]
    exact descriptor wide fault 1
  · rfl
  · change lookup (native wide fault) 6 = some (pointer fault)
    simp [native,lookup,key,Std.ExtDHashMap.get?_insert]
    rfl
private def origin (wide : Bool) (fault : Fin 3) : X86LegacyFetch.Basis (native wide fault) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [native,Std.ExtDHashMap.get?_insert]
  fault := by simp [native,Std.ExtDHashMap.get?_insert]
  msrs := by simp [native,Std.ExtDHashMap.get?_insert]
  segments := by simp [native,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [native,Std.ExtDHashMap.get?_insert]
  rip := by simp [native,Std.ExtDHashMap.get?_insert]
private def entry (write wide : Bool) (fault : Fin 3) :
    Entry (layout wide) 1 keys (modes write) (values write fault) (native wide fault) where
  origin := origin wide fault
  profile := profile
  flags := 512#32
  mapped := rfl
  known := observed write wide fault
  frameKnown := frameKnown wide fault
  frameArea := by
    change X86CanonicalSpan.Area (8192#64) 192
    exact X86CanonicalSpan.area_low _ _ (by decide)
  frameAligned := by change (8192 : Nat) % 8 = 0;decide
  holds := by
    refine ⟨?_,?_,512#32,?_,?_⟩
    all_goals simp [profile,native,Std.ExtDHashMap.get?_insert]
    decide
  flagsKnown := by simp [native,Std.ExtDHashMap.get?_insert]
  quiet := by simp [native,Std.ExtDHashMap.get?_insert]
  geometry := {
    extent := 512
    upper := by change (4096 : Int) + 512 < 2 ^ 47;decide
    codeWithin := by cases wide <;> decide
    rejectWithin := by change 256 ≤ 512;decide
    overflowDelta := by cases wide <;> decide
    shortDelta := by cases wide <;> decide
    rangeDelta := by cases wide <;> decide }
  loaded := by
    change codeLoaded (native wide fault) 4096 (X86Bounds.code (layout wide))
    intro index byte present
    have extent : (X86Bounds.code (layout wide)).length = 36 := by cases wide <;> decide
    have within : index < 36 := by have := (List.getElem?_eq_some_iff.mp present).1;omega
    have coordinates : ∀ index : Fin 36, ((address 4096 index.val).signExtend 52).toNat = 4096 + index.val := by decide
    rw [coordinates ⟨index,within⟩]
    apply cell
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨index,List.mem_range.mpr (by omega),?_⟩
    rw [present]
    rfl
  rangeFits := by
    change (12288#64).toNat + (length fault).toNat < 2 ^ 64
    fin_cases fault <;> decide

private theorem source_firing (write wide : Bool) (fault : Fin 3) :
    (CellEffects.profile [recipe write (width wide) (layout wide) 1]).theory.rewrites
      (encode keys (values write fault)) (encode keys (values write fault)) := by
  apply (P1Memory.bounds_failure_rewrite_iff write (width wide) 0 1 0 keys (values write fault) _).mpr
  refine ⟨?_,?_,?_,rfl⟩
  · intro observed member
    simpa [Recipe.support,Recipe.writes,P1Memory.boundsFailureRecipe,Memory.capabilityKeys,keys] using member
  · cases write <;> simp [values]
  · change Memory.access? (12288#64) (length fault) (pointer fault) 0 (width wide).bytes = none
    cases wide <;> fin_cases fault <;> decide

private def controlEdge (write wide : Bool) : Edge Key := ⟨0,0,256,recipe write (width wide) (layout wide) 1⟩
private def controlledValues (write : Bool) (fault : Fin 3) : Control.Location Key → Word
  | .inl _ => 0
  | .inr observed => values write fault observed

theorem controlled_rejection_without_data (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (write wide : Bool) (fault : Fin 3) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ afterValues : Control.Location Key → Word, ∃ after,
      (CellEffects.profile [(controlEdge write wide).recipe]).theory.rewrites
        (encode (scopedKeys 0 keys) (controlledValues write fault)) (encode (scopedKeys 0 keys) afterValues) ∧
      afterValues (.inl 0) = (256#64) ∧
      (X86FuelPrefix.fetches (if fault.val = 0 then 5 else 7)).run (native wide fault) = .ok () after ∧
      lookup after 10 = none ∧ lookup after 0 = none ∧ after.mem.get? 12289 = none ∧
      after.regs.get? .rip = some (4352#64) ∧
      (∀ location, after.mem.get? location = (native wide fault).mem.get? location) ∧
      ∀ prefixCount ≤ (if fault.val = 0 then 5 else 7), ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run (native wide fault) = .ok () seen →
          RegisterFrame X86Bounds.writes (native wide fault) seen := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  have sized : (width wide).bytes = (layout wide).count.val := by cases wide <;> decide
  obtain ⟨_unchanged,after,_flags,run,frame,_readbacks,rip,_flagsRead,_quiet,_control,_holds,prefixes⟩ :=
    source_executes other extra vector write (width wide) (layout wide) 1 sized keys (modes write) (values write fault)
      (native wide fault) (entry write wide fault) _ (source_firing write wide fault)
  obtain ⟨afterValues,next,_data,step⟩ := (controlEdge write wide).lift_firing keys (controlledValues write fault)
    _ rfl (source_firing write wide fault)
  have steps : count (layout wide) 1 (values write fault) = if fault.val = 0 then 5 else 7 := by
    cases wide <;> cases write <;> fin_cases fault <;> decide
  rw [steps] at run prefixes
  have endpoint : after.regs.get? .rip = some (4352#64) := by
    change after.regs.get? .rip = some ((X86Bounds.position (4096#48) 256).signExtend 64) at rip
    have final : (X86Bounds.position (4096#48) 256).signExtend 64 = (4352#64) := by decide
    simpa only [final] using rip
  refine ⟨afterValues,after,step,next,run,?_,?_,?_,endpoint,fun _ => by rw [frame.memory],prefixes⟩
  · rw [frame.lookup 10 (by decide)]
    simp [lookup,key,native,Std.ExtDHashMap.get?_insert]
  · rw [frame.lookup 0 (by decide)]
    simp [lookup,key,native,Std.ExtDHashMap.get?_insert]
  · rw [frame.memory]
    rw [native_memory]
    exact Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (by cases wide <;> fin_cases fault <;> decide)

theorem wrong_control_refused (write wide : Bool) (fault : Fin 3) (following : Multiset (Cell (Control.Location Key))) :
    ¬ (CellEffects.profile [(controlEdge write wide).recipe]).theory.rewrites
      (encode (scopedKeys 0 keys) (Function.update (controlledValues write fault) (.inl 0) 1)) following := by
  apply X86MemoryContinuation.wrong_control_refused
  simp [controlEdge]

theorem fitting_access_cannot_refuse (write wide : Bool) (following : World) :
    let admitted := Function.update (Function.update (values write 0) (.register 1) 12288) (.capabilityLength 0) 32
    ¬ (CellEffects.profile [recipe write (width wide) (layout wide) 1]).theory.rewrites (encode keys admitted) following := by
  dsimp only
  intro step
  obtain ⟨_included,_mode,access,_endpoint⟩ :=
    (P1Memory.bounds_failure_rewrite_iff write (width wide) 0 1 0 keys _ following).mp step
  have accepted : Memory.access? (12288#64) (32#64) (12288#64) 0 (width wide).bytes = some 12288 := by cases wide <;> decide
  have impossible : Memory.access? (12288#64) (32#64) (12288#64) 0 (width wide).bytes = none := by simpa [values] using access
  rw [accepted] at impossible
  cases impossible

#print axioms controlled_rejection_without_data
#print axioms wrong_control_refused
#print axioms fitting_access_cannot_refuse
end Mettapedia.Machines.TIsa.X86MemoryFailure.Controls
