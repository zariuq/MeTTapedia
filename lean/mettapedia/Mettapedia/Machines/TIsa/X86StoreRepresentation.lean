import Mettapedia.Machines.TIsa.X86BoundedStore
import Mettapedia.Machines.TIsa.X86BoundedLoadSource

/-!
# Exact source-byte updates for both native store widths

The source firing determines every written byte. Canonical physical-key
injectivity protects other byte cells; explicit descriptor exclusions protect
capability observations. Bounds scratch writes do not affect source registers.
The resulting representation theorem accepts actual execution-derived frames
and byte equations, and does not assume the desired source representation.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86StoreRepresentation
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback
open Cells CellEffects
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev width := X86BoundedLoadSource.width
abbrev target := X86MemoryStore.target
abbrev DescriptorsApart := X86MemoryStore.DescriptorsApart

theorem width_bytes (wide : Bool) : (width wide).bytes = X86DataStore.byteCount wide := by cases wide <;> rfl

theorem unpack64_byte (value : Word) (offset : Fin 8) :
    (unpackBytes 8 value)[offset.val]'(by rw [unpackBytes_length];exact offset.isLt) =
      value.extractLsb' (8 * offset.val) 8 := by
  fin_cases offset <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit within
  all_goals interval_cases bit <;> simp [unpackBytes]

theorem produced_byte (wide : Bool) (produced : Key → Word) (address : Nat) (value : Word)
    (output : (Memory.byteKeys address (X86DataStore.byteCount wide)).map produced =
      Memory.byteWords (unpackBytes (X86DataStore.byteCount wide) value))
    (offset : Fin (X86DataStore.byteCount wide)) :
    produced (.byte (address + offset.val)) = (value.extractLsb' (8 * offset.val) 8).zeroExtend 64 := by
  cases wide with
  | false => exact X86MemoryStore.produced_byte32 produced address value output offset
  | true =>
    have bound : offset.val < 8 := offset.isLt
    have entry := congrArg (fun words => words[offset.val]?) output
    simpa [Memory.byteKeys,Memory.byteWords,X86DataStore.byteCount,bound,unpackBytes_length,
      List.getElem?_eq_getElem,unpack64_byte value ⟨offset.val,bound⟩] using entry

theorem payload_byte (wide : Bool) (value : Word) (index : Nat) (within : index < X86DataStore.byteCount wide) :
    (X86DataStore.payload wide value).extractLsb' (8 * index) 8 = value.extractLsb' (8 * index) 8 := by
  cases wide with
  | true => rfl
  | false => exact X86MemoryStore.low32_extract value ⟨index,within⟩

theorem source_key_at (wide : Bool) (address offset : Nat)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) (X86DataStore.byteCount wide))
    (within : offset < X86DataStore.byteCount wide) :
    X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (address + offset)) =
      X86WriteWords.physicalAddress (target address) offset := by
  rw [BitVec.ofNat_add]
  exact X86CanonicalSpan.physicalKey_offset _ _ _ (by cases wide <;> decide) area within

theorem physical_byte_outside (wide : Bool) (address other : Nat) (addressBound : address < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) (X86DataStore.byteCount wide))
    (otherBound : other < 2 ^ 64) (otherCanonical : X86CanonicalSpan.Canonical (BitVec.ofNat 64 other))
    (outside : (Memory.Key.byte other : Key) ∉ (Memory.byteKeys address (X86DataStore.byteCount wide)).toFinset) :
    X86CanonicalSpan.physicalKey (BitVec.ofNat 64 other) ∉ X86DataStore.writes wide (target address) := by
  intro member
  obtain ⟨offset,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have within : offset < X86DataStore.byteCount wide := List.mem_range.mp inside
  have keyEq : X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (address + offset)) =
      X86CanonicalSpan.physicalKey (BitVec.ofNat 64 other) := (source_key_at wide address offset area within).trans same
  have wordEq := X86CanonicalSpan.physicalKey_injective _ _
    (by rw [BitVec.ofNat_add];exact area.2 offset within) otherCanonical keyEq
  have targetBound : address + offset < 2 ^ 64 := by
    have bound := area.1
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] at bound
    omega
  have coordinate : address + offset = other := by
    have sameNat := congrArg BitVec.toNat wordEq
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt targetBound,Nat.mod_eq_of_lt otherBound] using sameNat
  apply outside
  simp only [Memory.byteKeys,List.mem_toFinset,List.mem_map,List.mem_range]
  exact ⟨offset,within,congrArg Memory.Key.byte coordinate⟩

theorem registerReads_no_bounds (observed : Key) :
    ∀ register ∈ registerReads observed, register ∉ X86Bounds.writes := by
  cases observed with
  | register name =>
    have generic : ∀ register : Fin 12,
        key (placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register)) ∉
          X86Bounds.writes := by decide
    intro register member
    have same : register = key (placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64)
        (Registers.logicalSlot name)) := Finset.mem_singleton.mp member
    subst register
    exact generic name
  | byte _ => simp [registerReads]
  | capabilityMode _ => simp [registerReads]
  | capabilityBase _ => simp only [registerReads];split <;> simp [X86Bounds.writes]
  | capabilityLength _ => simp only [registerReads];split <;> simp [X86Bounds.writes]

theorem represents_after_store (wide : Bool) (view : View) (values : Key → Word) (before after : State)
    (region : Nat) (pointer source : P1Source.Reg) (displacement : Int) (address : Nat) (following : World)
    (known : ∀ location ∈ view.keys, readback view.modes before location = some (values location))
    (firing : (profile [P1Memory.storeRecipe (width wide) region pointer source displacement address]).theory.rewrites
      (encode view.keys values) following)
    (frame : X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes wide (target address)) before after)
    (stored : ∀ index < X86DataStore.byteCount wide,
      after.mem.get? (X86WriteWords.physicalAddress (target address) index) =
        some ((X86DataStore.payload wide (values (.register source))).extractLsb' (8 * index) 8))
    (descriptors : DescriptorsApart view before (X86DataStore.writes wide (target address))) :
    represents view following after := by
  obtain ⟨produced,included,_mode,access,output,followingEq⟩ :=
    (X86MemoryStore.source_store_iff (width wide) region pointer source displacement address view.keys values following).mp firing
  have bytesIncluded : ∀ offset < X86DataStore.byteCount wide, Memory.Key.byte (address + offset) ∈ view.keys := by
    intro offset within
    apply included
    apply Finset.mem_union_left
    simp [Recipe.writes,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,
      Memory.byteKeys,P1Memory.memoryWidth,width,X86BoundedLoadSource.width,Memory.Width.bytes,X86DataStore.byteCount] at within ⊢
    cases wide <;> simpa using within
  have area := X86MemoryStore.represented_byte_area view values before address _ (by cases wide <;> decide) known bytesIncluded
  have addressBound : address < 2 ^ 64 := by
    have noWrap := Memory.access?_no_wrap _ _ _ _ _ _ access
    rw [width_bytes] at noWrap
    have positive : 0 < X86DataStore.byteCount wide := by cases wide <;> decide
    omega
  let written := (P1Memory.storeRecipe (width wide) region pointer source displacement address).writes
  have writtenEq : written = (Memory.byteKeys address (X86DataStore.byteCount wide)).toFinset := by cases wide <;> rfl
  have outputExact : (Memory.byteKeys address (X86DataStore.byteCount wide)).map produced =
      Memory.byteWords (unpackBytes (X86DataStore.byteCount wide) (values (.register source))) := by
    simpa only [width_bytes] using output
  refine ⟨overwrite written values produced,followingEq,?_⟩
  intro observed member
  by_cases updated : observed ∈ written
  · rw [overwrite,if_pos updated]
    rw [writtenEq] at updated
    obtain ⟨offset,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp updated)
    have within : offset < X86DataStore.byteCount wide := List.mem_range.mp inside
    change Memory.Key.byte (address + offset) = observed at same
    subst observed
    rw [produced_byte wide produced address (values (.register source)) outputExact ⟨offset,within⟩]
    apply readback_byte_known
    · have bound := area.1
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] at bound
      omega
    · rw [BitVec.ofNat_add]
      exact area.2 offset within
    · rw [source_key_at wide address offset area within]
      simpa only [memory,payload_byte wide _ offset within] using stored offset within
  · rw [overwrite,if_neg updated]
    rw [readback_framed view.modes before after X86Bounds.writes _ frame observed (registerReads_no_bounds observed) ?_]
    · exact known observed member
    · cases observed with
      | register _ => simp [memoryReads]
      | capabilityMode _ => simp [memoryReads]
      | capabilityBase region => exact descriptors.1 region member
      | capabilityLength region => exact descriptors.2 region member
      | byte other =>
        intro physical present
        have same : physical = X86CanonicalSpan.physicalKey (BitVec.ofNat 64 other) := by simpa [memoryReads] using present
        subst physical
        obtain ⟨bound,canonical,_bytes⟩ := byte_observed view.modes before other _ (known _ member)
        exact physical_byte_outside wide address other addressBound area bound canonical (by simpa only [writtenEq] using updated)

#print axioms represents_after_store
end Mettapedia.Machines.TIsa.X86StoreRepresentation
