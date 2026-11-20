import Mettapedia.Machines.TIsa.X86MemoryReadback
import Mettapedia.Machines.TIsa.X86SibStore

/-!
# Source stores and the native byte representation

A genuine selected store firing supplies its bounds, writable mode and output
bytes. The native dword write realizes those bytes in the same memory view.
Other byte observations are preserved using canonical physical-key injectivity;
framed descriptors retain explicit exclusions from the physical write footprint.
No expected output or compiler-correctness premise is supplied. Native fetch,
bounds-prefix composition, admission and complete programs have separate joins.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryStore
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback
open Cells CellEffects
local instance : MemoryPrimitives := X86Memory.ordinary

theorem source_store_iff (width : P1Source.Width) (region : Nat) (pointer source : P1Source.Reg)
    (displacement : Int) (address : Nat) (keys : Finset Key) (before : Key → Word) (following : World) :
    (profile [P1Memory.storeRecipe width region pointer source displacement address]).theory.rewrites
      (encode keys before) following ↔
      ∃ produced : Key → Word,
        (P1Memory.storeRecipe width region pointer source displacement address).support ⊆ keys ∧
        before (.capabilityMode region) = 2 ∧
        Memory.access? (before (.capabilityBase region)) (before (.capabilityLength region))
          (before (.register pointer)) displacement width.bytes = some address ∧
        (Memory.byteKeys address width.bytes).map produced =
          Memory.byteWords (unpackBytes width.bytes (before (.register source))) ∧
        following = encode keys (overwrite
          (P1Memory.storeRecipe width region pointer source displacement address).writes before produced) := by
  rw [profile_rewrite_iff]
  constructor
  · rintro ⟨recipe, member, produced, included, guarded, endpoint⟩
    have same : recipe = P1Memory.storeRecipe width region pointer source displacement address := by simpa using member
    subst recipe
    obtain ⟨mode, access, output⟩ := (P1Memory.store_guard_iff width region pointer source displacement address before produced).mp guarded
    exact ⟨produced, included, mode, access, output, endpoint⟩
  · rintro ⟨produced, included, mode, access, output, endpoint⟩
    exact ⟨_, by simp, produced, included,
      (P1Memory.store_guard_iff width region pointer source displacement address before produced).mpr ⟨mode, access, output⟩,
      endpoint⟩

theorem unpack32_byte (value : Word) (offset : Fin 4) :
    (unpackBytes 4 value)[offset.val]'(by rw [unpackBytes_length]; exact offset.isLt) =
      value.extractLsb' (8 * offset.val) 8 := by
  fin_cases offset <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit within
  all_goals interval_cases bit <;> simp [unpackBytes]

theorem produced_byte32 (produced : Key → Word) (address : Nat) (value : Word)
    (output : (Memory.byteKeys address 4).map produced = Memory.byteWords (unpackBytes 4 value))
    (offset : Fin 4) :
    produced (.byte (address + offset.val)) = (value.extractLsb' (8 * offset.val) 8).zeroExtend 64 := by
  have entry := congrArg (fun words => words[offset.val]?) output
  simpa [Memory.byteKeys, Memory.byteWords, offset.isLt, unpackBytes_length,
    List.getElem?_eq_getElem, unpack32_byte] using entry

theorem represented_byte_area (view : View) (values : Key → Word) (native : State) (address count : Nat)
    (positive : 0 < count)
    (known : ∀ location ∈ view.keys, readback view.modes native location = some (values location))
    (included : ∀ offset < count, Memory.Key.byte (address + offset) ∈ view.keys) :
    X86CanonicalSpan.Area (BitVec.ofNat 64 address) count := by
  have observations (offset : Nat) (within : offset < count) :=
    byte_observed view.modes native (address + offset) _ (known _ (included offset within))
  have first := observations 0 positive
  have last := observations (count - 1) (by omega)
  have addressBound : address < 2 ^ 64 := by simpa only [Nat.add_zero] using first.1
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound]
    have := last.1
    omega
  · intro offset within
    rw [← BitVec.ofNat_add]
    exact (observations offset within).2.1

def target (address : Nat) : BitVec 48 := X86CanonicalSpan.narrow (BitVec.ofNat 64 address)

theorem source_key_at (address offset : Nat) (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) 4)
    (within : offset < 4) :
    X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (address + offset)) =
      X86WriteWords.physicalAddress (target address) offset := by
  rw [BitVec.ofNat_add]
  exact X86CanonicalSpan.physicalKey_offset _ 4 offset (by decide) area within

theorem physical_byte_outside (address other : Nat)
    (addressBound : address < 2 ^ 64) (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) 4)
    (otherBound : other < 2 ^ 64) (otherCanonical : X86CanonicalSpan.Canonical (BitVec.ofNat 64 other))
    (outside : (Memory.Key.byte other : Key) ∉ (Memory.byteKeys address 4).toFinset) :
    X86CanonicalSpan.physicalKey (BitVec.ofNat 64 other) ∉ X86SibStore.writes (target address) := by
  intro member
  obtain ⟨offset, inside, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have within : offset < 4 := List.mem_range.mp inside
  have keyEq : X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (address + offset)) =
      X86CanonicalSpan.physicalKey (BitVec.ofNat 64 other) := (source_key_at address offset area within).trans same
  have wordEq := X86CanonicalSpan.physicalKey_injective _ _
    (by rw [BitVec.ofNat_add]; exact area.2 offset within) otherCanonical keyEq
  have targetBound : address + offset < 2 ^ 64 := by
    have bound := area.1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound] at bound
    omega
  have coordinate : address + offset = other := by
    have sameNat := congrArg BitVec.toNat wordEq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt targetBound, Nat.mod_eq_of_lt otherBound] using sameNat
  apply outside
  simp only [Memory.byteKeys, List.mem_toFinset, List.mem_map, List.mem_range]
  exact ⟨offset, within, congrArg Memory.Key.byte coordinate⟩

theorem low32_extract (value : Word) (offset : Fin 4) :
    (X86DataStore.payload false value).extractLsb' (8 * offset.val) 8 =
      value.extractLsb' (8 * offset.val) 8 := by
  change (value.extractLsb' 0 32).extractLsb' (8 * offset.val) 8 = _
  exact BitVec.extractLsb'_extractLsb'_of_le (by have := offset.isLt; omega)

theorem stored_readback32 (modes : Fin 9 → Word) (before : State) (address : Nat) (next : BitVec 48)
    (value : Word) (addressBound : address < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) 4) (offset : Fin 4) :
    readback modes (X86SibStore.result before (target address) next value) (.byte (address + offset.val)) =
      some ((value.extractLsb' (8 * offset.val) 8).zeroExtend 64) := by
  have upper := X86CanonicalSpan.area_signed_upper (BitVec.ofNat 64 address) 4 (by decide) area
  rw [← X86CanonicalSpan.narrow_toInt _ (X86CanonicalSpan.area_base _ 4 (by decide) area)] at upper
  have bound : address + offset.val < 2 ^ 64 := by
    have spanBound := area.1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound] at spanBound
    omega
  apply readback_byte_known _ _ _ _ bound
  · rw [BitVec.ofNat_add]
    exact area.2 offset.val offset.isLt
  · rw [source_key_at address offset.val area offset.isLt]
    have observed := X86DataStore.byte_readback before false (target address) next value upper offset.val offset.isLt
    simpa only [memory, low32_extract value offset] using observed

def DescriptorsApart (view : View) (native : State) (written : Finset Nat) : Prop :=
  (∀ region, Memory.Key.capabilityBase region ∈ view.keys →
    ∀ address ∈ memoryReads native (.capabilityBase region), address ∉ written) ∧
  (∀ region, Memory.Key.capabilityLength region ∈ view.keys →
    ∀ address ∈ memoryReads native (.capabilityLength region), address ∉ written)

theorem store_represents (view : View) (values : Key → Word) (before : State)
    (region : Nat) (pointer source : P1Source.Reg) (displacement : Int) (address : Nat)
    (following : World) (next : BitVec 48)
    (known : ∀ location ∈ view.keys, readback view.modes before location = some (values location))
    (firing : (profile [P1Memory.storeRecipe .word32 region pointer source displacement address]).theory.rewrites
      (encode view.keys values) following)
    (descriptors : DescriptorsApart view before (X86SibStore.writes (target address))) :
    represents view following (X86SibStore.result before (target address) next (values (.register source))) := by
  obtain ⟨produced, included, _mode, access, output, followingEq⟩ :=
    (source_store_iff .word32 region pointer source displacement address view.keys values following).mp firing
  have bytesIncluded : ∀ offset < 4, Memory.Key.byte (address + offset) ∈ view.keys := by
    intro offset within
    apply included
    apply Finset.mem_union_left
    simp [CellEffects.Recipe.writes, P1Memory.storeRecipe, P1Memory.storeSpec, Memory.Store.recipe,
      Memory.byteKeys, P1Memory.memoryWidth, Memory.Width.bytes, within]
  have area := represented_byte_area view values before address 4 (by decide) known bytesIncluded
  have addressBound : address < 2 ^ 64 := by
    have noWrap := Memory.access?_no_wrap _ _ _ _ _ _ access
    change address + 4 ≤ 2 ^ 64 at noWrap
    omega
  let written := (P1Memory.storeRecipe .word32 region pointer source displacement address).writes
  have writtenEq : written = (Memory.byteKeys address 4).toFinset := rfl
  refine ⟨overwrite written values produced, followingEq, ?_⟩
  intro observed member
  by_cases updated : observed ∈ written
  · rw [overwrite, if_pos updated]
    rw [writtenEq] at updated
    obtain ⟨offset, within, same⟩ := List.mem_map.mp (List.mem_toFinset.mp updated)
    have bound : offset < 4 := List.mem_range.mp within
    change Memory.Key.byte (address + offset) = observed at same
    subst observed
    rw [stored_readback32 view.modes before address next (values (.register source)) addressBound area ⟨offset, bound⟩,
      produced_byte32 produced address (values (.register source)) output ⟨offset, bound⟩]
  · rw [overwrite, if_neg updated]
    rw [readback_store_frame view.modes before _ _
      (X86DataStore.result_frame false before (target address) next (values (.register source))) observed ?_]
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
          obtain ⟨bound, canonical, _bytes⟩ := byte_observed view.modes before other _ (known _ member)
          exact physical_byte_outside address other addressBound area bound canonical (by simpa only [writtenEq] using updated)

end Mettapedia.Machines.TIsa.X86MemoryStore
