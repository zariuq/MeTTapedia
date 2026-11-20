import Mettapedia.Machines.TIsa.X86MemoryView
import Mettapedia.Machines.TIsa.P1Memory
import Mathlib.Data.List.Forall2

/-!
# Inverting actual word and source-memory readbacks

A successful eight-byte observation yields canonical address geometry and
all actual backing-byte equations required by the existing Sail contracts.
Conversely, represented byte cells assemble the same native word. Applying
this to the established U64 load recipe derives the observed word and source
update from a genuine resource firing, without an expected-value premise.

These are representation and source-guard laws. Instruction execution,
alignment, native admission and whole-program hosting remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryReadback
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView

theorem sequence_some {α β : Type} (items : List α) (read : α → Option β) (values : List β)
    (known : items.mapM read = some values) : List.Forall₂ (fun item value => read item = some value) items values := by
  induction items generalizing values with
  | nil =>
    have same : [] = values := Option.some.inj known
    subst values
    exact List.Forall₂.nil
  | cons head tail ih =>
    rw [List.mapM_cons] at known
    obtain ⟨value,headRead,later⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨rest,tailRead,returned⟩ := Option.bind_eq_some_iff.mp later
    have same : value :: rest = values := Option.some.inj returned
    subst values
    exact List.Forall₂.cons headRead (ih rest tailRead)

theorem packed_extract (bytes : List (BitVec 8)) (length : bytes.length = 8) (offset : Fin 8) :
    (packBytes bytes).extractLsb' (8 * offset.val) 8 = bytes[offset.val]'(by omega) := by
  let entry : Fin 8 → BitVec 8 := fun index => bytes[index.val]'(by omega)
  have expanded : List.ofFn entry = bytes := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact length.symm)
    intro index inside here
    have within : index < 8 := by omega
    interval_cases index <;> simp [entry]
  have packed : packBytes bytes =
      packBytes [entry 0,entry 1,entry 2,entry 3,entry 4,entry 5,entry 6,entry 7] := by
    rw [←expanded]
    rfl
  rw [packed]
  fin_cases offset <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit inside
  all_goals interval_cases bit <;> simp [packBytes,entry]

theorem wordAt?_eq_some_iff (bytes : Nat → Option (BitVec 8)) (pointer value : Word) :
    wordAt? bytes pointer = some value ↔ span pointer ∧
      ∀ offset : Fin 8, bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset.val)) =
        some (value.extractLsb' (8 * offset.val) 8) := by
  constructor
  · intro known
    unfold wordAt? at known
    split at known
    next admitted =>
      obtain ⟨values,reads,packed⟩ := Option.map_eq_some_iff.mp known
      have matched := sequence_some (List.range 8)
        (fun offset => bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset))) values reads
      have length : values.length = 8 := by simpa only [List.length_range] using matched.length_eq.symm
      refine ⟨admitted,?_⟩
      intro offset
      have observed : bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset.val)) =
          some (values[offset.val]'(by omega)) := by
        simpa only [List.get_eq_getElem,List.getElem_range] using
          matched.get (i := offset.val) (by simp only [List.length_range]; exact offset.isLt) (by omega)
      have decoded := packed_extract values length offset
      rw [packed] at decoded
      exact observed.trans (congrArg some decoded.symm)
    next refused => simp at known
  · rintro ⟨admitted,reads⟩
    exact wordAt?_known bytes pointer value admitted (fun offset within => reads ⟨offset,within⟩)

theorem field?_bytes (native : State) (frame value : Word) (offset : Nat)
    (pointer : lookup native 7 = some frame) (known : field? native offset = some value) :
    span (frame + BitVec.ofNat 64 offset) ∧
      ∀ index : Fin 8, memory native (X86CanonicalSpan.physicalKey
        (frame + BitVec.ofNat 64 offset + BitVec.ofNat 64 index.val)) =
        some (value.extractLsb' (8 * index.val) 8) := by
  unfold field? at known
  rw [pointer] at known
  exact (wordAt?_eq_some_iff (memory native) _ value).mp known

theorem wordAt?_native_bytes (native : State) (pointer value : Word)
    (known : wordAt? (memory native) pointer = some value) :
    ∃ address : BitVec 48, pointer = address.signExtend 64 ∧
      address.toInt + 8 ≤ (2 ^ 47 : Int) ∧
      ∀ index < 8, native.mem.get? ((X86Execution.address address.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8) := by
  obtain ⟨admitted,bytes⟩ := (wordAt?_eq_some_iff (memory native) pointer value).mp known
  have area := (span_iff_area pointer).mp admitted
  refine ⟨X86CanonicalSpan.narrow pointer,?_,?_,?_⟩
  · exact (X86CanonicalSpan.narrow_representation pointer (X86CanonicalSpan.area_base pointer 8 (by decide) area)).symm
  · rw [X86CanonicalSpan.narrow_toInt pointer (X86CanonicalSpan.area_base pointer 8 (by decide) area)]
    exact X86CanonicalSpan.area_signed_upper pointer 8 (by decide) area
  · intro index within
    have observed := bytes ⟨index,within⟩
    rw [X86CanonicalSpan.physicalKey_offset pointer 8 index (by decide) area within] at observed
    exact observed

theorem wordAt?_narrow_bytes (native : State) (pointer value : Word)
    (known : wordAt? (memory native) pointer = some value) :
    pointer = (X86CanonicalSpan.narrow pointer).signExtend 64 ∧
      (X86CanonicalSpan.narrow pointer).toInt + 8 ≤ (2 ^ 47 : Int) ∧
      ∀ index < 8, native.mem.get?
        ((X86Execution.address (X86CanonicalSpan.narrow pointer).toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8) := by
  obtain ⟨admitted,bytes⟩ := (wordAt?_eq_some_iff (memory native) pointer value).mp known
  have area := (span_iff_area pointer).mp admitted
  refine ⟨?_,?_,?_⟩
  · exact (X86CanonicalSpan.narrow_representation pointer (X86CanonicalSpan.area_base pointer 8 (by decide) area)).symm
  · rw [X86CanonicalSpan.narrow_toInt pointer (X86CanonicalSpan.area_base pointer 8 (by decide) area)]
    exact X86CanonicalSpan.area_signed_upper pointer 8 (by decide) area
  · intro index within
    have observed := bytes ⟨index,within⟩
    rw [X86CanonicalSpan.physicalKey_offset pointer 8 index (by decide) area within] at observed
    exact observed

theorem byte_observed (modes : Fin 9 → Word) (native : State) (address : Nat) (value : Word)
    (known : readback modes native (.byte address) = some value) :
    address < 2 ^ 64 ∧ X86CanonicalSpan.Canonical (BitVec.ofNat 64 address) ∧
      ∃ byte : BitVec 8, memory native (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) = some byte ∧
        value = byte.zeroExtend 64 := by
  change (if address < 2 ^ 64 ∧ X86CanonicalSpan.Canonical (BitVec.ofNat 64 address) then
    (memory native (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address))).map (BitVec.zeroExtend 64)
    else none) = some value at known
  split at known
  next admitted =>
    obtain ⟨byte,present,same⟩ := Option.map_eq_some_iff.mp known
    exact ⟨admitted.1,admitted.2,byte,present,same.symm⟩
  next refused => simp at known

theorem byte_extract (byte : BitVec 8) : (byte.zeroExtend 64).extractLsb' 0 8 = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  have wide : bit < 64 := by omega
  simp [within,wide]

theorem byte_words_observed (view : View) (values : Key → Word) (native : State) (address : Nat)
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (present : ∀ offset < 8, Memory.Key.byte (address + offset) ∈ view.keys) :
    ∃ bytes : List (BitVec 8),
      (Memory.byteKeys address 8).map values = Memory.byteWords bytes ∧ bytes.length = 8 ∧
      wordAt? (memory native) (BitVec.ofNat 64 address) = some (packBytes bytes) := by
  let bytes := (List.range 8).map fun offset => (values (.byte (address + offset))).extractLsb' 0 8
  have observations (offset : Nat) (within : offset < 8) :=
    byte_observed view.modes native (address + offset) _ (known (.byte (address + offset)) (present offset within))
  have first := observations 0 (by decide)
  have last := observations 7 (by decide)
  have addressBound : address < 2 ^ 64 := by simpa only [Nat.add_zero] using first.1
  have addressNat : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound]
  have admitted : span (BitVec.ofNat 64 address) := by
    refine ⟨by rw [addressNat]; have := last.1; omega,?_⟩
    intro offset
    rw [←BitVec.ofNat_add]
    exact (observations offset.val offset.isLt).2.1
  have words : (Memory.byteKeys address 8).map values = Memory.byteWords bytes := by
    simp only [Memory.byteKeys,Memory.byteWords,bytes,List.map_map]
    apply List.map_congr_left
    intro offset member
    obtain ⟨byte,_read,equal⟩ := (observations offset (List.mem_range.mp member)).2.2
    simp only [Function.comp_apply]
    rw [equal,byte_extract]
  refine ⟨bytes,words,by simp [bytes],?_⟩
  rw [wordAt?,if_pos admitted]
  have reads := X86MemoryView.sequence_congr (List.range 8)
    (fun offset => memory native (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address + BitVec.ofNat 64 offset)))
    (fun offset => some ((values (.byte (address + offset))).extractLsb' 0 8)) (by
      intro offset member
      obtain ⟨byte,read,equal⟩ := (observations offset (List.mem_range.mp member)).2.2
      rw [←BitVec.ofNat_add,equal,byte_extract]
      exact read)
  rw [reads]
  have collected : (List.range 8).mapM (fun offset => some ((values (.byte (address + offset))).extractLsb' 0 8)) =
      some bytes := List.mapM_pure
  rw [collected]
  rfl

theorem source_load_word (view : View) (values : Key → Word) (native : State)
    (region : Nat) (destination pointer : P1Source.Reg) (displacement : Int) (address : Nat) (following : World)
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (source : (CellEffects.profile [P1Memory.loadRecipe .u64 .word64 region destination pointer displacement address]).theory.rewrites
      (Cells.encode view.keys values) following) :
    ∃ value,
      Memory.access? (values (.capabilityBase region)) (values (.capabilityLength region))
        (values (.register pointer)) displacement 8 = some address ∧
      wordAt? (memory native) (BitVec.ofNat 64 address) = some value ∧
      following = Cells.encode view.keys (Function.update values (.register destination) value) := by
  obtain ⟨value,included,_mode,access,parsed,endpoint⟩ :=
    (P1Memory.load_rewrite_iff .u64 .word64 region destination pointer displacement address view.keys values following).mp source
  simp only [P1Source.Width.bytes] at access parsed
  have present : ∀ offset < 8, Memory.Key.byte (address + offset) ∈ view.keys := by
    intro offset within
    apply included
    simp [CellEffects.Recipe.support,CellEffects.Recipe.writes,P1Memory.loadRecipe,
      Memory.capabilityKeys,Memory.byteKeys,P1Source.Width.bytes,within]
  obtain ⟨bytes,words,_length,read⟩ := byte_words_observed view values native address known present
  rw [words,P1Memory.load_byteWords] at parsed
  change some (packBytes bytes) = some value at parsed
  have same := Option.some.inj parsed
  exact ⟨value,access,by simpa only [same] using read,endpoint⟩

#print axioms packed_extract
#print axioms wordAt?_eq_some_iff
#print axioms wordAt?_narrow_bytes
#print axioms byte_words_observed
#print axioms source_load_word

end Mettapedia.Machines.TIsa.X86MemoryReadback
