import Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedWord
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstLeaf
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionReserve

/-!
# Transporting a live operand slot through a completed graph map

The same operation serves guard operands and roots for later
outputs. It replaces a handle, not an occurrence. Other slots
stay at the same addresses, including slots with equal handles.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRoots

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls footprint CodeApart)
open X86PlacedScalar (Code CompareBranch)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def rootsBase : X86IndexedAddress.Base := ⟨6, by decide⟩
def mapBase : X86IndexedAddress.Base := ⟨7, by decide⟩
def cursorRegister : X86PreparedLea.Index := ⟨1, by decide⟩
def rootRegister : X86PreparedLea.Index := ⟨2, by decide⟩

def emit (start malformed : ℕ) : List ℕ :=
  NativeIndexedWord.loadToCode rootsBase cursorRegister 2 ++
    (NativeDecisions.compareBytes .lessUnsigned 2 15 (start + 11) malformed ++
      (NativeIndexedWord.loadCode mapBase rootRegister ++ NativeIndexedWord.storeCode rootsBase cursorRegister))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 42 := by
  simp only [emit, List.length_append, NativeIndexedWord.load_to_size, NativeDecisions.compare_size,
    NativeIndexedWord.load_size, NativeIndexedWord.store_size]

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 42 ≤ image.size
  root : Code image start (NativeIndexedWord.loadToCode rootsBase cursorRegister 2)
  check : CompareBranch image (start + 11) malformed .lessUnsigned 2 15
  remap : Code image (start + 20) (NativeIndexedWord.loadCode mapBase rootRegister)
  store : Code image (start + 31) (NativeIndexedWord.storeCode rootsBase cursorRegister)

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ) (extent : start + 42 ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start malformed)) :
    Placed image start malformed := by
  obtain ⟨root, rest⟩ := NativeWords.code_append (show Code image start
    (NativeIndexedWord.loadToCode rootsBase cursorRegister 2 ++ _) from code)
  rw [NativeIndexedWord.load_to_size] at rest
  obtain ⟨test, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨map, store⟩ := NativeWords.code_append rest
  rw [NativeIndexedWord.load_size] at store
  exact ⟨extent, root, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short test, map, store⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rdx, .r10, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {rc mc : ℕ} {roots : Region rc} {map : Region mc} {words translated : Array Word}

structure Input (roots : Region rc) (map : Region mc) (words translated : Array Word) (i : ℕ) (before : Native) : Prop where
  operands : MapReady roots words before
  mapping : MapReady map translated before
  roots : lookup before 6 = some (roots.atWord 0)
  map : lookup before 7 = some (map.atWord 0)
  index : lookup before 1 = some (BitVec.ofNat 64 i)
  extent : lookup before 15 = some (BitVec.ofNat 64 translated.size)

def slotBytes (roots : Region rc) (i : Fin rc) : Finset ℕ := footprint ((roots.wordCell i).cell 0).address

theorem mapping_apart (separate : NativeBindingSelection.Separated map roots) (m : Fin mc) (r : Fin rc) :
    Disjoint (footprint ((map.wordCell m).cell 0).address) (slotBytes roots r) :=
  map.separate_arenas roots separate m.val 1 r.val 1 (by decide) (by decide) m.isLt r.isLt (by decide) (by decide) 0 0

theorem fetched_one (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (code : Placed image start malformed)
    (i : Fin words.size) (input : Input roots map words translated i.val before)
    (separate : NativeBindingSelection.Separated map roots)
    (apart : CodeApart image base (slotBytes roots ⟨i.val, i.isLt.trans_le input.operands.fits⟩)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after count, (X86FuelPrefix.fetches count).run before = .ok () after ∧
      match translated[words[i.val].toNat]? with
      | none => count = 4 ∧ X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base malformed)
      | some next => count = 8 ∧ X86StateFrame.Frame clobbers (slotBytes roots ⟨i.val, i.isLt.trans_le input.operands.fits⟩) before after ∧
        MapReady roots (words.set i.val next i.isLt) after ∧ MapReady map translated after ∧ Nonempty (At image after base (start + 42)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let ordinal := BitVec.ofNat 64 i.val
  let root := words[i.val]
  have extent := code.extent
  have indexExact : ordinal.toNat = i.val := NativeSubstitutionReserve.word_of_region roots _ (i.isLt.le.trans input.operands.fits)
  have sizeExact := NativeSubstitutionReserve.word_of_region map translated.size input.mapping.fits
  let slot : Fin rc := ⟨i.val, i.isLt.trans_le input.operands.fits⟩
  have inside : 0 + ordinal.toNat < rc := by rw [Nat.zero_add, indexExact]; exact slot.isLt
  have sameSlot : (⟨0 + ordinal.toNat, inside⟩ : Fin rc) = slot := Fin.ext ((Nat.zero_add _).trans indexExact)
  obtain ⟨a, loaded, loadFrame, original, ⟨atTest⟩⟩ := NativeIndexedWord.fetched_load_to other extra vector point controls
    (by omega) rootsBase cursorRegister 2 (by decide) roots 0 ordinal root inside input.roots input.index
    (by rw [sameSlot]; exact input.operands.read i) code.root
  obtain ⟨b, tested, cmp, ⟨selected⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector atTest .lessUnsigned 2 15 code.check root _ original ((loadFrame.lookup 15 (by decide)).trans input.extent)
  change At image b base (if decide (root.toNat < (BitVec.ofNat 64 translated.size).toNat)
    then start + 20 else malformed) at selected
  rw [sizeExact] at selected
  have beforeMap := loadFrame.trans (X86StateFrame.registerOnly cmp)
  have first := X86FuelPrefix.fetches_then 2 2 before a b loaded tested
  by_cases available : root.toNat < translated.size
  · have usable : At image b base (start + 20) := by simpa [available] using selected
    let new := translated[root.toNat]
    have mapRoom : 0 + root.toNat < mc := by simpa only [Nat.zero_add] using available.trans_le input.mapping.fits
    have mapSlot : (⟨0 + root.toNat, mapRoom⟩ : Fin mc) = ⟨root.toNat, available.trans_le input.mapping.fits⟩ :=
      Fin.ext (Nat.zero_add _)
    obtain ⟨c, remapped, remapFrame, value, ⟨atStore⟩⟩ := NativeIndexedWord.fetched_load other extra vector usable
      (controls.transport beforeMap (by decide)) (by omega) mapBase rootRegister map 0 root new mapRoom
      ((beforeMap.lookup 7 (by decide)).trans input.map) ((cmp.lookup 2 (by decide)).trans original)
      (by rw [mapSlot]; exact (input.mapping.read ⟨root.toNat, available⟩).preserved beforeMap (by simp)) code.remap
    have initialized := beforeMap.trans remapFrame
    obtain ⟨after, stored, writeFrame, readback, endpoint⟩ := NativeIndexedWord.fetched_store other extra vector
      (show At image c base (start + 31) from atStore) (controls.transport initialized (by decide)) (by omega)
      rootsBase cursorRegister roots 0 ordinal new inside ((initialized.lookup 6 (by decide)).trans input.roots)
      ((initialized.lookup 1 (by decide)).trans input.index) value code.store (by rw [sameSlot]; exact apart)
    rw [sameSlot] at writeFrame readback
    have all : X86StateFrame.Frame clobbers (slotBytes roots slot) before after :=
      (initialized.trans writeFrame).mono (by decide) (by
        simp only [Finset.empty_union, slotBytes]
        exact Finset.Subset.refl _)
    let changed := words.set i.val new i.isLt
    have size : changed.size = words.size := Array.size_set _
    have fits : changed.size ≤ rc := size ▸ input.operands.fits
    have wordReady : MapReady roots changed after := by
      refine ⟨fits, fun j => ?_⟩
      by_cases same : j.val = i.val
      · have sameIndex : (⟨j.val, j.isLt.trans_le fits⟩ : Fin rc) = slot := Fin.ext same
        have word : changed[j.val] = new := by simp [changed, same]
        change Reads after ((roots.wordCell ⟨j.val, j.isLt.trans_le fits⟩).cell 0).address changed[j.val]
        rw [sameIndex, word]
        exact readback
      · have lt : j.val < words.size := size ▸ j.isLt
        have word : changed[j.val] = words[j.val] := Array.getElem_set_ne i.isLt lt (Ne.symm same)
        change Reads after ((roots.wordCell ⟨j.val, j.isLt.trans_le fits⟩).cell 0).address changed[j.val]
        rw [word]
        exact (input.operands.read ⟨j.val, lt⟩).preserved all
          (roots.wordCells_disjoint (fun equal => same (congrArg Fin.val equal)))
    have mapReady := input.mapping.kept all (fun m => mapping_apart separate m slot)
    have ran := X86FuelPrefix.fetches_then 6 2 before c after
      (X86FuelPrefix.fetches_then 4 2 before b c first remapped) stored
    refine ⟨after, 8, ran, ?_⟩
    change match translated[root.toNat]? with | none => _ | some _ => _
    rw [Array.getElem?_eq_getElem available]
    exact ⟨rfl, all, wordReady, mapReady, endpoint⟩
  · have noRoot : At image b base malformed := by simpa [available] using selected
    refine ⟨b, 4, first, ?_⟩
    change match translated[root.toNat]? with | none => _ | some _ => _
    rw [Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt available)]
    exact ⟨rfl, beforeMap.mono (by decide) (by simp), ⟨noRoot⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRoots
