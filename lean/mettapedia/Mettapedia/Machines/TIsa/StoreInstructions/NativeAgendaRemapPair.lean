import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionReserve

/-!
# Remapping a pending equation from an initialized native map

Check both original handles against the initialized prefix
before loading either replacement. The two coordinates are
independent: equal handles need not be distinguished, but no
equation occurrence is combined with another.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRemapPair

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch)
open NativeArenaGeometry (Region)
open NativeChildMarkLoop (markBase)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def leftIndex : X86PreparedLea.Index := ⟨1, by decide⟩
def rightIndex : X86PreparedLea.Index := ⟨2, by decide⟩

def emit (start malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 1 15 start malformed ++
    (NativeDecisions.compareBytes .lessUnsigned 2 15 (start + 9) malformed ++
      (NativeIndexedWord.loadToCode markBase leftIndex 1 ++ NativeIndexedWord.loadToCode markBase rightIndex 2))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 40 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, NativeIndexedWord.load_to_size]

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 40 ≤ image.size
  leftBound : CompareBranch image start malformed .lessUnsigned 1 15
  rightBound : CompareBranch image (start + 9) malformed .lessUnsigned 2 15
  leftWord : Code image (start + 18) (NativeIndexedWord.loadToCode markBase leftIndex 1)
  rightWord : Code image (start + 29) (NativeIndexedWord.loadToCode markBase rightIndex 2)

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ) (extent : start + 40 ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start malformed)) :
    Placed image start malformed := by
  obtain ⟨left, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 1 15 start malformed ++ _) from code)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨right, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨loadLeft, loadRight⟩ := NativeWords.code_append rest
  rw [NativeIndexedWord.load_to_size] at loadRight
  exact ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short left,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short right, loadLeft, loadRight⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rcx, .rdx, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity : ℕ} {table : Region capacity} {mapping : Array Word}

structure Input (table : Region capacity) (mapping : Array Word) (left right : Word) (native : Native) : Prop where
  map : MapReady table mapping native
  pointer : lookup native 7 = some (table.atWord 0)
  count : lookup native 15 = some (BitVec.ofNat 64 mapping.size)
  left : lookup native 1 = some left
  right : lookup native 2 = some right

/-- The fetched pair rewrite has a complete run even for a
malformed coordinate. It never writes memory and does not
read any scratch word beyond the initialized map. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start malformed)
    (left right : Word) (input : Input table mapping left right before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      match PackedSubstitution.mappedPair mapping (left, right) with
      | none => (steps = 2 ∨ steps = 4) ∧ Nonempty (At image after base malformed)
      | some (l, r) => steps = 8 ∧ lookup after 1 = some l ∧ lookup after 2 = some r ∧
          Nonempty (At image after base (start + 40)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have exactCount := NativeSubstitutionReserve.word_of_region table mapping.size input.map.fits
  obtain ⟨a, first, checkLeft, ⟨atLeft⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector point .lessUnsigned 1 15 placed.leftBound left _ input.left input.count
  change At image a base (if decide (left.toNat < (BitVec.ofNat 64 mapping.size).toNat)
    then start + 9 else malformed) at atLeft
  rw [exactCount] at atLeft
  by_cases leftIn : left.toNat < mapping.size
  · have next : At image a base (start + 9) := by simpa [leftIn] using atLeft
    obtain ⟨b, second, checkRight, ⟨atRight⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector next .lessUnsigned 2 15 placed.rightBound right _
      ((checkLeft.lookup 2 (by decide)).trans input.right) ((checkLeft.lookup 15 (by decide)).trans input.count)
    change At image b base (if decide (right.toNat < (BitVec.ofNat 64 mapping.size).toNat)
      then start + 18 else malformed) at atRight
    rw [exactCount] at atRight
    have checked := X86FuelPrefix.fetches_then 2 2 before a b first second
    have registers := X86StateFrame.registerOnly (checkLeft.trans checkRight)
    by_cases rightIn : right.toNat < mapping.size
    · have data : At image b base (start + 18) := by simpa [rightIn] using atRight
      have lslot : 0 + left.toNat < capacity := by simpa only [Nat.zero_add] using leftIn.trans_le input.map.fits
      have rslot : 0 + right.toNat < capacity := by simpa only [Nat.zero_add] using rightIn.trans_le input.map.fits
      have leftSlot : (⟨0 + left.toNat, lslot⟩ : Fin capacity) =
          ⟨left.toNat, leftIn.trans_le input.map.fits⟩ := Fin.ext (Nat.zero_add _)
      have rightSlot : (⟨0 + right.toNat, rslot⟩ : Fin capacity) =
          ⟨right.toNat, rightIn.trans_le input.map.fits⟩ := Fin.ext (Nat.zero_add _)
      have lread := (input.map.read ⟨left.toNat, leftIn⟩).preserved registers (by simp)
      have rread := (input.map.read ⟨right.toNat, rightIn⟩).preserved registers (by simp)
      obtain ⟨c, loadLeft, fetchedLeft, valueLeft, ⟨atSecondLoad⟩⟩ := NativeIndexedWord.fetched_load_to
        other extra vector data (controls.transport registers (by decide)) (by omega)
        markBase leftIndex 1 (by decide) table 0 left mapping[left.toNat] lslot
        ((registers.lookup 7 (by decide)).trans input.pointer) ((registers.lookup 1 (by decide)).trans input.left)
        (by rw [leftSlot]; exact lread) placed.leftWord
      have soFar := registers.trans fetchedLeft
      obtain ⟨after, loadRight, fetchedRight, valueRight, endpoint⟩ := NativeIndexedWord.fetched_load_to
        other extra vector (show At image c base (start + 29) from atSecondLoad)
        (controls.transport soFar (by decide)) (by omega) markBase rightIndex 2 (by decide)
        table 0 right mapping[right.toNat] rslot ((soFar.lookup 7 (by decide)).trans input.pointer)
        ((soFar.lookup 2 (by decide)).trans input.right)
        (by rw [rightSlot]; exact rread.preserved fetchedLeft (by simp)) placed.rightWord
      have ran := X86FuelPrefix.fetches_then 6 2 before c after (X86FuelPrefix.fetches_then 4 2 before b c checked loadLeft) loadRight
      refine ⟨after, 8, ran, (soFar.trans fetchedRight).mono (by decide) (by simp), ?_⟩
      simp only [PackedSubstitution.mappedPair, Array.getElem?_eq_getElem leftIn, Array.getElem?_eq_getElem rightIn,
        Option.bind_some, Option.map_some]
      exact ⟨by trivial, (fetchedRight.lookup 1 (by decide)).trans valueLeft, valueRight, endpoint⟩
    · have halt : At image b base malformed := by simpa [rightIn] using atRight
      refine ⟨b, 4, checked, registers.mono (by decide) (Finset.Subset.refl _), ?_⟩
      simp only [PackedSubstitution.mappedPair, Array.getElem?_eq_getElem leftIn,
        Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt rightIn), Option.bind_some, Option.map_none]
      exact ⟨Or.inr (by trivial), ⟨halt⟩⟩
  · have halt : At image a base malformed := by simpa [leftIn] using atLeft
    refine ⟨a, 2, first, (X86StateFrame.registerOnly checkLeft).mono (by decide) (Finset.Subset.refl _), ?_⟩
    simp only [PackedSubstitution.mappedPair, Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt leftIn), Option.bind_none]
    exact ⟨Or.inl (by trivial), ⟨halt⟩⟩

namespace Examples

theorem lookups_preserve_the_pair_order :
    PackedSubstitution.mappedPair #[4, 5] (1, 0) = some (5, 4) := by decide +kernel

theorem a_mapped_left_does_not_license_a_missing_right :
    PackedSubstitution.mappedPair #[4, 5] (1, 2) = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRemapPair
