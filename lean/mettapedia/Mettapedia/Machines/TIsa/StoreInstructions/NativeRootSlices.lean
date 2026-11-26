import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRootMemory
import Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedMeaning

/-!
# Views of a native root vector

A span of occurrences is addressed within the existing
vector. Neither viewing a span nor selecting a pattern
copies roots, and the view still distinguishes positions
with equal handles. Empty spans need no dummy word.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRootSlices

open Mettapedia.Logic.LP
open NativeArenaGeometry (Region)
open NativeBindingRootMemory (Covered)
open NativeSubstLeaf (MapReady)
open X86PlacedMemory (Reads footprint)
open MemoryBinding (Native)

variable {capacity : ℕ}

def window (region : Region capacity) (offset size : ℕ) (inside : offset + size ≤ capacity) : Region size where
  pointer := region.atWord offset
  aligned := by
    have eight : 8 ∣ 2 ^ 64 := by decide
    have addend : (BitVec.ofNat 64 (8 * offset)).toNat % 8 = 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ eight, Nat.mul_mod_right]
    unfold Region.atWord
    rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ eight, Nat.add_mod, region.aligned, addend]
  area := by
    constructor
    · by_cases empty : size = 0
      · rw [empty, Nat.mul_zero, Nat.add_zero]
        exact (region.atWord offset).isLt.le
      · rw [region.atWord_nat offset (by omega)]
        have limit := region.area.1
        omega
    · intro byte present
      have address : region.atWord offset + BitVec.ofNat 64 byte =
          region.pointer + BitVec.ofNat 64 (8 * offset + byte) := by
        simp only [Region.atWord, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [address]
      exact region.area.2 _ (by omega)

theorem window_address (region : Region capacity) (offset size : ℕ) (inside : offset + size ≤ capacity) (i : Fin size) :
    (((window region offset size inside).wordCell i).cell 0).address =
      ((region.wordCell ⟨offset + i.val, by have := i.isLt; omega⟩).cell 0).address := by
  simp only [Region.wordCell, Region.slice_address, Fin.val_zero, Nat.add_zero]
  change X86CanonicalSpan.narrow (region.atWord offset + BitVec.ofNat 64 (8 * i.val)) = _
  rw [Region.atWord_next]

theorem window_covered (region : Region capacity) (offset size : ℕ) (inside : offset + size ≤ capacity) (i : Fin size) :
    Covered region (footprint (((window region offset size inside).wordCell i).cell 0).address) := by
  rw [window_address]
  exact Covered.word region _

structure View (all : Array Word) where
  pattern : Fin all.size
  offset : ℕ
  count : ℕ
  fits : offset + count ≤ all.size

def View.needle {all : Array Word} (view : View all) : Word := all[view.pattern]

def View.occurrences {all : Array Word} (view : View all) : Array Word := all.extract view.offset (view.offset + view.count)

theorem View.size {all : Array Word} (view : View all) : view.occurrences.size = view.count := by
  have room := view.fits
  simp only [View.occurrences, Array.size_extract, Nat.min_eq_left room]
  omega

theorem View.root_at {all : Array Word} (view : View all) (i : Fin view.count) :
    view.occurrences[i.val]'(view.size.symm ▸ i.isLt) =
      all[view.offset + i.val]'(by have := view.fits; have := i.isLt; omega) := by
  simp only [View.occurrences, Array.getElem_extract]

def View.region {all : Array Word} (view : View all) (rootRegion : Region capacity) (held : all.size ≤ capacity) :
    Region view.count :=
  window rootRegion view.offset view.count (view.fits.trans held)

/-- The occurrence array is borrowed at its native address,
not rematerialized. -/
theorem View.resident {all : Array Word} (view : View all) (rootRegion : Region capacity) {native : Native}
    (held : MapReady rootRegion all native) : MapReady (view.region rootRegion held.fits) view.occurrences native := by
  refine ⟨view.size.le, ?_⟩
  intro i
  have range : i.val < view.count := view.size ▸ i.isLt
  have coordinate : view.offset + i.val < all.size := by have := view.fits; omega
  have read := held.read ⟨view.offset + i.val, coordinate⟩
  change Reads native (((view.region rootRegion held.fits).wordCell ⟨i.val, range⟩).cell 0).address view.occurrences[i.val]
  rw [View.region, window_address, view.root_at ⟨i.val, range⟩]
  exact read

universe u p
variable {σ : LPSignature.{u,u,p,u}}

theorem View.read {all : Array Word} (view : View all) (symbols : UnifierHeaders.Symbols σ)
    (arena : PackedTerms.Arena) (decoded : List (Term σ))
    (reads : PackedRootedMeaning.roots symbols arena all = some decoded) :
    ∃ size : decoded.length = all.size,
      PackedTerms.lookup symbols arena view.needle = some (decoded[view.pattern.val]'(size.symm ▸ view.pattern.isLt)) ∧
      ∀ i : Fin view.occurrences.size, PackedTerms.lookup symbols arena view.occurrences[i.val] =
        some (decoded[view.offset + i.val]'(by
          have placed := view.fits
          have bound : i.val < view.count := by rw [← view.size]; exact i.isLt
          omega)) := by
  obtain ⟨length, coordinates⟩ := PackedOccursPrefix.mapM_coordinates (PackedTerms.lookup symbols arena) all.toList decoded reads
  have size : decoded.length = all.size := by simpa using length
  have exact (i : Fin all.size) : PackedTerms.lookup symbols arena all[i.val] =
      some (decoded[i.val]'(size.symm ▸ i.isLt)) := by
    have read := coordinates i.val
    rwa [Array.getElem?_toList, Array.getElem?_eq_getElem i.isLt, Option.bind_some,
      List.getElem?_eq_getElem (size.symm ▸ i.isLt)] at read
  refine ⟨size, ?_, ?_⟩
  · simpa only [View.needle, Fin.getElem_fin] using exact view.pattern
  · intro i
    have inside : i.val < view.count := view.size ▸ i.isLt
    have offset : view.offset + i.val < all.size := by have := view.fits; omega
    rw [view.root_at ⟨i.val, inside⟩]
    exact exact ⟨_, offset⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRootSlices
