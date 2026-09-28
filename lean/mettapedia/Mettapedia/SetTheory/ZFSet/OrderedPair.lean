import Mathlib.SetTheory.ZFC.Basic

/-!
# Projections of Kuratowski pairs

The projections collect the corresponding components and take their union.
They are defined on all sets; the computation laws apply to actual pairs.
No ambient carrier or choice of a dependent-pair type is needed.
-/

namespace Mettapedia.SetTheory.ZFSetOrderedPair

universe u

noncomputable def first (p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sep (fun x => ∃ y, p = ZFSet.pair x y) (ZFSet.sUnion p))

noncomputable def second (p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sep (fun y => ∃ x, p = ZFSet.pair x y) (ZFSet.sUnion p))

theorem first_pair (x y : ZFSet.{u}) : first (ZFSet.pair x y) = x := by
  ext z
  rw [first, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨a, member, inside⟩
    obtain ⟨b, equal⟩ := (ZFSet.mem_sep.mp member).2
    simpa only [(ZFSet.pair_inj.mp equal).1] using inside
  · intro inside
    exact ⟨x, ZFSet.mem_sep.mpr ⟨by simp [ZFSet.pair], y, rfl⟩, inside⟩

theorem second_pair (x y : ZFSet.{u}) : second (ZFSet.pair x y) = y := by
  ext z
  rw [second, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨b, member, inside⟩
    obtain ⟨a, equal⟩ := (ZFSet.mem_sep.mp member).2
    simpa only [(ZFSet.pair_inj.mp equal).2] using inside
  · intro inside
    exact ⟨y, ZFSet.mem_sep.mpr ⟨by simp [ZFSet.pair], x, rfl⟩, inside⟩

/-- The second projection is sensitive to its second component even when
the first component is fixed. -/
theorem second_pair_not_constant :
    second (ZFSet.pair (∅ : ZFSet.{u}) ∅) ≠
      second (ZFSet.pair (∅ : ZFSet.{u}) {∅}) := by
  rw [second_pair, second_pair]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

theorem pair_first_second {p : ZFSet.{u}} (paired : ∃ x y, p = ZFSet.pair x y) :
    ZFSet.pair (first p) (second p) = p := by
  obtain ⟨x, y, rfl⟩ := paired
  rw [first_pair, second_pair]

#print axioms second_pair_not_constant

end Mettapedia.SetTheory.ZFSetOrderedPair
