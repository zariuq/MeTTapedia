import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# Total projection values outside the ordered-pair image

The component-collecting definitions return the empty set when no ordered
pair has the supplied representation. The pair computation laws retain
their usual values on the image.
-/

namespace Mettapedia.SetTheory.ZFSetOrderedPair
universe u

theorem first_of_not_pair (point : ZFSet.{u}) (absent : ¬ ∃ left right, point = ZFSet.pair left right) :
    first point = ∅ := by
  apply ZFSet.ext
  intro value
  rw [first,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨left,present,_⟩
    obtain ⟨right,equal⟩ := (ZFSet.mem_sep.mp present).2
    exact False.elim (absent ⟨left,right,equal⟩)
  · intro present
    exact False.elim (ZFSet.notMem_empty _ present)

theorem second_of_not_pair (point : ZFSet.{u}) (absent : ¬ ∃ left right, point = ZFSet.pair left right) :
    second point = ∅ := by
  apply ZFSet.ext
  intro value
  rw [second,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨right,present,_⟩
    obtain ⟨left,equal⟩ := (ZFSet.mem_sep.mp present).2
    exact False.elim (absent ⟨left,right,equal⟩)
  · intro present
    exact False.elim (ZFSet.notMem_empty _ present)

end Mettapedia.SetTheory.ZFSetOrderedPair
