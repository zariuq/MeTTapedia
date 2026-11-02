import Mettapedia.OSLF.Syntax.BindingScopeEqualizer
import Mettapedia.OSLF.Syntax.BindingContextRows
import Mathlib.Data.Finset.Sort

/-!
# Computing the parameter positions fixed by two context maps

The retained table contains exactly the source positions with equal ambient
images. Recovery, inclusion and the inverse position law use the common typed
declaration-table operations. The set of sorts need not be decidable or finite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopeEqualizer.Finite

open ContextPositions

variable {S : Signature} {Δ Γ : Ctx S} (left right : Ren S Δ Γ)

abbrev Slot := { slot : Fin Δ.length //
  CommonABT.index (left _ (ofSlot Δ slot)) = CommonABT.index (right _ (ofSlot Δ slot)) }

instance : Fintype (Slot left right) := inferInstanceAs (Fintype (Subtype _))

def rows : List (Slot left right) := Finset.univ.sort (· ≤ ·)
theorem rows_distinct : (rows left right).Nodup := Finset.sort_nodup _ _
theorem slot_mem (slot : Slot left right) : slot ∈ rows left right := by simp [rows]

abbrev sortOf (slot : Slot left right) : S.Srt := Δ.get slot.val
def value (slot : Slot left right) : Var Δ (sortOf left right slot) := ofSlot Δ slot.val

theorem values_agree (slot : Slot left right) : left _ (value left right slot) = right _ (value left right slot) :=
  CommonABT.index_injective slot.property

abbrev fromVariable {sort : S.Srt} (position : Var Δ sort)
    (same : left sort position = right sort position) : Slot left right :=
  ⟨toSlot position, (map_index_ofSlot left position).trans
    ((congrArg (CommonABT.index (S := S)) same).trans (map_index_ofSlot right position).symm)⟩

abbrev context : Ctx S := ContextRows.context (sortOf left right) (rows left right)

def inclusion : Ren S (context left right) Δ :=
  ContextRows.project (sortOf left right) (rows left right) (value left right)

theorem commutes (sort : S.Srt) (position : Var (context left right) sort) :
    left sort (inclusion left right sort position) = right sort (inclusion left right sort position) := by
  let row := ContextRows.rowAt (sortOf left right) (rows left right) position
  let recorded := ContextRows.rowSort (sortOf left right) (rows left right) position
  change left sort (castSort recorded (value left right row)) =
    right sort (castSort recorded (value left right row))
  rw [map_castSort (S := S) left recorded, map_castSort (S := S) right recorded]
  exact congrArg (castSort recorded) (values_agree left right row)

def recover (sort : S.Srt) (position : Var Δ sort) (same : left sort position = right sort position) :
    Var (context left right) sort :=
  castSort (slot_sort position)
    (ContextRows.select (sortOf left right) (rows left right) (fromVariable left right position same)
      (slot_mem left right _))

theorem recover_inclusion (sort : S.Srt) (position : Var Δ sort)
    (same : left sort position = right sort position) :
    inclusion left right sort (recover left right sort position same) = position := by
  let slot := fromVariable left right position same
  have selected := ContextRows.project_select (sortOf left right) (rows left right) (value left right)
    slot (slot_mem left right slot)
  have lifted := map_castSort_heq (S := S) (inclusion left right) (slot_sort position)
    (ContextRows.select (sortOf left right) (rows left right) slot (slot_mem left right slot))
  exact eq_of_heq (lifted.trans (selected.heq.trans (ofSlot_toSlot_heq position)))

theorem from_projected {sort : S.Srt} (position : Var (context left right) sort)
    (same : left sort (inclusion left right sort position) = right sort (inclusion left right sort position)) :
    fromVariable left right (inclusion left right sort position) same =
      ContextRows.rowAt (sortOf left right) (rows left right) position := by
  apply Subtype.ext
  apply Fin.ext
  change CommonABT.index (inclusion left right sort position) = _
  rw [inclusion, ContextRows.index_project]
  exact index_ofSlot _ _

theorem recover_pair (sort : S.Srt) (position : Var (context left right) sort)
    (same : left sort (inclusion left right sort position) = right sort (inclusion left right sort position)) :
    recover left right sort (inclusion left right sort position) same = position := by
  apply CommonABT.index_injective (S := S)
  have indexRecovered := index_castSort (S := S) (slot_sort (inclusion left right sort position))
    (ContextRows.select (sortOf left right) (rows left right)
      (fromVariable left right (inclusion left right sort position) same) (slot_mem left right _))
  change CommonABT.index (castSort _ _) = _
  rw [indexRecovered, ContextRows.index_select, from_projected]
  have restored := ContextRows.index_select_rowAt (sortOf left right) (rows left right)
    (rows_distinct left right) position
  simpa only [ContextRows.index_select] using restored

def build : Mettapedia.OSLF.Binding.ScopeEqualizer left right where
  context := context left right
  inclusion := inclusion left right
  commutes := commutes left right
  recover := recover left right
  recover_inclusion := recover_inclusion left right
  recover_pair := fun sort position => recover_pair left right sort position (commutes left right sort position)

end Mettapedia.OSLF.Binding.ScopeEqualizer.Finite
