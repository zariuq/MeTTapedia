import Mettapedia.Data.List.FirstSelection

/-! First selection commutes with a representation map and an appended older
suffix when that map preserves the selection or replacement operation. -/

set_option autoImplicit false

namespace List.FirstSelection

universe u v
variable {α : Type u} {β : Type v}

theorem After.map_append {selected : α → Bool} {target : β → Bool} (map : α → β)
    (compatible : ∀ value, target (map value) = selected value)
    {source suffix : List α} (found : After selected source suffix) (older : List β) :
    After target (source.map map ++ older) (suffix.map map ++ older) := by
  induction found with
  | here chosen => exact .here ((compatible _).trans chosen)
  | skip missed found ih => exact .skip ((compatible _).trans missed) ih

theorem Change.map_append {replace : α → Option α} {target : β → Option β} (map : α → β)
    (compatible : ∀ value, target (map value) = (replace value).map map)
    {source changed : List α} (found : Change replace source changed) (older : List β) :
    Change target (source.map map ++ older) (changed.map map ++ older) := by
  induction found with
  | here replaced =>
      apply Change.here
      rw [compatible,replaced]
      rfl
  | skip missed found ih =>
      apply Change.skip _ ih
      rw [compatible,missed]
      rfl

end List.FirstSelection
