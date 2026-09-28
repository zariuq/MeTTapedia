import Mettapedia.GSLT.Topos.PresheafEventModalities
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Newly available events and internal universal modalities

The base has stages ordered by natural numbers. A directed event from false
to true is available at every positive stage and absent at zero. Thus a
pointwise assertion at stage zero can fail after restriction. The internal
box correctly quantifies over that future event already at stage zero.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafEventModalities.Controls

open CategoryTheory
open ConstructivePresheaf
open scoped ConstructivePresheaf

def vertices : ℕ ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id

def eventSections : ℕ ⥤ Type where
  obj n := PLift (0 < n)
  map arrow := TypeCat.ofHom (fun event => ⟨Nat.lt_of_lt_of_le event.down (leOfHom arrow)⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event
    rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event
    rfl

def growing : EventGraph ℕ where
  vertex := vertices
  edge := eventSections
  source :=
    { app _ := TypeCat.ofHom (fun _ => false)
      naturality _ _ _ := rfl }
  target :=
    { app _ := TypeCat.ofHom (fun _ => true)
      naturality _ _ _ := rfl }

theorem pointwise_box_at_zero :
    ∀ event : growing.edge.obj 0, growing.target.app 0 event = true →
      growing.source.app 0 event ∈ (⊥ : Subfunctor growing.vertex).obj 0 := by
  intro event
  exact (Nat.not_lt_zero 0 event.down).elim

/-- The newly available event invalidates the internal box at the earlier stage. -/
theorem internal_box_rejects_zero :
    true ∉ (box growing (⊥ : Subfunctor growing.vertex)).obj 0 := by
  intro holds
  exact holds 1 (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)) ⟨by decide⟩ rfl

theorem new_event_diamond :
    false ∈ (diamond growing (⊤ : Subfunctor growing.vertex)).obj 1 :=
  ⟨⟨by decide⟩, trivial, rfl⟩

theorem opposite_orientation_not_diamond :
    true ∉ (diamond growing (⊤ : Subfunctor growing.vertex)).obj 1 := by
  rintro ⟨event, _, same⟩
  cases same

theorem no_event_diamond_at_zero :
    false ∉ (diamond growing (⊤ : Subfunctor growing.vertex)).obj 0 := by
  rintro ⟨event, _, _⟩
  exact Nat.not_lt_zero 0 event.down

end Mettapedia.GSLT.Topos.PresheafEventModalities.Controls
