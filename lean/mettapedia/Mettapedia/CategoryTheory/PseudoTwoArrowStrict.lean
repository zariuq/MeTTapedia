import Mettapedia.CategoryTheory.AdjunctionTwoCategory
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Strictness of invertibly commuting arrow squares

Equality of the endpoint maps determines a square only when its complete
comparison cube uses the corresponding equality two-cells. The actual
unitors and associator provide those cubes when the ambient bicategory
is strict. Their comparison isomorphisms are therefore retained in the
proof of strictness, rather than discarded from the square data.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u
variable {B : Type u} [Bicategory.{w,v} B]

namespace PseudoTwoArrow

/-- The full cube with canonical endpoint cells forces equality of the
stored invertible square comparisons. -/
theorem Hom.ext_of_canonicalCell {source target : PseudoTwoArrow B}
    {first second : source ⟶ target}
    (left : first.left = second.left) (right : first.right = second.right)
    (cube : source.arrow ◁ eqToHom right ≫ second.comm.hom =
      first.comm.hom ≫ eqToHom left ▷ target.arrow) : first = second := by
  cases first with
  | mk firstLeft firstRight firstComm =>
    cases second with
    | mk secondLeft secondRight secondComm =>
      dsimp only at left right
      cases left
      cases right
      have same : secondComm.hom = firstComm.hom := by
        simpa only [eqToHom_refl, whiskerLeft_id, id_whiskerRight,
          Category.id_comp, Category.comp_id] using cube
      have comparisons : firstComm = secondComm := Iso.ext same.symm
      cases comparisons
      rfl

/-- A supplied actual square cell can witness equality when both of its
endpoint components are the canonical cells of the supplied equalities. -/
theorem Hom.ext_of_cell {source target : PseudoTwoArrow B}
    {first second : source ⟶ target}
    (left : first.left = second.left) (right : first.right = second.right)
    (change : first ⟶ second)
    (leftCell : change.left = eqToHom left)
    (rightCell : change.right = eqToHom right) : first = second := by
  apply Hom.ext_of_canonicalCell left right
  simpa only [leftCell, rightCell] using change.compatible

@[simp] theorem eqToHom_left {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same).left = eqToHom (congrArg Hom.left same) := by cases same; rfl

@[simp] theorem eqToHom_right {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} (same : first = second) :
    (eqToHom same).right = eqToHom (congrArg Hom.right same) := by cases same; rfl

variable [Bicategory.Strict B]

theorem id_comp_hom {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    𝟙 source ≫ route = route := by
  apply Hom.ext_of_cell (Bicategory.Strict.id_comp route.left)
    (Bicategory.Strict.id_comp route.right) (leftUnitor route).hom
  · change (λ_ route.left).hom = _
    rw [Bicategory.Strict.leftUnitor_eqToIso]
    rfl
  · change (λ_ route.right).hom = _
    rw [Bicategory.Strict.leftUnitor_eqToIso]
    rfl

theorem comp_id_hom {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    route ≫ 𝟙 target = route := by
  apply Hom.ext_of_cell (Bicategory.Strict.comp_id route.left)
    (Bicategory.Strict.comp_id route.right) (rightUnitor route).hom
  · change (ρ_ route.left).hom = _
    rw [Bicategory.Strict.rightUnitor_eqToIso]
    rfl
  · change (ρ_ route.right).hom = _
    rw [Bicategory.Strict.rightUnitor_eqToIso]
    rfl

theorem assoc_hom {first second third fourth : PseudoTwoArrow B}
    (earlier : first ⟶ second) (middle : second ⟶ third) (later : third ⟶ fourth) :
    (earlier ≫ middle) ≫ later = earlier ≫ (middle ≫ later) := by
  apply Hom.ext_of_cell (Bicategory.Strict.assoc earlier.left middle.left later.left)
    (Bicategory.Strict.assoc earlier.right middle.right later.right)
    (associator earlier middle later).hom
  · change (α_ earlier.left middle.left later.left).hom = _
    rw [Bicategory.Strict.associator_eqToIso]
    rfl
  · change (α_ earlier.right middle.right later.right).hom = _
    rw [Bicategory.Strict.associator_eqToIso]
    rfl

instance strict : Bicategory.Strict (PseudoTwoArrow B) where
  id_comp := id_comp_hom
  comp_id := comp_id_hom
  assoc := assoc_hom
  leftUnitor_eqToIso route := by
    apply Iso.ext
    apply Cell.ext
    · change (λ_ route.left).hom = (eqToHom (id_comp_hom route)).left
      rw [eqToHom_left, Bicategory.Strict.leftUnitor_eqToIso]
      rfl
    · change (λ_ route.right).hom = (eqToHom (id_comp_hom route)).right
      rw [eqToHom_right, Bicategory.Strict.leftUnitor_eqToIso]
      rfl
  rightUnitor_eqToIso route := by
    apply Iso.ext
    apply Cell.ext
    · change (ρ_ route.left).hom = (eqToHom (comp_id_hom route)).left
      rw [eqToHom_left, Bicategory.Strict.rightUnitor_eqToIso]
      rfl
    · change (ρ_ route.right).hom = (eqToHom (comp_id_hom route)).right
      rw [eqToHom_right, Bicategory.Strict.rightUnitor_eqToIso]
      rfl
  associator_eqToIso earlier middle later := by
    apply Iso.ext
    apply Cell.ext
    · change (α_ earlier.left middle.left later.left).hom =
        (eqToHom (assoc_hom earlier middle later)).left
      rw [eqToHom_left, Bicategory.Strict.associator_eqToIso]
      rfl
    · change (α_ earlier.right middle.right later.right).hom =
        (eqToHom (assoc_hom earlier middle later)).right
      rw [eqToHom_right, Bicategory.Strict.associator_eqToIso]
      rfl

end PseudoTwoArrow

namespace AdjunctionTwoCategory

/-- The actual induced adjunction-object bicategory inherits the earned
strict arrow-square structure. -/
instance strict [Bicategory.Strict B] : Bicategory.Strict (AdjunctionTwoCategory B) :=
  inferInstanceAs (Bicategory.Strict
    (InducedBicategory (PseudoTwoArrow B) (AdjunctionObject.rightArrow (B := B))))

end AdjunctionTwoCategory
end Mettapedia.CategoryTheory
