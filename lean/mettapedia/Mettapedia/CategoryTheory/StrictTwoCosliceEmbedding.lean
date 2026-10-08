import Mettapedia.CategoryTheory.StrictTwoArrow

/-!
# The fixed-source inclusion into the strict arrow two-category

The inclusion is a genuine strict pseudofunctor. Its local image consists
exactly of the compatible square two-cells with identity source component.
This identifies the two-dimensional fixed-source boundary without
replacing it by an ordinary comma-category condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.StrictTwoCoslice

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w,v} B] [Bicategory.Strict B] {base : B}

def arrowObject (source : StrictTwoCoslice B base) : StrictTwoArrow B :=
  ⟨base, source.target, source.leg⟩

def arrowMap {source target : StrictTwoCoslice B base} (route : source ⟶ target) :
    arrowObject source ⟶ arrowObject target where
  left := 𝟙 base
  right := route.hom
  comm := route.comm.trans (_root_.CategoryTheory.Category.id_comp target.leg).symm

def arrowCell {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} (change : first ⟶ second) :
    arrowMap first ⟶ arrowMap second where
  left := 𝟙 (𝟙 base)
  right := change.hom
  compatible := change.fixed.trans
    ((congr_arg_heq (fun leg => 𝟙 leg)
      (_root_.CategoryTheory.Category.id_comp target.leg)).symm.trans
      (heq_of_eq (id_whiskerRight (𝟙 base) target.leg)).symm)

def intoArrow : StrictPseudofunctor (StrictTwoCoslice B base) (StrictTwoArrow B) :=
  StrictPseudofunctor.mk'' {
    obj := arrowObject
    map := arrowMap
    map₂ := arrowCell
    map_id _ := rfl
    map_comp _ _ := by
      apply StrictTwoArrow.Hom.ext
      · exact (_root_.CategoryTheory.Category.id_comp (𝟙 base)).symm
      · rfl
    map₂_id _ := rfl
    map₂_comp _ _ := by
      apply StrictTwoArrow.Cell.ext
      · exact (_root_.CategoryTheory.Category.id_comp (𝟙 (𝟙 base))).symm
      · rfl
    map₂_whisker_left := by
      intros; apply StrictTwoArrow.Cell.ext <;> simp [arrowCell, arrowMap]
    map₂_whisker_right := by
      intros; apply StrictTwoArrow.Cell.ext <;> simp [arrowCell, arrowMap] }

instance localFaithful (source target : StrictTwoCoslice B base) :
    (intoArrow.mapFunctor source target).Faithful where
  map_injective same := Cell.ext (congrArg StrictTwoArrow.Cell.right same)

/-- Identity on the source is sufficient as well as necessary for a
compatible square two-cell to descend to the strict coslice. -/
def restrictCell {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target}
    (change : arrowMap first ⟶ arrowMap second) (fixedSource : change.left = 𝟙 (𝟙 base)) :
    first ⟶ second where
  hom := change.right
  fixed := by
    have compatible := change.compatible
    rw [fixedSource] at compatible
    exact compatible.trans
      ((heq_of_eq (id_whiskerRight (𝟙 base) target.leg)).trans
        (congr_arg_heq (fun leg => 𝟙 leg) (_root_.CategoryTheory.Category.id_comp target.leg)))

theorem arrowCell_restrict {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target}
    (change : arrowMap first ⟶ arrowMap second) (fixedSource : change.left = 𝟙 (𝟙 base)) :
    arrowCell (restrictCell change fixedSource) = change := by
  apply StrictTwoArrow.Cell.ext
  · exact fixedSource.symm
  · rfl

theorem image_iff_fixed_source {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} (change : arrowMap first ⟶ arrowMap second) :
    (∃ original : first ⟶ second, arrowCell original = change) ↔
      change.left = 𝟙 (𝟙 base) := by
  constructor
  · rintro ⟨original, same⟩
    rw [← same]
    rfl
  · intro fixed
    exact ⟨restrictCell change fixed, arrowCell_restrict change fixed⟩

theorem unique_restriction {source target : StrictTwoCoslice B base}
    {first second : source ⟶ target} (change : arrowMap first ⟶ arrowMap second)
    (fixedSource : change.left = 𝟙 (𝟙 base)) :
    ∃! original : first ⟶ second, arrowCell original = change := by
  refine ⟨restrictCell change fixedSource, arrowCell_restrict change fixedSource, ?_⟩
  intro original same
  apply Cell.ext
  exact congrArg StrictTwoArrow.Cell.right same

end Mettapedia.CategoryTheory.StrictTwoCoslice
