import Mettapedia.CategoryTheory.FibrationTwoCategory

/-!
# Complete fibration cells into a faithful projection

A compatible cell into a faithful target projection is determined by its
base component. The proof uses the complete total/base compatibility cube
and the actual faithfulness of the target projection at each component.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.FibrationTwoCategory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe u v

theorem cell_ext_of_base {source target : Fibration.{u,v}}
    [target.functor.Faithful] {first second : source ⟶ target}
    {earlier later : first ⟶ second} (same : earlier.hom.right = later.hom.right) :
    earlier = later := by
  have whiskered : earlier.hom.left ▷ target.projection.arrow =
      later.hom.left ▷ target.projection.arrow :=
    eq_of_heq (earlier.hom.compatible.symm.trans
      ((heq_of_eq (congrArg (fun component => source.projection.arrow ◁ component) same)).trans
        later.hom.compatible))
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext
  · apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    apply target.functor.map_injective
    exact congrArg (fun component => component.toNatTrans.app object) whiskered
  · exact same

end Mettapedia.CategoryTheory.FibrationTwoCategory
