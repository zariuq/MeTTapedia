import Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

/-!
# Identity and composition of the elementary-topos adjunction action

The comparisons retain both actual fibration endpoint maps and their
complete invertible comprehension square. They compare the mapped arrow
presentations without identifying independently chosen image objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open FibrationTwoCategory

universe u v

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

def mapIdentity (source : ElementaryTopos.{max u v,v}) :
    map (𝟙 source) ≅ 𝟙 (object source) :=
  InducedBicategory.isoMk (PseudoTwoArrow.isoMk
    (eqToIso predicateMap_identity) (eqToIso codomainMap_identity) (by
      apply Fibration.Cell.ext
      apply StrictTwoArrow.Cell.ext
      · apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext predicate
        apply Arrow.hom_ext <;>
          simp [map, object, comprehensionMap, predicateMap, codomainMap,
            FibrationAdjunctionTwoCategory.ofElementaryTopos,
            FibrationAdjunctionTwoCategory.imageObject, AdjunctionObject.rightArrow] <;> rfl
      · apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext base
        simp [map, object, comprehensionMap, predicateMap, codomainMap,
          FibrationAdjunctionTwoCategory.ofElementaryTopos,
          FibrationAdjunctionTwoCategory.imageObject, AdjunctionObject.rightArrow]
        rfl))

def mapComposition {source middle target : ElementaryTopos.{max u v,v}}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    map (first ≫ second) ≅ map first ≫ map second :=
  InducedBicategory.isoMk (PseudoTwoArrow.isoMk
    (eqToIso (predicateMap_composition first.functor second.functor))
    (eqToIso (codomainMap_composition first.functor second.functor)) (by
      apply Fibration.Cell.ext
      apply StrictTwoArrow.Cell.ext
      · apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext predicate
        apply Arrow.hom_ext <;>
          simp [map, object, comprehensionMap, predicateMap, codomainMap,
            rightAdjointSquare.vcomp, FibrationAdjunctionTwoCategory.ofElementaryTopos,
            FibrationAdjunctionTwoCategory.imageObject, AdjunctionObject.rightArrow]
        all_goals change 𝟙 _ ≫ second.functor.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
        all_goals simp
      · apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext base
        simp [map, object, comprehensionMap, predicateMap, codomainMap,
          rightAdjointSquare.vcomp, FibrationAdjunctionTwoCategory.ofElementaryTopos,
          FibrationAdjunctionTwoCategory.imageObject, AdjunctionObject.rightArrow]
        rfl))

end Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
