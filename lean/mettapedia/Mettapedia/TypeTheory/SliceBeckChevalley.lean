import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Dependent-sum base change in slice categories

Pullback pasting identifies substitution followed by dependent sum with
dependent sum followed by substitution. This is a natural isomorphism
for every pullback square in any category with pullbacks. Both projection
laws specify the comparison, including the map on retained witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SliceBeckChevalley

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B D E : C} {top : D ⟶ A} {left : D ⟶ E}
variable {right : A ⟶ B} {bottom : E ⟶ B}

/-- The component of dependent-sum base change is the canonical
isomorphism obtained by pasting the given pullback with a slice pullback. -/
noncomputable def sigmaBaseChangeComponent
    (square : IsPullback top left right bottom) (X : Over A) :
    ((Over.pullback top) ⋙ Over.map left).obj X ≅
      (Over.map right ⋙ Over.pullback bottom).obj X :=
  Over.isoMk ((IsPullback.of_hasPullback X.hom top).paste_vert square).isoPullback
    ((IsPullback.of_hasPullback X.hom top).paste_vert square).isoPullback_hom_snd

@[reassoc (attr := simp)] theorem sigmaBaseChangeComponent_fst
    (square : IsPullback top left right bottom) (X : Over A) :
    (sigmaBaseChangeComponent square X).hom.left ≫
        pullback.fst (X.hom ≫ right) bottom = pullback.fst X.hom top :=
  ((IsPullback.of_hasPullback X.hom top).paste_vert square).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem sigmaBaseChangeComponent_snd
    (square : IsPullback top left right bottom) (X : Over A) :
    (sigmaBaseChangeComponent square X).hom.left ≫
        pullback.snd (X.hom ≫ right) bottom = pullback.snd X.hom top ≫ left :=
  ((IsPullback.of_hasPullback X.hom top).paste_vert square).isoPullback_hom_snd

set_option backward.isDefEq.respectTransparency false in
/-- Dependent sums commute with substitution around any pullback square,
naturally in both the slice object and its maps. -/
noncomputable def sigmaBaseChange
    (square : IsPullback top left right bottom) :
    Over.pullback top ⋙ Over.map left ≅
      Over.map right ⋙ Over.pullback bottom := by
  refine NatIso.ofComponents (sigmaBaseChangeComponent square) ?_
  intro X Y k
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change
      (((Over.pullback top).map k).left ≫
        (sigmaBaseChangeComponent square Y).hom.left) ≫ _ =
      ((sigmaBaseChangeComponent square X).hom.left ≫
        ((Over.pullback bottom).map ((Over.map right).map k)).left) ≫ _
    simp only [Category.assoc, Over.map_obj_hom, sigmaBaseChangeComponent_fst,
      Over.pullback_map_left, Over.map_map_left, pullback.lift_fst]
    rw [← Category.assoc, sigmaBaseChangeComponent_fst]
  · change
      (((Over.pullback top).map k).left ≫
        (sigmaBaseChangeComponent square Y).hom.left) ≫ _ =
      ((sigmaBaseChangeComponent square X).hom.left ≫
        ((Over.pullback bottom).map ((Over.map right).map k)).left) ≫ _
    simp only [Category.assoc, Over.map_obj_hom, sigmaBaseChangeComponent_snd,
      Over.pullback_map_left, pullback.lift_snd, pullback.lift_snd_assoc]

end Mettapedia.TypeTheory.SliceBeckChevalley
