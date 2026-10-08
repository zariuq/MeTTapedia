import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Complete pullback comparisons of finite-limit functors

The functor between actual slices maps a chosen pullback to another
pullback. Its comparison with the target's choice is the unique complete
pullback isomorphism. Both projection readouts and naturality retain the
original display and base arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.SliceFunctorPullbackComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
variable {D : Type u₂} [Category.{v₂} D] [HasPullbacks D]
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable {X Y : C} (route : X ⟶ Y)

@[reassoc] theorem pullback_first_readout {Z W : C} (base : Z ⟶ W)
    {first second : Over W} (square : first ⟶ second) :
    ((Over.pullback base).map square).left ≫ pullback.fst second.hom base =
      pullback.fst first.hom base ≫ square.left := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_fst _ _ _

@[reassoc] theorem pullback_second_readout {Z W : C} (base : Z ⟶ W)
    {first second : Over W} (square : first ⟶ second) :
    ((Over.pullback base).map square).left ≫ pullback.snd second.hom base =
      pullback.snd first.hom base := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_snd _ _ _

omit [HasPullbacks C] [PreservesFiniteLimits F] in
@[reassoc] theorem mapped_pullback_first {first second : Over Y}
    (square : first ⟶ second) :
    ((Over.pullback (F.map route)).map ((Over.post F).map square)).left ≫
        pullback.fst (F.map second.hom) (F.map route) =
      pullback.fst (F.map first.hom) (F.map route) ≫ F.map square.left := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_fst _ _ _

omit [HasPullbacks C] [PreservesFiniteLimits F] in
@[reassoc] theorem mapped_pullback_second {first second : Over Y}
    (square : first ⟶ second) :
    ((Over.pullback (F.map route)).map ((Over.post F).map square)).left ≫
        pullback.snd (F.map second.hom) (F.map route) =
      pullback.snd (F.map first.hom) (F.map route) := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_snd _ _ _

def component (display : Over Y) :
    (Over.pullback route ⋙ Over.post F).obj display ≅
      (Over.post F ⋙ Over.pullback (F.map route)).obj display :=
  Over.isoMk ((IsPullback.of_hasPullback display.hom route).map F).isoPullback
    ((IsPullback.of_hasPullback display.hom route).map F).isoPullback_hom_snd

@[reassoc (attr := simp)] theorem component_first (display : Over Y) :
    (component F route display).hom.left ≫
      pullback.fst (F.map display.hom) (F.map route) =
    F.map (pullback.fst display.hom route) :=
  ((IsPullback.of_hasPullback display.hom route).map F).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem component_second (display : Over Y) :
    (component F route display).hom.left ≫
      pullback.snd (F.map display.hom) (F.map route) =
    F.map (pullback.snd display.hom route) :=
  ((IsPullback.of_hasPullback display.hom route).map F).isoPullback_hom_snd

def comparison : Over.pullback route ⋙ Over.post F ≅
    Over.post F ⋙ Over.pullback (F.map route) :=
  NatIso.ofComponents (component F route) (by
    intro first second square
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (F.map ((Over.pullback route).map square).left ≫
          (component F route second).hom.left) ≫
          pullback.fst (F.map second.hom) (F.map route) =
        ((component F route first).hom.left ≫
          ((Over.pullback (F.map route)).map ((Over.post F).map square)).left) ≫
          pullback.fst (F.map second.hom) (F.map route)
      calc
        _ = F.map ((Over.pullback route).map square).left ≫
              F.map (pullback.fst second.hom route) := by
          rw [Category.assoc, component_first]
        _ = F.map (((Over.pullback route).map square).left ≫
              pullback.fst second.hom route) := (F.map_comp _ _).symm
        _ = F.map (pullback.fst first.hom route ≫ square.left) := by
          rw [pullback_first_readout]
        _ = F.map (pullback.fst first.hom route) ≫ F.map square.left :=
          F.map_comp _ _
        _ = _ := by
          rw [Category.assoc, mapped_pullback_first,
            ← Category.assoc, component_first]
    · change (F.map ((Over.pullback route).map square).left ≫
          (component F route second).hom.left) ≫
          pullback.snd (F.map second.hom) (F.map route) =
        ((component F route first).hom.left ≫
          ((Over.pullback (F.map route)).map ((Over.post F).map square)).left) ≫
          pullback.snd (F.map second.hom) (F.map route)
      calc
        _ = F.map ((Over.pullback route).map square).left ≫
              F.map (pullback.snd second.hom route) := by
          rw [Category.assoc, component_second]
        _ = F.map (((Over.pullback route).map square).left ≫
              pullback.snd second.hom route) := (F.map_comp _ _).symm
        _ = F.map (pullback.snd first.hom route) := by
          rw [pullback_second_readout]
        _ = _ := by
          rw [Category.assoc, mapped_pullback_second, component_second])

end Mettapedia.CategoryTheory.SliceFunctorPullbackComparison
