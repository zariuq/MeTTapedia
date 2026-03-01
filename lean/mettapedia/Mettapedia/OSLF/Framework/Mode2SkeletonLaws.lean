import Mettapedia.OSLF.Framework.Mode2Skeleton

/-!
# Mode2SkeletonLaws

Bundled algebraic laws for `Mode2Skeleton.ModeHom`, paralleling
`LanguageEqCategoryLaws` and restricted to currently proved structure.
-/

namespace Mettapedia.OSLF.Framework.Mode2SkeletonLaws

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.Mode2Skeleton

/-- Bundled mode-skeleton laws over `ModeHom`. -/
structure ModeHomLaws where
  left_id :
    ∀ {X Y : ModeObj} (f : ModeHom X Y),
      (ModeHom.id (X := X)) ≫ f = f
  right_id :
    ∀ {X Y : ModeObj} (f : ModeHom X Y),
      f ≫ (ModeHom.id (X := Y)) = f
  assoc :
    ∀ {W X Y Z : ModeObj}
      (f : ModeHom W X) (g : ModeHom X Y) (h : ModeHom Y Z),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)
  mapPred_id :
    ∀ (X : ModeObj) (ψ : Pattern → Prop),
      ModeHom.mapPred (ModeHom.id (X := X)) ψ = ψ
  mapPred_comp :
    ∀ {X Y Z : ModeObj}
      (f : ModeHom X Y) (g : ModeHom Y Z)
      (ψ : Pattern → Prop),
      ModeHom.mapPred (f ≫ g) ψ =
        ModeHom.mapPred f (ModeHom.mapPred g ψ)

/-- Canonical bundled laws for `Mode2Skeleton.ModeHom`. -/
theorem mode2SkeletonLaws : ModeHomLaws where
  left_id := by
    intro X Y f
    exact ModeHom.comp_id_left f
  right_id := by
    intro X Y f
    exact ModeHom.comp_id_right f
  assoc := by
    intro W X Y Z f g h
    exact ModeHom.comp_assoc f g h
  mapPred_id := by
    intro X ψ
    exact ModeHom.mapPred_id X ψ
  mapPred_comp := by
    intro X Y Z f g ψ
    exact ModeHom.mapPred_comp f g ψ

/-- Access theorem: left identity. -/
theorem left_id_holds
    {X Y : ModeObj} (f : ModeHom X Y) :
    (ModeHom.id (X := X)) ≫ f = f :=
  mode2SkeletonLaws.left_id f

/-- Access theorem: right identity. -/
theorem right_id_holds
    {X Y : ModeObj} (f : ModeHom X Y) :
    f ≫ (ModeHom.id (X := Y)) = f :=
  mode2SkeletonLaws.right_id f

/-- Access theorem: associativity. -/
theorem assoc_holds
    {W X Y Z : ModeObj}
    (f : ModeHom W X) (g : ModeHom X Y) (h : ModeHom Y Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  mode2SkeletonLaws.assoc f g h

/-- Access theorem: identity law for predicate pullback. -/
theorem mapPred_id_holds
    (X : ModeObj) (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.id (X := X)) ψ = ψ :=
  mode2SkeletonLaws.mapPred_id X ψ

/-- Access theorem: composition law for predicate pullback. -/
theorem mapPred_comp_holds
    {X Y Z : ModeObj}
    (f : ModeHom X Y) (g : ModeHom Y Z)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (f ≫ g) ψ =
      ModeHom.mapPred f (ModeHom.mapPred g ψ) :=
  mode2SkeletonLaws.mapPred_comp f g ψ

end Mettapedia.OSLF.Framework.Mode2SkeletonLaws

