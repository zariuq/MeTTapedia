import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coherent canonical substitution on slice categories

The unit and composition comparisons are fixed by the projections of the
actual chosen pullbacks. Naturality, the two unit triangles and the
associative pasting equation are proved by their pullback universal
properties. No strict equality of chosen pullback objects is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CanonicalSlicePullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]

def identityComponent {base : C} (object : Over base) :
    (Over.pullback (𝟙 base)).obj object ≅ object :=
  Over.isoMk (IsPullback.of_id_fst (f := object.hom)).isoPullback.symm
    (IsPullback.of_id_fst (f := object.hom)).isoPullback_inv_snd

@[simp] theorem identityComponent_left {base : C} (object : Over base) :
    (identityComponent object).hom.left = pullback.fst object.hom (𝟙 base) := by
  have readout := (IsPullback.of_id_fst (f := object.hom)).isoPullback_inv_fst
  change (IsPullback.of_id_fst (f := object.hom)).isoPullback.inv = _
  simpa only [Category.comp_id] using readout

def identity (base : C) : Over.pullback (𝟙 base) ≅ 𝟭 (Over base) :=
  NatIso.ofComponents identityComponent (by
    intro first second arrow
    apply Over.OverMorphism.ext
    simp [Over.pullback_map_left])

variable {first middle last : C} (f : first ⟶ middle) (g : middle ⟶ last)

theorem compositionSquare (object : Over last) :
    IsPullback
      (pullback.fst (pullback.snd object.hom g) f ≫ pullback.fst object.hom g)
      (pullback.snd (pullback.snd object.hom g) f) object.hom (f ≫ g) :=
  (IsPullback.of_hasPullback (pullback.snd object.hom g) f).paste_horiz
    (IsPullback.of_hasPullback object.hom g)

def compositionInverseComponent (object : Over last) :
    (Over.pullback g ⋙ Over.pullback f).obj object ≅ (Over.pullback (f ≫ g)).obj object :=
  Over.isoMk (compositionSquare f g object).isoPullback
    (compositionSquare f g object).isoPullback_hom_snd

@[reassoc (attr := simp)] theorem compositionInverseComponent_fst (object : Over last) :
    (compositionInverseComponent f g object).hom.left ≫ pullback.fst object.hom (f ≫ g) =
      pullback.fst (pullback.snd object.hom g) f ≫ pullback.fst object.hom g :=
  (compositionSquare f g object).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem compositionInverseComponent_snd (object : Over last) :
    (compositionInverseComponent f g object).hom.left ≫ pullback.snd object.hom (f ≫ g) =
      pullback.snd (pullback.snd object.hom g) f :=
  (compositionSquare f g object).isoPullback_hom_snd

def compositionInverse : Over.pullback g ⋙ Over.pullback f ≅ Over.pullback (f ≫ g) :=
  NatIso.ofComponents (compositionInverseComponent f g) (by
    intro earlier later arrow
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [Over.pullback_map_left]
    · simp [Over.pullback_map_left])

def composition : Over.pullback (f ≫ g) ≅ Over.pullback g ⋙ Over.pullback f :=
  (compositionInverse f g).symm

def transport {source target : C} {earlier later : source ⟶ target} (same : earlier = later) :
    Over.pullback earlier ≅ Over.pullback later :=
  eqToIso (congrArg (fun route : source ⟶ target => Over.pullback route) same)

@[reassoc (attr := simp)] theorem transport_fst {source target : C}
    {earlier later : source ⟶ target} (same : earlier = later) (object : Over target) :
    ((transport same).hom.app object).left ≫ pullback.fst object.hom later =
      pullback.fst object.hom earlier := by
  cases same
  simp [transport]

@[reassoc (attr := simp)] theorem transport_snd {source target : C}
    {earlier later : source ⟶ target} (same : earlier = later) (object : Over target) :
    ((transport same).hom.app object).left ≫ pullback.snd object.hom later =
      pullback.snd object.hom earlier := by
  cases same
  simp [transport]

theorem right_unit (object : Over middle) :
    (Over.pullback f).map ((identity middle).hom.app object) =
      (compositionInverse f (𝟙 middle)).hom.app object ≫
        (transport (Category.comp_id f)).hom.app object := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [identity, compositionInverse, Over.pullback_map_left]
  · simp [identity, compositionInverse, Over.pullback_map_left]

theorem left_unit (object : Over middle) :
    (identity first).hom.app ((Over.pullback f).obj object) =
      (compositionInverse (𝟙 first) f).hom.app object ≫
        (transport (Category.id_comp f)).hom.app object := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [identity, compositionInverse]
  · simp only [identity, NatIso.ofComponents_hom_app, identityComponent_left,
      compositionInverse, Over.comp_left, Category.assoc, transport_snd,
      compositionInverseComponent_snd]
    exact (pullback.condition (f := pullback.snd object.hom f) (g := 𝟙 first)).trans
      (Category.comp_id _)

theorem associativity {final : C} (h : last ⟶ final) (object : Over final) :
    (Over.pullback f).map ((compositionInverse g h).hom.app object) ≫
        (compositionInverse f (g ≫ h)).hom.app object =
      (compositionInverse f g).hom.app ((Over.pullback h).obj object) ≫
        (compositionInverse (f ≫ g) h).hom.app object ≫
        (transport (Category.assoc f g h)).hom.app object := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [compositionInverse, Over.pullback_map_left, Category.assoc]
    simpa only [Over.pullback_obj_hom] using
      (compositionInverseComponent_fst_assoc f g ((Over.pullback h).obj object)
        (pullback.fst object.hom h)).symm
  · simp [compositionInverse, Over.pullback_map_left]
    simpa only [Over.pullback_obj_hom] using
      (compositionInverseComponent_snd f g ((Over.pullback h).obj object)).symm

end Mettapedia.CategoryTheory.CanonicalSlicePullback
