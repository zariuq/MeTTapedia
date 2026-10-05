import Mettapedia.TypeTheory.DisplayedPresheafSlice
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Substitution through the family--slice equivalence

Precomposition of displayed families along a natural context map corresponds
to the actual pullback functor on presheaf slices. The comparison is natural
in all maps of families, and is specified by both pullback projections.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution

open CategoryTheory CategoryTheory.Limits
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice

universe u v w
variable {C : Type u} [Category.{v} C]
variable {P Q : Face.{u, v, w} C}

/-- Dependent substitution is precomposition by the induced map on elements. -/
def reindexFunctor (f : Q ⟶ P) :
    DisplayedFamily.{u, v, w, w} P ⥤ DisplayedFamily.{u, v, w, w} Q :=
  (Functor.whiskeringLeft _ _ (Type w)).obj f.mapElements

/-- The comparison between displayed substitution and the chosen slice
pullback is determined by the existing comprehension pullback theorem. -/
noncomputable def reindexTotalIso (f : Q ⟶ P)
    (A : DisplayedFamily.{u, v, w, w} P) :
    (totalFunctor Q).obj ((reindexFunctor f).obj A) ≅
      (Over.pullback f).obj ((totalFunctor P).obj A) :=
  Over.isoMk (totalReindexMap_isPullback f A).flip.isoPullback
    (totalReindexMap_isPullback f A).flip.isoPullback_hom_snd

@[reassoc (attr := simp)] theorem reindexTotalIso_hom_fst
    (f : Q ⟶ P) (A : DisplayedFamily.{u, v, w, w} P) :
    (reindexTotalIso f A).hom.left ≫ pullback.fst (totalProjection A) f =
      totalReindexMap f A :=
  (totalReindexMap_isPullback f A).flip.isoPullback_hom_fst

@[reassoc (attr := simp)] theorem reindexTotalIso_hom_snd
    (f : Q ⟶ P) (A : DisplayedFamily.{u, v, w, w} P) :
    (reindexTotalIso f A).hom.left ≫ pullback.snd (totalProjection A) f =
      totalProjection (reindexDisplayed f A) :=
  (totalReindexMap_isPullback f A).flip.isoPullback_hom_snd

/-- A map of families commutes with its change of base on total spaces. -/
theorem totalHom_reindex (f : Q ⟶ P)
    {A B : DisplayedFamily.{u, v, w, w} P} (g : A ⟶ B) :
    totalHom ((reindexFunctor f).map g) ≫ totalReindexMap f B =
      totalReindexMap f A ≫ totalHom g := by
  ext c x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Family reindexing and slice pullback agree as functors, not only on
objects or inhabited fibres. -/
noncomputable def substitutionIso (f : Q ⟶ P) :
    reindexFunctor f ⋙ totalFunctor Q ≅
      totalFunctor P ⋙ Over.pullback f := by
  refine NatIso.ofComponents (reindexTotalIso f) ?_
  intro A B g
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change
      (totalHom ((reindexFunctor f).map g) ≫
        (reindexTotalIso f B).hom.left) ≫ _ =
      ((reindexTotalIso f A).hom.left ≫
        ((Over.pullback f).map ((totalFunctor P).map g)).left) ≫ _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    change (totalHom ((reindexFunctor f).map g) ≫
        (reindexTotalIso f B).hom.left) ≫ pullback.fst (totalProjection B) f =
      (reindexTotalIso f A).hom.left ≫
        pullback.fst (totalProjection A) f ≫ totalHom g
    rw [Category.assoc, reindexTotalIso_hom_fst,
      ← Category.assoc, reindexTotalIso_hom_fst]
    exact totalHom_reindex f g
  · change
      (totalHom ((reindexFunctor f).map g) ≫
        (reindexTotalIso f B).hom.left) ≫ _ =
      ((reindexTotalIso f A).hom.left ≫
        ((Over.pullback f).map ((totalFunctor P).map g)).left) ≫ _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    change (totalHom ((reindexFunctor f).map g) ≫
        (reindexTotalIso f B).hom.left) ≫ pullback.snd (totalProjection B) f =
      (reindexTotalIso f A).hom.left ≫ pullback.snd (totalProjection A) f
    rw [Category.assoc, reindexTotalIso_hom_snd, reindexTotalIso_hom_snd]
    exact totalHom_projection ((reindexFunctor f).map g)

end Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
