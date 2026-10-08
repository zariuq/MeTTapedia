import Mettapedia.CategoryTheory.ElementaryToposPredicateHeyting
import Mettapedia.CategoryTheory.MonoArrowImageCartesian
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Stable existential and universal predicate quantifiers

Existential quantification is the actual image of the selected mono followed
by the supplied map. Stable elementary-topos images earn Beck--Chevalley
over every actual pullback square. The adjunctions then derive universal
Beck--Chevalley and Frobenius, including the complete selected predicates.
The image instances used by these lemmas are derived from the elementary
classifier when the doctrine is assembled.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateImages

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposPredicateAdjoints ElementaryToposPredicateHeyting

universe u v
variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C] [HasImages C]

def existsAlong {X Y : C} (f : X ⟶ Y) (P : Subobject X) : Subobject Y :=
  imageSubobject (P.arrow ≫ f)

theorem exists_adj {X Y : C} (f : X ⟶ Y) :
    GaloisConnection (existsAlong f) (reindex f) := by
  intro P R
  change imageSubobject (P.arrow ≫ f) ≤ R ↔ P ≤ (Subobject.pullback f).obj R
  let square := Subobject.isPullback f R
  constructor
  · intro admitted
    let factor := factorThruImageSubobject (P.arrow ≫ f) ≫
      Subobject.ofLE (imageSubobject (P.arrow ≫ f)) R admitted
    have recovers : factor ≫ R.arrow = P.arrow ≫ f := by
      dsimp only [factor]
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    exact Subobject.le_of_comm (square.lift factor P.arrow recovers)
      (square.lift_snd _ _ _)
  · intro admitted
    apply imageSubobject_le (P.arrow ≫ f)
      (Subobject.ofLE P ((Subobject.pullback f).obj R) admitted ≫ Subobject.pullbackπ f R)
    rw [Category.assoc, square.w, ← Category.assoc, Subobject.ofLE_arrow]

theorem exists_mono {X Y : C} (f : X ⟶ Y) : Monotone (existsAlong f) :=
  (exists_adj f).monotone_l

omit [HasPullbacks C] in
theorem exists_id {X : C} (P : Subobject X) : existsAlong (𝟙 X) P = P := by
  simp only [existsAlong, Category.comp_id, imageSubobject_mono, Subobject.mk_arrow]

theorem exists_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Subobject X) :
    existsAlong (f ≫ g) P = existsAlong g (existsAlong f P) := by
  apply le_antisymm
  · apply (exists_adj (f ≫ g) P _).mpr
    rw [reindex_comp]
    exact ((exists_adj f).le_u_l P).trans
      (reindex_mono f ((exists_adj g).le_u_l (existsAlong f P)))
  · apply (exists_adj g _ _).mpr
    apply (exists_adj f _ _).mpr
    rw [← reindex_comp]
    exact (exists_adj (f ≫ g)).le_u_l P

theorem exists_mono_arrow {X Y : C} (f : X ⟶ Y) [Mono f] (P : Subobject X) :
    existsAlong f P = (Subobject.map f).obj P :=
  (exists_adj f).l_unique (map_adj f) (fun _ => rfl)

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable [HasImageMaps C]

include classifier in
theorem exists_baseChange {P Q R S : C} (top : P ⟶ Q) (left : P ⟶ R)
    (right : Q ⟶ S) (bottom : R ⟶ S) (square : IsPullback top left right bottom)
    (predicate : Subobject Q) :
    reindex bottom (existsAlong right predicate) =
      existsAlong left (reindex top predicate) := by
  let pulled := reindex top predicate
  have total : IsPullback (Subobject.pullbackπ top predicate) (pulled.arrow ≫ left)
      (predicate.arrow ≫ right) bottom :=
    (Subobject.isPullback top predicate).paste_vert square
  let arrow : Arrow.mk (pulled.arrow ≫ left) ⟶ Arrow.mk (predicate.arrow ≫ right) :=
    Arrow.homMk (Subobject.pullbackπ top predicate) bottom total.w
  exact Subobject.pullback_obj_mk
    (MonoArrowImageAdjunction.image_square_pullback classifier arrow total)

theorem forall_baseChange {P Q R S : C} (top : P ⟶ Q) (left : P ⟶ R)
    (right : Q ⟶ S) (bottom : R ⟶ S) (square : IsPullback top left right bottom)
    (predicate : Subobject Q) :
    reindex bottom (forallAlong classifier right predicate) =
      forallAlong classifier left (reindex top predicate) := by
  have probes (test : Subobject R) :
      test ≤ reindex bottom (forallAlong classifier right predicate) ↔
        test ≤ forallAlong classifier left (reindex top predicate) := by
    rw [← exists_adj bottom, ← forall_adj classifier right,
      exists_baseChange classifier left top bottom right square.flip test,
      exists_adj top, forall_adj classifier left]
  exact le_antisymm ((probes _).mp le_rfl) ((probes _).mpr le_rfl)

include classifier in
theorem frobenius {X Y : C} (f : X ⟶ Y) (P : Subobject X) (R : Subobject Y) :
    existsAlong f (P ⊓ reindex f R) = existsAlong f P ⊓ R := by
  let pulled := (Subobject.pullback f).obj R
  let route := Subobject.pullbackπ f R
  have square := Subobject.isPullback f R
  calc
    existsAlong f (P ⊓ reindex f R) =
        existsAlong f ((Subobject.map pulled.arrow).obj (reindex pulled.arrow P)) := by
      congr 1
      exact (inf_comm P pulled).trans (Subobject.inf_eq_map_pullback pulled P)
    _ = existsAlong f (existsAlong pulled.arrow (reindex pulled.arrow P)) := by
      exact congrArg (existsAlong f) (exists_mono_arrow pulled.arrow _).symm
    _ = existsAlong (pulled.arrow ≫ f) (reindex pulled.arrow P) :=
      (exists_comp _ _ _).symm
    _ = existsAlong (route ≫ R.arrow) (reindex pulled.arrow P) := by
      exact congrArg (fun arrow => existsAlong arrow (reindex pulled.arrow P)) square.w.symm
    _ = existsAlong R.arrow (existsAlong route (reindex pulled.arrow P)) :=
      exists_comp _ _ _
    _ = (Subobject.map R.arrow).obj (reindex R.arrow (existsAlong f P)) := by
      exact (congrArg (existsAlong R.arrow)
        (exists_baseChange classifier pulled.arrow route f R.arrow square.flip P).symm).trans
          (exists_mono_arrow R.arrow _)
    _ = R ⊓ existsAlong f P := (Subobject.inf_eq_map_pullback _ _).symm
    _ = existsAlong f P ⊓ R := inf_comm _ _

theorem reindex_implication {X Y : C} (f : X ⟶ Y) (P Q : Subobject Y) :
    reindex f (implication classifier P Q) =
      implication classifier (reindex f P) (reindex f Q) := by
  rw [implication, forall_baseChange classifier (Subobject.pullbackπ f P)
    (reindex f P).arrow P.arrow f (Subobject.isPullback f P)]
  change forallAlong classifier (reindex f P).arrow
      (reindex (Subobject.pullbackπ f P) (reindex P.arrow Q)) =
    forallAlong classifier (reindex f P).arrow
      (reindex (reindex f P).arrow (reindex f Q))
  exact congrArg (forallAlong classifier (reindex f P).arrow)
    ((reindex_comp (Subobject.pullbackπ f P) P.arrow Q).symm.trans
      ((congrArg (fun arrow => reindex arrow Q) (Subobject.isPullback f P).w).trans
        (reindex_comp ((Subobject.pullback f).obj P).arrow f Q)))

end Mettapedia.CategoryTheory.ElementaryToposPredicateImages
