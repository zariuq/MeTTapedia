import Mettapedia.CategoryTheory.ElementaryToposPredicateQuantification
import Mettapedia.CategoryTheory.PredicateDoctrine
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.GaloisConnection.Basic

/-!
# Universal quantification and implication in an elementary topos

Universal quantification is the subobject defined by equality of the names
of a complete graph and its restriction. Its right-adjoint property follows
from the actual fibre-factorization theorem. Implication is universal
quantification along a predicate inclusion; no lattice of joins or finite
colimits is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateAdjoints

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposPredicateQuantification

universe u v
variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]

def reindex {X Y : C} (f : X ⟶ Y) : Subobject Y → Subobject X :=
  (Subobject.pullback f).obj

theorem reindex_mono {X Y : C} (f : X ⟶ Y) : Monotone (reindex f) :=
  (Subobject.pullback f).monotone

theorem reindex_id (X : C) (P : Subobject X) : reindex (𝟙 X) P = P := by
  simp only [reindex, Subobject.pullback_id]

theorem reindex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Subobject Z) :
    reindex (f ≫ g) P = reindex f (reindex g P) := by
  simp only [reindex, Subobject.pullback_comp]

theorem reindex_top {X Y : C} (f : X ⟶ Y) : reindex f ⊤ = ⊤ :=
  Subobject.pullback_top f

theorem reindex_inf {X Y : C} (f : X ⟶ Y) (P Q : Subobject Y) :
    reindex f (P ⊓ Q) = reindex f P ⊓ reindex f Q :=
  Subobject.inf_pullback f P Q

variable [HasEqualizers C]

omit [HasPullbacks C] in
theorem le_equalizer_iff {X Y : C} (P : Subobject X) (a b : X ⟶ Y) :
    P ≤ Subobject.mk (equalizer.ι a b) ↔ P.arrow ≫ a = P.arrow ≫ b := by
  constructor
  · intro admitted
    rw [← Subobject.ofLEMk_comp admitted, Category.assoc, Category.assoc,
      equalizer.condition]
  · intro equal
    exact Subobject.le_mk_of_comm (equalizer.lift P.arrow equal) (equalizer.lift_ι _ _)

variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (classifier : Subobject.Classifier C)

def forallAlong {X Y : C} (f : X ⟶ Y) (P : Subobject X) : Subobject Y :=
  Subobject.mk (universalInclusion classifier f P.arrow)

theorem forall_adj {X Y : C} (f : X ⟶ Y) :
    GaloisConnection (reindex f) (forallAlong classifier f) := by
  intro R P
  change (Subobject.pullback f).obj R ≤ P ↔
    R ≤ Subobject.mk (universalInclusion classifier f P.arrow)
  rw [le_equalizer_iff]
  have fibre := fibre_factor_iff classifier f P.arrow R.arrow
    ((Subobject.pullback f).obj R).arrow (Subobject.pullbackπ f R)
    (Subobject.isPullback f R).flip
  constructor
  · intro admitted
    exact fibre.mpr ⟨Subobject.ofLE _ _ admitted, Subobject.ofLE_arrow admitted⟩
  · intro equal
    obtain ⟨factor, recovers⟩ := fibre.mp equal
    exact Subobject.le_of_comm factor recovers

theorem forall_mono {X Y : C} (f : X ⟶ Y) :
    Monotone (forallAlong classifier f) :=
  (forall_adj classifier f).monotone_u

theorem forall_counit {X Y : C} (f : X ⟶ Y) (P : Subobject X) :
    reindex f (forallAlong classifier f P) ≤ P :=
  (forall_adj classifier f).l_u_le P

theorem forall_unit {X Y : C} (f : X ⟶ Y) (R : Subobject Y) :
    R ≤ forallAlong classifier f (reindex f R) :=
  (forall_adj classifier f).le_u_l R

def implication {X : C} (P Q : Subobject X) : Subobject X :=
  forallAlong classifier P.arrow (reindex P.arrow Q)

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
/-- The existing mono direct-image adjunction, expressed in its actual order. -/
theorem map_adj {X Y : C} (f : X ⟶ Y) [Mono f] :
    GaloisConnection (Subobject.map f).obj (reindex f) := by
  intro P Q
  constructor
  · intro admitted
    exact ((Subobject.mapPullbackAdj f).homEquiv P Q (homOfLE admitted)).le
  · intro admitted
    exact ((Subobject.mapPullbackAdj f).homEquiv P Q).symm (homOfLE admitted) |>.le

theorem implication_adj {X : C} (R P Q : Subobject X) :
    R ≤ implication classifier P Q ↔ R ⊓ P ≤ Q := by
  rw [implication, ← forall_adj classifier P.arrow,
    ← map_adj P.arrow, inf_comm, Subobject.inf_eq_map_pullback]
  rfl

theorem implication_mono_right {X : C} (P : Subobject X) :
    Monotone (implication classifier P) := by
  intro Q R admitted
  exact forall_mono classifier P.arrow (reindex_mono P.arrow admitted)

theorem implication_evaluation {X : C} (P Q : Subobject X) :
    implication classifier P Q ⊓ P ≤ Q :=
  (implication_adj classifier _ _ _).mp le_rfl

theorem implication_self {X : C} (P : Subobject X) :
    implication classifier P P = ⊤ := by
  apply le_antisymm le_top
  exact (implication_adj classifier ⊤ P P).mpr
    (by simpa only [top_inf_eq] using (le_rfl : P ≤ P))

theorem implication_eq_top {X : C} (P Q : Subobject X) :
    implication classifier P Q = ⊤ ↔ P ≤ Q := by
  rw [eq_top_iff, implication_adj, top_inf_eq]

theorem implication_top_left {X : C} (P : Subobject X) :
    implication classifier ⊤ P = P := by
  apply le_antisymm
  · simpa only [inf_top_eq] using implication_evaluation classifier ⊤ P
  · exact (implication_adj classifier P ⊤ P).mpr
      (by simpa only [inf_top_eq] using (le_rfl : P ≤ P))

end Mettapedia.CategoryTheory.ElementaryToposPredicateAdjoints
