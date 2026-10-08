import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Coherence of the two predicate quantifiers

Quantifiers along composites, identities and isomorphisms are determined by
their actual Galois connections. No additional quantifier choices or coherence
fields are required. The pointwise equations also identify the corresponding
functors between the ordered predicate fibres.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateDoctrine.FirstOrder

open _root_.CategoryTheory

universe u v p
variable {C : Type u} [Category.{v} C]
variable (D : FirstOrder.{u,v,p} C)

theorem exists_unit {X Y : C} (f : X ⟶ Y) (φ : D.Fiber X) :
    φ ≤ D.reindex f (D.existsAlong f φ) :=
  (D.exists_adj f _ _).mp le_rfl

theorem exists_counit {X Y : C} (f : X ⟶ Y) (ψ : D.Fiber Y) :
    D.existsAlong f (D.reindex f ψ) ≤ ψ :=
  (D.exists_adj f _ _).mpr le_rfl

theorem forall_unit {X Y : C} (f : X ⟶ Y) (ψ : D.Fiber Y) :
    ψ ≤ D.forallAlong f (D.reindex f ψ) :=
  (D.forall_adj f _ _).mp le_rfl

theorem forall_counit {X Y : C} (f : X ⟶ Y) (φ : D.Fiber X) :
    D.reindex f (D.forallAlong f φ) ≤ φ :=
  (D.forall_adj f _ _).mpr le_rfl

theorem existsAlong_id (X : C) (φ : D.Fiber X) :
    D.existsAlong (𝟙 X) φ = φ := by
  apply le_antisymm
  · apply (D.exists_adj _ _ _).mpr
    rw [D.reindex_id]
  · simpa only [D.reindex_id] using D.exists_unit (𝟙 X) φ

theorem forallAlong_id (X : C) (φ : D.Fiber X) :
    D.forallAlong (𝟙 X) φ = φ := by
  apply le_antisymm
  · simpa only [D.reindex_id] using D.forall_counit (𝟙 X) φ
  · apply (D.forall_adj _ _ _).mp
    rw [D.reindex_id]

theorem existsAlong_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (φ : D.Fiber X) :
    D.existsAlong (f ≫ g) φ = D.existsAlong g (D.existsAlong f φ) := by
  apply le_antisymm
  · apply (D.exists_adj _ _ _).mpr
    rw [D.reindex_comp]
    exact (D.exists_unit f φ).trans
      (D.reindex_mono f (D.exists_unit g (D.existsAlong f φ)))
  · apply (D.exists_adj g _ _).mpr
    apply (D.exists_adj f _ _).mpr
    rw [← D.reindex_comp]
    exact D.exists_unit (f ≫ g) φ

theorem forallAlong_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (φ : D.Fiber X) :
    D.forallAlong (f ≫ g) φ = D.forallAlong g (D.forallAlong f φ) := by
  apply le_antisymm
  · apply (D.forall_adj g _ _).mp
    apply (D.forall_adj f _ _).mp
    rw [← D.reindex_comp]
    exact D.forall_counit (f ≫ g) φ
  · apply (D.forall_adj _ _ _).mp
    rw [D.reindex_comp]
    exact (D.reindex_mono f (D.forall_counit g (D.forallAlong f φ))).trans
      (D.forall_counit f φ)

theorem reindex_hom_inv {X Y : C} (e : X ≅ Y) (φ : D.Fiber X) :
    D.reindex e.hom (D.reindex e.inv φ) = φ := by
  rw [← D.reindex_comp, e.hom_inv_id, D.reindex_id]

theorem reindex_inv_hom {X Y : C} (e : X ≅ Y) (ψ : D.Fiber Y) :
    D.reindex e.inv (D.reindex e.hom ψ) = ψ := by
  rw [← D.reindex_comp, e.inv_hom_id, D.reindex_id]

theorem existsAlong_iso {X Y : C} (e : X ≅ Y) (φ : D.Fiber X) :
    D.existsAlong e.hom φ = D.reindex e.inv φ := by
  apply le_antisymm
  · apply (D.exists_adj _ _ _).mpr
    rw [D.reindex_hom_inv]
  · have unit := D.reindex_mono e.inv (D.exists_unit e.hom φ)
    simpa only [D.reindex_inv_hom] using unit

theorem forallAlong_iso {X Y : C} (e : X ≅ Y) (φ : D.Fiber X) :
    D.forallAlong e.hom φ = D.reindex e.inv φ := by
  apply le_antisymm
  · have counit := D.reindex_mono e.inv (D.forall_counit e.hom φ)
    simpa only [D.reindex_inv_hom] using counit
  · apply (D.forall_adj _ _ _).mp
    rw [D.reindex_hom_inv]

theorem existsAlong_iso_reindex {X Y : C} (e : X ≅ Y) (ψ : D.Fiber Y) :
    D.existsAlong e.hom (D.reindex e.hom ψ) = ψ := by
  rw [D.existsAlong_iso, D.reindex_inv_hom]

theorem forallAlong_iso_reindex {X Y : C} (e : X ≅ Y) (ψ : D.Fiber Y) :
    D.forallAlong e.hom (D.reindex e.hom ψ) = ψ := by
  rw [D.forallAlong_iso, D.reindex_inv_hom]

theorem existsFunctor_identity (X : C) : D.existsFunctor (𝟙 X) = 𝟭 (D.Fiber X) := by
  refine _root_.CategoryTheory.Functor.ext (D.existsAlong_id X) ?_
  intros
  apply Subsingleton.elim

theorem forallFunctor_identity (X : C) : D.forallFunctor (𝟙 X) = 𝟭 (D.Fiber X) := by
  refine _root_.CategoryTheory.Functor.ext (D.forallAlong_id X) ?_
  intros
  apply Subsingleton.elim

theorem existsFunctor_composition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.existsFunctor (f ≫ g) = D.existsFunctor f ⋙ D.existsFunctor g := by
  refine _root_.CategoryTheory.Functor.ext (D.existsAlong_comp f g) ?_
  intros
  apply Subsingleton.elim

theorem forallFunctor_composition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.forallFunctor (f ≫ g) = D.forallFunctor f ⋙ D.forallFunctor g := by
  refine _root_.CategoryTheory.Functor.ext (D.forallAlong_comp f g) ?_
  intros
  apply Subsingleton.elim

end Mettapedia.CategoryTheory.PredicateDoctrine.FirstOrder
