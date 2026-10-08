import Mettapedia.CategoryTheory.PredicateDoctrineClosed
import Mettapedia.CategoryTheory.PredicateDoctrineEquality
import Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth
import Mettapedia.GSLT.Topos.PresheafPredicateCartesianClosed
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The higher-order predicate fibration over a presheaf category

The actual subfunctor projection has fibred finite logical operations and
Cartesian closure, equality with its diagonal adjunction and Frobenius law,
both simple quantifiers with parameter Beck--Chevalley, and the actual generic
truth predicate with unique Cartesian classification. Its total category has
the previously constructed cosmic structure. All these constructions use the
same original projection, with presheaf values and small diagrams in the base
category's universe.

This realizes Proposition 19 of Williams and Stay's Native Type Theory.
Substitution here is a map of presheaves over a fixed category; restriction
along a change of the indexing category has different logical comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
  MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory.PredicateDoctrine
open scoped _root_.CategoryTheory.SemilatticeInf
  Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed

universe u z
variable {C : Type u} [Category.{u} C]

/-- The complete first-order and generic-predicate structure on the actual
presheaf predicate action, over the actual Cartesian closed base. -/
noncomputable def higherOrder (C : Type u) [Category.{u} C] :
    HigherOrder.{u+1,u,u} (Cᵒᵖ ⥤ Type u) where
  toFirstOrder := PresheafPredicateFirstOrder.firstOrder C
  generic := PresheafPredicateGenericTruth.generic C

theorem projection_is_original :
    (higherOrder C).toIndexedHeyting.projection = presheafPredicateProjection C := rfl

theorem action_is_original :
    (higherOrder C).toIndexedHeyting.indexedFunctor = presheafPredicateFunctor C := rfl

theorem projection_isFibered : IsFibered (presheafPredicateProjection C) :=
  (higherOrder C).toIndexedHeyting.projection_fibered

/-- The selected subfunctor fibre is equivalent to the actual categorical
fibre of the original projection. -/
noncomputable def fibreEquivalence (P : Cᵒᵖ ⥤ Type u) :
    Subfunctor P ≌ Fiber (presheafPredicateProjection C) P :=
  (HasFibers.inducedFunctor (presheafPredicateProjection C) P).asEquivalence

/-- Fibred products and exponentials are actual categorical choices, with
their order-category universal properties. -/
@[instance_reducible]
noncomputable def fibreCartesian (P : Cᵒᵖ ⥤ Type u) :
    CartesianMonoidalCategory (Subfunctor P) := inferInstance

@[instance_reducible]
noncomputable def fibreClosed (P : Cᵒᵖ ⥤ Type u) :
    MonoidalClosed (Subfunctor P) := inferInstance

theorem fibreFiniteCoproducts (P : Cᵒᵖ ⥤ Type u) :
    HasFiniteCoproducts (Subfunctor P) :=
  hasFiniteCoproducts_of_has_binary_and_initial

theorem substitution_preservesLimits {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    PreservesLimitsOfSize.{z,z} (predicateReindex f) :=
  (PresheafPredicateFirstOrder.firstOrder C).reindex_preservesLimits f

theorem substitution_preservesColimits {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    PreservesColimitsOfSize.{z,z} (predicateReindex f) :=
  (PresheafPredicateFirstOrder.firstOrder C).reindex_preservesColimits f

noncomputable instance originalReindex_preservesFiniteProducts
    {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    PreservesFiniteProducts (predicateReindex f) :=
  (PresheafPredicateFirstOrder.firstOrder C).reindex_preservesFiniteProducts f

/-- The original substitution functor has invertible canonical exponential
comparisons, not merely a pointwise implication equation. -/
theorem substitutionClosed {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    MonoidalClosedFunctor (predicateReindex f) :=
  (PresheafPredicateFirstOrder.firstOrder C).reindex_monoidalClosed f

/-- Actual equality in a full parameter context. -/
noncomputable def contextualEquality (Γ A : Cᵒᵖ ⥤ Type u) :
    Subfunctor (Γ ⊗ (A ⊗ A)) :=
  (higherOrder C).toFirstOrder.equalityWithParameters Γ A

theorem contextualEquality_readout (Γ A : Cᵒᵖ ⥤ Type u) (world : Cᵒᵖ)
    (value : (Γ ⊗ (A ⊗ A)).obj world) :
    value ∈ (contextualEquality Γ A).obj world ↔ value.2.1 = value.2.2 := by
  change (∃ input : (Γ ⊗ A).obj world,
    input ∈ (⊤ : Subfunctor (Γ ⊗ A)).obj world ∧
      (input.1, (input.2, input.2)) = value) ↔ value.2.1 = value.2.2
  constructor
  · rintro ⟨input, _, same⟩
    exact (congrArg (fun x => x.2.1) same).symm.trans
      (congrArg (fun x => x.2.2) same)
  · intro same
    exact ⟨(value.1, value.2.1), trivial,
      Prod.ext rfl (Prod.ext rfl same)⟩

theorem contextualEquality_substitution {Γ Δ : Cᵒᵖ ⥤ Type u}
    (σ : Γ ⟶ Δ) (A : Cᵒᵖ ⥤ Type u) :
    (contextualEquality Δ A).preimage (σ ⊗ₘ 𝟙 (A ⊗ A)) =
      contextualEquality Γ A :=
  (higherOrder C).toFirstOrder.equality_parameter_substitution σ A

/-- Generic classification uses the full Cartesian arrow universal property
in the same total category whose cosmic structure was constructed. -/
theorem generic_cartesian_unique (a : PresheafPredicateTotal C) :
    ∃! arrow : a ⟶ PresheafPredicateGenericTruth.totalTruth C,
      IsStronglyCartesian (presheafPredicateProjection C) arrow.base arrow :=
  PresheafPredicateGenericTruth.unique_cartesian_classification a

/-- The higher-order fibration and cosmic total structure concern exactly the
same total category. The diagram sizes are explicit; larger universes are
not silently included. -/
theorem cosmic_higherOrder :
    Nonempty (HigherOrder.{u+1,u,u} (Cᵒᵖ ⥤ Type u)) ∧
      Nonempty (MonoidalClosed (PresheafPredicateTotal C)) ∧
      HasLimitsOfSize.{u,u} (PresheafPredicateTotal C) ∧
      HasColimitsOfSize.{u,u} (PresheafPredicateTotal C) ∧
      MonoidalClosedFunctor (presheafPredicateProjection C) ∧
      PreservesLimitsOfSize.{u,u} (presheafPredicateProjection C) ∧
      PreservesColimitsOfSize.{u,u} (presheafPredicateProjection C) := by
  exact ⟨⟨higherOrder C⟩, ⟨inferInstance⟩, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder
