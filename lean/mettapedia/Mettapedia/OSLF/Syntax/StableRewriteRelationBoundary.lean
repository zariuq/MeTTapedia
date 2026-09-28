import Mathlib.Data.Set.Finite.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Subfunctor.Subobject

/-!
# Substitution stability does not make a rewrite relation a subobject

A relation on arrows into a fixed carrier that is stable under precomposition
is a sieve-like predicate. It need not be represented by a single subobject of
the carrier. The finite-image predicate is a concrete counterexample: it holds
of every point but fails for an injective map out of the natural numbers.

This separates the natural relation-family interface from the representable
reduction subobject required in a classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.StableRewriteRelationBoundary

open CategoryTheory
open CategoryTheory.Limits

universe u v

/-- A genuine reduction subobject induces a two-arrow contextual relation by
factorization of the paired endpoint map. -/
def RepresentedRewrite {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (programs : C) (reduction : Subobject (programs ⨯ programs))
    {Γ : C} (source target : Γ ⟶ programs) : Prop :=
  reduction.Factors (prod.lift source target)

/-- The relation induced by an actual subobject is stable under substitution;
the converse is refuted below. -/
theorem representedRewrite_precomp {C : Type u} [Category.{v} C]
    [HasBinaryProducts C] (programs : C)
    (reduction : Subobject (programs ⨯ programs))
    {Γ Δ : C} (substitution : Δ ⟶ Γ)
    (source target : Γ ⟶ programs)
    (fires : RepresentedRewrite programs reduction source target) :
    RepresentedRewrite programs reduction
      (substitution ≫ source) (substitution ≫ target) := by
  have factor : reduction.Factors
      (substitution ≫ prod.lift source target) :=
    Subobject.factors_of_factors_right substitution fires
  simpa only [RepresentedRewrite, prod.comp_lift] using factor

/-- For a type-valued functor, factoring through an actual subobject is
equivalent to holding pointwise at every context and every element. This is
the missing representability check behind a stable relation family. -/
theorem subfunctor_factors_iff_pointwise
    {C : Type u} [Category.{v} C] {F H : C ⥤ Type}
    (relation : Subfunctor F) (map : H ⟶ F) :
    (Subobject.mk relation.ι).Factors map ↔
      ∀ (X : C) (point : H.obj X), map.app X point ∈ relation.obj X := by
  constructor
  · intro factors X point
    obtain ⟨lift, equal⟩ := (Subobject.mk_factors_iff _ _).mp factors
    have atPoint := congrArg
      (fun component : H.obj X ⟶ F.obj X => component point)
      (NatTrans.congr_app equal X)
    change ((lift.app X point).val : F.obj X) = map.app X point at atPoint
    rw [← atPoint]
    exact (lift.app X point).property
  · intro held
    have range_le : Subfunctor.range map ≤ relation := by
      intro X pair membership
      obtain ⟨point, rfl⟩ := membership
      exact held X point
    exact (Subobject.mk_factors_iff _ _).mpr
      ⟨Subfunctor.lift map range_le, Subfunctor.lift_ι map range_le⟩

/-- A context-indexed predicate on arrows into a pair of natural numbers. -/
def FiniteImage {Γ : Type} (map : Γ → Nat × Nat) : Prop :=
  (Set.range map).Finite

/-- Finite image is stable under substitution (precomposition). -/
theorem finiteImage_precomp {Γ Δ : Type} (map : Γ → Nat × Nat)
    (substitution : Δ → Γ) (finite : FiniteImage map) :
    FiniteImage (map ∘ substitution) := by
  apply finite.subset
  rintro pair ⟨point, rfl⟩
  exact ⟨substitution point, rfl⟩

/-- Every individual endpoint pair belongs to the finite-image relation. -/
theorem finiteImage_point (pair : Nat × Nat) :
    FiniteImage (fun _ : Unit => pair) := by
  simp [FiniteImage]

/-- The map with infinitely many distinct source coordinates does not have
finite image. -/
theorem not_finiteImage_infinite_spine :
    ¬ FiniteImage (fun n : Nat => (n, 0)) := by
  exact (Set.infinite_range_of_injective (fun a b equal =>
    congrArg Prod.fst equal)).not_finite

/-- No carrier map represents this stable family by factorization of all
context-indexed arrows. The obstruction holds even without asking the map to
be mono. Hence precomposition stability alone cannot supply the reduction
subobject claimed by a classifying theory. -/
theorem finiteImage_not_representable :
    ¬ ∃ (R : Type) (inclusion : R → Nat × Nat),
        ∀ (Γ : Type) (map : Γ → Nat × Nat),
          FiniteImage map ↔
            ∃ lift : Γ → R, inclusion ∘ lift = map := by
  rintro ⟨R, inclusion, represents⟩
  have surjective : Function.Surjective inclusion := by
    intro pair
    obtain ⟨lift, equal⟩ :=
      (represents Unit (fun _ => pair)).mp (finiteImage_point pair)
    exact ⟨lift (), congrFun equal ()⟩
  let spine : Nat → Nat × Nat := fun n => (n, 0)
  have lifts : ∃ lift : Nat → R, inclusion ∘ lift = spine := by
    let lift : Nat → R := fun n => Classical.choose (surjective (spine n))
    refine ⟨lift, ?_⟩
    funext n
    exact Classical.choose_spec (surjective (spine n))
  exact not_finiteImage_infinite_spine ((represents Nat spine).mpr lifts)

/-- The same family in the two-arrow shape used for a reduction relation. -/
def FiniteImageRewrite {Γ : Type} (source target : Γ → Nat) : Prop :=
  FiniteImage (fun point => (source point, target point))

/-- A genuinely pointwise reduction predicate, by contrast, is represented
by the inclusion of its subset of endpoint pairs. -/
def PointwiseRewrite (R : Set (Nat × Nat)) {Γ : Type}
    (source target : Γ → Nat) : Prop :=
  ∀ point, (source point, target point) ∈ R

theorem pointwiseRewrite_represented (R : Set (Nat × Nat))
    (Γ : Type) (source target : Γ → Nat) :
    PointwiseRewrite R source target ↔
      ∃ lift : Γ → R,
        Subtype.val ∘ lift = fun point => (source point, target point) := by
  constructor
  · intro held
    exact ⟨fun point => ⟨(source point, target point), held point⟩, rfl⟩
  · rintro ⟨lift, equal⟩ point
    have atPoint := congrFun equal point
    change (lift point).val = (source point, target point) at atPoint
    rw [← atPoint]
    exact (lift point).property

/-- This two-arrow relation satisfies exactly the usual substitution-stability
law for a contextual rewrite relation. -/
theorem finiteImageRewrite_precomp {Γ Δ : Type}
    (substitution : Δ → Γ) (source target : Γ → Nat)
    (fires : FiniteImageRewrite source target) :
    FiniteImageRewrite (source ∘ substitution) (target ∘ substitution) :=
  finiteImage_precomp (fun point => (source point, target point)) substitution fires

/-- Substitution stability in that two-arrow interface still does not yield a
representing reduction subobject of the endpoint product. -/
theorem finiteImageRewrite_not_subobject :
    ¬ ∃ (R : Type) (inclusion : R → Nat × Nat),
        ∀ (Γ : Type) (source target : Γ → Nat),
          FiniteImageRewrite source target ↔
            ∃ lift : Γ → R,
              inclusion ∘ lift = fun point => (source point, target point) := by
  rintro ⟨R, inclusion, represents⟩
  apply finiteImage_not_representable
  refine ⟨R, inclusion, ?_⟩
  intro Γ map
  simpa only [FiniteImageRewrite, Function.comp_def, Prod.mk.eta] using
    represents Γ (fun point => (map point).1) (fun point => (map point).2)

end Mettapedia.OSLF.Binding.StableRewriteRelationBoundary
