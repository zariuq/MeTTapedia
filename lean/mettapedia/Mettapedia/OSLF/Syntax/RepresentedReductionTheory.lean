import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.OSLF.Syntax.StableRewriteRelationBoundary

/-!
# Represented operational reduction

A substitution-stable relation on generalized terms is an operational
interface.  A classifying interpretation needs more: an actual mono into the
product of program objects whose factorization predicate is that relation.
The two interfaces are kept separate because stability alone does not imply
representability.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RepresentedReductionTheory

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Binding.StableRewriteRelationBoundary

/-- A representation of an existing operational relation by a categorical
subobject of paired programs. The comparison is required at every context,
not merely at closed points. -/
structure ReductionRepresentation (T : LambdaTheory) where
  subobject : Subobject (T.Pr ⨯ T.Pr)
  represents : ∀ {Γ : T.Obj} (source target : Γ ⟶ T.Pr),
    T.rewriteRel source target ↔
      RepresentedRewrite T.Pr subobject source target

/-- A classifying consumer uses this comparison when it passes from the broad
operational relation to a categorical subobject. -/
theorem ReductionRepresentation.rewrite_iff_factors
    (T : LambdaTheory) (R : ReductionRepresentation T) {Γ : T.Obj}
    (source target : Γ ⟶ T.Pr) :
    T.rewriteRel source target ↔
      R.subobject.Factors (prod.lift source target) :=
  R.represents source target

/-- Representation implies the ordinary substitution law. This proves the
one-way comparison without identifying the two interfaces. -/
theorem ReductionRepresentation.precomp (T : LambdaTheory)
    (R : ReductionRepresentation T) {Γ Δ : T.Obj}
    (substitution : Δ ⟶ Γ) (source target : Γ ⟶ T.Pr)
    (fires : T.rewriteRel source target) :
    T.rewriteRel (substitution ≫ source) (substitution ≫ target) := by
  apply (R.represents _ _).mpr
  exact representedRewrite_precomp T.Pr R.subobject substitution source target
    ((R.represents source target).mp fires)

/-- A pointwise reduction subfunctor represents a relation on any isomorphic
choice of the pair object. This separates the categorical product choice from
the underlying endpoint predicate. -/
theorem factors_through_transport {C : Type*} [Category C]
    {P Q H : C ⥤ Type} (relation : Subfunctor P) (pairIso : Q ≅ P)
    (map : H ⟶ Q) :
    (Subobject.mk (relation.ι ≫ pairIso.inv)).Factors map ↔
      ∀ (X : C) (point : H.obj X),
        (map ≫ pairIso.hom).app X point ∈ relation.obj X := by
  have pointwise := subfunctor_factors_iff_pointwise
    relation (map ≫ pairIso.hom)
  constructor
  · intro factors
    obtain ⟨lift, equal⟩ := (Subobject.mk_factors_iff _ _).mp factors
    change lift ≫ (relation.ι ≫ pairIso.inv) = map at equal
    apply pointwise.mp
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    have afterIso := congrArg (fun arrow => arrow ≫ pairIso.hom) equal
    calc
      lift ≫ relation.ι =
          (lift ≫ relation.ι) ≫ (pairIso.inv ≫ pairIso.hom) := by simp
      _ = (lift ≫ (relation.ι ≫ pairIso.inv)) ≫ pairIso.hom := by
            exact congrArg (fun arrow => arrow ≫ pairIso.hom)
              (Category.assoc lift relation.ι pairIso.inv)
      _ = map ≫ pairIso.hom := afterIso
  · intro held
    obtain ⟨lift, equal⟩ := (Subobject.mk_factors_iff _ _).mp
      (pointwise.mpr held)
    change lift ≫ relation.ι = map ≫ pairIso.hom at equal
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    have afterIso := congrArg (fun arrow => arrow ≫ pairIso.inv) equal
    calc
      lift ≫ (relation.ι ≫ pairIso.inv) =
          (lift ≫ relation.ι) ≫ pairIso.inv := by
            exact (Category.assoc _ _ _).symm
      _ = (map ≫ pairIso.hom) ≫ pairIso.inv := afterIso
      _ = map := by simp [Category.assoc]

/-- A generalized section factors through a presheaf subobject precisely
when its characteristic sieve contains the identity at every component.
The statement quantifies over every test presheaf, not just global elements. -/
theorem subfunctor_factors_iff_characteristic_truth
    {C : Type} [SmallCategory C]
    {P H : Cᵒᵖ ⥤ Type}
    (G : Subfunctor P) (generalized : H ⟶ P) :
    (Subobject.mk G.ι).Factors generalized ↔
      ∀ (X : Cᵒᵖ) (point : H.obj X),
        ((Mettapedia.GSLT.Topos.chiOfSubfunctor P G).app X
          (generalized.app X point)).arrows (𝟙 X.unop) := by
  rw [subfunctor_factors_iff_pointwise]
  constructor
  · intro held X point
    change (P.map (𝟙 X.unop).op (generalized.app X point)) ∈ G.obj X
    simpa using held X point
  · intro held X point
    have atPoint := held X point
    change (P.map (𝟙 X.unop).op (generalized.app X point)) ∈ G.obj X at atPoint
    simpa using atPoint

end Mettapedia.OSLF.Binding.RepresentedReductionTheory
