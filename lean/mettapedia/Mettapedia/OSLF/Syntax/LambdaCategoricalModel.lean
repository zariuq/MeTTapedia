import Mettapedia.OSLF.Syntax.LambdaReductionSubobject
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# The Chapter 7 lambda reduction as a subobject of programs squared

The one-sorted lambda term presheaf is the distinguished program object in
this concrete presheaf model. Its categorical binary product agrees with the
sorted endpoint-pair presheaf, so the least scoped reduction gives an actual
subobject of `Pr × Pr`. Factorization through that mono is equivalent to the
four-rule reduction judgment at every test context. This model is not the
free finite-limit cartesian-closed classifying category of the presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaCategoricalModel

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.LambdaReductionSubobject

abbrev Base := (Syntactic.Ctxt sig)ᵒᵖ

/-- The context-indexed program carrier is already represented by the
single-variable context through `Syntactic.termPresheafYonedaIso`. -/
abbrev Programs : Base ⥤ Type := Syntactic.termPresheaf sig .term

/-- The explicit pointwise product of program presheaves. -/
abbrev ProgramPairs : Base ⥤ Type := FunctorToTypes.prod Programs Programs

/-- The sorted pair presheaf is the pointwise product in the one-sort lambda
instance. The comparison commutes with all simultaneous substitutions. -/
def sortedPairsIso : rootPairsPresheaf sig ≅ ProgramPairs where
  hom := {
    app X := TypeCat.ofHom (fun pair =>
      match pair with
      | ⟨.term, source, target⟩ => (source, target))
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      rintro ⟨sort, source, target⟩
      cases sort
      rfl }
  inv := {
    app X := TypeCat.ofHom (fun pair =>
      (⟨Srt.term, pair.1, pair.2⟩ : rootPairs sig X.unop.vars))
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      rintro ⟨source, target⟩
      rfl }
  hom_inv_id := by
    ext X pair
    rcases pair with ⟨sort, source, target⟩
    cases sort
    rfl
  inv_hom_id := by
    ext X pair
    rcases pair with ⟨source, target⟩
    all_goals rfl

/-- Mathlib's chosen categorical product is naturally isomorphic to the
actual sorted endpoint-pair presheaf. -/
noncomputable def productIso :
    Programs ⨯ Programs ≅ rootPairsPresheaf sig :=
  FunctorToTypes.binaryProductIso Programs Programs ≪≫ sortedPairsIso.symm

/-- The source reduction is a mono into the genuine categorical product of
the two program presheaves, not merely a substitution-stable predicate. -/
noncomputable def reductionSubobject : Subobject (Programs ⨯ Programs) :=
  Subobject.mk (reduction.ι ≫ productIso.inv)

/-- A family of program pairs factors through the reduction mono exactly
when all its pointwise pairs satisfy the scoped four-rule relation. -/
theorem factors_iff_steps
    {test : Base ⥤ Type} (endpoints : test ⟶ Programs ⨯ Programs) :
    reductionSubobject.Factors endpoints ↔
      ∀ (X : Base) (point : test.obj X),
        (match (endpoints ≫ productIso.hom).app X point with
          | ⟨.term, source, target⟩ =>
              LambdaContextualRung.Step X.unop.vars source target) := by
  have pointwise := factors_iff_pointwise_steps test
    (endpoints ≫ productIso.hom)
  constructor
  · intro factors
    obtain ⟨lift, equality⟩ :=
      (Subobject.mk_factors_iff _ _).mp factors
    change lift ≫ (reduction.ι ≫ productIso.inv) = endpoints at equality
    apply pointwise.mp
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫ reduction.ι = endpoints ≫ productIso.hom
    have afterIso := congrArg (fun arrow => arrow ≫ productIso.hom) equality
    calc
      lift ≫ reduction.ι =
          (lift ≫ reduction.ι) ≫ (productIso.inv ≫ productIso.hom) := by simp
      _ = (lift ≫ (reduction.ι ≫ productIso.inv)) ≫ productIso.hom :=
            congrArg (fun arrow => arrow ≫ productIso.hom)
              (Category.assoc lift reduction.ι productIso.inv)
      _ = endpoints ≫ productIso.hom := afterIso
  · intro held
    obtain ⟨lift, equality⟩ :=
      (Subobject.mk_factors_iff _ _).mp (pointwise.mpr held)
    change lift ≫ reduction.ι = endpoints ≫ productIso.hom at equality
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫ (reduction.ι ≫ productIso.inv) = endpoints
    have afterIso := congrArg (fun arrow => arrow ≫ productIso.inv) equality
    calc
      lift ≫ (reduction.ι ≫ productIso.inv) =
          (lift ≫ reduction.ι) ≫ productIso.inv := by
            exact (Category.assoc _ _ _).symm
      _ = (endpoints ≫ productIso.hom) ≫ productIso.inv := afterIso
      _ = endpoints := by simp [Category.assoc]

end Mettapedia.OSLF.Binding.LambdaCategoricalModel
