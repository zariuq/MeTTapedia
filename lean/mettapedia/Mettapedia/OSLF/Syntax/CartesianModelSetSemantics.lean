import Mettapedia.OSLF.Syntax.CartesianModelFiniteGeneration
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Set-valued semantics of relative finite-limit presentations

A cartesian model interprets a finite-presentation object by its set of maps
into that model. Since represented hom-functors send colimits to limits, this
is a finite-limit-preserving extension of the original set-valued model. The
converse classification of all such extensions is a separate universal-property
obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The inclusion of finite presentations computes finite colimits in the
ambient cartesian model category. -/
theorem finitePresentationInclusion_preservesFiniteColimits :
    PreservesFiniteColimits
      (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι := by
  let P := isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}
  refine ⟨fun J _ _ => ?_⟩
  have hJ : HasCardinalLT (Arrow J) Cardinal.aleph0.{0} :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have hclosed : P.IsClosedUnderColimitsOfShape J :=
    isClosedUnderColimitsOfShape_isCardinalPresentable (Models C) hJ
  have hambient : HasColimitsOfShape J (Models C) := inferInstance
  have hcreates : CreatesColimitsOfShape J P.ι := inferInstance
  change PreservesColimitsOfShape J P.ι
  exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape P.ι

/-- A cartesian model evaluates each finite presentation by its solutions. -/
noncomputable def finitePresentationSemantics (M : Models C) :
    FinitePresentationObjects C ⥤ Type :=
  ((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).op ⋙ yoneda.obj M

/-- Model morphisms act on solution sets by postcomposition. This is the
functorial action of the set-valued interpretation, not only its objects. -/
noncomputable def finitePresentationSemanticsFunctor :
    Models C ⥤ (FinitePresentationObjects C ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    ((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).op

/-- Solution-set semantics preserves all finite limits of the relative
finite-limit presentation category. -/
theorem finitePresentationSemantics_preservesFiniteLimits (M : Models C) :
    PreservesFiniteLimits (finitePresentationSemantics C M) := by
  have hι : PreservesFiniteColimits
      (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι :=
    finitePresentationInclusion_preservesFiniteColimits C
  have hop : PreservesFiniteLimits
      ((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).op :=
    preservesFiniteLimits_op _
  have hy : PreservesLimits (yoneda.obj M) := inferInstance
  change PreservesFiniteLimits
    (((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).op ⋙ yoneda.obj M)
  exact comp_preservesFiniteLimits _ _

/-- At an authored context, a solution of the represented presentation is
exactly an element of the original cartesian model at that context. -/
noncomputable def authoredContextSolutionEquiv (M : Models C) (X : C) :
    (authoredContext C ⋙ finitePresentationSemantics C M).obj X ≃
      M.1.obj X := by
  change ((representedContext C).obj (Opposite.op X) ⟶ M) ≃ M.1.obj X
  refine ⟨fun f => coyonedaEquiv f.hom,
    fun x => ObjectProperty.homMk (coyonedaEquiv.symm x), ?_, ?_⟩
  · intro f
    apply ObjectProperty.hom_ext
    exact coyonedaEquiv.symm_apply_apply f.hom
  · intro x
    exact coyonedaEquiv.apply_symm_apply x

/-- Restricting a model's finite-limit semantics to authored contexts recovers
that model by the covariant Yoneda lemma, naturally in context substitutions. -/
noncomputable def authoredContextSemanticsIso (M : Models C) :
    authoredContext C ⋙ finitePresentationSemantics C M ≅ M.1 := by
  refine NatIso.ofComponents
    (fun X => (authoredContextSolutionEquiv C M X).toIso) ?_
  intro X Y f
  ext a
  change ((representedContext C).obj (Opposite.op X) ⟶ M) at a
  change coyonedaEquiv (((representedContext C).map f.op ≫ a).hom) =
    M.1.map f (coyonedaEquiv a.hom)
  exact (coyonedaEquiv_naturality a.hom f).symm

/-- Yoneda recovery is also natural in model morphisms: restriction of the
whole solution-set semantics functor is the original model inclusion. -/
noncomputable def modelSemanticsRestrictionIso :
    finitePresentationSemanticsFunctor C ⋙
      (Functor.whiskeringLeft C (FinitePresentationObjects C) Type).obj
        (authoredContext C) ≅ (ProductModel C).ι := by
  refine NatIso.ofComponents (fun M => authoredContextSemanticsIso C M) ?_
  intro M N f
  ext X a
  change ((representedContext C).obj (Opposite.op X) ⟶ M) at a
  change coyonedaEquiv (a.hom ≫ f.hom) =
    f.hom.app X (coyonedaEquiv a.hom)
  exact coyonedaEquiv_comp a.hom f.hom

/-- The solution-set functor is the restricted Yoneda functor, with its
universe bookkeeping removed by the canonical ULift isomorphism. -/
noncomputable def finitePresentationSemanticsULiftIso :
    Presheaf.restrictedULiftYoneda.{0}
        (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι ≅
      finitePresentationSemanticsFunctor C := by
  exact Functor.isoWhiskerRight (uliftYonedaIsoYoneda (C := Models C))
    ((Functor.whiskeringLeft _ _ _).obj
      ((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).op)

/-- Finite presentations determine model maps: the solution-set semantics
functor is fully faithful, by density of the finite-presentation inclusion. -/
theorem finitePresentationSemanticsFunctor_full :
    (finitePresentationSemanticsFunctor C).Full := by
  have hdense := finitePresentationInclusion_dense C
  exact Functor.Full.of_iso (finitePresentationSemanticsULiftIso C)

theorem finitePresentationSemanticsFunctor_faithful :
    (finitePresentationSemanticsFunctor C).Faithful := by
  have hdense := finitePresentationInclusion_dense C
  exact Functor.Faithful.of_iso (finitePresentationSemanticsULiftIso C)

omit [HasFiniteProducts C] in
/-- Finite-presentation solution sets commute with filtered colimits of
cartesian models, because every testing presentation is finitely presentable. -/
theorem finitePresentationSemanticsFunctor_finitary :
    (finitePresentationSemanticsFunctor C).IsCardinalAccessible
      Cardinal.aleph0.{0} := by
  refine ⟨fun J _ _ => ?_⟩
  apply preservesColimitsOfShape_of_evaluation
    (finitePresentationSemanticsFunctor C) J
  intro P
  change PreservesColimitsOfShape J
    (coyoneda.obj (Opposite.op P.unop.1))
  have hP : IsCardinalPresentable P.unop.1 Cardinal.aleph0.{0} :=
    P.unop.2
  exact (coyoneda.obj (Opposite.op P.unop.1)).preservesColimitsOfShape_of_isCardinalAccessible
    Cardinal.aleph0 J

end Mettapedia.OSLF.CartesianContextModels
