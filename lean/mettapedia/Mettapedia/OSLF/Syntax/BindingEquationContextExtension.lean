import Mettapedia.OSLF.Syntax.BindingCloneContextComparison
import Mettapedia.OSLF.Syntax.BindingEquationExtension
import Mettapedia.OSLF.Syntax.EquationTransport

/-!
# Context categories under authored equation extension

Increasing the equation set gives a canonical functor between the context
categories of the corresponding binding-equation models. It preserves finite
products, is full and essentially surjective, and obeys the identity and
composition laws on the actual equation classes. New equations may still
identify previously distinct arrows.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationExtension

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

variable {S : Signature} {M : List (MetaArity S)}

/-- Inclusion of authored equation obligations induces a functor between
finite-product context categories of their initial binding-clone models. -/
noncomputable def comparisonContextFunctor
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    ContextObject ((BindingEquationQuotientModel.algebra E).substitution.toClone) ⥤
      ContextObject ((BindingEquationQuotientModel.algebra F).substitution.toClone) :=
  (comparisonHom includeAxiom).toCloneTranslation.contextFunctor

theorem comparisonContextFunctor_preservesFiniteProducts
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    CategoryTheory.Limits.PreservesFiniteProducts
      (comparisonContextFunctor includeAxiom) :=
  (comparisonHom includeAxiom).toCloneTranslation.preservesFiniteProducts

/-- The context functor maps a single-output equation class by the canonical
quotient comparison, on every representative. -/
theorem comparisonContextFunctor_operation
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    (comparisonContextFunctor includeAxiom).map
      (((BindingEquationQuotientModel.algebra E).substitution.toClone).operationAsSingletonMorphism
        (Quotient.mk _ term)) =
      ((BindingEquationQuotientModel.algebra F).substitution.toClone).operationAsSingletonMorphism
        (Quotient.mk _ term) := by
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  exact comparisonHom_mk includeAxiom term

instance comparisonContextFunctor_full
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    (comparisonContextFunctor includeAxiom).Full where
  map_surjective := by
    intro source target arrow
    refine ⟨fun i => (comparisonHom_surjective includeAxiom (arrow i)).choose, ?_⟩
    funext i
    exact (comparisonHom_surjective includeAxiom (arrow i)).choose_spec

/-- The quotient extension changes arrows while retaining every context. -/
theorem comparisonContextFunctor_obj_surjective
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    Function.Surjective (comparisonContextFunctor includeAxiom).obj := by
  intro target
  cases target with
  | mk context marker =>
      refine ⟨ContextObject.ofList _ context, ?_⟩
      cases marker
      rfl

instance comparisonContextFunctor_essSurj
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    (comparisonContextFunctor includeAxiom).EssSurj :=
  Functor.essSurj_of_surj
    (comparisonContextFunctor_obj_surjective includeAxiom)

/-- A presentation compared with itself acts identically on contexts and
substitutions. -/
theorem comparisonContextFunctor_id (E : List (EqAxiom S M)) :
    comparisonContextFunctor (axiomInclusion_refl E) =
      Functor.id
        (ContextObject ((BindingEquationQuotientModel.algebra E).substitution.toClone)) := by
  have mapEq :
      (comparisonHom (axiomInclusion_refl E)).toCloneTranslation =
        Mettapedia.GSLT.LanguageDef.CloneTranslation.id
          ((BindingEquationQuotientModel.algebra E).substitution.toClone) := by
    apply Mettapedia.GSLT.LanguageDef.CloneTranslation.ext
    intro Γ sort q
    induction q using Quotient.inductionOn with
    | _ term => exact comparisonHom_mk (axiomInclusion_refl E) term
  change (comparisonHom (axiomInclusion_refl E)).toCloneTranslation.contextFunctor =
    Functor.id
      (ContextObject ((BindingEquationQuotientModel.algebra E).substitution.toClone))
  rw [mapEq]
  exact Mettapedia.GSLT.LanguageDef.CloneTranslation.contextFunctor_id _

/-- Extending authored equation lists in two stages agrees with their direct
extension on all context substitutions. -/
theorem comparisonContextFunctor_comp
    {E F G : List (EqAxiom S M)}
    (first : AxiomInclusion E F) (later : AxiomInclusion F G) :
    comparisonContextFunctor (axiomInclusion_trans first later) =
      comparisonContextFunctor first ⋙ comparisonContextFunctor later := by
  have mapEq :
      (comparisonHom (axiomInclusion_trans first later)).toCloneTranslation =
        ((comparisonHom first).toCloneTranslation).comp
          ((comparisonHom later).toCloneTranslation) := by
    apply Mettapedia.GSLT.LanguageDef.CloneTranslation.ext
    intro Γ sort q
    exact comparisonHom_comp first later q
  change (comparisonHom (axiomInclusion_trans first later)).toCloneTranslation.contextFunctor =
    ((comparisonHom first).toCloneTranslation).contextFunctor ⋙
      ((comparisonHom later).toCloneTranslation).contextFunctor
  rw [mapEq]
  exact Mettapedia.GSLT.LanguageDef.CloneTranslation.contextFunctor_comp _ _

/-- Passing from raw authored syntax to the stronger quotient is independent
of whether the weaker quotient is formed on the way. -/
theorem quotientContextFunctor_extension
    {E F : List (EqAxiom S M)} (includeAxiom : AxiomInclusion E F) :
    Mettapedia.OSLF.Binding.quotientContextFunctor F =
      Mettapedia.OSLF.Binding.quotientContextFunctor E ⋙
        comparisonContextFunctor includeAxiom := by
  have mapEq :
      (BindingEquationQuotientModel.projection F).toCloneTranslation =
        ((BindingEquationQuotientModel.projection E).toCloneTranslation).comp
          ((comparisonHom includeAxiom).toCloneTranslation) := by
    apply Mettapedia.GSLT.LanguageDef.CloneTranslation.ext
    intro Γ sort term
    exact (comparisonHom_mk includeAxiom term).symm
  change (BindingEquationQuotientModel.projection F).toCloneTranslation.contextFunctor =
    ((BindingEquationQuotientModel.projection E).toCloneTranslation).contextFunctor ⋙
      ((comparisonHom includeAxiom).toCloneTranslation).contextFunctor
  rw [mapEq]
  exact Mettapedia.GSLT.LanguageDef.CloneTranslation.contextFunctor_comp _ _

end Mettapedia.OSLF.Binding.BindingEquationExtension

namespace Mettapedia.OSLF.Binding.BindingEquationContextControls

open Mettapedia.OSLF.Binding.BindingEquationExtension
open Mettapedia.OSLF.Binding.Duplication
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

private theorem emptyIncluded :
    AxiomInclusion ([] : List (EqAxiom dsig [])) dupE := by
  intro i
  exact Fin.elim0 i

private noncomputable abbrev emptyClone :=
  (BindingEquationQuotientModel.algebra
    ([] : List (EqAxiom dsig []))).substitution.toClone

private noncomputable abbrev oneEmpty : ContextObject emptyClone :=
  ContextObject.ofList emptyClone [Srt2.tm]

private noncomputable def bareHole : oneEmpty ⟶ oneEmpty :=
  emptyClone.operationAsSingletonMorphism (Quotient.mk _ hole1)

private noncomputable def duplicatedHole : oneEmpty ⟶ oneEmpty :=
  emptyClone.operationAsSingletonMorphism (Quotient.mk _ hole2)

private theorem holes_distinct : bareHole ≠ duplicatedHole := by
  intro equal
  have classesEqual := congrFun equal (0 : Fin 1)
  have termsEqual : hole1 = hole2 :=
    eqClosure_empty_eq (Quotient.exact classesEqual)
  have countsEqual := congrArg (holeCount (S := dsig) (Γ := [])
    (c := Srt2.tm)) termsEqual
  rw [holeCount_hole1, holeCount_hole2] at countsEqual
  omega

private theorem holes_identified :
    (comparisonContextFunctor emptyIncluded).map bareHole =
      (comparisonContextFunctor emptyIncluded).map duplicatedHole := by
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  change (comparisonHom emptyIncluded).raw.map (Quotient.mk _ hole1) =
    (comparisonHom emptyIncluded).raw.map (Quotient.mk _ hole2)
  rw [comparisonHom_mk, comparisonHom_mk]
  exact Quotient.sound hole1_eq_hole2

/-- A genuine authored equation extension can identify previously distinct
substitution arrows, so fullness and object-surjectivity do not imply
faithfulness. -/
theorem equation_extension_not_faithful :
    ¬ (comparisonContextFunctor emptyIncluded).Faithful := by
  intro faithful
  exact holes_distinct (faithful.map_injective holes_identified)

end Mettapedia.OSLF.Binding.BindingEquationContextControls
