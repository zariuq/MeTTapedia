import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafCategoricalModel
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBaseAdapter
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafReduction
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEventsExtension
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafExtensionFold
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images

/-!
# Interpretation in the actual operational presheaf model

The categorical model uses the original clone and its retained local events.
Its paired endpoint image is the concrete witness predicate, and the genuine
left Kan extension maps the generic reduction epimorphically onto that image.
No preservation of image inclusions is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open IntrinsicScopedLocalPolynomial (LocalRule)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel)
open IntrinsicScopedOperationalPresheafPrograms (target power)
open IntrinsicScopedOperationalPresheafCategoricalModel (categoricalModel)

universe u
variable {S : Signature} {schema : List (MetaArity S)}
variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) (Y : SubstitutionModel.{u,u} R A)
variable (equations : List (EqAxiom S schema))
variable (satisfies : BindingEquationInterpretation.Satisfies A equations)

/-- The same construction on the actual authored contextual equation quotient. -/
def quotientModel
    (events : SubstitutionModel.{0,0} R (BindingEquationQuotientModel.algebra equations)) :
    IntrinsicScopedLocalActedCategoricalModels.CategoricalModel R equations
      (D := target (BindingEquationQuotientModel.algebra equations)) :=
  categoricalModel R events equations (BindingEquationQuotientModel.algebra_satisfies equations)

/-- Actual substitution-closed local trees over equation-class states give
the canonical quotient instance. Their seeds are indexed by those states;
this construction makes no claim of raw-event descent through equations. -/
def quotientFreeModel
    (Seed : (s : S.Srt) →
      IntrinsicScopedConditionalJudgmentCategory.State
        (BindingEquationQuotientModel.algebra equations) s → Type) :
    IntrinsicScopedLocalActedCategoricalModels.CategoricalModel R equations
      (D := target (BindingEquationQuotientModel.algebra equations)) :=
  quotientModel R equations
    (IntrinsicScopedLocalActedFree.freeModel R (BindingEquationQuotientModel.algebra equations) Seed)

/-- The constructed model's actual endpoint map is the retained-event graph map. -/
theorem eventEndpoints_eq (Γ : Ctx S) (s : S.Srt) :
    (categoricalModel R Y equations satisfies).toEventModel.eventEndpoints Γ s =
      FreePresheafEventImage.endpointMap
        (IntrinsicScopedOperationalPresheafReduction.graph Y.toAction Γ s) := rfl

/-- The categorical image is the actual pointwise retained-witness range. -/
def reductionImageIso (Γ : Ctx S) (s : S.Srt) :
    image ((categoricalModel R Y equations satisfies).toEventModel.eventEndpoints Γ s) ≅
      (IntrinsicScopedOperationalPresheafReduction.reduction Y.toAction Γ s).toFunctor :=
  IsImage.isoExt (Image.isImage _)
    (FunctorToTypes.monoFactorisationIsImage
      ((categoricalModel R Y equations satisfies).toEventModel.eventEndpoints Γ s))

/-- The image comparison preserves the actual program endpoint pair. -/
theorem reductionImageIso_hom_ι (Γ : Ctx S) (s : S.Srt) :
    (reductionImageIso R Y equations satisfies Γ s).hom ≫
        (IntrinsicScopedOperationalPresheafReduction.reduction Y.toAction Γ s).ι =
      image.ι ((categoricalModel R Y equations satisfies).toEventModel.eventEndpoints Γ s) :=
  IsImage.isoExt_hom_m _ _

/-- The image comparison retains the same event's concrete endpoints. -/
theorem factorThruImage_reductionImageIso (Γ : Ctx S) (s : S.Srt) :
    factorThruImage ((categoricalModel R Y equations satisfies).toEventModel.eventEndpoints Γ s) ≫
        (reductionImageIso R Y equations satisfies Γ s).hom =
      Subfunctor.toRange (FreePresheafEventImage.endpointMap
        (IntrinsicScopedOperationalPresheafReduction.graph Y.toAction Γ s)) :=
  IsImage.e_isoExt_hom _ _

/-- The genuine extension maps generic reduction onto the concrete retained-witness predicate. -/
def extensionReductionComparison (Γ : Ctx S) (s : S.Srt) :
    (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
      (categoricalModel R Y equations satisfies)).obj
        (IntrinsicScopedLocalActedPresheaf.genericReduction.{u} R equations Γ s).toFunctor ⟶
      (IntrinsicScopedOperationalPresheafReduction.reduction Y.toAction Γ s).toFunctor :=
  IntrinsicScopedLocalActedPresheaf.extensionReductionComparison.{0}
      (categoricalModel R Y equations satisfies) Γ s ≫
    (reductionImageIso R Y equations satisfies Γ s).hom

/-- Coverage is epimorphic even when the extension does not preserve the image inclusion. -/
theorem extensionReductionComparison_epi (Γ : Ctx S) (s : S.Srt) :
    Epi (extensionReductionComparison R Y equations satisfies Γ s) := by
  let := IntrinsicScopedLocalActedPresheaf.extensionReductionComparison_epi.{0}
    (categoricalModel R Y equations satisfies) Γ s
  exact epi_comp _ _

/-- Epimorphic coverage is actual surjectivity at every original clone stage. -/
theorem extensionReductionComparison_surjective (Γ : Ctx S) (s : S.Srt)
    (X : IntrinsicScopedConditionalPresheaf.Base A) :
    Function.Surjective ((extensionReductionComparison R Y equations satisfies Γ s).app X) := by
  let := extensionReductionComparison_epi R Y equations satisfies Γ s
  exact surjective_of_epi _

/-- An extended generic reduction section exists over precisely those endpoint
pairs supported by an original local witness in the full extended context. -/
theorem extension_section_iff (Γ : Ctx S) (s : S.Srt)
    (X : IntrinsicScopedConditionalPresheaf.Base A)
    (first last : (power A Γ s).obj X) :
    (∃ input : ((IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
        (categoricalModel R Y equations satisfies)).obj
          (IntrinsicScopedLocalActedPresheaf.genericReduction.{u} R equations Γ s).toFunctor).obj X,
      ((extensionReductionComparison R Y equations satisfies Γ s).app X input).val =
        (first, last)) ↔
      Nonempty (Y.carrier ⟨Γ ++ X.unop.context, s,
        MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s first,
        MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s last⟩) := by
  constructor
  · rintro ⟨input, endpoints⟩
    apply (IntrinsicScopedOperationalPresheafReduction.mem_reduction_iff
      Y.toAction Γ s X first last).mp
    exact endpoints ▸ ((extensionReductionComparison R Y equations satisfies Γ s).app X input).property
  · intro witness
    let pair : (IntrinsicScopedOperationalPresheafReduction.reduction Y.toAction Γ s).toFunctor.obj X :=
      ⟨(first, last), (IntrinsicScopedOperationalPresheafReduction.mem_reduction_iff
        Y.toAction Γ s X first last).mpr witness⟩
    obtain ⟨input, covers⟩ := extensionReductionComparison_surjective R Y equations satisfies Γ s X pair
    exact ⟨input, congrArg Subtype.val covers⟩

/-- The comparison records the same actual program endpoint pair. -/
theorem extensionReductionComparison_ι (Γ : Ctx S) (s : S.Srt) :
    extensionReductionComparison R Y equations satisfies Γ s ≫
        (IntrinsicScopedOperationalPresheafReduction.reduction Y.toAction Γ s).ι =
      (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
        (categoricalModel R Y equations satisfies)).map
          (IntrinsicScopedLocalActedPresheaf.genericReduction.{u} R equations Γ s).ι ≫
        (IntrinsicScopedLocalActedPresheaf.interpretationPairIso
          (categoricalModel R Y equations satisfies)
          (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
            (categoricalModel R Y equations satisfies))
          (IntrinsicScopedLocalActedPresheaf.modelPresheafExtensionRestriction.{0}
            (categoricalModel R Y equations satisfies)) Γ s).hom := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, reductionImageIso_hom_ι]
  exact IntrinsicScopedLocalActedPresheaf.extensionReductionComparison_ι.{0}
    (categoricalModel R Y equations satisfies) Γ s

/-- An extended generic event lands at its original retained event's endpoint pair. -/
theorem extensionReductionComparison_events (Γ : Ctx S) (s : S.Srt) :
    (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
      (categoricalModel R Y equations satisfies)).map
        (Subfunctor.toRange
          (IntrinsicScopedLocalActedPresheaf.genericEndpointMap.{u} R equations Γ s)) ≫
      extensionReductionComparison R Y equations satisfies Γ s =
        (IntrinsicScopedLocalActedPresheaf.interpretationEventIso
          (categoricalModel R Y equations satisfies)
          (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
            (categoricalModel R Y equations satisfies))
          (IntrinsicScopedLocalActedPresheaf.modelPresheafExtensionRestriction.{0}
            (categoricalModel R Y equations satisfies)) Γ s).hom ≫
        Subfunctor.toRange (FreePresheafEventImage.endpointMap
          (IntrinsicScopedOperationalPresheafReduction.graph Y.toAction Γ s)) := by
  let N := categoricalModel R Y equations satisfies
  let I := reductionImageIso R Y equations satisfies Γ s
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun map => map ≫ I.hom)
      (IntrinsicScopedLocalActedPresheaf.extensionReductionComparison_events.{0} N Γ s)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun map =>
          (IntrinsicScopedLocalActedPresheaf.interpretationEventIso N
            (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0} N)
            (IntrinsicScopedLocalActedPresheaf.modelPresheafExtensionRestriction.{0} N) Γ s).hom ≫ map)
          (factorThruImage_reductionImageIso R Y equations satisfies Γ s))))

/-- Isomorphism needs the additional, explicit preservation of the reduction inclusion. -/
theorem extensionReductionComparison_isIso (Γ : Ctx S) (s : S.Srt)
    [Mono ((IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
      (categoricalModel R Y equations satisfies)).map
        (IntrinsicScopedLocalActedPresheaf.genericReduction.{u} R equations Γ s).ι)] :
    IsIso (extensionReductionComparison R Y equations satisfies Γ s) := by
  let := IntrinsicScopedLocalActedPresheaf.extensionReductionComparison_isIso.{0}
    (categoricalModel R Y equations satisfies) Γ s
  exact IsIso.comp_isIso

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafInterpretation
