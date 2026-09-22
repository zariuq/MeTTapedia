import Mettapedia.GSLT.LanguageDef.CertificateGSLTFunctionalHomPresheaf
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The semantic function object of certificate presheaves

The existing certificate-context category has finite products but need not
have exponentials. In its Type-valued presheaf category, the internal hom of
representable proof presheaves nevertheless exists. Its elements at a context
are exactly the open certificate maps from that context extended by an input
premise. This identifies the semantic function object without treating it as
an authored function-type constructor or changing judgmental equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory MonoidalCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

private def homToTensorNat
    {definition : ValidatedCalculusLanguageDef}
    (context input output : ClassifyingContext definition)
    (function : ClassifyingContext.concat context input ⟶ output) :
    (yoneda.obj input ⊗ yoneda.obj context) ⟶ yoneda.obj output where
  app stage := TypeCat.ofHom fun pair =>
    ClassifyingContext.pair pair.2 pair.1 ≫ function
  naturality source target substitution := by
    apply ConcreteCategory.hom_ext
    intro pair
    rcases pair with ⟨argument, environment⟩
    change ClassifyingContext.pair
        (substitution.unop ≫ environment)
        (substitution.unop ≫ argument) ≫ function =
      substitution.unop ≫
        (ClassifyingContext.pair environment argument ≫ function)
    rw [← ClassifyingContext.comp_pair, Category.assoc]

private def tensorNatToHom
    {definition : ValidatedCalculusLanguageDef}
    (context input output : ClassifyingContext definition)
    (transformation :
      (yoneda.obj input ⊗ yoneda.obj context) ⟶ yoneda.obj output) :
    ClassifyingContext.concat context input ⟶ output :=
  transformation.app (Opposite.op (ClassifyingContext.concat context input))
    (ClassifyingContext.sndProjection context input,
      ClassifyingContext.fstProjection context input)

/-- The presheaf-category function object has, at a context, precisely the
open certificate maps from that context extended by the input context. -/
def contextualFunctionObjectEquiv
    {definition : ValidatedCalculusLanguageDef}
    (context input output : ClassifyingContext definition) :
    ((yoneda.obj input).functorHom (yoneda.obj output)).obj
        (Opposite.op context) ≃
      (ClassifyingContext.concat context input ⟶ output) :=
  (yonedaEquiv.symm).trans
    ((FunctorToTypes.functorHomEquiv
      (yoneda.obj input) (yoneda.obj context)
      (yoneda.obj output)).trans {
        toFun := tensorNatToHom context input output
        invFun := homToTensorNat context input output
        left_inv := by
          intro transformation
          apply NatTrans.ext
          funext stage
          apply ConcreteCategory.hom_ext
          intro pair
          rcases pair with ⟨argument, environment⟩
          let substitution := ClassifyingContext.pair environment argument
          let canonical : (yoneda.obj input ⊗ yoneda.obj context).obj
              (Opposite.op (ClassifyingContext.concat context input)) := by
            change (ClassifyingContext.concat context input ⟶ input) ×
              (ClassifyingContext.concat context input ⟶ context)
            exact (ClassifyingContext.sndProjection context input,
              ClassifyingContext.fstProjection context input)
          have pointwise := transformation.naturality_apply
            (Quiver.Hom.op substitution) canonical
          change transformation.app stage
              (substitution ≫ ClassifyingContext.sndProjection context input,
                substitution ≫ ClassifyingContext.fstProjection context input) =
            substitution ≫
              tensorNatToHom context input output transformation
            at pointwise
          have argumentLaw :
              substitution ≫ ClassifyingContext.sndProjection context input =
                argument := ClassifyingContext.pair_snd environment argument
          have environmentLaw :
              substitution ≫ ClassifyingContext.fstProjection context input =
                environment := ClassifyingContext.pair_fst environment argument
          rw [argumentLaw, environmentLaw] at pointwise
          change substitution ≫
              tensorNatToHom context input output transformation =
            transformation.app stage (argument, environment)
          exact pointwise.symm
        right_inv := by
          intro function
          change ClassifyingContext.pair
              (ClassifyingContext.fstProjection context input)
              (ClassifyingContext.sndProjection context input) ≫
                function = function
          have pairIdentity :
              ClassifyingContext.pair
                  (ClassifyingContext.fstProjection context input)
                  (ClassifyingContext.sndProjection context input) =
                𝟙 (ClassifyingContext.concat context input) := by
            simpa using ClassifyingContext.pair_eta
              (𝟙 (ClassifyingContext.concat context input))
          rw [pairIdentity]
          exact Category.id_comp function
      })

/-- Evaluation of an internal-hom element is directly its component at the
extended context, applied to the two canonical projections. -/
theorem contextualFunctionObjectEquiv_apply
    {definition : ValidatedCalculusLanguageDef}
    (context input output : ClassifyingContext definition)
    (function : ((yoneda.obj input).functorHom (yoneda.obj output)).obj
      (Opposite.op context)) :
    contextualFunctionObjectEquiv context input output function =
      (function.app (Opposite.op (ClassifyingContext.concat context input))
        (Quiver.Hom.op (ClassifyingContext.fstProjection context input)))
        (ClassifyingContext.sndProjection context input) := by
  change tensorNatToHom context input output
      ((FunctorToTypes.functorHomEquiv
        (yoneda.obj input) (yoneda.obj context)
        (yoneda.obj output)) (yonedaEquiv.symm function)) = _
  change (function.app
      (Opposite.op (ClassifyingContext.concat context input))
      ((Quiver.Hom.op (ClassifyingContext.fstProjection context input)) ≫
        𝟙 (Opposite.op (ClassifyingContext.concat context input))))
      (ClassifyingContext.sndProjection context input) = _
  rw [Category.comp_id]

/-- Restriction of the presheaf internal hom is precomposition by the
corresponding ordered-context extension, so the comparison is natural in
the contextual input. -/
theorem contextualFunctionObjectEquiv_reindex
    {definition : ValidatedCalculusLanguageDef}
    (input output : ClassifyingContext definition)
    {source target : (ClassifyingContext definition)ᵒᵖ}
    (substitution : source ⟶ target)
    (function : ((yoneda.obj input).functorHom (yoneda.obj output)).obj source) :
    contextualFunctionObjectEquiv target.unop input output
        (((yoneda.obj input).functorHom (yoneda.obj output)).map
          substitution function) =
      extendContextRight input substitution.unop ≫
        contextualFunctionObjectEquiv source.unop input output function := by
  rw [contextualFunctionObjectEquiv_apply,
    contextualFunctionObjectEquiv_apply]
  let extension := extendContextRight input substitution.unop
  have naturality := function.naturality
    (Quiver.Hom.op extension)
    (Quiver.Hom.op (ClassifyingContext.fstProjection source.unop input))
  have pointwise := ConcreteCategory.congr_hom naturality
    (ClassifyingContext.sndProjection source.unop input)
  change
      (function.app (Opposite.op (ClassifyingContext.concat target.unop input))
        (Quiver.Hom.op (ClassifyingContext.fstProjection source.unop input) ≫
          Quiver.Hom.op extension))
        (extension ≫ ClassifyingContext.sndProjection source.unop input) =
      extension ≫
        (function.app
          (Opposite.op (ClassifyingContext.concat source.unop input))
          (Quiver.Hom.op (ClassifyingContext.fstProjection source.unop input)))
          (ClassifyingContext.sndProjection source.unop input) at pointwise
  have sndLaw : extension ≫
      ClassifyingContext.sndProjection source.unop input =
        ClassifyingContext.sndProjection target.unop input :=
    extendContextRight_snd input substitution.unop
  have fstOp :
      Quiver.Hom.op (ClassifyingContext.fstProjection source.unop input) ≫
          Quiver.Hom.op extension =
        substitution ≫
          Quiver.Hom.op (ClassifyingContext.fstProjection target.unop input) := by
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op
      (extendContextRight_fst input substitution.unop)
  rw [sndLaw, fstOp] at pointwise
  change
      (function.app (Opposite.op (ClassifyingContext.concat target.unop input))
        (substitution ≫
          Quiver.Hom.op (ClassifyingContext.fstProjection target.unop input)))
        (ClassifyingContext.sndProjection target.unop input) =
      extension ≫
        (function.app
          (Opposite.op (ClassifyingContext.concat source.unop input))
          (Quiver.Hom.op (ClassifyingContext.fstProjection source.unop input)))
          (ClassifyingContext.sndProjection source.unop input)
  exact pointwise

/-- For arbitrary input and output contexts, the contextual certificate-map
presheaf is naturally the internal hom of their Yoneda proof presheaves.
This is semantic closure, not a new authored function constructor. -/
def contextualFunctionFaceIso
    (definition : ValidatedCalculusLanguageDef)
    (input output : ClassifyingContext definition) :
    ((yoneda.obj input).functorHom (yoneda.obj output)) ≅
      contextualFunctionFace definition input output := by
  refine NatIso.ofComponents
    (fun context =>
      (contextualFunctionObjectEquiv context.unop input output).toIso)
    ?_
  intro source target substitution
  apply ConcreteCategory.hom_ext
  intro function
  exact contextualFunctionObjectEquiv_reindex input output substitution function

/-- The one-judgment self-function face is the corresponding specialization
of the general semantic internal-hom comparison. -/
def semanticFunctionFaceIso
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    ((yoneda.obj (⟨[goal]⟩ : ClassifyingContext definition)).functorHom
        (yoneda.obj (⟨[goal]⟩ : ClassifyingContext definition))) ≅
      functionHomFace definition goal :=
  contextualFunctionFaceIso definition ⟨[goal]⟩ ⟨[goal]⟩

/-- Even the actual internal hom of representable proof presheaves can fail
to be represented by an authored certificate context. The obstruction is
objectwise, hence stronger than failure of a natural representation. -/
theorem semanticFunctionObject_not_representable_of_no_closed
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (noClosed : ∀ candidate : Pattern,
      ¬ Nonempty (OpenDerivation definition [] candidate)) :
    ¬ ∃ exponent : ClassifyingContext definition,
      ∀ context : ClassifyingContext definition,
        Nonempty
          (((yoneda.obj (⟨[goal]⟩ : ClassifyingContext definition)).functorHom
            (yoneda.obj (⟨[goal]⟩ : ClassifyingContext definition))).obj
              (Opposite.op context) ≃
            (yoneda.obj exponent).obj (Opposite.op context)) := by
  rintro ⟨exponent, represented⟩
  apply functionHomFace_not_representable_of_no_closed definition goal noClosed
  refine ⟨exponent, ?_⟩
  intro context
  obtain ⟨equivalence⟩ := represented context
  exact ⟨(contextualFunctionObjectEquiv context
    (⟨[goal]⟩ : ClassifyingContext definition)
    (⟨[goal]⟩ : ClassifyingContext definition)).symm.trans equivalence⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.contextualFunctionObjectEquiv
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.contextualFunctionObjectEquiv_reindex
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.contextualFunctionFaceIso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.semanticFunctionFaceIso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.semanticFunctionObject_not_representable_of_no_closed
