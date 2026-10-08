import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualProducts
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualControls

/-!
# Codomain annotations and domain-only lambda views

Two genuinely formed lambdas have the same domain and body, with different
generated-equal codomain annotations. The generated term quotient identifies
them. A domain-only view therefore preserves this particular quotient class,
but cannot reconstruct both authored raw annotations. This distinguishes a
surface view from the evidence-retaining core presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.LambdaAnnotationBoundaryControls

open Contextual ContextualControls

def firstLambda := Products.rawLam witness
def secondLambda := Products.rawLam convertedWitness

/-- The domain-only view has no claim to infer an authored codomain. -/
def domainBodyView {n : Nat} (code : TermExpr symbols n) :
    Option (TypeExpr symbols n × TermExpr symbols (n + 1)) :=
  match code with
  | .lam domain _ body => some (domain, body)
  | _ => none

theorem both_lambdas_are_formed :
    Holds signature (.term functionContext.raw firstLambda.code
      (Contextual.DependentTypes.rawPi firstFamily firstAnnotation).code) ∧
    Holds signature (.term functionContext.raw secondLambda.code
      (Contextual.DependentTypes.rawPi firstFamily secondAnnotation).code) :=
  ⟨firstLambda.typed, secondLambda.typed⟩

theorem domain_only_views_agree :
    domainBodyView firstLambda.code = domainBodyView secondLambda.code := rfl

theorem retained_codomain_annotations_differ : firstAnnotation.code ≠ secondAnnotation.code := by
  intro same
  have arguments := eq_of_heq (TypeExpr.family.inj same).2
  have first := congrFun arguments 0
  cases first

theorem authored_lambda_codes_differ : firstLambda.code ≠ secondLambda.code := by
  intro same
  exact retained_codomain_annotations_differ (TermExpr.lam.inj same).2.1

/-- Mixed annotation congruence preserves the generated semantic class. -/
theorem generated_lambda_classes_agree : QTerm.mk firstLambda = QTerm.mk secondLambda := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · exact conclude (.piCongruence functionContext.raw firstFamily.code firstFamily.code
      firstAnnotation.code secondAnnotation.code)
      ⟨typeEquality_refl firstFamily, annotations_substituted, secondAnnotation.formed, trivial⟩
  · exact conclude (.lambdaAnnotationCongruence functionContext.raw firstFamily.code
      firstFamily.code firstAnnotation.code secondAnnotation.code witness.code convertedWitness.code)
      ⟨typeEquality_refl firstFamily, annotations_substituted, secondAnnotation.formed,
        termEquality_refl witness, convertedWitness.typed, trivial⟩

theorem no_exact_raw_reconstruction :
    ¬ ∃ reconstruct : Option (TypeExpr symbols 1 × TermExpr symbols 2) → TermExpr symbols 1,
      reconstruct (domainBodyView firstLambda.code) = firstLambda.code ∧
        reconstruct (domainBodyView secondLambda.code) = secondLambda.code := by
  rintro ⟨reconstruct, first, second⟩
  have views := congrArg reconstruct domain_only_views_agree
  exact authored_lambda_codes_differ (first.symm.trans (views.trans second))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.LambdaAnnotationBoundaryControls
