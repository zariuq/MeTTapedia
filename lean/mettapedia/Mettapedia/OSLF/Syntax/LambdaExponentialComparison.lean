import Mettapedia.OSLF.Syntax.BoundTermExponential

/-!
# Categorical body evaluation and authored beta in the Chapter 7 lambda model

The binder-extended program presheaf satisfies the exponential hom-set
property. Its canonical evaluation map is capture-avoiding body application.
The authored application of an authored abstraction is a distinct syntax tree;
the checked comparison is the operational beta witness in the reduction
subobject, rather than an equality of raw terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaExponentialComparison

open CategoryTheory
open Mettapedia.OSLF.Binding.ContextualTermAbstraction
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaPresheafOperations

/-- The general exponential hom equivalence specialized to the authored
lambda signature, for every contextual test presheaf. -/
def lambdaHomEquiv (test : Base ⥤ Type) :
    (FunctorToTypes.prod test Programs ⟶ Programs) ≃
      (test ⟶ Bodies) :=
  boundTermHomEquiv test Srt.term Srt.term

/-- Evaluation obtained from the identity of the representing body object. -/
def exponentialEvaluation : FunctorToTypes.prod Bodies Programs ⟶ Programs :=
  uncurryBody Bodies Srt.term Srt.term (𝟙 Bodies)

/-- Categorical evaluation is exactly the previously defined
capture-avoiding body application, at every open context. -/
theorem exponentialEvaluation_eq_bodyAt : exponentialEvaluation = bodyAt := by
  ext X pair
  rfl

/-- The canonical evaluation map curries back to the identity of the body
object, as required by the exponential universal property. -/
theorem curry_exponentialEvaluation :
    curryBody Bodies Srt.term Srt.term exponentialEvaluation = 𝟙 Bodies := by
  exact curry_uncurry Bodies Srt.term Srt.term (𝟙 Bodies)

/-- The beta contractum in the operational square is the categorical
evaluation of the body at its argument. -/
theorem betaPairs_use_exponentialEvaluation :
    betaPairs =
      FunctorToTypes.prod.lift betaRedex exponentialEvaluation ≫
        sortedPairsIso.inv := by
  rw [exponentialEvaluation_eq_bodyAt]
  rfl

/-- Despite the exponential representation, authored beta is not an equality
of raw syntax at the open variable control. -/
theorem open_beta_not_exponential_equality :
    betaRedex.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) ≠
    exponentialEvaluation.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) := by
  rw [exponentialEvaluation_eq_bodyAt]
  exact open_beta_not_raw_equality

end Mettapedia.OSLF.Binding.LambdaExponentialComparison
