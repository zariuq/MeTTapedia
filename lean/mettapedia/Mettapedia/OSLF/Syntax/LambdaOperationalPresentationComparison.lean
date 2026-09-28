import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory
import Mettapedia.OSLF.Syntax.LambdaRulePolynomialMorphism

/-!
# The authored lambda rule system in the free operational adjunction

The generic free equipped-presentation adjunction specializes to the
semantic beta and congruence rules. Its universal interpretation agrees
with the earlier context-aware interpreter on every firing history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaOperationalPresentationComparison

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial
open Mettapedia.OSLF.Binding.LambdaRulePolynomialMorphism
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

universe u

/-- The authored lambda rules equipped with their free proof-relevant
firing-tree algebra. -/
def lambdaFree (A : BindingCloneAlgebra.Algebra.{u} sig) :=
  IndexedOperationalPresentationCategory.free (lambdaPresentation A)

/-- The general universal lift of a clone interpretation is the existing
semantic interpretation of each complete beta/congruence firing history. -/
theorem lambda_lift_agrees
    {A B : BindingCloneAlgebra.Algebra.{u} sig}
    (h : FreeBindingClone.Hom A B)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    (IndexedOperationalPresentationCategory.lift (lambdaFree B)
      (lambdaPresentationMap h)).toFun () j tree =
        mapTree h j tree := by
  exact relativeFold_lambda_eq_mapTree h j tree

#print axioms lambda_lift_agrees

end Mettapedia.OSLF.Binding.LambdaOperationalPresentationComparison
