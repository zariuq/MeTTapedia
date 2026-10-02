import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassification
/-!
# Reading the free fold through a structured classifier functor

At every generalized valuation, the independent operational fold has the
underlying arrow obtained by applying the functor to the tree representative.
The comparison is proved for an abstract structured functor before it is
specialized to a presheaf or another concrete semantic target.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
open _root_.CategoryTheory
open CategoricalBindingModel SecondOrderContext IntrinsicScopedLocalPolynomial
open IntrinsicScopedLocalActedClassifier
universe u v
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {K : List (MetaArity S)}
variable {R : List (LocalRule S)} {equations : List (EqAxiom S K)}
namespace StructuredFunctor
variable (F : StructuredFunctor R equations (D := D))
/-- The underlying arrow of the interpreted retained tree is the image of
its actual classifier representative, at every generalized valuation. -/
theorem evaluate_valuation_val {a : Classifier R equations} {Z : D}
    (g : Z ⟶ F.carrier.obj a)
    (j : AuthoredPositionedRulePolynomial.Judgment (modelAt equations a.base))
    (tree : IntrinsicScopedLocalActedFree.Tree R _
      (IntrinsicScopedLocalActedFiniteContext.seeds R _ (events R equations a)) j) :
    ((F.valuation g).evaluate j tree).1 = g ≫ F.carrier.map (rep R equations j tree) := by
  have read := congrArg Subtype.val (F.evaluate_valuation g j tree)
  exact read.trans (F.treeEvent_val j tree g)
end StructuredFunctor
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
end
