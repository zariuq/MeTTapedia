import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramConstructorOperator
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramConstructorMetavariable
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorFoldRead
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEvents

/-!
# The structured Yoneda interpretation of an authored operational classifier

The real program restriction has the represented products and binder powers,
with their evaluation, currying and all three constructor laws. Together with
Yoneda's preservation of the actual event-projection pullbacks, these laws
supply a model through the existing classifying equivalence. Its classifying
functor agrees naturally with Yoneda and reads each retained firing through
the original free fold, at every generalized valuation.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
open IntrinsicScopedLocalActedCategoricalModels
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- The actual program restriction obeys all constructor laws, using the
represented selected powers and their proved ordered evaluation. -/
def programPreserving : Preserving (programRestriction.{w} R equations) where
  toPreservingData := programData R equations
  meaning_var := programRestrictionData_meaning_var R equations
  meaning_op := programRestrictionData_meaning_op R equations
  meaning_meta := programRestrictionData_meaning_meta R equations

/-- Lifted Yoneda preserves the independently proved program structure and
each actual pullback used to reindex an event variable. -/
def yonedaStructured : StructuredFunctor R equations (D := Presheaf.{w} R equations) where
  carrier := embedding R equations
  program := programPreserving R equations
  pullback f j := embedding_eventPullback R equations f j

/-- Recovery through the classifying equivalence supplies the generic
categorical model, including its substitution and ordered rule actions. -/
abbrev yonedaModel : CategoricalModel R equations (D := Presheaf.{w} R equations) :=
  (yonedaStructured.{w} R equations).model

/-- The recovered model's classifying functor agrees naturally with the
actual lifted Yoneda embedding on every program and event context. -/
def yonedaClassifyingIso : (yonedaModel.{w} R equations).classifyingFunctor ≅
    embedding R equations :=
  (yonedaStructured.{w} R equations).counitIso

/-- At the small presheaf universe the same recovered model classifies
through ordinary Yoneda. -/
def yonedaClassifyingZeroIso : (yonedaModel.{0} R equations).classifyingFunctor ≅ yoneda :=
  yonedaClassifyingIso.{0} R equations ≪≫ embeddingZeroIso R equations

/-- The comparison is natural at every classifier arrow, including
substituted event leaves and authored rule-constructor representatives. -/
theorem yonedaClassifyingIso_natural {a b : Classifier R equations} (f : a ⟶ b) :
    (yonedaModel.{w} R equations).classifyingFunctor.map f ≫
      (yonedaClassifyingIso.{w} R equations).hom.app b =
    (yonedaClassifyingIso.{w} R equations).hom.app a ≫ (embedding R equations).map f :=
  (yonedaClassifyingIso.{w} R equations).hom.naturality f

/-- The natural comparison retains the complete program-and-event
valuation of every generalized point. -/
theorem yonedaClassifyingIso_valuation (a : Classifier R equations)
    {Z : Presheaf.{w} R equations} (g : Z ⟶ (embedding R equations).obj a) :
    ((yonedaModel.{w} R equations).valuationsRepresentableBy a).homEquiv
      (g ≫ (yonedaClassifyingIso.{w} R equations).inv.app a) =
    ((yonedaStructured.{w} R equations).valuationsRepresentableBy a).homEquiv g :=
  (yonedaStructured.{w} R equations).homEquiv_counitIso_inv a g

/-- Interpretation of every retained tree, including substituted event
leaves and binder-local rule nodes, is the actual Yoneda image of its
representative arrow at every generalized valuation. -/
theorem yoneda_firing_evaluate {a : Classifier R equations}
    {Z : Presheaf.{w} R equations} (g : Z ⟶ (embedding R equations).obj a)
    (j : AuthoredPositionedRulePolynomial.Judgment (modelAt equations a.base))
    (tree : IntrinsicScopedLocalActedFree.Tree R _
      (IntrinsicScopedLocalActedFiniteContext.seeds R _ (events R equations a)) j) :
    (((yonedaStructured.{w} R equations).valuation g).evaluate j tree).1 =
      g ≫ (embedding R equations).map (rep R equations j tree) :=
  (yonedaStructured.{w} R equations).evaluate_valuation_val g j tree

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
