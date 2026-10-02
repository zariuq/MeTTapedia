import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetObjects
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFoldComparison

/-!
# Change of target for the actual free firing-tree fold

At every stage of the new target, a represented firing-tree arrow is the
image of the original operational fold applied to its new generalized point.
This includes stages outside the image of the target-change functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree freeModelUniversal)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace CategoricalModel

variable (M : CategoricalModel R equations (D := D))

/-- The operational fold at the universal program/event valuation. -/
def foldOperation {a : Classifier R equations} (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    M.classifyingObject a ⟶ M.objects.event j.1 j.2.1 :=
  ((M.genericValuation a).evaluate j tree).1

/-- The source operation arrow is the original free fold, not a new
interpretation supplied by target change. -/
theorem foldOperation_rep {a : Classifier R equations} (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    M.classifyingFunctor.map (rep R equations j tree) ≫ (M.eventIso j.1 j.2.1).inv =
      M.foldOperation j tree := by
  have law := M.comp_rep_eventIso_inv (𝟙 (M.classifyingObject a)) j tree
  exact (congrArg (· ≫ (M.eventIso j.1 j.2.1).inv)
    (Category.id_comp (M.classifyingFunctor.map (rep R equations j tree)))).symm.trans law

/-- The actual mapped operation is interpreted at every new target stage
by precomposition with the image of the source free-fold operation arrow. -/
theorem postcompose_tree_freeFold {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((M.structured.postcompose H).treeEvent j tree g).1 ≫ H.map (M.eventIso j.1 j.2.1).inv =
      g ≫ H.map (M.foldOperation j tree) := by
  change (g ≫ H.map (M.classifyingFunctor.map (rep R equations j tree))) ≫
    H.map (M.eventIso j.1 j.2.1).inv = _
  exact (Category.assoc _ _ _).trans (congrArg (g ≫ ·)
    ((H.map_comp _ _).symm.trans (congrArg H.map (M.foldOperation_rep j tree))))

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
