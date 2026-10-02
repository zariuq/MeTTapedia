import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetOperations

/-!
# The target-classification comparison preserves the original free fold

The natural comparison with postcomposition transports represented
valuations to valuations on the actual image objects. At a generic event it
uses the specified event comparison, and at every represented firing tree
it agrees with the image of the independently defined operation arrow.
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
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u v u' v'
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D'] [HasPullbacks D']
variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace CategoricalModel

variable (M : CategoricalModel R equations (D := D))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse classification comparison retains the full program/event
valuation at every object of the new target. -/
theorem targetClassification_valuation {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) :
    ((M.targetModel H).valuationsRepresentableBy a).homEquiv
      (g ≫ ((targetClassificationIso H).inv.app M).app a) = M.imageValuation H g := by
  have moved := homEquiv_classifyingMap (M.targetModelIso H).inv a
    (g ≫ (M.structured.postcompose H).counitIso.inv.app a)
  have read := (M.structured.postcompose H).homEquiv_counitIso_inv a g
  have core := moved.trans (congrArg (M.targetModelIso H).inv.valuation read)
  simp only [targetClassificationIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  erw [Category.id_comp, Category.comp_id]
  erw [NatTrans.comp_app]
  have inverse : (transportModelsRecoveryIso H).inv.app M = (M.targetModelIso H).inv := rfl
  rw [inverse]
  rw [← Category.assoc]
  exact core

set_option backward.isDefEq.respectTransparency false in
/-- At the canonical new-model point, the comparison transports the full
ordered valuation to the actual image valuation. -/
theorem targetClassification_genericValuation (a : Classifier R equations) :
    (M.targetModel H).genericValuation a =
      M.imageValuation H (((targetClassificationIso H).hom.app M).app a) := by
  have value := M.targetClassification_valuation H
    (((targetClassificationIso H).hom.app M).app a)
  have inverse := ((targetClassificationIso H).app M).hom_inv_id
  have component := congrArg (fun α => α.app a) inverse
  change (((targetClassificationIso H).hom.app M).app a) ≫
    (((targetClassificationIso H).inv.app M).app a) = 𝟙 _ at component
  exact (congrArg ((M.targetModel H).valuationsRepresentableBy a).homEquiv component).symm.trans value

set_option backward.isDefEq.respectTransparency false in
/-- The actual natural classification comparison commutes with every
original firing-tree fold operation, including substituted event leaves. -/
theorem targetClassification_freeFold {a : Classifier R equations}
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (((targetClassificationIso H).hom.app M).app a) ≫ H.map (M.foldOperation j tree) =
      (M.targetModel H).foldOperation j tree := by
  have value := M.targetClassification_genericValuation H a
  have folded := M.targetModel_tree_evaluate H
    (((targetClassificationIso H).hom.app M).app a) j tree
  rw [← value] at folded
  exact folded.symm

set_option backward.isDefEq.respectTransparency false in
/-- The comparison identifies the actual classifier map of every
represented firing tree at any new target stage with the image source fold. -/
theorem targetClassification_rep_freeFold {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ (M.targetModel H).classifyingObject a)
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (g ≫ (M.targetModel H).classifyingFunctor.map (rep R equations j tree)) ≫
        ((M.targetModel H).eventIso j.1 j.2.1).inv =
      (g ≫ (((targetClassificationIso H).hom.app M).app a)) ≫ H.map (M.foldOperation j tree) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (g ≫ ·) (((M.targetModel H).foldOperation_rep j tree).trans
      (M.targetClassification_freeFold H j tree).symm)).trans (Category.assoc _ _ _).symm)

/-- The generic one-event leaf is the inverse event-object comparison. -/
theorem foldOperation_eventLeaf (Γ : Ctx S) (s : S.Srt) :
    M.foldOperation (a := eventObject R equations Γ s) (pairJudgment equations Γ s)
      (leaf R (events R equations (eventObject R equations Γ s))
        (first R (pairJudgment equations Γ s) (Context.empty R _))) =
      (M.eventIso Γ s).inv := by
  let a := eventObject R equations Γ s
  let position := first R (pairJudgment equations Γ s) (Context.empty R _)
  have leafLaw := congrArg Subtype.val ((M.genericValuation a).evaluate_leaf position)
  have read := M.comp_eventIso_inv (Γ := Γ) (s := s) (𝟙 (M.classifyingObject a))
  simp only [Category.id_comp] at read
  exact leafLaw.trans read.symm

set_option backward.isDefEq.respectTransparency false in
/-- At the generic event object, the actual classification comparison uses
the image of the specified source event comparison. -/
theorem targetClassification_eventIso_inv (Γ : Ctx S) (s : S.Srt) :
    (((targetClassificationIso H).hom.app M).app (eventObject R equations Γ s)) ≫
      H.map (M.eventIso Γ s).inv = ((M.targetModel H).eventIso Γ s).inv := by
  have law := M.targetClassification_freeFold H (a := eventObject R equations Γ s) (pairJudgment equations Γ s)
    (leaf R (events R equations (eventObject R equations Γ s))
      (first R (pairJudgment equations Γ s) (Context.empty R _)))
  rw [M.foldOperation_eventLeaf Γ s, (M.targetModel H).foldOperation_eventLeaf Γ s] at law
  exact law

end CategoricalModel
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
