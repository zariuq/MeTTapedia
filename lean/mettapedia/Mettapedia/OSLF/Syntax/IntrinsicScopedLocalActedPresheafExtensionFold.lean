import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafExtension
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetFold

/-!
# The presheaf extension interprets the original operational fold

On representables, the extension evaluates every substituted firing tree
through the model's existing fold. The Kan-unit comparison is natural at
the actual representative arrow, including rule nodes under local binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.CategoryTheory.PresheafStructuredExtension

universe w u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {R : List (LocalRule S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable [HasColimitsOfSize.{0, max w v} D]
variable (M : CategoricalModel R equations (D := D))

namespace CocontinuousInterpretation

/-- The actual extension of every tree representative is the model's free
fold, after its canonical comparisons on the source and event objects. -/
theorem extension_freeFold {a : Classifier R equations}
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app a ≫
      ((classificationEquivalence.{w, u, v}).functor.obj M).carrier.map
        (embedding.{w, 0, 0, v}.map (rep R equations j tree)) ≫
      ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).inv.app
        (eventObject R equations j.1 j.2.1) ≫
      (M.eventIso j.1 j.2.1).inv = M.foldOperation j tree := by
  let U := (unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor
  change U.hom.app a ≫
    ((embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.obj M.classifyingFunctor).map
      (embedding.{w, 0, 0, v}.map (rep R equations j tree)) ≫
    U.inv.app (eventObject R equations j.1 j.2.1) ≫ (M.eventIso j.1 j.2.1).inv = _
  have nat : M.classifyingFunctor.map (rep R equations j tree) ≫
      U.hom.app (eventObject R equations j.1 j.2.1) =
      U.hom.app a ≫ ((embedding.{w, 0, 0, v} (C := Classifier R equations)).lan.obj
        M.classifyingFunctor).map (embedding.{w, 0, 0, v}.map (rep R equations j tree)) :=
    U.hom.naturality (rep R equations j tree)
  rw [← Category.assoc, ← Category.assoc, ← nat]
  simp only [Category.assoc, U.hom_inv_id_app_assoc]
  exact M.foldOperation_rep j tree

/-- The fold comparison holds at every semantic stage, rather than only
at points coming from a selected image. -/
theorem extension_freeFold_stage {a : Classifier R equations} {Z : D}
    (g : Z ⟶ M.classifyingObject a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (g ≫ ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app a) ≫
      ((classificationEquivalence.{w, u, v}).functor.obj M).carrier.map
        (embedding.{w, 0, 0, v}.map (rep R equations j tree)) ≫
      ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).inv.app
        (eventObject R equations j.1 j.2.1) ≫
      (M.eventIso j.1 j.2.1).inv = g ≫ M.foldOperation j tree := by
  simpa only [Category.assoc] using congrArg (g ≫ ·) (extension_freeFold M j tree)

end CocontinuousInterpretation
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
