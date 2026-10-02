import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassification
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorModelMaps

/-!
# Naturality of the comparison with a structure-preserving functor

The objectwise comparison between a structure-preserving functor and the
classifying functor of its recovered model is natural on every natural
transformation. The proof compares their represented valuations: recovering
a model map moves precisely the program point and event-variable values of
the original transformation.
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
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace StructuredFunctor

variable {F G : StructuredFunctor R equations (D := D)}

/-- Recovering a model map moves the valuation of a generalized element by
the original natural transformation. -/
theorem valuation_modelHom (α : F ⟶ G) {a : Classifier R equations} {Z : D}
    (g : Z ⟶ F.carrier.obj a) :
    (modelHom α).valuation (F.valuation g) = G.valuation (g ≫ α.app a) := by
  apply ClassifierTarget.Valuation.ext'
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (g ≫ ·) (programPoint_naturality α a)).trans
        (Category.assoc _ _ _).symm)).symm
  · intro position
    exact ((modelHom α).valuation_event (F.valuation g) position).trans
      (treeEvent_map α _ (leaf R (events R equations a) position) g).symm

variable [HasPullbacks D]

/-- The inverse comparisons are natural on all transformations, including
noninvertible transformations. -/
theorem counitIso_inv_naturality (α : F ⟶ G) (a : Classifier R equations) :
    α.app a ≫ G.counitIso.inv.app a =
      F.counitIso.inv.app a ≫ (CategoricalModel.classifyingMap (modelHom α)).app a := by
  apply (G.model.valuationsRepresentableBy a).homEquiv.injective
  have left := G.homEquiv_counitIso_inv a (α.app a)
  have right := CategoricalModel.homEquiv_classifyingMap (modelHom α) a
    (F.counitIso.inv.app a)
  have first : (F.model.valuationsRepresentableBy a).homEquiv (F.counitIso.inv.app a) =
      F.valuation (𝟙 (F.carrier.obj a)) :=
    (congrArg (F.model.valuationsRepresentableBy a).homEquiv
      (Category.id_comp (F.counitIso.inv.app a))).symm.trans
        (F.homEquiv_counitIso_inv a (𝟙 (F.carrier.obj a)))
  have moved : (modelHom α).valuation (F.valuation (𝟙 (F.carrier.obj a))) =
      G.valuation (α.app a) := by
    simpa only [Category.id_comp] using valuation_modelHom α (𝟙 (F.carrier.obj a))
  exact left.trans (moved.symm.trans ((congrArg (modelHom α).valuation first).symm.trans right.symm))

/-- The comparison is an isomorphism in the category of structured functors. -/
noncomputable def counitStructuredIso (F : StructuredFunctor R equations (D := D)) :
    F.model.structured ≅ F where
  hom := F.counitIso.hom
  inv := F.counitIso.inv
  hom_inv_id := F.counitIso.hom_inv_id
  inv_hom_id := F.counitIso.inv_hom_id

/-- The forward comparisons are natural on all transformations. -/
theorem counitIso_hom_naturality (α : F ⟶ G) :
    CategoricalModel.classifyingMap (modelHom α) ≫ G.counitIso.hom =
      F.counitIso.hom ≫ α := by
  apply NatTrans.ext
  funext a
  have inverse := counitIso_inv_naturality α a
  have moved := congrArg (fun f => F.counitIso.hom.app a ≫ f ≫ G.counitIso.hom.app a) inverse
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Iso.hom_inv_id_app_assoc] at moved
  exact moved.symm

end StructuredFunctor

/-- Recovering a model and classifying it is naturally isomorphic to the
original structure-preserving functor. -/
noncomputable def counitNatIso [HasPullbacks D] :
    modelFunctor (R := R) (equations := equations) ⋙ classifyFunctor ≅
      𝟭 (StructuredFunctor R equations (D := D)) :=
  NatIso.ofComponents StructuredFunctor.counitStructuredIso
    (fun α => StructuredFunctor.counitIso_hom_naturality α)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
