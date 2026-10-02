import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetPostcomposition

/-!
# Program maps under qualified target change

Recovering a program map from a postcomposed natural transformation gives the
actual image of its sort and binding function-object components. The proof
uses the canonical family comparisons and applies to noninvertible maps.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace StructuredFunctor

variable {F G : StructuredFunctor R equations (D := D)}

set_option backward.isDefEq.respectTransparency.types false in
/-- The recovered program map is the actual mapped interpretation map. -/
theorem programHom_postcompose (α : F ⟶ G) :
    programHom (F := F.postcompose H) (G := G.postcompose H) (Functor.whiskerRight α H) =
      mapInterpretationHom H (programHom α) := by
  apply (CategoricalBindingInterpretationMaps.interpretationHomEquiv _ _).injective
  change CategoricalBindingInterpretationMaps.classifyingMap
      (CategoricalBindingInterpretationMaps.Hom.ofNat
        (programNat (F := F.postcompose H) (G := G.postcompose H) (Functor.whiskerRight α H))) =
    CategoricalBindingInterpretationMaps.classifyingMap (mapInterpretationHom H (programHom α))
  rw [CategoricalBindingInterpretationMaps.Hom.classifyingMap_ofNat]
  apply NatTrans.ext
  funext X
  apply (cancel_epi ((F.program.postcompose H).famIso X.arities).hom).mp
  apply (cancel_mono (familyComparison H G.programModel.power X.arities).hom).mp
  have natural := F.programIso_naturality α
    ((authoredEquationPresentation S equations).quotientFunctor.obj X)
  have familyF : ((F.program.postcompose H).famIso X.arities).hom ≫
      (familyComparison H F.programModel.power X.arities).hom =
      H.map (F.program.famIso X.arities).hom :=
    F.program.toPreservingData.postcompose_famIso H X.arities
  have familyG : ((G.program.postcompose H).famIso X.arities).hom ≫
      (familyComparison H G.programModel.power X.arities).hom =
      H.map (G.program.famIso X.arities).hom :=
    G.program.toPreservingData.postcompose_famIso H X.arities
  have comparison : (familyComparison H F.programModel.power X.arities).hom ≫
      H.map (Model.familyMap (programHom α).underlying.power X.arities) =
      Model.familyMap (M := mapModel H F.programModel) (N := mapModel H G.programModel)
        (fun Γ s => H.map ((programHom α).underlying.power Γ s)) X.arities ≫
        (familyComparison H G.programModel.power X.arities).hom :=
    familyComparison_natural H (programHom α).underlying.power X.arities
  change (((F.program.postcompose H).famIso X.arities).hom ≫
      (((F.program.postcompose H).famIso X.arities).inv ≫ H.map (α.app _) ≫
        ((G.program.postcompose H).famIso X.arities).hom)) ≫
      (familyComparison H G.programModel.power X.arities).hom =
    (((F.program.postcompose H).famIso X.arities).hom ≫
      Model.familyMap (M := mapModel H F.programModel) (N := mapModel H G.programModel)
        (fun Γ s => H.map ((programHom α).underlying.power Γ s)) X.arities) ≫
      (familyComparison H G.programModel.power X.arities).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [familyG, ← comparison]
  have mapped : H.map (α.app ((programSection R equations).obj
      ((authoredEquationPresentation S equations).quotientFunctor.obj X))) ≫
      H.map (G.program.famIso X.arities).hom =
      H.map (F.program.famIso X.arities).hom ≫
        H.map (Model.familyMap (programHom α).underlying.power X.arities) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map natural).trans (H.map_comp _ _))
  have rhs := congrArg (· ≫ H.map (Model.familyMap (programHom α).underlying.power X.arities)) familyF
  exact mapped.trans (rhs.symm.trans (Category.assoc _ _ _))

/-- The recovered sort component is the image of the source sort map. -/
theorem programHom_postcompose_sort (α : F ⟶ G) (s : S.Srt) :
    (programHom (F := F.postcompose H) (G := G.postcompose H)
      (Functor.whiskerRight α H)).underlying.sort s =
      H.map ((programHom α).underlying.sort s) :=
  congrArg (fun f => f.underlying.sort s) (programHom_postcompose H α)

/-- The recovered binder-function component is the image of the source map. -/
theorem programHom_postcompose_power (α : F ⟶ G) (Γ : Ctx S) (s : S.Srt) :
    (programHom (F := F.postcompose H) (G := G.postcompose H)
      (Functor.whiskerRight α H)).underlying.power Γ s =
      H.map ((programHom α).underlying.power Γ s) :=
  congrArg (fun f => f.underlying.power Γ s) (programHom_postcompose H α)

/-- Model reconstruction has the same actual target-change law on program maps. -/
theorem modelFunctor_postcompose_program (α : F ⟶ G) :
    ((modelFunctor (R := R) (equations := equations) (D := D')).map
      ((postcomposeStructured H).map α)).program =
      mapInterpretationHom H ((modelFunctor (R := R) (equations := equations) (D := D)).map α).program :=
  programHom_postcompose H α

end StructuredFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
