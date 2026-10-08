import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeModelAction
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorModelEquivalence
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationCells

/-!
# Native translation comparisons from independent complete models

The identity diagram of the target generated category is reconstructed as
an independently realized model. Equality of its complete restrictions
therefore yields an actual natural isomorphism between the supplied source
functors. Applied to the earned native model laws, this constructs the
native identity and composition comparisons without identifying raw
equalizer presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory SemanticModels

universe k

variable {C D H : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H]
variable {symbols nextSymbols lastSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}

private instance identity_closed (A : Type k) [Category.{k} A]
    [CartesianMonoidalCategory A] [MonoidalClosed A] : MonoidalClosedFunctor (𝟭 A) where
  comparison_iso argument := by
    suffices ∀ result : A, IsIso ((expComparison (𝟭 A) argument).natTrans.app result) from
      NatIso.isIso_of_isIso_app _
    intro result
    rw [CartesianClosedFunctorCoherence.exponential_identity]
    exact IsIso.id (C := A) ((ihom argument).obj result)

def selfModel (headers : HeaderFormation next) : Model next (Object next) :=
  FunctorModelEquivalence.extracted headers
    (⟨𝟭 (Object next), inferInstance, inferInstance⟩ : ClosedModels.Diagram next (Object next))

def selfComparison (headers : HeaderFormation next) :
    𝟭 (Object next) ≅ (selfModel headers).diagram :=
  FunctorModelEquivalence.comparison headers
    (⟨𝟭 (Object next), inferInstance, inferInstance⟩ : ClosedModels.Diagram next (Object next))

variable (before after : Translation signature next) (headers : HeaderFormation next)

def ofModelEquality
    (same : before.precomposeModel (selfModel headers) = after.precomposeModel (selfModel headers)) :
    before.functor ≅ after.functor :=
  (Functor.rightUnitor before.functor).symm ≪≫
    Functor.isoWhiskerLeft before.functor (selfComparison headers) ≪≫
      before.precomposeComparison (selfModel headers) ≪≫
        eqToIso (congrArg Model.diagram same) ≪≫
          (after.precomposeComparison (selfModel headers)).symm ≪≫
            (Functor.isoWhiskerLeft after.functor (selfComparison headers)).symm ≪≫
              Functor.rightUnitor after.functor

private theorem conjugate_eqToHom {A : Type k} [Category.{k} A]
    {mapping : A ⥤ A} (comparison : 𝟭 A ≅ mapping) {source target middle first : A}
    (same : source = target) (one : mapping.obj source = first)
    (two : first = middle) (three : middle = mapping.obj target) :
    comparison.hom.app source ≫ eqToHom one ≫ eqToHom two ≫ eqToHom three ≫
      comparison.inv.app target ≫ 𝟙 target = eqToHom same := by
  subst target
  subst first
  subst middle
  simp only [eqToHom_refl, Category.id_comp]
  exact (Category.assoc (comparison.hom.app source) (comparison.inv.app source) (𝟙 source)).symm.trans
    ((congrArg (fun arrow : source ⟶ source => arrow ≫ 𝟙 source)
      (comparison.hom_inv_id_app source)).trans (Category.id_comp (𝟙 source)))

private theorem precompose_hom_component (mapping : Translation signature next)
    (model : Model next (Object next)) (source : Object signature) :
    (mapping.precomposeComparison model).hom.app source =
      eqToHom (Functor.congr_obj (mapping.functor_precompose model.meanings model.realization) source) :=
  eqToHom_app (mapping.functor_precompose model.meanings model.realization) source

private theorem precompose_inv_component (mapping : Translation signature next)
    (model : Model next (Object next)) (source : Object signature) :
    (mapping.precomposeComparison model).inv.app source =
      eqToHom (Functor.congr_obj (mapping.functor_precompose model.meanings model.realization).symm source) :=
  eqToHom_app (mapping.functor_precompose model.meanings model.realization).symm source

theorem ofModelEquality_hom_component
    (same : before.precomposeModel (selfModel headers) = after.precomposeModel (selfModel headers))
    (source : Object signature) (objects : before.object source = after.object source) :
    (ofModelEquality before after headers same).hom.app source = eqToHom objects := by
  simp only [ofModelEquality, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app,
    precompose_hom_component, precompose_inv_component, Category.id_comp]
  exact conjugate_eqToHom (selfComparison headers) objects
    (Functor.congr_obj (before.functor_precompose (selfModel headers).meanings
      (selfModel headers).realization) source)
    (Functor.congr_obj (congrArg Model.diagram same) source)
    (Functor.congr_obj (after.functor_precompose (selfModel headers).meanings
      (selfModel headers).realization).symm source)

section Native

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]

def identity (formed : HeaderFormation signature) :
    (NativeExtension.extended (Translation.identity formed)).functor ≅ 𝟭 (Object (BaseExtension.extend signature)) :=
  let augmentedHeaders := BaseExtension.headers signature formed
  let model := selfModel augmentedHeaders
  let same := (NativeModelAction.identity_model formed model).trans
    (ModelLaws.identity augmentedHeaders model).symm
  ofModelEquality (NativeExtension.extended (Translation.identity formed))
      (Translation.identity augmentedHeaders) augmentedHeaders same ≪≫
    eqToIso (Translation.functor_identity augmentedHeaders)

variable (first : Translation signature next) (last : Translation next final)
variable [PreservesFiniteLimits first.data.base] [MonoidalClosedFunctor first.data.base]
variable [PreservesFiniteLimits last.data.base] [MonoidalClosedFunctor last.data.base]

private instance composite_lex : PreservesFiniteLimits (first.compose last).data.base :=
  comp_preservesFiniteLimits first.data.base last.data.base

private instance composite_closed : MonoidalClosedFunctor (first.compose last).data.base :=
  CartesianClosedFunctorCoherence.closed_composition first.data.base last.data.base

def compose (formed : HeaderFormation final) :
    (NativeExtension.extended first).functor ⋙ (NativeExtension.extended last).functor ≅
      (NativeExtension.extended (first.compose last)).functor :=
  let augmentedHeaders := BaseExtension.headers final formed
  let model := selfModel augmentedHeaders
  let same := (ModelLaws.compose (NativeExtension.extended first) (NativeExtension.extended last) model).symm.trans
    (NativeModelAction.compose_model first last model)
  eqToIso (Translation.functor_compose (NativeExtension.extended first) (NativeExtension.extended last)) ≪≫
    ofModelEquality ((NativeExtension.extended first).compose (NativeExtension.extended last))
      (NativeExtension.extended (first.compose last)) augmentedHeaders same

end Native

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeComparison
