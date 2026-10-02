import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaParameterContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterCoordinates

/-!
# Coordinates of the ordered parameter representable comparison

The product comparison identifies the actual parameter-product projections
with the ordered environment projections used by contextual evaluation.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open SecondOrderContext IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
open CategoricalBindingModel
universe w
variable {S : Signature} (R : List (LocalRule S))
variable {K : List (MetaArity S)} (equations : List (EqAxiom S K))

private theorem map_parameterSourceHead (Γ : Ctx S) (a : S.Srt) :
    (parameterEmbedding.{w} R equations).map (parameterSourceHead equations Γ a) ≫
        (parameterClosedSortIso R equations a).hom =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (prod.snd : parameterContext equations (a :: Γ) ⟶
          (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a)) := by
  apply NatTrans.ext
  funext stage
  apply ConcreteCategory.hom_ext
  intro point
  rfl

private theorem map_parameterSourceTail (Γ : Ctx S) (a : S.Srt) :
    (parameterEmbedding.{w} R equations).map (parameterSourceTail equations Γ a) =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (prod.fst : parameterContext equations (a :: Γ) ⟶ parameterContext equations Γ) := by
  apply NatTrans.ext
  funext stage
  apply ConcreteCategory.hom_ext
  intro point
  rfl

private theorem map_parameterSourceCoordinate {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    (parameterEmbedding.{w} R equations).map (parameterSourceCoordinate equations v) ≫
        (parameterClosedSortIso R equations s).hom =
      (programSection R equations ⋙ embedding.{w} R equations).map (parameterVariable equations v) := by
  apply NatTrans.ext
  funext stage
  apply ConcreteCategory.hom_ext
  intro point
  rfl

theorem parameterPairIso_fst (Γ : Ctx S) (a : S.Srt) :
    (parameterPairIso.{w} R equations Γ a).hom ≫ fst _ _ =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (prod.fst : parameterContext equations (a :: Γ) ⟶ parameterContext equations Γ) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact (ParameterImage.imagePair_tail (parameterEmbedding R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (parameterSourcePairs equations)
    (parameterSourceTail equations) (parameterSourcePairs_tail equations) (parameterClosedSortIso R equations) Γ a).trans
      (map_parameterSourceTail R equations Γ a)

theorem parameterPairIso_snd (Γ : Ctx S) (a : S.Srt) :
    (parameterPairIso.{w} R equations Γ a).hom ≫ snd _ _ =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (prod.snd : parameterContext equations (a :: Γ) ⟶
          (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a)) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact (ParameterImage.imagePair_head (parameterEmbedding R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (parameterSourcePairs equations)
    (parameterSourceHead equations) (parameterSourcePairs_head equations) (parameterClosedSortIso R equations) Γ a).trans
      (map_parameterSourceHead R equations Γ a)

theorem parameterPairIso_hom (Γ : Ctx S) (a : S.Srt) :
    (parameterPairIso.{w} R equations Γ a).hom =
      lift ((programSection R equations ⋙ embedding.{w} R equations).map
          (prod.fst : parameterContext equations (a :: Γ) ⟶ parameterContext equations Γ))
        ((programSection R equations ⋙ embedding.{w} R equations).map
          (prod.snd : parameterContext equations (a :: Γ) ⟶
            (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a))) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (parameterPairIso_fst R equations Γ a).trans (lift_fst _ _).symm
  · exact (parameterPairIso_snd R equations Γ a).trans (lift_snd _ _).symm

theorem parameterContextRepresentableIso_cons (a : S.Srt) (Γ : Ctx S) :
    parameterContextRepresentableIso.{w} R equations (a :: Γ) =
      parameterPairIso R equations Γ a ≪≫
        whiskerRightIso (parameterContextRepresentableIso R equations Γ)
          (program R equations [] a) ≪≫
        (β_ (contextOf (program R equations []) Γ) (program R equations [] a)) := rfl

theorem parameterContextRepresentableIso_head (a : S.Srt) (Γ : Ctx S) :
    (parameterContextRepresentableIso.{w} R equations (a :: Γ)).hom ≫ fst _ _ =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (prod.snd : parameterContext equations (a :: Γ) ⟶
          (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a)) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact (ParameterImage.contextIso_head (parameterEmbedding R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (terminalIsTerminal (C := Base equations))
    (parameterSourcePairs equations) (parameterSourceHead equations) (parameterSourcePairs_head equations)
    (parameterClosedSortIso R equations) Γ a).trans (map_parameterSourceHead R equations Γ a)

theorem parameterContextRepresentableIso_tail (a : S.Srt) (Γ : Ctx S) :
    (parameterContextRepresentableIso.{w} R equations (a :: Γ)).hom ≫ snd _ _ =
      (programSection R equations ⋙ embedding.{w} R equations).map
          (prod.fst : parameterContext equations (a :: Γ) ⟶ parameterContext equations Γ) ≫
        (parameterContextRepresentableIso.{w} R equations Γ).hom := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  have generic := ParameterImage.contextIso_tail (parameterEmbedding R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (terminalIsTerminal (C := Base equations))
    (parameterSourcePairs equations) (parameterSourceTail equations) (parameterSourcePairs_tail equations)
    (parameterClosedSortIso R equations) Γ a
  exact generic.trans (congrArg (fun f => f ≫ (parameterContextRepresentableIso R equations Γ).hom)
    (map_parameterSourceTail R equations Γ a))

theorem parameterContextRepresentableIso_variable {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    (parameterContextRepresentableIso.{w} R equations Γ).hom ≫
        projectVar (program.{w} R equations []) v =
      (programSection R equations ⋙ embedding.{w} R equations).map
        (parameterVariable equations v) := by
  let _ := programEmbedding_preservesLimits.{w} R equations
  exact (ParameterImage.contextIso_variable (parameterEmbedding R equations) (parameterContext equations)
    (parameterSourceSort equations) (program R equations []) (terminalIsTerminal (C := Base equations))
    (parameterSourcePairs equations) (parameterSourceHead equations) (parameterSourceTail equations)
    (parameterSourcePairs_head equations) (parameterSourcePairs_tail equations) (parameterClosedSortIso R equations)
    (parameterSourceCoordinate equations) (parameterSourceCoordinate_head equations)
    (parameterSourceCoordinate_succ equations) v).trans (map_parameterSourceCoordinate R equations v)


end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
