import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationModelLaws

/-!
# Genuine identity and composition of native model restriction

The coded native identity and composites may change raw equalizer codes.
Their actions on every independently realized model nevertheless satisfy
complete identity and composition. Restriction first recovers the old
expression meanings; independent uniqueness of the added native comparison
inverses then recovers the entire augmented model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeModelAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k w

variable {C D H : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable {symbols nextSymbols lastSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

private instance identity_lex (headers : HeaderFormation signature) :
    PreservesFiniteLimits (Translation.identity headers).data.base := by
  change PreservesFiniteLimits (𝟭 C)
  infer_instance

private instance identity_closed (headers : HeaderFormation signature) :
    MonoidalClosedFunctor (Translation.identity headers).data.base where
  comparison_iso argument := by
    have (result : C) : IsIso ((expComparison (Translation.identity headers).data.base argument).natTrans.app result) := by
      change IsIso ((expComparison (𝟭 C) argument).natTrans.app result)
      rw [CartesianClosedFunctorCoherence.exponential_identity]
      exact IsIso.id (C := C) ((ihom argument).obj result)
    exact NatIso.isIso_of_isIso_app _

theorem identity_model (headers : HeaderFormation signature) (model : Model (BaseExtension.extend signature) E) :
    (NativeExtension.extended (Translation.identity headers)).precomposeModel model = model := by
  apply NativeModels.restriction_injective
  exact (NativeModels.restriction_model (Translation.identity headers) model).trans
    (ModelLaws.identity headers (BaseExtension.Models.restrict model).model)

variable (first : Translation signature next) (last : Translation next final)
variable [PreservesFiniteLimits first.data.base] [MonoidalClosedFunctor first.data.base]
variable [PreservesFiniteLimits last.data.base] [MonoidalClosedFunctor last.data.base]

private instance composite_lex : PreservesFiniteLimits (first.compose last).data.base :=
  comp_preservesFiniteLimits first.data.base last.data.base

private instance composite_closed : MonoidalClosedFunctor (first.compose last).data.base :=
  CartesianClosedFunctorCoherence.closed_composition first.data.base last.data.base

theorem compose_model (model : Model (BaseExtension.extend final) E) :
    (NativeExtension.extended first).precomposeModel ((NativeExtension.extended last).precomposeModel model) =
      (NativeExtension.extended (first.compose last)).precomposeModel model := by
  apply NativeModels.restriction_injective
  exact (NativeModels.restriction_model first ((NativeExtension.extended last).precomposeModel model)).trans
    ((congrArg first.precomposeModel (NativeModels.restriction_model last model)).trans
      ((ModelLaws.compose first last (BaseExtension.Models.restrict model).model).trans
        (NativeModels.restriction_model (first.compose last) model).symm))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeModelAction
