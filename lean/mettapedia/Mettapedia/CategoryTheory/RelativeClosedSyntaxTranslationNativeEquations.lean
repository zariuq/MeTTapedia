import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeClosed

/-!
# Generated inverse equations for the native expression translation

The independently typed forward and inverse target expressions are proved
inverse using their complete canonical comparison readings. Exactness of
the generated typed-arrow quotient then supplies actual equation trees for
the two local declarations. These trees admit an augmented translation;
no desired equation or all-expression compatibility is a model field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeEquations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory NativeData NativeForward NativeClosed

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

def inverse_forward (choice : BaseComparisons.Choice C) :
    Derivation (BaseExtension.extend next)
      (.equation (formal mapping choice).code (formal mapping choice).code
        (.compose (inverseCode mapping choice) (forwardCode mapping choice))
        (.identity (formal mapping choice).code)) := by
  have complete : classOf (RawHom.compose (inverseRaw mapping choice) (forwardRaw mapping choice)) =
      classOf (RawHom.identity (formal mapping choice)) :=
    (congrArg₂ (fun first second => first ≫ second)
      (inverse_complete mapping choice) (forward_complete mapping choice)).trans
        (completeComparison mapping choice).inv_hom_id
  exact (Quotient.exact complete).some

def forward_inverse (choice : BaseComparisons.Choice C) :
    Derivation (BaseExtension.extend next)
      (.equation (old mapping choice).code (old mapping choice).code
        (.compose (forwardCode mapping choice) (inverseCode mapping choice))
        (.identity (old mapping choice).code)) := by
  have complete : classOf (RawHom.compose (forwardRaw mapping choice) (inverseRaw mapping choice)) =
      classOf (RawHom.identity (old mapping choice)) :=
    (congrArg₂ (fun first second => first ≫ second)
      (forward_complete mapping choice) (inverse_complete mapping choice)).trans
        (completeComparison mapping choice).hom_inv_id
  exact (Quotient.exact complete).some

def native_equation_typed (origin : BaseComparisons.Choice C × Bool) :
    Derivation (BaseExtension.extend next)
      (.equation (((BaseExtension.extend signature).equationSource (.inl origin)).translate (NativeData.data mapping))
        (((BaseExtension.extend signature).equationTarget (.inl origin)).translate (NativeData.data mapping))
        (((BaseExtension.extend signature).left (.inl origin)).translate (NativeData.data mapping))
        (((BaseExtension.extend signature).right (.inl origin)).translate (NativeData.data mapping))) := by
  rcases origin with ⟨choice, side⟩
  cases side with
  | false =>
      cases choice with
      | terminal => exact forward_inverse mapping .terminal
      | product first second => exact forward_inverse mapping (.product first second)
      | equalizer first second => exact forward_inverse mapping (.equalizer first second)
      | exponential argument result => exact forward_inverse mapping (.exponential argument result)
  | true =>
      cases choice with
      | terminal => exact inverse_forward mapping .terminal
      | product first second => exact inverse_forward mapping (.product first second)
      | equalizer first second => exact inverse_forward mapping (.equalizer first second)
      | exponential argument result => exact inverse_forward mapping (.exponential argument result)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeEquations
