import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeForward

/-!+# Full exponential reading of a weak native expression translation

The target-native exponential comparison is the genuine canonical comparison
of its base inclusion. The translated abstraction retains the original
evaluation and both inputs of the product inverse. The actual exchange and
uncurry equations identify its complete value with the composite canonical
comparison, rather than identifying independently selected objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeClosed

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory NativeData NativeForward

universe k

private theorem abstraction_readout {E : Type k} [Category.{k} E]
    {names : Symbols.{k}} {presentation : Signature (C := E) (symbols := names)}
    {context argument result : Object presentation}
    (body : product context argument ⟶ result) :
    GeneratedCategory.abstraction body = Interpretation.abstraction body := by
  apply MonoidalClosed.uncurry_injective
  rw [monoidal_uncurry, unabstract_abstraction, Interpretation.abstraction,
    MonoidalClosed.uncurry_curry, cartesian_exchange]
  rfl

private theorem comparison_of_equal_functors {E H : Type k} [Category.{k} E] [Category.{k} H]
    [CartesianMonoidalCategory E] [MonoidalClosed E]
    [CartesianMonoidalCategory H] [MonoidalClosed H]
    {first second : E ⥤ H} [PreservesFiniteProducts first] [PreservesFiniteProducts second]
    (same : first = second) (argument result : E) :
    HEq ((expComparison first argument).natTrans.app result)
      ((expComparison second argument).natTrans.app result) := by
  cases same
  rfl

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

theorem target_exponential_canonical (argument result : D) :
    (targetComparison (next := next) (.exponential argument result)).hom =
      (expComparison (J (next := next)) argument).natTrans.app result := by
  have original := congrArg (BaseExtension.comparisonMap next).functor.map
    (BaseComparisons.canonicalExponentialComparison_mathlib argument result)
  have composed := CartesianClosedFunctorCoherence.exponential_composition
    (BaseComparisons.base (C := D)) (BaseExtension.comparisonMap next).functor argument result
  rw [SignatureMap.expComparison_identity] at composed
  have trimmed := composed.trans (Category.comp_id _)
  have transported := comparison_of_equal_functors
    (BaseExtension.comparison_base_recovery next) argument result
  exact original.trans (trimmed.symm.trans (eq_of_heq transported))

theorem exponential_canonical (argument result : C) :
    (completeComparison mapping (.exponential argument result)).hom =
      (expComparison (mapping.data.base ⋙ J (next := next)) argument).natTrans.app result := by
  change (J (next := next)).map ((expComparison mapping.data.base argument).natTrans.app result) ≫
      (targetComparison (next := next)
        (.exponential (mapping.data.base.obj argument) (mapping.data.base.obj result))).hom = _
  rw [target_exponential_canonical]
  exact (CartesianClosedFunctorCoherence.exponential_composition mapping.data.base
    (J (next := next)) argument result).symm

theorem forward_exponential (argument result : C) :
    classOf (forwardRaw mapping (.exponential argument result)) =
      (completeComparison mapping (.exponential argument result)).hom := by
  have : PreservesFiniteLimits (mapping.data.base ⋙ J (next := next)) :=
    comp_preservesFiniteLimits _ _
  have actual : classOf (forwardRaw mapping (.exponential argument result)) =
      GeneratedCategory.abstraction
        (context := (J (next := next)).obj (mapping.data.base.obj (argument ⟶[C] result)))
        (argument := (J (next := next)).obj (mapping.data.base.obj argument))
        (result := (J (next := next)).obj (mapping.data.base.obj result))
        (classOf (inverseRaw mapping (.product (argument ⟶[C] result) argument)) ≫
          (mapping.data.base ⋙ J (next := next)).map (Interpretation.evaluation argument result)) := rfl
  rw [actual, inverse_product_canonical, abstraction_readout, exponential_canonical]
  exact BaseComparisons.CanonicalReadout.right_exponential_comparison
    (mapping.data.base ⋙ J (next := next)) argument result

theorem forward_complete (choice : BaseComparisons.Choice C) :
    classOf (forwardRaw mapping choice) = (completeComparison mapping choice).hom := by
  cases choice with
  | terminal => exact forward_terminal mapping
  | product first second => exact forward_product mapping first second
  | equalizer first second => exact forward_equalizer mapping first second
  | exponential argument result => exact forward_exponential mapping argument result

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeClosed
