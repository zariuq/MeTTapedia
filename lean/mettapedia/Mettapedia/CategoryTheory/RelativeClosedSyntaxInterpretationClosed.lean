import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationLimits
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosedReadout
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Actual closed preservation of an independently interpreted presentation

The authored evaluation code has a complete native readout. Transporting its
exchange produces the genuine tensor-left evaluation of the chosen closed
structure. At a common hom universe this computes Mathlib's canonical
exponential comparison as the earned object-comparison arrow, and therefore
proves closed preservation. No constructor preservation is a model field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v a w z k

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (assignment : Assignment C symbols D) (realization : Realization signature assignment)

theorem functor_leftEvaluation_heq (argument result : Object signature) :
    HEq ((functor assignment realization).map ((ihom.ev argument).app result))
      ((ihom.ev ((functor assignment realization).obj argument)).app
        ((functor assignment realization).obj result)) := by
  let function := exponentialObject argument result
  let raw : RawHom (product argument function) result :=
    ⟨.compose (.pair (.second argument.code function.code) (.first argument.code function.code))
      (.evaluation argument.code result.code),
      ⟨.compose (.pair (.second argument.formed.some function.formed.some)
        (.first argument.formed.some function.formed.some))
        (.evaluation argument.formed.some result.formed.some)⟩⟩
  have represented : (ihom.ev argument).app result = classOf raw :=
    (MonoidalClosed.uncurry_id_eq_ev argument result).symm.trans
      ((monoidal_uncurry (𝟙 function)).trans
        (congrArg ((GeneratedCategory.exchange function argument).inv ≫ ·)
          (unabstract_identity argument result)))
  have argumentRead := objectValue_readout assignment realization argument
  have resultRead := objectValue_readout assignment realization result
  have functionRead := assignment.evaluate_exponential argumentRead resultRead
  have swapped := assignment.evaluate_pair _ _
    (assignment.evaluate_second argumentRead functionRead)
    (assignment.evaluate_first argumentRead functionRead)
  have applied := assignment.evaluate_evaluation argumentRead resultRead
  have nativeRead : assignment.evaluateArrow raw.code =
      some ⟨(functor assignment realization).obj argument ⊗
          ((functor assignment realization).obj argument ⟶[D] (functor assignment realization).obj result),
        (functor assignment realization).obj result,
        (ihom.ev ((functor assignment realization).obj argument)).app
          ((functor assignment realization).obj result)⟩ := by
    have complete : assignment.evaluateArrow raw.code =
        some ⟨(functor assignment realization).obj argument ⊗
            ((functor assignment realization).obj argument ⟶[D] (functor assignment realization).obj result),
          (functor assignment realization).obj result,
          Interpretation.exchange ((functor assignment realization).obj argument)
            ((functor assignment realization).obj argument ⟶[D] (functor assignment realization).obj result) ≫
              Interpretation.evaluation ((functor assignment realization).obj argument)
                ((functor assignment realization).obj result)⟩ :=
      assignment.evaluate_compose _ _ swapped applied
    have cancelled : Interpretation.exchange ((functor assignment realization).obj argument)
          ((functor assignment realization).obj argument ⟶[D] (functor assignment realization).obj result) ≫
        Interpretation.evaluation ((functor assignment realization).obj argument)
          ((functor assignment realization).obj result) =
        (ihom.ev ((functor assignment realization).obj argument)).app
          ((functor assignment realization).obj result) := by
      rw [Interpretation.evaluation, ← Category.assoc, exchange_exchange, Category.id_comp]
    exact complete.trans (congrArg
      (fun arrow => some (⟨_, _, arrow⟩ : ArrowValue D)) cancelled)
  exact (heq_of_eq (congrArg (functor assignment realization).map represented)).trans
    (functor_map_heq assignment realization raw _ nativeRead)

set_option backward.isDefEq.respectTransparency false in
theorem functor_leftEvaluation (argument result : Object signature) :
    (functor assignment realization).map ((ihom.ev argument).app result) =
      eqToHom ((functor_product_object assignment realization argument (exponentialObject argument result)).trans
        (congrArg (fun value : D => (functor assignment realization).obj argument ⊗ value)
          (functor_exponential_object assignment realization argument result))) ≫
        (ihom.ev ((functor assignment realization).obj argument)).app
          ((functor assignment realization).obj result) := by
  let mapped : (functor assignment realization).obj (product argument (exponentialObject argument result)) ⟶
      (functor assignment realization).obj result :=
    (functor assignment realization).map ((ihom.ev argument).app result)
  change mapped = _
  simpa only [Functor.id_obj, mapped, eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq _ _
      ((functor_product_object assignment realization argument (exponentialObject argument result)).trans
        (congrArg (fun value : D => (functor assignment realization).obj argument ⊗ value)
          (functor_exponential_object assignment realization argument result))) rfl).mpr
      (functor_leftEvaluation_heq assignment realization argument result)

section CommonHomUniverse

variable {E : Type k} [Category.{k} E] {names : Symbols.{k}}
variable {presentation : Signature (C := E) (symbols := names)}
variable {H : Type w} [Category.{k} H]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable (meanings : Assignment E names H) (admitted : Realization presentation meanings)

theorem functor_expComparison (argument result : Object presentation) :
    (expComparison (functor meanings admitted) argument).natTrans.app result =
      eqToHom (functor_exponential_object meanings admitted argument result) := by
  have inverse : inv (CartesianMonoidalCategory.prodComparison (functor meanings admitted) argument
      (exponentialObject argument result)) =
      eqToHom (functor_product_object meanings admitted argument (exponentialObject argument result)).symm := by
    symm
    apply IsIso.eq_inv_of_hom_inv_id
    rw [functor_productComparison]
    simp only [eqToHom_trans, eqToHom_refl]
  apply MonoidalClosed.uncurry_injective
  have actual := uncurry_expComparison (functor meanings admitted) argument result
  have replaced := congrArg
    (fun incoming => incoming ≫ (functor meanings admitted).map ((ihom.ev argument).app result)) inverse
  have evaluated := congrArg
    (fun outgoing => eqToHom
      (functor_product_object meanings admitted argument (exponentialObject argument result)).symm ≫ outgoing)
    (functor_leftEvaluation meanings admitted argument result)
  have casted : eqToHom
      (functor_product_object meanings admitted argument (exponentialObject argument result)).symm ≫
        (eqToHom ((functor_product_object meanings admitted argument (exponentialObject argument result)).trans
          (congrArg (fun value : H => (functor meanings admitted).obj argument ⊗ value)
            (functor_exponential_object meanings admitted argument result))) ≫
          (ihom.ev ((functor meanings admitted).obj argument)).app
            ((functor meanings admitted).obj result)) =
      MonoidalClosed.uncurry (eqToHom (functor_exponential_object meanings admitted argument result)) := by
    rw [MonoidalClosed.uncurry_eq, MonoidalCategory.whiskerLeft_eqToHom]
    simp only [← Category.assoc, eqToHom_trans]
  exact actual.trans (replaced.trans (evaluated.trans casted))

instance functor_expComparison_isIso (argument result : Object presentation) :
    IsIso ((expComparison (functor meanings admitted) argument).natTrans.app result) := by
  rw [functor_expComparison]
  exact (inferInstance : IsIso (eqToHom
    (functor_exponential_object meanings admitted argument result) :
      (functor meanings admitted).obj (exponentialObject argument result) ⟶
        ((functor meanings admitted).obj argument ⟶[H] (functor meanings admitted).obj result)))

instance functor_closed : MonoidalClosedFunctor (functor meanings admitted) where
  comparison_iso _argument := NatIso.isIso_of_isIso_app _

end CommonHomUniverse

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
