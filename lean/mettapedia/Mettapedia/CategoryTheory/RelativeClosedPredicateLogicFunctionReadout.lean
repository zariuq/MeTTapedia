import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicOperations
import Mettapedia.CategoryTheory.InternalPredicateQuantifier

/-!
# Complete function readouts of the authored predicate presentation

The raw pointwise conjunction and base-arrow precomposition agree with the
actual exponential adjunction of the generated category. The proof reads
both supplied functions at the complete argument and parameter context.
It also retains the exchange between raw context-first abstraction and
categorical argument-first evaluation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C]

theorem cartesian_pairing {context first second : Object (lawfulSignature (C := C))}
    (before : context ⟶ first) (after : context ⟶ second) :
    lift before after = pairing before after := by
  apply product_joint_cancel
  · exact (lift_fst before after).trans (pairing_first before after).symm
  · exact (lift_snd before after).trans (pairing_second before after).symm

abbrev valueObject (value : C) := baseObject (lawfulSignature (C := C)) value

abbrev functionObject (value : C) :=
  InternalPredicateFunctionObject.power (operations (C := C)) (valueObject value)

theorem abstraction_read {context argument result : Object (lawfulSignature (C := C))}
    (body : product context argument ⟶ result) :
    MonoidalClosed.uncurry (abstraction body) = (exchange context argument).inv ≫ body := by
  rw [monoidal_uncurry, unabstract_abstraction]

theorem powerConjunction_readout (value : C) :
    (inclusion (C := C)).functor.map (classOf (powerConjunctionRaw value)) =
      (InternalPredicateFunctionObject.operations (operations (C := C)) (valueObject value)).conjunction := by
  let before : product (functionObject value) (functionObject value) ⟶ functionObject value :=
    fst _ _
  let after : product (functionObject value) (functionObject value) ⟶ functionObject value :=
    snd _ _
  have authored : inclusion.functor.map (classOf (powerConjunctionRaw value)) =
      abstraction (operations.meet (unabstract before) (unabstract after)) := by
    change abstraction (pairing (unabstract before) (unabstract after) ≫ operations.conjunction) = _
    unfold InternalConjunctiveObject.Operations.meet
    rw [cartesian_pairing]
  rw [authored]
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (abstraction (operations.meet (unabstract before) (unabstract after))) =
    MonoidalClosed.uncurry (MonoidalClosed.curry
      (operations.meet (MonoidalClosed.uncurry before) (MonoidalClosed.uncurry after)))
  rw [abstraction_read, uncurry_curry]
  have natural := operations.reindex_meet
    (exchange (product (functionObject value) (functionObject value)) (valueObject value)).inv
    (unabstract before) (unabstract after)
  exact natural.trans (congrArg₂ operations.meet (monoidal_uncurry before).symm
    (monoidal_uncurry after).symm)

theorem powerMeet_readout {context : Object (signature (C := C))} (value : C)
    (before after : RawHom context (power value)) :
    inclusion.functor.map (classOf (powerMeetRaw value before after)) =
      (InternalPredicateFunctionObject.operations (operations (C := C)) (valueObject value)).meet
        (inclusion.functor.map (classOf before)) (inclusion.functor.map (classOf after)) := by
  change pairing (inclusion.functor.map (classOf before)) (inclusion.functor.map (classOf after)) ≫
    inclusion.functor.map (classOf (powerConjunctionRaw value)) = _
  rw [powerConjunction_readout]
  unfold InternalConjunctiveObject.Operations.meet
  rw [cartesian_pairing]

theorem precomposition_readout {source target : C} (route : source ⟶ target) :
    (inclusion (C := C)).functor.map (classOf (precompositionRaw route)) =
      InternalPredicateQuantifier.precomposition (operations (C := C))
        ((baseFunctor (lawfulSignature (C := C))).map route) := by
  let actual : valueObject source ⟶ valueObject target :=
    (baseFunctor (lawfulSignature (C := C))).map route
  let context := functionObject (C := C) target
  have authored : inclusion.functor.map (classOf (precompositionRaw route)) =
      abstraction (pairing (first context (valueObject source))
        (second context (valueObject source) ≫ actual) ≫
          evaluation (valueObject target) operations.proposition) := rfl
  rw [authored]
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (abstraction _) =
    MonoidalClosed.uncurry (MonoidalClosed.curry
      ((actual ▷ context) ≫ (ihom.ev (valueObject target)).app operations.proposition))
  rw [abstraction_read, uncurry_curry, SignatureMap.monoidal_left_evaluation]
  have complete : (exchange context (valueObject source)).inv ≫
      pairing (first context (valueObject source))
        (second context (valueObject source) ≫ actual) =
      (actual ▷ context) ≫ (exchange context (valueObject target)).inv := by
    apply product_joint_cancel
    · simp only [Category.assoc, pairing_first, exchange]
      exact (CartesianMonoidalCategory.whiskerRight_snd actual context).symm
    · simp only [Category.assoc, pairing_second, exchange]
      rw [← Category.assoc, pairing_second]
      exact (CartesianMonoidalCategory.whiskerRight_fst actual context).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ evaluation (valueObject target) operations.proposition) complete).trans
      (Category.assoc _ _ _))

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations
