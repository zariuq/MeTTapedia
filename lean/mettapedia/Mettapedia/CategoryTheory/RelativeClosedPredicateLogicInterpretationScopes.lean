import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicInterpretationFunctions

/-!
# Independently evaluated ordered predicate and function scopes

The authored equalizer scopes are read at the actual target equalizers.
Both coordinate arrows retain the complete supplied target predicate or
function. These readings need only primitive meanings, not logical-law
admission or any equation realization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning base)

theorem orderedPredicates_read :
    RawInterpretation.ObjectReads (assignment base meaning) (orderedPredicates (C := C))
      (InternalPredicateImplication.orderedPairs meaning.predicates) :=
  (assignment base meaning).evaluate_equalizer meaning.predicates.conjunction (fst _ _)
    ((assignment base meaning).evaluate_product (omega_read base meaning) (omega_read base meaning))
    (omega_read base meaning) rfl
    (RawInterpretation.first (assignment base meaning) (left := omega) (right := omega)
      (omega_read base meaning) (omega_read base meaning))

theorem smaller_read : RawInterpretation.Reads (assignment base meaning) (smallerRaw (C := C))
    (InternalPredicateImplication.smaller meaning.predicates) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.inclusion (assignment base meaning) (source := product omega omega) (target := omega)
      ((assignment base meaning).evaluate_product (omega_read base meaning) (omega_read base meaning))
      (omega_read base meaning) rfl
      (RawInterpretation.first (assignment base meaning) (left := omega) (right := omega)
        (omega_read base meaning) (omega_read base meaning)))
    (RawInterpretation.first (assignment base meaning) (left := omega) (right := omega)
      (omega_read base meaning) (omega_read base meaning))

theorem larger_read : RawInterpretation.Reads (assignment base meaning) (largerRaw (C := C))
    (InternalPredicateImplication.larger meaning.predicates) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.inclusion (assignment base meaning) (source := product omega omega) (target := omega)
      ((assignment base meaning).evaluate_product (omega_read base meaning) (omega_read base meaning))
      (omega_read base meaning) rfl
      (RawInterpretation.first (assignment base meaning) (left := omega) (right := omega)
        (omega_read base meaning) (omega_read base meaning)))
    (RawInterpretation.second (assignment base meaning) (left := omega) (right := omega)
      (omega_read base meaning) (omega_read base meaning))

theorem orderedFunctions_read (value : C) :
    RawInterpretation.ObjectReads (assignment base meaning) (orderedFunctions value)
      (InternalPredicateQuantifier.orderedPairs meaning.predicates (base.obj value)) :=
  (assignment base meaning).evaluate_equalizer (targetFunctions base meaning value).conjunction (fst _ _)
    ((assignment base meaning).evaluate_product (power_read base meaning value) (power_read base meaning value))
    (power_read base meaning value) (powerConjunction_read base meaning value)
    (RawInterpretation.first (assignment base meaning) (left := power value) (right := power value)
      (power_read base meaning value) (power_read base meaning value))

theorem smallerFunction_read (value : C) :
    RawInterpretation.Reads (assignment base meaning) (smallerFunctionRaw value)
      (InternalPredicateQuantifier.firstInput meaning.predicates (base.obj value)) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.inclusion (assignment base meaning)
      (source := product (power value) (power value)) (target := power value)
      ((assignment base meaning).evaluate_product (power_read base meaning value) (power_read base meaning value))
      (power_read base meaning value) (powerConjunction_read base meaning value)
      (RawInterpretation.first (assignment base meaning) (left := power value) (right := power value)
        (power_read base meaning value) (power_read base meaning value)))
    (RawInterpretation.first (assignment base meaning) (left := power value) (right := power value)
      (power_read base meaning value) (power_read base meaning value))

theorem largerFunction_read (value : C) :
    RawInterpretation.Reads (assignment base meaning) (largerFunctionRaw value)
      (InternalPredicateQuantifier.secondInput meaning.predicates (base.obj value)) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.inclusion (assignment base meaning)
      (source := product (power value) (power value)) (target := power value)
      ((assignment base meaning).evaluate_product (power_read base meaning value) (power_read base meaning value))
      (power_read base meaning value) (powerConjunction_read base meaning value)
      (RawInterpretation.first (assignment base meaning) (left := power value) (right := power value)
        (power_read base meaning value) (power_read base meaning value)))
    (RawInterpretation.second (assignment base meaning) (left := power value) (right := power value)
      (power_read base meaning value) (power_read base meaning value))

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation
