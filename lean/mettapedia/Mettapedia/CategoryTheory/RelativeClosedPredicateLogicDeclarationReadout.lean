import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicInterpretationScopes

/-!
# Complete target readings of the thirteen authored law families

Every declaration side is evaluated independently, before the local laws
are admitted. The readings preserve the entire ordered-consequent scope,
ordered function pair, and supplied quantifier input. Equalities between
these complete values are separate semantic admission obligations.
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

def leftValue (origin : Law C) : ArrowValue D := match origin with
  | .commutativity => ⟨_, _, meaning.predicates.swapBody⟩
  | .associativity => ⟨_, _, meaning.predicates.associateLeft⟩
  | .idempotence => ⟨_, _, meaning.predicates.diagonalBody⟩
  | .truthUnit => ⟨_, _, meaning.predicates.truthUnitBody⟩
  | .implicationMonotonicity => ⟨_, _, meaning.predicates.meet
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
        (InternalPredicateImplication.antecedent meaning.predicates)
        (InternalPredicateImplication.largerConsequent meaning.predicates))
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
        (InternalPredicateImplication.antecedent meaning.predicates)
        (InternalPredicateImplication.smallerConsequent meaning.predicates))⟩
  | .implicationUnit => ⟨_, _, meaning.predicates.meet
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication (fst _ _)
        (meaning.predicates.meet (fst _ _) (snd _ _)))
      (snd meaning.predicates.proposition meaning.predicates.proposition)⟩
  | .implicationCounit => ⟨_, _, meaning.predicates.meet (snd meaning.predicates.proposition meaning.predicates.proposition)
      (meaning.predicates.meet (fst _ _)
        (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication (fst _ _) (snd _ _)))⟩
  | .universalMonotonicity (source := source) (target := target) route => ⟨_, _,
      (targetFunctions base meaning target).meet
        (InternalPredicateQuantifier.secondInput meaning.predicates (base.obj source) ≫ meaning.universal route)
        (InternalPredicateQuantifier.firstInput meaning.predicates (base.obj source) ≫ meaning.universal route)⟩
  | .universalUnit (target := target) route => ⟨_, _,
      (targetFunctions base meaning target).meet
        (InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.universal route)
        (𝟙 (targetPower base meaning target))⟩
  | .universalCounit (source := source) route => ⟨_, _,
      (targetFunctions base meaning source).meet (𝟙 (targetPower base meaning source))
        (meaning.universal route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route))⟩
  | .existentialMonotonicity (source := source) (target := target) route => ⟨_, _,
      (targetFunctions base meaning target).meet
        (InternalPredicateQuantifier.secondInput meaning.predicates (base.obj source) ≫ meaning.existential route)
        (InternalPredicateQuantifier.firstInput meaning.predicates (base.obj source) ≫ meaning.existential route)⟩
  | .existentialUnit (source := source) route => ⟨_, _,
      (targetFunctions base meaning source).meet
        (meaning.existential route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route))
        (𝟙 (targetPower base meaning source))⟩
  | .existentialCounit (target := target) route => ⟨_, _,
      (targetFunctions base meaning target).meet (𝟙 (targetPower base meaning target))
        (InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.existential route)⟩

def rightValue (origin : Law C) : ArrowValue D := match origin with
  | .commutativity => ⟨_, _, meaning.predicates.conjunction⟩
  | .associativity => ⟨_, _, meaning.predicates.associateRight⟩
  | .idempotence => ⟨_, _, 𝟙 meaning.predicates.proposition⟩
  | .truthUnit => ⟨_, _, 𝟙 meaning.predicates.proposition⟩
  | .implicationMonotonicity => ⟨_, _,
      InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
        (InternalPredicateImplication.antecedent meaning.predicates)
        (InternalPredicateImplication.smallerConsequent meaning.predicates)⟩
  | .implicationUnit => ⟨_, _, snd meaning.predicates.proposition meaning.predicates.proposition⟩
  | .implicationCounit => ⟨_, _, meaning.predicates.meet (fst _ _)
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
        (fst meaning.predicates.proposition meaning.predicates.proposition) (snd _ _))⟩
  | .universalMonotonicity (source := source) route => ⟨_, _,
      InternalPredicateQuantifier.firstInput meaning.predicates (base.obj source) ≫ meaning.universal route⟩
  | .universalUnit (target := target) _ => ⟨_, _, 𝟙 (targetPower base meaning target)⟩
  | .universalCounit route => ⟨_, _,
      meaning.universal route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route)⟩
  | .existentialMonotonicity (source := source) route => ⟨_, _,
      InternalPredicateQuantifier.firstInput meaning.predicates (base.obj source) ≫ meaning.existential route⟩
  | .existentialUnit (source := source) _ => ⟨_, _, 𝟙 (targetPower base meaning source)⟩
  | .existentialCounit route => ⟨_, _,
      InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.existential route⟩

theorem declaration_left_read (origin : Law C) :
    (assignment base meaning).evaluateArrow (declaration origin).left.code = some (leftValue base meaning origin) := by
  let values := assignment base meaning
  have omegaRead := omega_read base meaning
  have pairRead := values.evaluate_product omegaRead omegaRead
  have first := RawInterpretation.first values (left := omega) (right := omega) omegaRead omegaRead
  have second := RawInterpretation.second values (left := omega) (right := omega) omegaRead omegaRead
  have conjunction : RawInterpretation.Reads values (conjunctionRaw (C := C)) meaning.predicates.conjunction := rfl
  cases origin with
  | commutativity =>
      exact RawInterpretation.compose values
        (RawInterpretation.exchange values (left := omega) (right := omega) omegaRead omegaRead) conjunction
  | associativity =>
      exact meet_read base meaning
        (RawInterpretation.compose values
          (RawInterpretation.first values (left := product omega omega) (right := omega) pairRead omegaRead) conjunction)
        (RawInterpretation.second values (left := product omega omega) (right := omega) pairRead omegaRead)
  | idempotence =>
      exact meet_read base meaning
        (RawInterpretation.identity values (source := omega) omegaRead)
        (RawInterpretation.identity values (source := omega) omegaRead)
  | truthUnit =>
      exact meet_read base meaning
        (RawInterpretation.identity values (source := omega) omegaRead)
        (RawInterpretation.compose values (RawInterpretation.terminal values (source := omega) omegaRead) rfl)
  | implicationMonotonicity =>
      have fixed := RawInterpretation.first values (left := omega) (right := orderedPredicates)
        omegaRead (orderedPredicates_read base meaning)
      have ordered := RawInterpretation.second values (left := omega) (right := orderedPredicates)
        omegaRead (orderedPredicates_read base meaning)
      exact meet_read base meaning
        (implication_read base meaning fixed (RawInterpretation.compose values ordered (larger_read base meaning)))
        (implication_read base meaning fixed (RawInterpretation.compose values ordered (smaller_read base meaning)))
  | implicationUnit =>
      exact meet_read base meaning
        (implication_read base meaning first (meet_read base meaning first second)) second
  | implicationCounit =>
      exact meet_read base meaning second
        (meet_read base meaning first (implication_read base meaning first second))
  | universalMonotonicity route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.compose values (largerFunction_read base meaning _) rfl)
        (RawInterpretation.compose values (smallerFunction_read base meaning _) rfl)
  | universalUnit route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.compose values (precomposition_read base meaning route) rfl)
        (RawInterpretation.identity values (source := power _) (power_read base meaning _))
  | universalCounit route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.identity values (source := power _) (power_read base meaning _))
        (RawInterpretation.compose values rfl (precomposition_read base meaning route))
  | existentialMonotonicity route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.compose values (largerFunction_read base meaning _) rfl)
        (RawInterpretation.compose values (smallerFunction_read base meaning _) rfl)
  | existentialUnit route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.compose values rfl (precomposition_read base meaning route))
        (RawInterpretation.identity values (source := power _) (power_read base meaning _))
  | existentialCounit route =>
      exact powerMeet_read base meaning _
        (RawInterpretation.identity values (source := power _) (power_read base meaning _))
        (RawInterpretation.compose values (precomposition_read base meaning route) rfl)

theorem declaration_right_read (origin : Law C) :
    (assignment base meaning).evaluateArrow (declaration origin).right.code = some (rightValue base meaning origin) := by
  let values := assignment base meaning
  have omegaRead := omega_read base meaning
  have pairRead := values.evaluate_product omegaRead omegaRead
  have first := RawInterpretation.first values (left := omega) (right := omega) omegaRead omegaRead
  have second := RawInterpretation.second values (left := omega) (right := omega) omegaRead omegaRead
  cases origin with
  | commutativity => rfl
  | associativity =>
      exact meet_read base meaning
        (RawInterpretation.compose values
          (RawInterpretation.first values (left := product omega omega) (right := omega) pairRead omegaRead) first)
        (meet_read base meaning
          (RawInterpretation.compose values
            (RawInterpretation.first values (left := product omega omega) (right := omega) pairRead omegaRead) second)
          (RawInterpretation.second values (left := product omega omega) (right := omega) pairRead omegaRead))
  | idempotence =>
      exact RawInterpretation.identity values (source := omega) omegaRead
  | truthUnit =>
      exact RawInterpretation.identity values (source := omega) omegaRead
  | implicationMonotonicity =>
      have fixed := RawInterpretation.first values (left := omega) (right := orderedPredicates)
        omegaRead (orderedPredicates_read base meaning)
      have ordered := RawInterpretation.second values (left := omega) (right := orderedPredicates)
        omegaRead (orderedPredicates_read base meaning)
      exact implication_read base meaning fixed (RawInterpretation.compose values ordered (smaller_read base meaning))
  | implicationUnit =>
      exact second
  | implicationCounit =>
      exact meet_read base meaning first (implication_read base meaning first second)
  | universalMonotonicity route =>
      exact RawInterpretation.compose values (smallerFunction_read base meaning _) rfl
  | universalUnit route =>
      exact RawInterpretation.identity values (source := power _) (power_read base meaning _)
  | universalCounit route =>
      exact RawInterpretation.compose values rfl (precomposition_read base meaning route)
  | existentialMonotonicity route =>
      exact RawInterpretation.compose values (smallerFunction_read base meaning _) rfl
  | existentialUnit route =>
      exact RawInterpretation.identity values (source := power _) (power_read base meaning _)
  | existentialCounit route =>
      exact RawInterpretation.compose values (precomposition_read base meaning route) rfl

theorem local_values_equal (admitted : Admission base meaning) (origin : Law C) :
    leftValue base meaning origin = rightValue base meaning origin := by
  cases origin with
  | commutativity =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.conjunction.commutativity
  | associativity =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.conjunction.associativity
  | idempotence =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.conjunction.idempotence
  | truthUnit =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.conjunction.truthUnit
  | implicationMonotonicity =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.implicationMonotonicity
  | implicationUnit =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.implicationUnit
  | implicationCounit =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) admitted.implicationCounit
  | universalMonotonicity route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D))
        (admitted.universalMonotonicity route).ordered
  | universalUnit route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) (admitted.universalUnit route)
  | universalCounit route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) (admitted.universalCounit route)
  | existentialMonotonicity route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D))
        (admitted.existentialMonotonicity route).ordered
  | existentialUnit route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) (admitted.existentialUnit route)
  | existentialCounit route =>
      exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) (admitted.existentialCounit route)

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation
