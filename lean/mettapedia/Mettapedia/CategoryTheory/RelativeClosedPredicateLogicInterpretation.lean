import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicQuantifiers
import Mettapedia.CategoryTheory.RelativeClosedRawInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation

/-!
# Independent meanings for the generated predicate-law presentation

Primitive meanings are complete target arrows, separately from their
finite local admission. Their headers are read by the independent
structural evaluator. The admission record contains only the four
conjunctive diagrams and the three diagrams for each logical operation;
it contains no whole-expression or generated-equation soundness field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation
open GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure Meaning (base : C ⥤ D) where
  predicates : InternalConjunctiveObject.Operations D
  implication : predicates.proposition ⊗ predicates.proposition ⟶ predicates.proposition
  universal {source target : C} (route : source ⟶ target) :
    InternalPredicateFunctionObject.power predicates (base.obj source) ⟶
      InternalPredicateFunctionObject.power predicates (base.obj target)
  existential {source target : C} (route : source ⟶ target) :
    InternalPredicateFunctionObject.power predicates (base.obj source) ⟶
      InternalPredicateFunctionObject.power predicates (base.obj target)

variable (base : C ⥤ D) (meaning : Meaning base)

abbrev targetPower (value : C) := InternalPredicateFunctionObject.power meaning.predicates (base.obj value)
abbrev targetFunctions (value : C) := InternalPredicateFunctionObject.operations meaning.predicates (base.obj value)

structure Admission : Prop where
  conjunction : meaning.predicates.Laws
  implicationMonotonicity : meaning.predicates.meet
    (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
      (InternalPredicateImplication.antecedent meaning.predicates)
      (InternalPredicateImplication.largerConsequent meaning.predicates))
    (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
      (InternalPredicateImplication.antecedent meaning.predicates)
      (InternalPredicateImplication.smallerConsequent meaning.predicates)) =
    InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
      (InternalPredicateImplication.antecedent meaning.predicates)
      (InternalPredicateImplication.smallerConsequent meaning.predicates)
  implicationUnit : meaning.predicates.meet
    (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication (fst _ _)
      (meaning.predicates.meet (fst _ _) (snd _ _)))
    (snd meaning.predicates.proposition meaning.predicates.proposition) = snd _ _
  implicationCounit : meaning.predicates.meet (snd meaning.predicates.proposition meaning.predicates.proposition)
    (meaning.predicates.meet (fst _ _)
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication (fst _ _) (snd _ _))) =
    meaning.predicates.meet (fst _ _)
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication (fst _ _) (snd _ _))
  universalMonotonicity {source target : C} (route : source ⟶ target) :
    InternalPredicateQuantifier.Monotonicity meaning.predicates (meaning.universal route)
  universalUnit {source target : C} (route : source ⟶ target) :
    (targetFunctions base meaning target).meet
      (InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.universal route)
      (𝟙 (targetPower base meaning target)) = 𝟙 _
  universalCounit {source target : C} (route : source ⟶ target) :
    (targetFunctions base meaning source).meet (𝟙 (targetPower base meaning source))
      (meaning.universal route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route)) =
    meaning.universal route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route)
  existentialMonotonicity {source target : C} (route : source ⟶ target) :
    InternalPredicateQuantifier.Monotonicity meaning.predicates (meaning.existential route)
  existentialUnit {source target : C} (route : source ⟶ target) :
    (targetFunctions base meaning source).meet
      (meaning.existential route ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map route))
      (𝟙 (targetPower base meaning source)) = 𝟙 _
  existentialCounit {source target : C} (route : source ⟶ target) :
    (targetFunctions base meaning target).meet (𝟙 (targetPower base meaning target))
      (InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.existential route) =
    InternalPredicateQuantifier.precomposition meaning.predicates (base.map route) ≫ meaning.existential route

def assignment : Assignment C (symbols C) D where
  base := base
  object _ := meaning.predicates.proposition
  arrow
    | .truth => ⟨𝟙_ D, meaning.predicates.proposition, meaning.predicates.truth⟩
    | .conjunction => ⟨meaning.predicates.proposition ⊗ meaning.predicates.proposition,
        meaning.predicates.proposition, meaning.predicates.conjunction⟩
    | .implication => ⟨meaning.predicates.proposition ⊗ meaning.predicates.proposition,
        meaning.predicates.proposition, meaning.implication⟩
    | .universal (source := source) (target := target) route =>
        ⟨targetPower base meaning source, targetPower base meaning target, meaning.universal route⟩
    | .existential (source := source) (target := target) route =>
        ⟨targetPower base meaning source, targetPower base meaning target, meaning.existential route⟩

theorem omega_read :
    (assignment base meaning).evaluateObject (omegaCode (C := C)) = some meaning.predicates.proposition := rfl

theorem power_read (value : C) :
    (assignment base meaning).evaluateObject (powerCode value) = some (targetPower base meaning value) :=
  (assignment base meaning).evaluate_exponential rfl (omega_read base meaning)

theorem headers_realized : Realization (signature (C := C)) (assignment base meaning) where
  source origin := by
    cases origin with
    | truth => rfl
    | conjunction => exact (assignment base meaning).evaluate_product rfl rfl
    | implication => exact (assignment base meaning).evaluate_product rfl rfl
    | universal route => exact power_read base meaning _
    | existential route => exact power_read base meaning _
  target origin := by
    cases origin with
    | truth => rfl
    | conjunction => rfl
    | implication => rfl
    | universal route => exact power_read base meaning _
    | existential route => exact power_read base meaning _
  equation origin := origin.down.elim

theorem meet_read {context : Object (signature (C := C))} {value : D}
    {before after : RawHom context omega} {first second : value ⟶ meaning.predicates.proposition}
    (beforeRead : RawInterpretation.Reads (assignment base meaning) before first)
    (afterRead : RawInterpretation.Reads (assignment base meaning) after second) :
    RawInterpretation.Reads (assignment base meaning) (meetRaw before after)
      (meaning.predicates.meet first second) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.pair (assignment base meaning) beforeRead afterRead) rfl

theorem implication_read {context : Object (signature (C := C))} {value : D}
    {before after : RawHom context omega} {first second : value ⟶ meaning.predicates.proposition}
    (beforeRead : RawInterpretation.Reads (assignment base meaning) before first)
    (afterRead : RawInterpretation.Reads (assignment base meaning) after second) :
    RawInterpretation.Reads (assignment base meaning) (implyRaw before after)
      (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication first second) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.pair (assignment base meaning) beforeRead afterRead) rfl

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation
