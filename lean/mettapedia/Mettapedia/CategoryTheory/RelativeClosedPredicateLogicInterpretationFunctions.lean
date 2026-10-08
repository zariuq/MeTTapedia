import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicInterpretation

/-!
# Independent readings of authored complete predicate functions

The target evaluator reads the actual curried pointwise conjunction and
base-arrow precomposition terms. Argument-first categorical evaluation is
compared with the retained raw context-first construction. The ordered
function and predicate scopes are the actual target equalizers of those
independently computed arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation
open GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

omit [HasFiniteLimits D] in
private theorem pointwise_abstraction (original : InternalConjunctiveObject.Operations D) (value : D) :
    let P := InternalPredicateFunctionObject.power original value
    RelativeClosedSyntax.Interpretation.abstraction (original.meet
      (lift (fst (P ⊗ P) value ≫ fst P P) (snd (P ⊗ P) value) ≫
        RelativeClosedSyntax.Interpretation.evaluation value original.proposition)
      (lift (fst (P ⊗ P) value ≫ snd P P) (snd (P ⊗ P) value) ≫
        RelativeClosedSyntax.Interpretation.evaluation value original.proposition)) =
      (InternalPredicateFunctionObject.operations original value).conjunction := by
  dsimp only
  let P := InternalPredicateFunctionObject.power original value
  let first := fst P P
  let second := snd P P
  let firstApplication := lift (fst (P ⊗ P) value ≫ first) (snd (P ⊗ P) value) ≫
    RelativeClosedSyntax.Interpretation.evaluation value original.proposition
  let secondApplication := lift (fst (P ⊗ P) value ≫ second) (snd (P ⊗ P) value) ≫
    RelativeClosedSyntax.Interpretation.evaluation value original.proposition
  change MonoidalClosed.curry (RelativeClosedSyntax.Interpretation.exchange value (P ⊗ P) ≫
      original.meet firstApplication secondApplication) =
    MonoidalClosed.curry (original.meet (MonoidalClosed.uncurry first) (MonoidalClosed.uncurry second))
  apply congrArg MonoidalClosed.curry
  have firstRead : RelativeClosedSyntax.Interpretation.exchange value (P ⊗ P) ≫ firstApplication =
      MonoidalClosed.uncurry first := by
    dsimp only [firstApplication]
    rw [RelativeClosedSyntax.Interpretation.application_eq, ← Category.assoc,
      RelativeClosedSyntax.Interpretation.exchange_exchange, Category.id_comp]
  have secondRead : RelativeClosedSyntax.Interpretation.exchange value (P ⊗ P) ≫ secondApplication =
      MonoidalClosed.uncurry second := by
    dsimp only [secondApplication]
    rw [RelativeClosedSyntax.Interpretation.application_eq, ← Category.assoc,
      RelativeClosedSyntax.Interpretation.exchange_exchange, Category.id_comp]
  exact (original.reindex_meet _ firstApplication secondApplication).trans
    (congrArg₂ original.meet firstRead secondRead)

omit [HasFiniteLimits D] in
private theorem precomposition_abstraction (original : InternalConjunctiveObject.Operations D)
    {source target : D} (route : source ⟶ target) :
    let P := InternalPredicateFunctionObject.power original target
    RelativeClosedSyntax.Interpretation.abstraction
      (lift (fst P source) (snd P source ≫ route) ≫
        RelativeClosedSyntax.Interpretation.evaluation target original.proposition) =
      InternalPredicateQuantifier.precomposition original route := by
  dsimp only
  let P := InternalPredicateFunctionObject.power original target
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (MonoidalClosed.curry _) =
    MonoidalClosed.uncurry (MonoidalClosed.curry _)
  rw [uncurry_curry, uncurry_curry]
  unfold RelativeClosedSyntax.Interpretation.evaluation
  have square : RelativeClosedSyntax.Interpretation.exchange source P ≫
      lift (fst P source) (snd P source ≫ route) ≫
        RelativeClosedSyntax.Interpretation.exchange P target = route ▷ P := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, RelativeClosedSyntax.Interpretation.exchange_first,
        lift_snd, RelativeClosedSyntax.Interpretation.exchange_second_assoc]
      exact (whiskerRight_fst route P).symm
    · simp only [Category.assoc, RelativeClosedSyntax.Interpretation.exchange_second,
        lift_fst, RelativeClosedSyntax.Interpretation.exchange_first]
      exact (whiskerRight_snd route P).symm
  simpa only [Category.assoc] using congrArg (· ≫ (ihom.ev target).app original.proposition) square

variable (base : C ⥤ D) (meaning : Meaning base)

theorem powerConjunction_read (value : C) :
    RawInterpretation.Reads (assignment base meaning) (powerConjunctionRaw value)
      (targetFunctions base meaning value).conjunction := by
  let values := assignment base meaning
  let P := targetPower base meaning value
  let rawPower := power (C := C) value
  let rawValue := baseObject (signature (C := C)) value
  let rawContext := product rawPower rawPower
  have powerRead : RawInterpretation.ObjectReads values rawPower P := power_read base meaning value
  have valueRead : RawInterpretation.ObjectReads values rawValue (base.obj value) := rfl
  have contextRead := values.evaluate_product powerRead powerRead
  have firstFunction := RawInterpretation.compose values
    (RawInterpretation.first values (left := rawContext) (right := rawValue) contextRead valueRead)
    (RawInterpretation.first values (left := rawPower) (right := rawPower) powerRead powerRead)
  have secondFunction := RawInterpretation.compose values
    (RawInterpretation.first values (left := rawContext) (right := rawValue) contextRead valueRead)
    (RawInterpretation.second values (left := rawPower) (right := rawPower) powerRead powerRead)
  have argument := RawInterpretation.second values (left := rawContext) (right := rawValue) contextRead valueRead
  have evaluation := RawInterpretation.evaluation values (argument := rawValue) (result := omega)
    valueRead (omega_read base meaning)
  have firstApplication := RawInterpretation.compose values (RawInterpretation.pair values firstFunction argument)
    evaluation
  have secondApplication := RawInterpretation.compose values (RawInterpretation.pair values secondFunction argument)
    evaluation
  have body := meet_read base meaning firstApplication secondApplication
  have complete := RawInterpretation.abstract values (context := rawContext) (argument := rawValue) (result := omega)
    contextRead valueRead (omega_read base meaning) body
  exact complete.trans (congrArg
    (fun arrow => some (⟨P ⊗ P, P, arrow⟩ : ArrowValue D))
    (pointwise_abstraction meaning.predicates (base.obj value)))

theorem powerMeet_read {context : Object (signature (C := C))} {value : D} (argument : C)
    {before after : RawHom context (power argument)}
    {first second : value ⟶ targetPower base meaning argument}
    (beforeRead : RawInterpretation.Reads (assignment base meaning) before first)
    (afterRead : RawInterpretation.Reads (assignment base meaning) after second) :
    RawInterpretation.Reads (assignment base meaning) (powerMeetRaw argument before after)
      ((targetFunctions base meaning argument).meet first second) :=
  RawInterpretation.compose (assignment base meaning)
    (RawInterpretation.pair (assignment base meaning) beforeRead afterRead)
    (powerConjunction_read base meaning argument)

theorem precomposition_read {source target : C} (route : source ⟶ target) :
    RawInterpretation.Reads (assignment base meaning) (precompositionRaw route)
      (InternalPredicateQuantifier.precomposition meaning.predicates (base.map route)) := by
  let values := assignment base meaning
  let P := targetPower base meaning target
  let rawPower := power (C := C) target
  let rawSource := baseObject (signature (C := C)) source
  let rawTarget := baseObject (signature (C := C)) target
  have powerRead : RawInterpretation.ObjectReads values rawPower P := power_read base meaning target
  have sourceRead : RawInterpretation.ObjectReads values rawSource (base.obj source) := rfl
  have targetRead : RawInterpretation.ObjectReads values rawTarget (base.obj target) := rfl
  have routeRead : RawInterpretation.Reads values
      (⟨.base route, ⟨.baseArrow route⟩⟩ : RawHom rawSource rawTarget) (base.map route) := rfl
  have input := RawInterpretation.pair values
    (RawInterpretation.first values (left := rawPower) (right := rawSource) powerRead sourceRead)
    (RawInterpretation.compose values
      (RawInterpretation.second values (left := rawPower) (right := rawSource) powerRead sourceRead) routeRead)
  have body := RawInterpretation.compose values input
    (RawInterpretation.evaluation values (argument := rawTarget) (result := omega)
      targetRead (omega_read base meaning))
  have complete := RawInterpretation.abstract values (context := rawPower) (argument := rawSource) (result := omega)
    powerRead sourceRead (omega_read base meaning) body
  exact complete.trans (congrArg
    (fun arrow => some (⟨P, targetPower base meaning source, arrow⟩ : ArrowValue D))
    (precomposition_abstraction meaning.predicates (base.map route)))

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation
