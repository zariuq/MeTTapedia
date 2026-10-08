import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierSyntax
import Mettapedia.CategoryTheory.RelativeClosedRawInterpretation
import Mettapedia.CategoryTheory.InternalPredicateQuantifier

/-!
# Independent complete function readouts at generated raw scopes

The proposition and conjunction have only their own successful target
readings. Actual raw object and arrow readings then earn power, pointwise
conjunction and precomposition at arbitrary generated scopes. Context-first
raw abstraction is compared with the actual argument-first evaluation.
No all-expression compatibility law is assumed in these local interfaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Readout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {original : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

omit [HasFiniteLimits D] in
theorem pointwise_abstraction (operations : InternalConjunctiveObject.Operations D) (value : D) :
    let P := InternalPredicateFunctionObject.power operations value
    RelativeClosedSyntax.Interpretation.abstraction (operations.meet
      (lift (fst (P ⊗ P) value ≫ fst P P) (snd (P ⊗ P) value) ≫
        RelativeClosedSyntax.Interpretation.evaluation value operations.proposition)
      (lift (fst (P ⊗ P) value ≫ snd P P) (snd (P ⊗ P) value) ≫
        RelativeClosedSyntax.Interpretation.evaluation value operations.proposition)) =
      (InternalPredicateFunctionObject.operations operations value).conjunction := by
  dsimp only
  let P := InternalPredicateFunctionObject.power operations value
  let first := fst P P
  let second := snd P P
  let firstApplication := lift (fst (P ⊗ P) value ≫ first) (snd (P ⊗ P) value) ≫
    RelativeClosedSyntax.Interpretation.evaluation value operations.proposition
  let secondApplication := lift (fst (P ⊗ P) value ≫ second) (snd (P ⊗ P) value) ≫
    RelativeClosedSyntax.Interpretation.evaluation value operations.proposition
  change MonoidalClosed.curry (RelativeClosedSyntax.Interpretation.exchange value (P ⊗ P) ≫
      operations.meet firstApplication secondApplication) =
    MonoidalClosed.curry (operations.meet (MonoidalClosed.uncurry first) (MonoidalClosed.uncurry second))
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
  exact (operations.reindex_meet _ firstApplication secondApplication).trans
    (congrArg₂ operations.meet firstRead secondRead)

omit [HasFiniteLimits D] in
theorem precomposition_abstraction (operations : InternalConjunctiveObject.Operations D)
    {source target : D} (route : source ⟶ target) :
    let P := InternalPredicateFunctionObject.power operations target
    RelativeClosedSyntax.Interpretation.abstraction
      (lift (fst P source) (snd P source ≫ route) ≫
        RelativeClosedSyntax.Interpretation.evaluation target operations.proposition) =
      InternalPredicateQuantifier.precomposition operations route := by
  dsimp only
  let P := InternalPredicateFunctionObject.power operations target
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (MonoidalClosed.curry _) = MonoidalClosed.uncurry (MonoidalClosed.curry _)
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
  simpa only [Category.assoc] using congrArg (· ≫ (ihom.ev target).app operations.proposition) square

variable (language : PredicateSyntax original) (meanings : Assignment C symbols D)
variable (operations : InternalConjunctiveObject.Operations D)

theorem power_read (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    {raw : Object original} {value : D} (valueRead : RawInterpretation.ObjectReads meanings raw value) :
    RawInterpretation.ObjectReads meanings (language.power raw) (InternalPredicateFunctionObject.power operations value) :=
  meanings.evaluate_exponential valueRead propositionRead

theorem meet_read (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {context : Object original} {value : D} {before after : RawHom context language.proposition}
    {first second : value ⟶ operations.proposition}
    (beforeRead : RawInterpretation.Reads meanings before first)
    (afterRead : RawInterpretation.Reads meanings after second) :
    RawInterpretation.Reads meanings (language.meet before after) (operations.meet first second) :=
  RawInterpretation.compose meanings (RawInterpretation.pair meanings beforeRead afterRead) conjunctionRead

theorem powerConjunction_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {raw : Object original} {value : D} (valueRead : RawInterpretation.ObjectReads meanings raw value) :
    RawInterpretation.Reads meanings (language.powerConjunction raw)
      (InternalPredicateFunctionObject.operations operations value).conjunction := by
  let P := InternalPredicateFunctionObject.power operations value
  let rawPower := language.power raw
  let rawContext := product rawPower rawPower
  have powerRead := power_read language meanings operations propositionRead valueRead
  have contextRead := meanings.evaluate_product powerRead powerRead
  have firstFunction := RawInterpretation.compose meanings
    (RawInterpretation.first meanings (left := rawContext) (right := raw) contextRead valueRead)
    (RawInterpretation.first meanings (left := rawPower) (right := rawPower) powerRead powerRead)
  have secondFunction := RawInterpretation.compose meanings
    (RawInterpretation.first meanings (left := rawContext) (right := raw) contextRead valueRead)
    (RawInterpretation.second meanings (left := rawPower) (right := rawPower) powerRead powerRead)
  have argument := RawInterpretation.second meanings (left := rawContext) (right := raw) contextRead valueRead
  have evaluation := RawInterpretation.evaluation meanings (argument := raw) (result := language.proposition)
    valueRead propositionRead
  have firstApplication := RawInterpretation.compose meanings (RawInterpretation.pair meanings firstFunction argument) evaluation
  have secondApplication := RawInterpretation.compose meanings (RawInterpretation.pair meanings secondFunction argument) evaluation
  have body := meet_read language meanings operations conjunctionRead firstApplication secondApplication
  have complete := RawInterpretation.abstract meanings (context := rawContext) (argument := raw)
    (result := language.proposition) contextRead valueRead propositionRead body
  exact complete.trans (congrArg (fun arrow => some (⟨P ⊗ P, P, arrow⟩ : ArrowValue D))
    (pointwise_abstraction operations value))

theorem powerMeet_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {context raw : Object original} {value parameter : D} (valueRead : RawInterpretation.ObjectReads meanings raw value)
    {before after : RawHom context (language.power raw)}
    {first second : parameter ⟶ InternalPredicateFunctionObject.power operations value}
    (beforeRead : RawInterpretation.Reads meanings before first)
    (afterRead : RawInterpretation.Reads meanings after second) :
    RawInterpretation.Reads meanings (language.powerMeet raw before after)
      ((InternalPredicateFunctionObject.operations operations value).meet first second) :=
  RawInterpretation.compose meanings (RawInterpretation.pair meanings beforeRead afterRead)
    (powerConjunction_read language meanings operations propositionRead conjunctionRead valueRead)

theorem precomposition_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (route : Route original) {source target : D}
    (sourceRead : RawInterpretation.ObjectReads meanings route.source source)
    (targetRead : RawInterpretation.ObjectReads meanings route.target target)
    {arrow : source ⟶ target} (arrowRead : RawInterpretation.Reads meanings route.arrow arrow) :
    RawInterpretation.Reads meanings (language.precomposition route)
      (InternalPredicateQuantifier.precomposition operations arrow) := by
  let P := InternalPredicateFunctionObject.power operations target
  let rawPower := language.power route.target
  have powerRead := power_read language meanings operations propositionRead targetRead
  have input := RawInterpretation.pair meanings
    (RawInterpretation.first meanings (left := rawPower) (right := route.source) powerRead sourceRead)
    (RawInterpretation.compose meanings
      (RawInterpretation.second meanings (left := rawPower) (right := route.source) powerRead sourceRead) arrowRead)
  have body := RawInterpretation.compose meanings input
    (RawInterpretation.evaluation meanings (argument := route.target) (result := language.proposition) targetRead propositionRead)
  have complete := RawInterpretation.abstract meanings (context := rawPower) (argument := route.source)
    (result := language.proposition) powerRead sourceRead propositionRead body
  exact complete.trans (congrArg
    (fun output => some (⟨P, InternalPredicateFunctionObject.power operations source, output⟩ : ArrowValue D))
    (precomposition_abstraction operations arrow))

theorem orderedFunctions_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {raw : Object original} {value : D} (valueRead : RawInterpretation.ObjectReads meanings raw value) :
    RawInterpretation.ObjectReads meanings (language.orderedFunctions raw)
      (InternalPredicateQuantifier.orderedPairs operations value) :=
  meanings.evaluate_equalizer (InternalPredicateFunctionObject.operations operations value).conjunction (fst _ _)
    (meanings.evaluate_product (power_read language meanings operations propositionRead valueRead)
      (power_read language meanings operations propositionRead valueRead))
    (power_read language meanings operations propositionRead valueRead)
    (powerConjunction_read language meanings operations propositionRead conjunctionRead valueRead)
    (RawInterpretation.first meanings (left := language.power raw) (right := language.power raw)
      (power_read language meanings operations propositionRead valueRead)
      (power_read language meanings operations propositionRead valueRead))

theorem smaller_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {raw : Object original} {value : D} (valueRead : RawInterpretation.ObjectReads meanings raw value) :
    RawInterpretation.Reads meanings (language.smaller raw) (InternalPredicateQuantifier.firstInput operations value) :=
  RawInterpretation.compose meanings
    (RawInterpretation.inclusion meanings (source := product (language.power raw) (language.power raw))
      (target := language.power raw)
      (meanings.evaluate_product (power_read language meanings operations propositionRead valueRead)
        (power_read language meanings operations propositionRead valueRead))
      (power_read language meanings operations propositionRead valueRead)
      (powerConjunction_read language meanings operations propositionRead conjunctionRead valueRead)
      (RawInterpretation.first meanings (left := language.power raw) (right := language.power raw)
        (power_read language meanings operations propositionRead valueRead)
        (power_read language meanings operations propositionRead valueRead)))
    (RawInterpretation.first meanings (left := language.power raw) (right := language.power raw)
      (power_read language meanings operations propositionRead valueRead)
      (power_read language meanings operations propositionRead valueRead))

theorem larger_read
    (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
    (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)
    {raw : Object original} {value : D} (valueRead : RawInterpretation.ObjectReads meanings raw value) :
    RawInterpretation.Reads meanings (language.larger raw) (InternalPredicateQuantifier.secondInput operations value) :=
  RawInterpretation.compose meanings
    (RawInterpretation.inclusion meanings (source := product (language.power raw) (language.power raw))
      (target := language.power raw)
      (meanings.evaluate_product (power_read language meanings operations propositionRead valueRead)
        (power_read language meanings operations propositionRead valueRead))
      (power_read language meanings operations propositionRead valueRead)
      (powerConjunction_read language meanings operations propositionRead conjunctionRead valueRead)
      (RawInterpretation.first meanings (left := language.power raw) (right := language.power raw)
        (power_read language meanings operations propositionRead valueRead)
        (power_read language meanings operations propositionRead valueRead)))
    (RawInterpretation.second meanings (left := language.power raw) (right := language.power raw)
      (power_read language meanings operations propositionRead valueRead)
      (power_read language meanings operations propositionRead valueRead))

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Readout
