import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierPresentation
import Mettapedia.CategoryTheory.InternalPredicateExistential
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapNormalization

/-!
# Predicate functions in the actual generated source category

The proposition, truth and conjunction retain their authored raw objects
and arrows. Pointwise function conjunction and precomposition are compared
with the source category's actual exponential adjunction, including its
argument exchange. The authored ordered-function equalizer is compared
with the chosen semantic equalizer through its universal property. No
literal identification of the two object presentations is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {original : Signature (C := C) (symbols := symbols)}
variable (language : PredicateSyntax original)
variable (truth : RawHom (terminal original) language.proposition)

def operations : InternalConjunctiveObject.Operations (Object original) where
  proposition := language.proposition
  truth := classOf truth
  conjunction := classOf language.conjunction

abbrev functions (value : Object original) :=
  InternalPredicateFunctionObject.operations (operations language truth) value

theorem cartesian_pairing {context first second : Object original}
    (before : context ⟶ first) (after : context ⟶ second) :
    lift before after = pairing before after := by
  apply product_joint_cancel
  · exact (lift_fst before after).trans (pairing_first before after).symm
  · exact (lift_snd before after).trans (pairing_second before after).symm

theorem abstraction_read {context argument result : Object original}
    (body : product context argument ⟶ result) :
    MonoidalClosed.uncurry (abstraction body) = (exchange context argument).inv ≫ body := by
  rw [monoidal_uncurry, unabstract_abstraction]

theorem powerConjunction_read (value : Object original) :
    classOf (language.powerConjunction value) = (functions language truth value).conjunction := by
  let before : product (language.power value) (language.power value) ⟶ language.power value := fst _ _
  let after : product (language.power value) (language.power value) ⟶ language.power value := snd _ _
  have authored : classOf (language.powerConjunction value) =
      abstraction ((operations language truth).meet (unabstract before) (unabstract after)) := by
    change abstraction (pairing (unabstract before) (unabstract after) ≫ classOf language.conjunction) = _
    unfold InternalConjunctiveObject.Operations.meet
    rw [cartesian_pairing]
    rfl
  rw [authored]
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (abstraction ((operations language truth).meet (unabstract before) (unabstract after))) =
    MonoidalClosed.uncurry (MonoidalClosed.curry
      ((operations language truth).meet (MonoidalClosed.uncurry before) (MonoidalClosed.uncurry after)))
  rw [abstraction_read, uncurry_curry]
  have natural := (operations language truth).reindex_meet
    (exchange (product (language.power value) (language.power value)) value).inv
    (unabstract before) (unabstract after)
  exact natural.trans (congrArg₂ (operations language truth).meet
    (monoidal_uncurry before).symm (monoidal_uncurry after).symm)

theorem powerMeet_read {context : Object original} (value : Object original)
    (before after : RawHom context (language.power value)) :
    classOf (language.powerMeet value before after) =
      (functions language truth value).meet (classOf before) (classOf after) := by
  change pairing (classOf before) (classOf after) ≫ classOf (language.powerConjunction value) = _
  rw [powerConjunction_read]
  unfold InternalConjunctiveObject.Operations.meet
  rw [cartesian_pairing]

theorem precomposition_read (route : Route original) :
    classOf (language.precomposition route) =
      InternalPredicateQuantifier.precomposition (operations language truth) (classOf route.arrow) := by
  let actual : route.source ⟶ route.target := classOf route.arrow
  let context := language.power route.target
  have authored : classOf (language.precomposition route) =
      abstraction (pairing (first context route.source) (second context route.source ≫ actual) ≫
        evaluation route.target language.proposition) := rfl
  rw [authored]
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry (abstraction _) =
    MonoidalClosed.uncurry (MonoidalClosed.curry
      ((actual ▷ context) ≫ (ihom.ev route.target).app language.proposition))
  rw [abstraction_read, uncurry_curry, SignatureMap.monoidal_left_evaluation]
  have complete : (exchange context route.source).inv ≫
      pairing (first context route.source) (second context route.source ≫ actual) =
      (actual ▷ context) ≫ (exchange context route.target).inv := by
    apply product_joint_cancel
    · simp only [Category.assoc, pairing_first, exchange]
      exact (CartesianMonoidalCategory.whiskerRight_snd actual context).symm
    · simp only [Category.assoc, pairing_second, exchange]
      rw [← Category.assoc, pairing_second]
      exact (CartesianMonoidalCategory.whiskerRight_fst actual context).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ evaluation route.target language.proposition) complete).trans (Category.assoc _ _ _))

def orderedFunctionIsLimit (value : Object original) :
    IsLimit (Fork.ofι
      (classOf (RawHom.inclusion (language.powerConjunction value)
        (RawHom.first (language.power value) (language.power value))))
      (by
        change PresentedEqualizer.inclusion (language.powerConjunction value)
          (RawHom.first (language.power value) (language.power value)) ≫
            (functions language truth value).conjunction = _
        rw [← powerConjunction_read]
        exact PresentedEqualizer.condition (language.powerConjunction value)
          (RawHom.first (language.power value) (language.power value))) :
      Fork (functions language truth value).conjunction
        (fst (language.power value) (language.power value))) := by
  let before := language.powerConjunction value
  let after := RawHom.first (language.power value) (language.power value)
  have condition (cone : Fork (functions language truth value).conjunction
      (fst (language.power value) (language.power value))) :
      cone.ι ≫ classOf before = cone.ι ≫ classOf after :=
    (congrArg (cone.ι ≫ ·) (powerConjunction_read language truth value)).trans cone.condition
  refine Fork.IsLimit.mk _
    (fun cone => PresentedEqualizer.lift before after cone.ι (condition cone)) ?_ ?_
  · intro cone
    exact PresentedEqualizer.lift_inclusion before after cone.ι (condition cone)
  · intro cone candidate factors
    apply PresentedEqualizer.joint_cancel before after
    exact factors.trans (PresentedEqualizer.lift_inclusion before after cone.ι (condition cone)).symm

def orderedFunctionComparison (value : Object original) :
    language.orderedFunctions value ≅
      InternalPredicateQuantifier.orderedPairs (operations language truth) value :=
  (orderedFunctionIsLimit language truth value).conePointUniqueUpToIso (limit.isLimit _)

theorem orderedFunctionComparison_inclusion (value : Object original) :
    (orderedFunctionComparison language truth value).inv ≫
      classOf (RawHom.inclusion (language.powerConjunction value)
        (RawHom.first (language.power value) (language.power value))) =
      InternalPredicateQuantifier.orderInclusion (operations language truth) value :=
  IsLimit.conePointUniqueUpToIso_inv_comp (orderedFunctionIsLimit language truth value)
    (limit.isLimit _) WalkingParallelPair.zero

theorem orderedFunctionComparison_first (value : Object original) :
    (orderedFunctionComparison language truth value).inv ≫ classOf (language.smaller value) =
      InternalPredicateQuantifier.firstInput (operations language truth) value := by
  change (orderedFunctionComparison language truth value).inv ≫
    classOf (RawHom.inclusion (language.powerConjunction value)
      (RawHom.first (language.power value) (language.power value))) ≫
      first (language.power value) (language.power value) = _
  rw [← Category.assoc, orderedFunctionComparison_inclusion]
  rfl

theorem orderedFunctionComparison_second (value : Object original) :
    (orderedFunctionComparison language truth value).inv ≫ classOf (language.larger value) =
      InternalPredicateQuantifier.secondInput (operations language truth) value := by
  change (orderedFunctionComparison language truth value).inv ≫
    classOf (RawHom.inclusion (language.powerConjunction value)
      (RawHom.first (language.power value) (language.power value))) ≫
      second (language.power value) (language.power value) = _
  rw [← Category.assoc, orderedFunctionComparison_inclusion]
  rfl

theorem monotonicity_comparison {source target : Object original}
    (operation : language.power source ⟶ language.power target)
    (localDiagram : (functions language truth target).meet
      (classOf (language.larger source) ≫ operation)
      (classOf (language.smaller source) ≫ operation) =
      classOf (language.smaller source) ≫ operation) :
    InternalPredicateQuantifier.Monotonicity (operations language truth) operation where
  ordered := by
    let incoming := (orderedFunctionComparison language truth source).inv
    have natural := (functions language truth target).reindex_meet incoming
      (classOf (language.larger source) ≫ operation) (classOf (language.smaller source) ≫ operation)
    have complete := natural.symm.trans (congrArg (fun arrow => incoming ≫ arrow) localDiagram)
    simpa only [InternalConjunctiveObject.Operations.reindex, ← Category.assoc,
      incoming, orderedFunctionComparison_first, orderedFunctionComparison_second] using complete

variable {nextSymbols : Symbols.{k}}
variable {next : Signature (C := C) (symbols := nextSymbols)}

/-- Each of the four finite conjunctive laws survives an actual generated
signature map. The complete truth and conjunction arrows are retained. -/
theorem translated_laws (mapping : SignatureMap original next)
    (laws : (operations language truth).Laws) :
    (operations (language.translate mapping) (mapping.rawArrow truth)).Laws where
  commutativity := by
    have complete := congrArg mapping.functor.map laws.commutativity
    simp only [InternalConjunctiveObject.Operations.swapBody, mapping.functor.map_comp,
      mapping.functor_lift] at complete
    exact complete
  associativity := by
    have complete := congrArg mapping.functor.map laws.associativity
    simp only [InternalConjunctiveObject.Operations.associateLeft,
      InternalConjunctiveObject.Operations.associateRight, mapping.functor.map_comp,
      mapping.functor_lift] at complete
    exact complete
  idempotence := by
    have complete := congrArg mapping.functor.map laws.idempotence
    simp only [InternalConjunctiveObject.Operations.diagonalBody, mapping.functor.map_comp,
      mapping.functor.map_id, mapping.functor_lift] at complete
    exact complete
  truthUnit := by
    have complete := congrArg mapping.functor.map laws.truthUnit
    simp only [InternalConjunctiveObject.Operations.truthUnitBody, mapping.functor.map_comp,
      mapping.functor.map_id, mapping.functor_lift, mapping.functor_toUnit] at complete
    exact complete

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations
