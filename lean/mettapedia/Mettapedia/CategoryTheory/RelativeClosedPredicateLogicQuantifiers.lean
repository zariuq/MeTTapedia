import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicFunctionReadout
import Mettapedia.CategoryTheory.InternalPredicateExistential

/-!
# The generated predicate presentation earns its quantifier adjunctions

Each authored ordered-function equalizer is compared with the actual
chosen ordered-function object. The comparison reads both complete input
functions. Its local diagram and the independently declared unit/counit
then earn universal and existential Galois connections in every generated
parameter context. Quantifier indices remain actual arrows of the declared
base; this does not introduce indices for all newly generated arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C]

abbrev functionOperations (value : C) :=
  InternalPredicateFunctionObject.operations (operations (C := C)) (valueObject value)

def orderedFunctionIsLimit (value : C) :
    IsLimit (Fork.ofι
      (inclusion.functor.map (classOf (RawHom.inclusion (powerConjunctionRaw value)
        (RawHom.first (power value) (power value)))))
      (by
        exact (congrArg
          (fun arrow => inclusion.functor.map
            (classOf (RawHom.inclusion (powerConjunctionRaw value)
              (RawHom.first (power value) (power value)))) ≫ arrow)
          (powerConjunction_readout value)).symm.trans
            (PresentedEqualizer.condition (inclusion.rawArrow (powerConjunctionRaw value))
              (inclusion.rawArrow (RawHom.first (power value) (power value))))) :
      Fork (functionOperations value).conjunction
        (fst (functionObject value) (functionObject value))) := by
  let before := inclusion.rawArrow (powerConjunctionRaw value)
  let after := inclusion.rawArrow (RawHom.first (power value) (power value))
  have condition (cone : Fork (functionOperations value).conjunction
      (fst (functionObject value) (functionObject value))) :
      cone.ι ≫ classOf before = cone.ι ≫ classOf after :=
    (congrArg (cone.ι ≫ ·) (powerConjunction_readout value)).trans cone.condition
  refine Fork.IsLimit.mk _
    (fun cone => PresentedEqualizer.lift before after cone.ι (condition cone)) ?_ ?_
  · intro cone
    exact PresentedEqualizer.lift_inclusion before after cone.ι (condition cone)
  · intro cone candidate factors
    apply PresentedEqualizer.joint_cancel before after
    exact factors.trans (PresentedEqualizer.lift_inclusion before after cone.ι (condition cone)).symm

def orderedFunctionComparison (value : C) :
    inclusion.object (orderedFunctions value) ≅
      InternalPredicateQuantifier.orderedPairs (operations (C := C)) (valueObject value) :=
  (orderedFunctionIsLimit value).conePointUniqueUpToIso (limit.isLimit _)

theorem orderedFunctionComparison_inclusion (value : C) :
    (orderedFunctionComparison value).inv ≫
      inclusion.functor.map (classOf (RawHom.inclusion (powerConjunctionRaw value)
        (RawHom.first (power value) (power value)))) =
      InternalPredicateQuantifier.orderInclusion (operations (C := C)) (valueObject value) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (orderedFunctionIsLimit value)
    (limit.isLimit _) WalkingParallelPair.zero

theorem orderedFunctionComparison_first (value : C) :
    (orderedFunctionComparison value).inv ≫ inclusion.functor.map (classOf (smallerFunctionRaw value)) =
      InternalPredicateQuantifier.firstInput (operations (C := C)) (valueObject value) := by
  change (orderedFunctionComparison value).inv ≫ inclusion.functor.map
      (classOf (RawHom.inclusion (powerConjunctionRaw value) (RawHom.first (power value) (power value)))) ≫
      first (functionObject value) (functionObject value) = _
  rw [← Category.assoc, orderedFunctionComparison_inclusion]
  rfl

theorem orderedFunctionComparison_second (value : C) :
    (orderedFunctionComparison value).inv ≫ inclusion.functor.map (classOf (largerFunctionRaw value)) =
      InternalPredicateQuantifier.secondInput (operations (C := C)) (valueObject value) := by
  change (orderedFunctionComparison value).inv ≫ inclusion.functor.map
      (classOf (RawHom.inclusion (powerConjunctionRaw value) (RawHom.first (power value) (power value)))) ≫
      second (functionObject value) (functionObject value) = _
  rw [← Category.assoc, orderedFunctionComparison_inclusion]
  rfl

theorem monotonicity_comparison {source target : C}
    (operation : functionObject source ⟶ functionObject target)
    (localDiagram : (functionOperations target).meet
      (inclusion.functor.map (classOf (largerFunctionRaw source)) ≫ operation)
      (inclusion.functor.map (classOf (smallerFunctionRaw source)) ≫ operation) =
      inclusion.functor.map (classOf (smallerFunctionRaw source)) ≫ operation) :
    InternalPredicateQuantifier.Monotonicity (operations (C := C)) operation where
  ordered := by
    let incoming := (orderedFunctionComparison source).inv
    have natural := (functionOperations target).reindex_meet incoming
      (inclusion.functor.map (classOf (largerFunctionRaw source)) ≫ operation)
      (inclusion.functor.map (classOf (smallerFunctionRaw source)) ≫ operation)
    have complete := natural.symm.trans (congrArg (fun arrow => incoming ≫ arrow) localDiagram)
    simpa only [InternalConjunctiveObject.Operations.reindex, ← Category.assoc,
      incoming, orderedFunctionComparison_first, orderedFunctionComparison_second] using complete

def universalQualification {source target : C} (route : source ⟶ target) :
    InternalPredicateQuantifier.Universal (operations (C := C))
      ((baseFunctor (lawfulSignature (C := C))).map route) where
  operation := inclusion.functor.map (classOf (universalRaw route))
  monotonicity := monotonicity_comparison _ (by
    have complete := (powerMeet_readout target
      ((largerFunctionRaw source).compose (universalRaw route))
      ((smallerFunctionRaw source).compose (universalRaw route))).symm.trans
        (declared_law (Law.universalMonotonicity route))
    exact complete)
  unit := by
    have complete := (powerMeet_readout target
      ((precompositionRaw route).compose (universalRaw route))
      (RawHom.identity (power target))).symm.trans (declared_law (Law.universalUnit route))
    change (functionOperations target).meet
      (inclusion.functor.map (classOf (precompositionRaw route)) ≫
        inclusion.functor.map (classOf (universalRaw route))) (𝟙 (functionObject target)) = 𝟙 _ at complete
    rw [precomposition_readout] at complete
    exact complete
  counit := by
    have complete := (powerMeet_readout source (RawHom.identity (power source))
      ((universalRaw route).compose (precompositionRaw route))).symm.trans
        (declared_law (Law.universalCounit route))
    change (functionOperations source).meet (𝟙 (functionObject source))
      (inclusion.functor.map (classOf (universalRaw route)) ≫
        inclusion.functor.map (classOf (precompositionRaw route))) =
      inclusion.functor.map (classOf (universalRaw route)) ≫
        inclusion.functor.map (classOf (precompositionRaw route)) at complete
    rw [precomposition_readout] at complete
    exact complete

def existentialQualification {source target : C} (route : source ⟶ target) :
    InternalPredicateExistential.Existential (operations (C := C))
      ((baseFunctor (lawfulSignature (C := C))).map route) where
  operation := inclusion.functor.map (classOf (existentialRaw route))
  monotonicity := monotonicity_comparison _ (by
    have complete := (powerMeet_readout target
      ((largerFunctionRaw source).compose (existentialRaw route))
      ((smallerFunctionRaw source).compose (existentialRaw route))).symm.trans
        (declared_law (Law.existentialMonotonicity route))
    exact complete)
  unit := by
    have complete := (powerMeet_readout source
      ((existentialRaw route).compose (precompositionRaw route))
      (RawHom.identity (power source))).symm.trans (declared_law (Law.existentialUnit route))
    change (functionOperations source).meet
      (inclusion.functor.map (classOf (existentialRaw route)) ≫
        inclusion.functor.map (classOf (precompositionRaw route))) (𝟙 (functionObject source)) = 𝟙 _ at complete
    rw [precomposition_readout] at complete
    exact complete
  counit := by
    have complete := (powerMeet_readout target (RawHom.identity (power target))
      ((precompositionRaw route).compose (existentialRaw route))).symm.trans
        (declared_law (Law.existentialCounit route))
    change (functionOperations target).meet (𝟙 (functionObject target))
      (inclusion.functor.map (classOf (precompositionRaw route)) ≫
        inclusion.functor.map (classOf (existentialRaw route))) =
      inclusion.functor.map (classOf (precompositionRaw route)) ≫
        inclusion.functor.map (classOf (existentialRaw route)) at complete
    rw [precomposition_readout] at complete
    exact complete

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations
