import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderContextInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderTensorRecovery

/-!
# Complete firing-word correspondence of shared first-order execution

The generic contextual implementation retains every original first-order
firing, including through transported continuations. Existing separated runs
supply its local checks. The resulting native run equals the independent
construction obtained from the established tensor theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport Separated)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

theorem sites_moveRun : ∀ {left right : Configuration T O} (iso : (firstOrderTransport A label).Iso left right)
    (run : (firstOrder A label).toStep.Run left),
    sites A label ((firstOrderTransport A label).moveRun iso run) = sites A label run
  | _, _, _, .nil _ => rfl
  | _, _, iso, .cons f allowed rest => by
      change f :: sites A label ((firstOrderTransport A label).moveRun
        ((firstOrderTransport A label).result_move iso f allowed) rest) = f :: sites A label rest
      rw [sites_moveRun _ rest]

theorem plan_sites : ∀ {left right : Configuration T O}
    (place : (contextualRunInterpretation A label).Place left right) (run : (firstOrder A label).toStep.Run left)
    (plan : (contextualRunInterpretation A label).Plan (right := right) place run),
    sites A label (plan.realize (contextualRunInterpretation A label) place run).execution = sites A label run
  | _, _, _, .nil _, .nil _ => rfl
  | _, _, place, .cons f allowed rest, .cons framed nativeAllowed tail => by
      let later := tail.realize (contextualRunInterpretation A label) PUnit.unit rest
      let iso := (contextualRunInterpretation A label).resultIso place f allowed framed nativeAllowed
      change f :: sites A label ((firstOrderTransport A label).moveRun
        ((firstOrderTransport A label).symm iso) later.execution) = f :: sites A label rest
      rw [sites_moveRun, plan_sites PUnit.unit rest tail]

theorem tensor_sites {left right : Configuration T O}
    {first : (firstOrder A label).toStep.Run left} {second : (firstOrder A label).toStep.Run right}
    (plan : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second) :
    sites A label (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution =
      sites A label first ++ sites A label second := by
  let I := contextualRunInterpretation A label
  let flip := contextualFlip A label
  let one := plan.leftPlan.realize I PUnit.unit first
  let two := plan.rightPlan.realize I (flip.swap one.target) second
  let bridge := (firstOrderTransport A label).trans (flip.stateIso one.target)
    ((firstOrderTransport A label).symm one.resultIso)
  change sites A label (one.execution.append ((firstOrderTransport A label).moveRun bridge two.execution)) = _
  rw [sites_append, sites_moveRun, plan_sites, plan_sites]

def planOfSeparated : ∀ {left right : Configuration T O} (run : (firstOrder A label).toStep.Run left)
    (other : List (Firing T S O)), Separated A label left (sites A label run) right other →
      (contextualRunInterpretation A label).Plan (right := right) PUnit.unit run
  | _, _, .nil _, _, _ => .nil _
  | _, right, .cons _f _allowed rest, other, separated =>
      .cons (I := contextualRunInterpretation A label) (right := right) (place := PUnit.unit)
        (separated.head_left_apart A label) separated.head_left_valid
        (planOfSeparated rest other separated.tail_left)

def tensorOfSeparated {left right : Configuration T O}
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right)
    (separated : Separated A label left (sites A label first) right (sites A label second)) :
    (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second := by
  let one := planOfSeparated A label first (sites A label second) separated
  have remaining : Separated A label first.last [] right (sites A label second) := by
    rw [last_eq_follow]
    apply AnnotatedRuns.Separated.drop_left (sites A label first)
    simpa only [List.append_nil] using separated
  exact ⟨one, planOfSeparated A label second [] remaining.symm⟩

theorem recovers_existing_tensor {left right : Configuration T O}
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right)
    (separated : Separated A label left (sites A label first) right (sites A label second)) :
    ((tensorOfSeparated A label first second separated).realize (contextualRunInterpretation A label)
      (contextualFlip A label)).execution =
        (tensor_of_separated A label left right (sites A label first) (sites A label second) separated).execution := by
  apply sites_injective A label
  exact (tensor_sites A label _).trans (TensorExecution.word _).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
