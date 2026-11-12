import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderRoundTrace

/-!
# Four-block coherence of the native first-order tensor

The sequential composite of two actual tensor executions agrees in the native
trace quotient with the tensor of the local sequential composites. The
established separation theorem supplies the squares, and the complete-word
bridge places its interchange in the shared native run category.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport Separated)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

def sequentialTensor {left right : Configuration T O}
    {first : (firstOrder A label).toStep.Run left} {second : (firstOrder A label).toStep.Run right}
    {afterFirst : (firstOrder A label).toStep.Run first.last} {afterSecond : (firstOrder A label).toStep.Run second.last}
    (before : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second)
    (after : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit afterFirst afterSecond) :
    (firstOrder A label).toStep.Run (AnnotatedRuns.tensor left right) :=
  let one := before.realize (contextualRunInterpretation A label) (contextualFlip A label)
  let two := after.realize (contextualRunInterpretation A label) (contextualFlip A label)
  one.execution.append ((firstOrderTransport A label).moveRun
    ((firstOrderTransport A label).symm one.resultIso) two.execution)

theorem sites_sequentialTensor {left right : Configuration T O}
    {first : (firstOrder A label).toStep.Run left} {second : (firstOrder A label).toStep.Run right}
    {afterFirst : (firstOrder A label).toStep.Run first.last} {afterSecond : (firstOrder A label).toStep.Run second.last}
    (before : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second)
    (after : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit afterFirst afterSecond) :
    sites A label (sequentialTensor A label before after) =
      (sites A label first ++ sites A label second) ++ (sites A label afterFirst ++ sites A label afterSecond) := by
  rw [sequentialTensor, sites_append, sites_moveRun, tensor_sites, tensor_sites]

theorem four_block {left right : Configuration T O}
    {first : (firstOrder A label).toStep.Run left} {second : (firstOrder A label).toStep.Run right}
    {afterFirst : (firstOrder A label).toStep.Run first.last} {afterSecond : (firstOrder A label).toStep.Run second.last}
    (before : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second)
    (after : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit afterFirst afterSecond)
    (whole : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
      (first.append afterFirst) (second.append afterSecond))
    (separated : Separated A label left (sites A label (first.append afterFirst))
      right (sites A label (second.append afterSecond))) :
    (firstOrderTransport A label).TraceEquiv (AnnotatedRuns.tensor left right)
      (sequentialTensor A label before after)
      (whole.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution := by
  apply (native_trace_iff_word_trace A label _ _).mpr
  rw [sites_sequentialTensor, tensor_sites, sites_append, sites_append]
  apply round_trace_word A label
  apply AnnotatedRuns.interchange_law A label left right
  simpa only [sites_append] using separated

structure FourBlock {left right : Configuration T O}
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right)
    (afterFirst : (firstOrder A label).toStep.Run first.last) (afterSecond : (firstOrder A label).toStep.Run second.last) where
  before : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit first second
  after : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit afterFirst afterSecond
  whole : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
    (first.append afterFirst) (second.append afterSecond)
  interchange : (firstOrderTransport A label).TraceEquiv (AnnotatedRuns.tensor left right)
    (sequentialTensor A label before after)
    (whole.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution

def fourBlockOfSeparated {left right : Configuration T O}
    (first : (firstOrder A label).toStep.Run left) (second : (firstOrder A label).toStep.Run right)
    (afterFirst : (firstOrder A label).toStep.Run first.last) (afterSecond : (firstOrder A label).toStep.Run second.last)
    (separated : Separated A label left (sites A label (first.append afterFirst))
      right (sites A label (second.append afterSecond))) : FourBlock A label first second afterFirst afterSecond := by
  have expanded : Separated A label left (sites A label first ++ sites A label afterFirst)
      right (sites A label second ++ sites A label afterSecond) := by
    simpa only [sites_append] using separated
  have before : Separated A label left (sites A label first) right (sites A label second) :=
    expanded.take_left.take_right
  have after : Separated A label first.last (sites A label afterFirst) second.last (sites A label afterSecond) := by
    have one := AnnotatedRuns.Separated.drop_left (sites A label first) expanded
    have two := (AnnotatedRuns.Separated.drop_left (sites A label second) one.symm).symm
    simpa only [← last_eq_follow A label first, ← last_eq_follow A label second] using two
  let beforePlan := tensorOfSeparated A label first second before
  let afterPlan := tensorOfSeparated A label afterFirst afterSecond after
  let wholePlan := tensorOfSeparated A label (first.append afterFirst) (second.append afterSecond) separated
  exact ⟨beforePlan, afterPlan, wholePlan, four_block A label beforePlan afterPlan wholePlan separated⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
