import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchange

/-!
# The interchange law of proofs is the four-block law of runs

The tensor of two runs is the cut of two framed runs (`tensor_execution`). The interchange law
of proofs compares, for four runs, the cut of two tensors with the tensor of two cuts. On the
step this is a statement about two native runs from one placed state, and it is asked in the
trace quotient of the transport.

* `cutOfTensors`, `InterchangeAt`: the cut of two tensors, and the interchange law at four runs.
* `InterchangeAt.same_last`: the two sides end in one class of states.
* `FirstOrder.interchange_of_separated`: the first-order four-block law is the interchange law
  at four separated runs.
* `helper_interchange`: the four-block law of the binding-aware helper step is the interchange
  law at every four runs whose three tensors exist.

The interchange law is not a consequence of the three grades alone for every admission: the
controls file has two native runs that exchange a block of two firings with one counting firing
and are not one trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF uI uP

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T) (flip : I.Flip)

/-- The cut of two tensors of runs: the second tensor is run where the first one ends. -/
def cutOfTensors {left right : State} {place : I.Place left right} {first : P.Run left}
    {second : P.Run right} {afterFirst : P.Run first.last} {afterSecond : P.Run second.last}
    (before : I.TensorPlan flip place first second)
    (after : I.TensorPlan flip (before.realize I flip).target afterFirst afterSecond) :
    P.Run (I.pair place).state :=
  (before.realize I flip).execution.append
    (T.moveRun (T.symm (before.realize I flip).resultIso) (after.realize I flip).execution)

/-- **The interchange law of proofs at four runs**: the cut of two tensors and the tensor of the
two cuts are one trace. -/
def InterchangeAt {left right : State} {place : I.Place left right} {first : P.Run left}
    {second : P.Run right} {afterFirst : P.Run first.last} {afterSecond : P.Run second.last}
    (before : I.TensorPlan flip place first second)
    (after : I.TensorPlan flip (before.realize I flip).target afterFirst afterSecond)
    (whole : I.TensorPlan flip place (first.append afterFirst) (second.append afterSecond)) : Prop :=
  T.TraceEquiv (I.pair place).state (cutOfTensors I flip before after)
    (whole.realize I flip).execution

/-- Where the interchange law holds, its two sides end in one class of states. -/
theorem InterchangeAt.same_last {left right : State} {place : I.Place left right}
    {first : P.Run left} {second : P.Run right} {afterFirst : P.Run first.last}
    {afterSecond : P.Run second.last} {before : I.TensorPlan flip place first second}
    {after : I.TensorPlan flip (before.realize I flip).target afterFirst afterSecond}
    {whole : I.TensorPlan flip place (first.append afterFirst) (second.append afterSecond)}
    (law : InterchangeAt I flip before after whole) :
    T.Same (cutOfTensors I flip before after).last (whole.realize I flip).execution.last :=
  Transport.TraceEquiv.same_last law

end Generic

namespace FirstOrder

open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns

universe uTm uSub uOc
variable {T : Type uTm} {S : Type uSub} {O : Type uOc} [DecidableEq O]

/-- **The first-order four-block law is the interchange law of proofs**, at four separated
runs. -/
theorem interchange_of_separated (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} {first : (firstOrder A label).toStep.Run left}
    {second : (firstOrder A label).toStep.Run right}
    {afterFirst : (firstOrder A label).toStep.Run first.last}
    {afterSecond : (firstOrder A label).toStep.Run second.last}
    (before : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
      first second)
    (after : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label)
      (before.realize (contextualRunInterpretation A label) (contextualFlip A label)).target
      afterFirst afterSecond)
    (whole : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
      (first.append afterFirst) (second.append afterSecond))
    (separated : AnnotatedRuns.Separated A label left (sites A label (first.append afterFirst))
      right (sites A label (second.append afterSecond))) :
    InterchangeAt (contextualRunInterpretation A label) (contextualFlip A label) before after whole :=
  four_block A label before after whole separated

end FirstOrder

section Helper

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The four-block law of the binding-aware helper step is the interchange law of proofs**, at
every four runs whose three tensors exist. -/
theorem helper_interchange {left right : Helpers.State S O}
    {place : Helpers.ContextPlacement left right}
    {first : Helpers.helperStep.Run left} {second : Helpers.helperStep.Run right}
    {afterFirst : Helpers.helperStep.Run first.last}
    {afterSecond : Helpers.helperStep.Run second.last}
    (before : Helpers.TensorPlan place first second)
    (after : Helpers.TensorPlan (Helpers.TensorPlan.realize before).target afterFirst afterSecond)
    (whole : Helpers.TensorPlan place (first.append afterFirst) (second.append afterSecond)) :
    InterchangeAt Helpers.contextualRunInterpretation Helpers.contextualFlip before after whole :=
  Helpers.TensorPlan.four_block before after whole

end Helper

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
