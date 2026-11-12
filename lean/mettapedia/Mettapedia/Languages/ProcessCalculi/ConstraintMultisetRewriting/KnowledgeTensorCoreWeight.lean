import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreInterchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreGrade
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Opposite

/-!
# Weights of runs: one functor, tensors as products, interchange as commutativity

Give every firing a weight in a monoid. The weight of a run is the product of the weights of its
firings, in order: the step's own `account`. Positive weights need nothing else.

* `weightFunctor`, `weightFunctor_run`, `weightFunctor_unique`: the weight is the functor from the
  free category of runs to the monoid, seen as a category with one object, that extends the
  weights of single events, and it is the only one. This is the weighted twin of
  `gradeFunctor_unique`: the grade is a functor into partial maps of placements, the weight a
  functor into a monoid.
* `account_map`: a monoid map carries the weight of every run to the weight under the composite
  weights. With the free commutative monoid or the provenance polynomials as the source, every
  weight in a commutative semiring is the image of one universal weight.
* `account_of_places`, `tensor_weight`: when weights respect the transport and placement keeps
  the weight of a firing, a placed run weighs what the local run weighs, and the tensor of two runs
  weighs the product of their weights.
* `interchange_weights`: the two sides of the interchange law weigh `(a * b) * (c * d)` and
  `(a * c) * (b * d)`; in a commutative monoid they agree. So weights see interchange only
  through commutativity, and a commutative weight cannot see where interchange fails.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI uP uM uN

/-! ## The weight is the unique functor fixed by the weights of events -/

section Functor

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Step X O State Firing)
  {M : Type uM} [Monoid M] (weight : (t : State) → Firing t → M)

/-- The generators of the weight: every state goes to the one object, an event to the weight of
its firing. The opposite monoid makes composition of runs read in execution order. -/
def weightGenerators :
    EffectCore.EventObject P.effectCore P.eventAdmission ⥤q SingleObj Mᵐᵒᵖ where
  obj _ := SingleObj.star Mᵐᵒᵖ
  map {s _} event := MulOpposite.op (weight s event.firing)

/-- **The weight functor**: the extension of the event weights to the free category of runs. -/
def weightFunctor : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ SingleObj Mᵐᵒᵖ :=
  P.effectCore.interpret P.eventAdmission (weightGenerators P weight)

/-- **The weight functor computes the account**: on a run it is the product of the weights of its
firings, in order. -/
theorem weightFunctor_run : ∀ {s : State} (run : P.Run s),
    (weightFunctor P weight).map (run.eventPath P) = MulOpposite.op (run.account weight)
  | _, .nil _ => rfl
  | s, .cons f allowed rest => by
      have split := (weightFunctor P weight).map_comp
        (X := (s : EffectCore.RunCategory P.effectCore P.eventAdmission))
        (Quiver.Hom.toPath (P.event f allowed)) (rest.eventPath P)
      have single : (weightFunctor P weight).map (Quiver.Hom.toPath (P.event f allowed)) =
          (weightGenerators P weight).map (P.event f allowed) :=
        Paths.lift_toPath (weightGenerators P weight) (P.event f allowed)
      rw [single, weightFunctor_run rest, SingleObj.comp_as_mul] at split
      have path : (Step.Run.cons f allowed rest).eventPath P =
          (Quiver.Hom.toPath (P.event f allowed)).comp (rest.eventPath P) := rfl
      rw [path]
      refine split.trans ?_
      show MulOpposite.op (rest.account weight) * MulOpposite.op (weight s f) =
        MulOpposite.op (weight s f * rest.account weight)
      rw [MulOpposite.op_mul]

/-- **The weight functor is the only functor with the weights of single events.** -/
theorem weightFunctor_unique
    (other : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ SingleObj Mᵐᵒᵖ)
    (agrees : Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q
      other.toPrefunctor = weightGenerators P weight) :
    other = weightFunctor P weight :=
  Paths.lift_unique (weightGenerators P weight) other agrees

/-- Every functor that agrees with the weights of events computes the account of every run. -/
theorem map_run_of_agrees
    (other : EffectCore.RunCategory P.effectCore P.eventAdmission ⥤ SingleObj Mᵐᵒᵖ)
    (agrees : Paths.of (EffectCore.EventObject P.effectCore P.eventAdmission) ⋙q
      other.toPrefunctor = weightGenerators P weight)
    {s : State} (run : P.Run s) :
    other.map (run.eventPath P) = MulOpposite.op (run.account weight) := by
  rw [weightFunctor_unique P weight other agrees]
  exact weightFunctor_run P weight run

variable {P}

/-- **Weights move along monoid maps.** -/
theorem account_map {N : Type uN} [Monoid N] (φ : M →* N) :
    ∀ {s : State} (run : P.Run s), φ (run.account weight) = run.account (fun t f => φ (weight t f))
  | _, .nil _ => φ.map_one
  | _, .cons f _ rest => by
      show φ (weight _ f * rest.account weight) = φ (weight _ f) * rest.account _
      rw [φ.map_mul, account_map φ rest]

end Functor

/-! ## Tensors weigh the product of their parts -/

section Tensor

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)
  {M : Type uM} [Monoid M] (weight : (t : State) → Firing t → M)

/-- **Weights respect the transport**: a moved firing weighs what the firing weighs, and alike
firings weigh the same. -/
structure RespectsTransport (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P) : Prop where
  move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s), weight t (T.move i f) = weight s f
  alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → weight s f = weight s f'

/-- **Placement keeps weights**: the placed candidate of a firing weighs what the firing weighs. -/
def KeepsWeights : Prop :=
  ∀ {left right : State} (place : I.Place left right) (f : Firing left),
    weight (I.pair place).state (I.candidate place f) = weight left f

variable {weight}

/-- A run carried along an isomorphism weighs what it weighed. -/
theorem account_moveRun (respects : RespectsTransport weight T) :
    ∀ {s t : State} (i : T.Iso s t) (run : P.Run s), (T.moveRun i run).account weight = run.account weight
  | _, _, _, .nil _ => rfl
  | _, _, i, .cons f admitted rest => by
      show weight _ (T.move i f) * (T.moveRun (T.result_move i f admitted) rest).account weight =
        weight _ f * rest.account weight
      rw [respects.move i f, account_moveRun respects _ rest]

/-- **Similar runs weigh the same.** -/
theorem account_of_similar (respects : RespectsTransport weight T) :
    ∀ {s t : State} {one : P.Run s} {two : P.Run t}, T.Similar one two →
      one.account weight = two.account weight
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .cons f _ rest, .cons f' _ rest', similar => by
      obtain ⟨i, moved, tail⟩ := Transport.similar_cons_cons.mp similar
      show weight _ f * rest.account weight = weight _ f' * rest'.account weight
      rw [← respects.move i f, respects.alike moved, account_of_similar respects tail]
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

/-- **A placed run weighs what the local run weighs.** -/
theorem account_of_places (respects : RespectsTransport weight T) (keeps : KeepsWeights I weight) :
    ∀ {left right : State} {place : I.Place left right} {run : P.Run left}
      {native : P.Run (I.pair place).state}, Places I place run native →
        native.account weight = run.account weight
  | _, _, _, _, _, .nil _ => rfl
  | _, _, place, .cons f _ _, _, .cons (moved := moved) _ _ tail similar => by
      show weight _ (I.candidate place f) * moved.account weight = weight _ f * _
      rw [keeps place f, ← account_of_similar respects similar, account_of_places respects keeps tail]

/-- The realization of a plan weighs what its local run weighs. -/
theorem account_realize (respects : RespectsTransport weight T) (keeps : KeepsWeights I weight)
    {left right : State} (place : I.Place left right) (run : P.Run left) (plan : I.Plan place run) :
    (plan.realize I place run).execution.account weight = run.account weight :=
  account_of_places I respects keeps (realize_places I place run plan)

/-- **The tensor of two runs weighs the product of their weights.** -/
theorem tensor_weight (respects : RespectsTransport weight T) (keeps : KeepsWeights I weight)
    (flip : I.Flip) {left right : State} {place : I.Place left right}
    {first : P.Run left} {second : P.Run right} (plan : I.TensorPlan flip place first second) :
    (plan.realize I flip).execution.account weight = first.account weight * second.account weight := by
  rw [tensor_execution I flip plan, Step.Run.account_append, account_realize I respects keeps,
    account_moveRun respects, account_realize I respects keeps]

/-- **The two sides of the interchange law**: the cut of two tensors weighs `(a * b) * (c * d)` and
the tensor of the two cuts weighs `(a * c) * (b * d)`. -/
theorem interchange_sides_weights (respects : RespectsTransport weight T)
    (keeps : KeepsWeights I weight) (flip : I.Flip) {left right : State} {place : I.Place left right}
    {first : P.Run left} {second : P.Run right} {afterFirst : P.Run first.last}
    {afterSecond : P.Run second.last} (before : I.TensorPlan flip place first second)
    (after : I.TensorPlan flip (before.realize I flip).target afterFirst afterSecond)
    (whole : I.TensorPlan flip place (first.append afterFirst) (second.append afterSecond)) :
    (cutOfTensors I flip before after).account weight =
        (first.account weight * second.account weight) *
          (afterFirst.account weight * afterSecond.account weight) ∧
      (whole.realize I flip).execution.account weight =
        (first.account weight * afterFirst.account weight) *
          (second.account weight * afterSecond.account weight) := by
  refine ⟨?_, ?_⟩
  · show ((before.realize I flip).execution.append
        (T.moveRun (T.symm (before.realize I flip).resultIso) (after.realize I flip).execution)).account
          weight = _
    rw [Step.Run.account_append, account_moveRun respects, tensor_weight I respects keeps flip before,
      tensor_weight I respects keeps flip after]
  · rw [tensor_weight I respects keeps flip whole, Step.Run.account_append, Step.Run.account_append]

/-- **Interchange is commutativity.** In a commutative monoid the two sides of the interchange
law weigh the same, whether or not they are one trace. -/
theorem interchange_weights {M : Type uM} [CommMonoid M] {weight : (t : State) → Firing t → M}
    (respects : RespectsTransport weight T) (keeps : KeepsWeights I weight) (flip : I.Flip)
    {left right : State} {place : I.Place left right}
    {first : P.Run left} {second : P.Run right} {afterFirst : P.Run first.last}
    {afterSecond : P.Run second.last} (before : I.TensorPlan flip place first second)
    (after : I.TensorPlan flip (before.realize I flip).target afterFirst afterSecond)
    (whole : I.TensorPlan flip place (first.append afterFirst) (second.append afterSecond)) :
    (cutOfTensors I flip before after).account weight =
      (whole.realize I flip).execution.account weight := by
  obtain ⟨cut, tensor⟩ := interchange_sides_weights I respects keeps flip before after whole
  rw [cut, tensor, mul_mul_mul_comm]

end Tensor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
