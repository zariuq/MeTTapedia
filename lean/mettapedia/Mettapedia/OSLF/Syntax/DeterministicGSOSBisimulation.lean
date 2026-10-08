import Mettapedia.OSLF.Syntax.DeterministicGSOSCoalgebraMonad

/-!
# Direct constructor congruence from the actual coalgebra monad

A bisimulation is an actual span of coalgebra morphisms. The maximal
relation of such witnesses is itself represented by a coalgebra span.
Lifting that span through the earned free monad, then composing with the
actual coalgebra-compatible multiplication, proves preservation by every
free term context. Constructor congruence is a consequence for arbitrary
independently supplied related arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.Bisimulation

open _root_.CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

/-- A genuine bisimulation span, with both complete transition squares. -/
structure Span (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) where
  carrier : Endofunctor.Coalgebra (behaviourFunctor S Actions)
  first : carrier ⟶ object
  second : carrier ⟶ object

/-- A supplied point in a bisimulation span, retaining both exact projections. -/
structure Witness (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (first second : object.V base sort) where
  span : Span object
  point : span.carrier.V base sort
  first_read : span.first.f base sort point = first
  second_read : span.second.f base sort point = second

/-- Coalgebraic bisimilarity via independently supplied span witnesses. -/
def Related (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (first second : object.V base sort) : Prop :=
  Nonempty (Witness object base sort first second)

/-- Bisimilar states agree on availability of every actual action. -/
theorem availability_equal (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) {first second : object.V base sort}
    (related : Related object base sort first second) (action : Actions sort) :
    (object.str base sort first action).isSome = (object.str base sort second action).isSome := by
  rcases related with ⟨witness⟩
  have firstSquare := congrArg (fun arrow => (arrow base sort witness.point action).isSome)
    witness.span.first.h
  have secondSquare := congrArg (fun arrow => (arrow base sort witness.point action).isSome)
    witness.span.second.h
  change ((witness.span.carrier.str base sort witness.point action).map
      (witness.span.first.f base sort)).isSome =
    (object.str base sort (witness.span.first.f base sort witness.point) action).isSome at firstSquare
  change ((witness.span.carrier.str base sort witness.point action).map
      (witness.span.second.f base sort)).isSome =
    (object.str base sort (witness.span.second.f base sort witness.point) action).isSome at secondSquare
  simp only [Option.isSome_map, witness.first_read] at firstSquare
  simp only [Option.isSome_map, witness.second_read] at secondSquare
  exact firstSquare.symm.trans secondSquare

/-- The carrier of all related pairs has the same universe as the original values. -/
abbrev RelatedPairs (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) : S.Families :=
  fun base sort => { pair : object.V base sort × object.V base sort //
    Related object base sort pair.1 pair.2 }

/-- Select an already supplied witness; no transition or equation is assumed anew. -/
noncomputable def chosenWitness
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    {base : PUnit.{u + 1}} {sort : S.Srt} (pair : RelatedPairs object base sort) :
    Witness object base sort pair.val.1 pair.val.2 := Classical.choice pair.property

/-- Every successor in the witness span supplies an actual related pair. -/
def successorPair (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    {base : PUnit.{u + 1}} {sort : S.Srt} {first second : object.V base sort}
    (witness : Witness object base sort first second) (next : witness.span.carrier.V base sort) :
    RelatedPairs object base sort :=
  ⟨(witness.span.first.f base sort next, witness.span.second.f base sort next),
    ⟨⟨witness.span, next, rfl, rfl⟩⟩⟩

/-- The relation itself is equipped with the actual matched witness transitions. -/
noncomputable def relationCoalgebra
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  V := RelatedPairs object
  str base sort := ↾(fun pair action =>
    let witness := chosenWitness object pair
    (witness.span.carrier.str base sort witness.point action).map (successorPair object witness))

/-- First projection preserves every enabled transition and every disabled action. -/
noncomputable def relationFirst
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    relationCoalgebra object ⟶ object where
  f base sort := ↾(fun pair => pair.val.1)
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    let witness := chosenWitness object pair
    change ((witness.span.carrier.str base sort witness.point action).map
      (successorPair object witness)).map (fun pair => pair.val.1) = object.str base sort pair.val.1 action
    rw [Option.map_map]
    have exactSquare := congrArg (fun arrow => arrow base sort witness.point action) witness.span.first.h
    change (witness.span.carrier.str base sort witness.point action).map
      (witness.span.first.f base sort) =
        object.str base sort (witness.span.first.f base sort witness.point) action at exactSquare
    exact exactSquare.trans (congrArg (fun state => object.str base sort state action) witness.first_read)

/-- Second projection retains the same full transition information. -/
noncomputable def relationSecond
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    relationCoalgebra object ⟶ object where
  f base sort := ↾(fun pair => pair.val.2)
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    let witness := chosenWitness object pair
    change ((witness.span.carrier.str base sort witness.point action).map
      (successorPair object witness)).map (fun pair => pair.val.2) = object.str base sort pair.val.2 action
    rw [Option.map_map]
    have exactSquare := congrArg (fun arrow => arrow base sort witness.point action) witness.span.second.h
    change (witness.span.carrier.str base sort witness.point action).map
      (witness.span.second.f base sort) =
        object.str base sort (witness.span.second.f base sort witness.point) action at exactSquare
    exact exactSquare.trans (congrArg (fun state => object.str base sort state action) witness.second_read)

/-- Independently supplied bisimulation witnesses assemble into one complete relation span. -/
noncomputable def relationSpan
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) : Span object where
  carrier := relationCoalgebra object
  first := relationFirst object
  second := relationSecond object

variable (law : Law S Actions)

/-- A context acts on a genuine bisimulation by lifting and actual monad flattening. -/
noncomputable def contextSpan
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (span : Span (Operational.liftObject law object)) : Span (Operational.liftObject law object) where
  carrier := Operational.liftObject law span.carrier
  first := Operational.liftMap law span.first ≫ (Operational.liftMultiplication law).app object
  second := Operational.liftMap law span.second ≫ (Operational.liftMultiplication law).app object

/-- Every complete free term context preserves the supplied relation pointwise. -/
theorem context_related
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (context : S.polynomial.Free (RelatedPairs (Operational.liftObject law object)) base sort) :
    Related (Operational.liftObject law object) base sort
      (IndexedPolynomial.Free.bind S.polynomial
        (fun _ _ pair => pair.val.1) base sort context)
      (IndexedPolynomial.Free.bind S.polynomial
        (fun _ _ pair => pair.val.2) base sort context) := by
  refine ⟨⟨contextSpan law object (relationSpan (Operational.liftObject law object)),
    context, ?_, ?_⟩⟩
  · change IndexedPolynomial.Free.join S.polynomial
      (IndexedPolynomial.Free.map S.polynomial (fun _ _ pair => pair.val.1) base sort context) = _
    unfold IndexedPolynomial.Free.join IndexedPolynomial.Free.map
    rw [IndexedPolynomial.Free.bind_assoc]
    rfl
  · change IndexedPolynomial.Free.join S.polynomial
      (IndexedPolynomial.Free.map S.polynomial (fun _ _ pair => pair.val.2) base sort context) = _
    unfold IndexedPolynomial.Free.join IndexedPolynomial.Free.map
    rw [IndexedPolynomial.Free.bind_assoc]
    rfl

/-- Constructor congruence for arbitrary independently supplied related arguments. -/
theorem constructor_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (first second : (position : S.Position operator) →
      (Operational.liftObject law object).V base (S.argument operator position))
    (related : ∀ position, Related (Operational.liftObject law object) base
      (S.argument operator position) (first position) (second position)) :
    Related (Operational.liftObject law object) base sort
      (IndexedPolynomial.Free.node S.polynomial operator first)
      (IndexedPolynomial.Free.node S.polynomial operator second) := by
  let context : S.polynomial.Free (RelatedPairs (Operational.liftObject law object)) base sort :=
    IndexedPolynomial.Free.node S.polynomial operator (fun position =>
      IndexedPolynomial.Free.pure S.polynomial ⟨(first position, second position), related position⟩)
  have complete := context_related law object base sort context
  exact complete

end Mettapedia.OSLF.DeterministicGSOS.Bisimulation
