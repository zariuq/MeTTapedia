import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Bind

/-!
# Answer effects and their information-preserving maps

Nondeterministic language semantics need more than a carrier of alternatives.
They need an empty computation, finite choice, a singleton computation, and
dependent sequencing.  `AnswerEffect` records those operations together with
the laws required by query and evaluation composition.

The interface deliberately does not require choice to be commutative or
idempotent.  Those are separate profile properties:

* lists retain operational order;
* multisets forget order but retain occurrence multiplicity;
* finite support forgets both order and duplicate occurrences.

`Morphism` is the translation contract between answer profiles.  It preserves
empty choice, finite choice, singleton answers, and bind.  Thus a morphism
commutes with arbitrary Kleisli composition, not only with one isolated query.

The canonical chain

```
List -> Multiset -> Finset
```

is constructed below.  Both arrows preserve answer-effect structure, while
negative theorems state exactly what they forget.
-/

namespace Mettapedia.GSLT.Dynamics.AnswerEffects

universe u

/-- A finite-choice effect with lawful dependent sequencing.

Only left distribution of bind over outer choice is part of the core.  Right
distribution through choices made separately by each continuation is a
strictly stronger property: it holds for order-free bag and support effects,
but fails for ordered list enumeration. -/
structure AnswerEffect where
  Carrier : Type u -> Type u
  pure : {alpha : Type u} -> alpha -> Carrier alpha
  empty : {alpha : Type u} -> Carrier alpha
  choice : {alpha : Type u} -> Carrier alpha -> Carrier alpha -> Carrier alpha
  bind : {alpha beta : Type u} ->
    Carrier alpha -> (alpha -> Carrier beta) -> Carrier beta
  pure_bind : forall {alpha beta : Type u} (value : alpha)
    (next : alpha -> Carrier beta),
    bind (pure value) next = next value
  bind_pure : forall {alpha : Type u} (answers : Carrier alpha),
    bind answers pure = answers
  bind_assoc : forall {alpha beta gamma : Type u}
    (answers : Carrier alpha) (next : alpha -> Carrier beta)
    (later : beta -> Carrier gamma),
    bind (bind answers next) later =
      bind answers (fun answer => bind (next answer) later)
  choice_assoc : forall {alpha : Type u}
    (first second third : Carrier alpha),
    choice (choice first second) third = choice first (choice second third)
  empty_choice : forall {alpha : Type u} (answers : Carrier alpha),
    choice empty answers = answers
  choice_empty : forall {alpha : Type u} (answers : Carrier alpha),
    choice answers empty = answers
  empty_bind : forall {alpha beta : Type u} (next : alpha -> Carrier beta),
    bind empty next = empty
  bind_empty : forall {alpha beta : Type u} (answers : Carrier alpha),
    bind answers (fun _ => empty) = (empty : Carrier beta)
  choice_bind : forall {alpha beta : Type u}
    (first second : Carrier alpha) (next : alpha -> Carrier beta),
    bind (choice first second) next =
      choice (bind first next) (bind second next)

namespace AnswerEffect

/-- Ordinary mapping derived from singleton answers and bind. -/
def map (effect : AnswerEffect.{u}) {alpha beta : Type u}
    (function : alpha -> beta) (answers : effect.Carrier alpha) :
    effect.Carrier beta :=
  effect.bind answers (fun answer => effect.pure (function answer))

@[simp] theorem map_pure (effect : AnswerEffect.{u})
    {alpha beta : Type u} (function : alpha -> beta) (value : alpha) :
    effect.map function (effect.pure value) = effect.pure (function value) := by
  simp [map, effect.pure_bind]

@[simp] theorem map_empty (effect : AnswerEffect.{u})
    {alpha beta : Type u} (function : alpha -> beta) :
    effect.map function (effect.empty : effect.Carrier alpha) = effect.empty := by
  simp [map, effect.empty_bind]

/-- Choice is commutative at this profile. -/
def ChoiceCommutative (effect : AnswerEffect.{u}) : Prop :=
  forall {alpha : Type u} (first second : effect.Carrier alpha),
    effect.choice first second = effect.choice second first

/-- Choice is idempotent at this profile. -/
def ChoiceIdempotent (effect : AnswerEffect.{u}) : Prop :=
  forall {alpha : Type u} (answers : effect.Carrier alpha),
    effect.choice answers answers = answers

/-- Continuation-local choice may be pulled outside bind.

Ordered lists fail this property because pulling out the choice changes the
enumeration from answer-major to branch-major order.  Bags and support satisfy
it because that order is not part of their carrier. -/
def BindDistributesChoice (effect : AnswerEffect.{u}) : Prop :=
  forall {alpha beta : Type u} (answers : effect.Carrier alpha)
    (first second : alpha -> effect.Carrier beta),
    effect.bind answers
        (fun answer => effect.choice (first answer) (second answer)) =
      effect.choice (effect.bind answers first) (effect.bind answers second)

/-- A natural, operation-preserving map between answer effects. -/
structure Morphism (source target : AnswerEffect.{u}) where
  map : {alpha : Type u} -> source.Carrier alpha -> target.Carrier alpha
  map_pure : forall {alpha : Type u} (value : alpha),
    map (source.pure value) = target.pure value
  map_empty : forall {alpha : Type u},
    map (source.empty : source.Carrier alpha) = target.empty
  map_choice : forall {alpha : Type u}
    (first second : source.Carrier alpha),
    map (source.choice first second) = target.choice (map first) (map second)
  map_bind : forall {alpha beta : Type u}
    (answers : source.Carrier alpha) (next : alpha -> source.Carrier beta),
    map (source.bind answers next) =
      target.bind (map answers) (fun answer => map (next answer))

namespace Morphism

/-- Identity translation of an answer effect. -/
def id (effect : AnswerEffect.{u}) : Morphism effect effect where
  map := fun answers => answers
  map_pure := by intros; rfl
  map_empty := by intros; rfl
  map_choice := by intros; rfl
  map_bind := by intros; rfl

/-- Composition of answer-effect translations. -/
def comp {first second third : AnswerEffect.{u}}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  map := fun answers => right.map (left.map answers)
  map_pure := by
    intro alpha value
    rw [left.map_pure, right.map_pure]
  map_empty := by
    intro alpha
    rw [left.map_empty, right.map_empty]
  map_choice := by
    intro alpha firstAnswers secondAnswers
    rw [left.map_choice, right.map_choice]
  map_bind := by
    intro alpha beta answers next
    rw [left.map_bind, right.map_bind]

/-- A morphism is faithful when it loses no distinctions at any result type. -/
def Faithful {source target : AnswerEffect.{u}}
    (morphism : Morphism source target) : Prop :=
  forall {alpha : Type u}, Function.Injective (@morphism.map alpha)

end Morphism

end AnswerEffect

/-! ## Three canonical answer profiles -/

/-- Ordered, duplicate-sensitive answer enumeration. -/
def listEffect : AnswerEffect.{u} where
  Carrier := List
  pure := fun value => [value]
  empty := []
  choice := List.append
  bind := fun answers next => answers.flatMap next
  pure_bind := by intros; simp
  bind_pure := by intros; simp
  bind_assoc := by intros; simp [List.flatMap_assoc]
  choice_assoc := by intros; exact List.append_assoc _ _ _
  empty_choice := by intros; rfl
  choice_empty := by intros; simp
  empty_bind := by intros; rfl
  bind_empty := by intros; simp
  choice_bind := by intros; simp

/-- Unordered, occurrence-sensitive answer bags. -/
def bagEffect : AnswerEffect.{u} where
  Carrier := Multiset
  pure := fun value => {value}
  empty := 0
  choice := fun first second => first + second
  bind := Multiset.bind
  pure_bind := by intros; simp
  bind_pure := by
    intro alpha answers
    simpa using Multiset.bind_singleton answers (fun value => value)
  bind_assoc := by intros; exact Multiset.bind_assoc
  choice_assoc := by intros; exact add_assoc _ _ _
  empty_choice := by intros; exact zero_add _
  choice_empty := by intros; exact add_zero _
  empty_bind := by intros; exact Multiset.zero_bind _
  bind_empty := by intros; exact Multiset.bind_zero _
  choice_bind := by intros; exact Multiset.add_bind _ _ _

/-- Unordered, duplicate-insensitive finite answer support. -/
noncomputable def supportEffect : AnswerEffect.{u} := by
  classical
  exact
    { Carrier := Finset
      pure := fun value => {value}
      empty := Finset.empty
      choice := fun first second => Union.union first second
      bind := fun answers next => answers.biUnion next
      pure_bind := by
        intros
        exact Finset.singleton_biUnion
      bind_pure := by
        intros
        exact Finset.biUnion_singleton_eq_self
      bind_assoc := by
        intros
        exact Finset.biUnion_biUnion _ _ _
      choice_assoc := by
        intros
        exact Finset.union_assoc _ _ _
      empty_choice := by
        intros
        exact Finset.empty_union _
      choice_empty := by
        intros
        exact Finset.union_empty _
      empty_bind := by
        intros
        exact Finset.biUnion_empty
      bind_empty := by
        intro alpha beta answers
        ext value
        simp only [Finset.mem_biUnion]
        constructor
        case mp =>
          intro member
          apply Exists.elim member
          intro answer memberRest
          exact memberRest.2
        case mpr =>
          intro impossible
          exact (Finset.notMem_empty value impossible).elim
      choice_bind := by
        intros
        exact Finset.union_biUnion }

/-! ## Profile laws and separating examples -/

theorem bag_choice_commutative : bagEffect.ChoiceCommutative := by
  intro alpha
  change forall first second : Multiset alpha,
    first + second = second + first
  exact fun first second => add_comm first second

theorem bag_bind_distributes_choice : bagEffect.BindDistributesChoice := by
  intro alpha beta
  change forall (answers : Multiset alpha)
    (first second : alpha -> Multiset beta),
    answers.bind (fun answer => first answer + second answer) =
      answers.bind first + answers.bind second
  exact fun answers first second => Multiset.bind_add answers first second

theorem support_choice_commutative : supportEffect.ChoiceCommutative := by
  classical
  intro alpha
  change forall first second : Finset alpha,
    Union.union first second = Union.union second first
  exact fun first second => Finset.union_comm first second

theorem support_choice_idempotent : supportEffect.ChoiceIdempotent := by
  classical
  intro alpha
  change forall answers : Finset alpha, Union.union answers answers = answers
  exact Finset.union_idempotent

theorem support_bind_distributes_choice : supportEffect.BindDistributesChoice := by
  classical
  intro alpha beta
  change forall (answers : Finset alpha)
    (first second : alpha -> Finset beta),
    answers.biUnion
        (fun answer => Union.union (first answer) (second answer)) =
      Union.union (answers.biUnion first) (answers.biUnion second)
  exact fun _ _ _ => Finset.biUnion_union

/-- Ordered list choice is not commutative. -/
theorem list_choice_not_commutative :
    Not listEffect.{0}.ChoiceCommutative := by
  intro commutative
  have impossible := commutative ([false] : List Bool) [true]
  simp [listEffect] at impossible

/-- Ordered list choice is not idempotent. -/
theorem list_choice_not_idempotent :
    Not listEffect.{0}.ChoiceIdempotent := by
  intro idempotent
  have impossible := idempotent ([()] : List Unit)
  simp [listEffect] at impossible

/-- Occurrence bags are not idempotent. -/
theorem bag_choice_not_idempotent :
    Not bagEffect.{0}.ChoiceIdempotent := by
  intro idempotent
  have impossible := idempotent ({()} : Multiset Unit)
  have cardEquality := congrArg Multiset.card impossible
  simp [bagEffect] at cardEquality

/-- Ordered bind does not distribute a continuation-local choice outward.
The two sides contain the same answers but enumerate them differently. -/
theorem list_bind_not_distributes_choice :
    Not listEffect.{0}.BindDistributesChoice := by
  intro distributes
  let answers : List Bool := [false, true]
  let first : Bool -> List Nat := fun value => if value then [2] else [0]
  let second : Bool -> List Nat := fun value => if value then [3] else [1]
  have impossible := distributes answers first second
  simp [answers, first, second, listEffect] at impossible

/-! ## The canonical morphism chain -/

/-- Forget list enumeration order while retaining every occurrence. -/
def listToBag : AnswerEffect.Morphism listEffect bagEffect where
  map := fun {alpha} (answers : List alpha) => (answers : Multiset alpha)
  map_pure := by intros; rfl
  map_empty := by intros; rfl
  map_choice := by
    intro alpha first second
    change List alpha at first second
    change
      ((first ++ second : List alpha) : Multiset alpha) =
        (first : Multiset alpha) + (second : Multiset alpha)
    exact (Multiset.coe_add first second).symm
  map_bind := by intros; exact (Multiset.coe_bind _ _).symm

/-- Forget occurrence multiplicity while retaining finite support. -/
noncomputable def bagToSupport :
    AnswerEffect.Morphism bagEffect supportEffect := by
  classical
  exact
    { map := fun {alpha} (answers : Multiset alpha) => answers.toFinset
      map_pure := by
        intro alpha value
        change ({value} : Multiset alpha).toFinset = ({value} : Finset alpha)
        simp
      map_empty := by
        intro alpha
        change (0 : Multiset alpha).toFinset = (Finset.empty : Finset alpha)
        exact Multiset.toFinset_zero
      map_choice := by
        intro alpha first second
        change Multiset alpha at first second
        change (first + second).toFinset =
          Union.union first.toFinset second.toFinset
        exact Multiset.toFinset_add first second
      map_bind := by
        intro alpha beta answers next
        change (answers.bind next).toFinset =
          answers.toFinset.biUnion (fun answer => (next answer).toFinset)
        exact Finset.bind_toFinset answers next }

@[simp] theorem listToBag_map {alpha : Type u} (answers : List alpha) :
    listToBag.map answers = (answers : Multiset alpha) :=
  rfl

@[simp] theorem bagToSupport_map {alpha : Type u} [DecidableEq alpha]
    (answers : Multiset alpha) :
    bagToSupport.map answers = answers.toFinset := by
  classical
  simp only [bagToSupport]
  apply Finset.ext
  intro value
  simp

/-- Forget both list order and occurrence multiplicity. -/
noncomputable def listToSupport :
    AnswerEffect.Morphism listEffect supportEffect :=
  listToBag.comp bagToSupport

/-! ## The losses are real -/

/-- Quotienting an ordered enumeration to a bag is not faithful. -/
theorem listToBag_not_faithful : Not listToBag.{0}.Faithful := by
  intro faithful
  have sameImage :
      listToBag.{0}.map ([false, true] : List Bool) =
        listToBag.{0}.map ([true, false] : List Bool) := by
    change
      (([false, true] : List Bool) : Multiset Bool) =
        (([true, false] : List Bool) : Multiset Bool)
    decide
  have impossible : ([false, true] : List Bool) = [true, false] :=
    faithful sameImage
  simp at impossible

/-- Quotienting an occurrence bag to support is not faithful. -/
theorem bagToSupport_not_faithful : Not bagToSupport.{0}.Faithful := by
  intro faithful
  have sameImage :
      bagToSupport.{0}.map ({()} : Multiset Unit) =
        bagToSupport.{0}.map ({(), ()} : Multiset Unit) := by
    classical
    simp
  have impossible : ({()} : Multiset Unit) = {(), ()} :=
    faithful sameImage
  have cardEquality := congrArg Multiset.card impossible
  simp at cardEquality

/-- No post-processing of support can recover every occurrence bag. -/
theorem no_bag_recovery_from_support :
    Not (exists restore : Finset Unit -> Multiset Unit,
      forall answers : Multiset Unit,
        restore (bagToSupport.{0}.map answers) = answers) := by
  intro existsRestore
  apply Exists.elim existsRestore
  intro restore restores
  have one := restores ({()} : Multiset Unit)
  have two := restores ({(), ()} : Multiset Unit)
  have sameSupport :
      bagToSupport.{0}.map ({()} : Multiset Unit) =
        bagToSupport.{0}.map ({(), ()} : Multiset Unit) := by
    classical
    simp
  rw [sameSupport, two] at one
  have cardEquality := congrArg Multiset.card one
  simp at cardEquality

end Mettapedia.GSLT.Dynamics.AnswerEffects
