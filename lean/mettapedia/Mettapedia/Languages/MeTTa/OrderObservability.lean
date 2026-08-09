import Mathlib.Data.Multiset.Basic
import Mettapedia.Languages.MeTTa.ZeroObserverExpressibility

/-!
# When "bag" is a claim and when it is a pretence

Nondeterminism is a choice operator plus whatever equations are imposed on
it, and the equations *are* the semantics:

```
   assoc + comm + idem     set          membership only
   assoc + comm            multiset     + multiplicity
   assoc                   sequence     + order
```

A specification written at bag level asserts commutativity.  A single-
threaded implementation resolves the choice deterministically, so it produces
a sequence, and the order it produces is stable and repeatable.  The question
is whether that gap is an abstraction or a pretence, and the answer is
decided by exactly one thing: whether the language has an observer that can
see position.

* `bagView_determines_count`, `bagView_determines_zeroTest` — order-blind
  observers factor through the multiset.  For these the bag reading is sound
  and commutativity holds observationally.
* `bagView_not_determines_firstAnswer` — a positional observer does not.  For
  these two orderings are contextually distinguishable, and the bag reading
  is false of the implementation, not merely unproved.

So a deterministic implementation **refines** a bag specification without
**validating** its equations
(`deterministic_choice_does_not_validate_commutativity`).  Refinement is
legitimate; claiming the equations hold observationally is not, unless the
positional observers are given up.

The practical consequence is that answer order is *unspecified but
observable*.  Programs may depend on it accidentally, implementations may
differ on it legitimately, and any conformance test that fixes an answer
order is testing behaviour no specification pins down.
-/

namespace Mettapedia.Languages.MeTTa.OrderObservability

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.ZeroObservers
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The order-blind view -/

/-- Forget the order, keep the multiplicities: the bag reading of a run. -/
def bagView (answers : List Datum) : Multiset Datum := (answers : Multiset Datum)

/-- Choice is commutative *at bag level*.  This is the specification's claim,
and it is true of the specification. -/
theorem bagView_choice_comm (left right : List Datum) :
    bagView (left ++ right) = bagView (right ++ left) :=
  Quot.sound List.perm_append_comm

/-! ## Order-blind observers validate the claim -/

theorem bagView_determines_count : Factors bagView count :=
  ⟨Multiset.card, fun _ => rfl⟩

theorem bagView_determines_zeroTest : Factors bagView zeroTest :=
  ⟨fun bag => decide (Multiset.card bag = 0), fun answers => by
    cases answers <;> rfl⟩

/-! ## A positional observer refutes it -/

/-- Two runs with the same answers in different orders. -/
def orderFiber : NonTrivialFiber bagView firstAnswer where
  left := [.unit, .nil]
  right := [.nil, .unit]
  sameShadow := by decide
  differentValue := by decide

/-- **Order is not determined by the bag.**  So a language with a positional
observer cannot claim its choice operator is commutative: the claim is
refutable inside the language. -/
theorem bagView_not_determines_firstAnswer : ¬ Factors bagView firstAnswer :=
  orderFiber.not_factors

/-- The separating context, exhibited concretely: swapping the operands of a
choice changes which answer comes first. -/
theorem first_separates_swapped_choice :
    firstAnswer ([Datum.unit] ++ [Datum.nil]) ≠
      firstAnswer ([Datum.nil] ++ [Datum.unit]) := by
  decide

/-! ## Refinement is not validation

The two claims a deterministic implementation might make, distinguished. -/

/-- **A deterministic choice refines a bag specification without validating
it.**  The bag-level equation holds (first component), the implementation
still distinguishes the two orderings (second), and a positional observer
exhibits the difference (third).  All three at once, which is exactly the
situation: the abstraction is sound only where nothing looks. -/
theorem deterministic_choice_does_not_validate_commutativity :
    (∀ left right : List Datum, bagView (left ++ right) = bagView (right ++ left)) ∧
      ([Datum.unit] ++ [Datum.nil]) ≠ ([Datum.nil] ++ [Datum.unit]) ∧
      ¬ Factors bagView firstAnswer :=
  ⟨bagView_choice_comm, by decide, bagView_not_determines_firstAnswer⟩

/-- **The exact boundary.**  The bag reading is validated for precisely those
observers that factor through the multiset.  Giving up positional observation
is what would make it true of the implementation; keeping it is what makes
answer order unspecified-but-observable. -/
theorem bag_reading_sound_exactly_for_order_blind_observers :
    (Factors bagView count ∧ Factors bagView zeroTest) ∧
      ¬ Factors bagView firstAnswer :=
  ⟨⟨bagView_determines_count, bagView_determines_zeroTest⟩,
    bagView_not_determines_firstAnswer⟩

/-! ## Naming the level on the observer

The level is a property of observation, so it belongs on the observer rather
than on the collection.  That placement is principled and not merely tidy:
an observer may honestly be given a bag-level name exactly when it is
permutation-invariant, and that is a checkable condition. -/

/-- An observer is **bag level** when it factors through the multiset — when
nothing it reports depends on the order answers were produced in. -/
def BagLevel {View : Type} (observer : List Datum → View) : Prop :=
  Factors bagView observer

/-- **Bag-level observers are permutation invariant.**  A program using only
these cannot detect a reordering, so it behaves identically under any
implementation's answer order.  This is the portability guarantee. -/
theorem bagLevel_permutation_invariant {View : Type} {observer : List Datum → View}
    (bagLevel : BagLevel observer) {left right : List Datum}
    (reordered : left.Perm right) : observer left = observer right :=
  bagLevel.constantOnFibers left right (Quot.sound reordered)

/-- **And conversely.**  Permutation invariance is not merely necessary for a
bag-level name; it is sufficient.  So "may this observer be called bag level?"
is decided by a single question about reorderings, with no reference to how it
is implemented. -/
theorem bagLevel_iff_permutation_invariant {View : Type}
    (observer : List Datum → View) :
    BagLevel observer ↔
      ∀ left right : List Datum, left.Perm right → observer left = observer right := by
  refine ⟨fun bagLevel left right reordered =>
      bagLevel_permutation_invariant bagLevel reordered, fun invariant => ?_⟩
  exact ⟨Quot.lift observer (fun left right reordered => invariant left right reordered),
    fun _ => rfl⟩

/-- The positional observer is not permutation invariant, so it may not carry
a bag-level name — the ladder's rungs are separated by a decidable question
rather than by convention. -/
theorem firstAnswer_not_bagLevel : ¬ BagLevel firstAnswer :=
  bagView_not_determines_firstAnswer

/-- Counting and emptiness may. -/
theorem count_bagLevel : BagLevel count := bagView_determines_count

theorem zeroTest_bagLevel : BagLevel zeroTest := bagView_determines_zeroTest

end Mettapedia.Languages.MeTTa.OrderObservability
