import Mettapedia.Languages.MeTTa.ZeroObserverExpressibility

/-!
# Reification and superposition as universal operators

The lattice of observers has a top, and the top is not an accident of which
observers happened to be listed.  It has a universal property, and so does
its dual.

* **Reification is the universal observer.**  *Every* observation of an
  answer bag — of any kind, into any type — is recoverable from the reified
  bag (`reify_universal`).  So an operator designed to extract as much
  information as possible is forced to be this one, up to equivalence
  (`universal_observer_unique`).

* **Superposition is the universal constructor.**  Dually, *every* way of
  producing an answer bag from data factors through it
  (`superpose_universal`).

Both hold for the same reason: the two exhibit answer bags as a **retract**
of data.  Superposing after reifying is the identity, so nothing is lost in
that direction, and losing nothing is precisely what universality means here.
That single split idempotent gives both universal properties at once, which
is why the two operators come as a pair rather than as two independent design
choices.

Stated in the preorder of `Core.NonFactorization`: observers ordered by
"determines" have `reify` as top, and any other top is equivalent to it.  In
the categorified version — objects are observations, morphisms are
factorizations — that is the usual uniqueness of a universal object up to
isomorphism, and it is proved here in the elementary form.

## What this does and does not characterize

It pins the *answer-algebra* operators: the constructor, the observer, and
(with `UnitAndChoiceZero`) the unit, the choice, and its zero.  Together
those are a monad with a monoid on top plus a retraction to data, and each is
determined by a property rather than by fiat.

It does not characterize matching, spaces, or typing.  Those need structure
this module does not have, and no claim is made that the language's whole
operator set is settled by these arguments.
-/

namespace Mettapedia.Languages.MeTTa.Universality

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip
open Mettapedia.GSLT.Core.NonFactorization

/-! ## Bags are a retract of data

Everything below rests on this one fact. -/

/-- Superposing a reified bag returns it: nothing is lost by reification. -/
theorem bags_retract_of_data (bag : List Datum) : decode (encode bag) = bag :=
  decode_encode bag

/-- Normalizing a datum to a collection is idempotent, so the retract is
split by an idempotent on data whose image is exactly the collections. -/
theorem normalize_idempotent (datum : Datum) :
    encode (decode (encode (decode datum))) = encode (decode datum) := by
  rw [decode_encode]

/-! ## Reification is the universal observer -/

/-- **Every observer factors through reification.**  Whatever an observation
reports, and into whatever type, it can be computed from the reified bag.
An operator built to extract the most information possible is therefore this
one. -/
theorem reify_universal {View : Type} (observer : List Datum → View) :
    Factors encode observer :=
  ⟨fun datum => observer (decode datum), fun bag => by
    show observer (decode (encode bag)) = observer bag
    rw [decode_encode]⟩

/-- Two observers are equivalent when each determines the other. -/
def Equivalent {View Other : Type} (first : List Datum → View)
    (second : List Datum → Other) : Prop :=
  Factors first second ∧ Factors second first

theorem Equivalent.refl {View : Type} (observer : List Datum → View) :
    Equivalent observer observer :=
  ⟨⟨id, fun _ => rfl⟩, ⟨id, fun _ => rfl⟩⟩

theorem Equivalent.symm {View Other : Type} {first : List Datum → View}
    {second : List Datum → Other} (equivalent : Equivalent first second) :
    Equivalent second first :=
  ⟨equivalent.2, equivalent.1⟩

/-- **The universal observer is unique up to equivalence.**  Any observer
that determines every other one is interchangeable with reification: it can
be computed from reification, and reification from it.  So "get as much
information as possible" does not merely happen to be reification — it
identifies it. -/
theorem universal_observer_unique {View : Type} (observer : List Datum → View)
    (determinesEverything :
      ∀ (Other : Type) (other : List Datum → Other), Factors observer other) :
    Equivalent observer encode :=
  ⟨determinesEverything Datum encode, reify_universal observer⟩

/-- Reification really is a top: it determines each of the observers studied
earlier, and they do not determine it. -/
theorem reify_strictly_above_the_others :
    (Factors encode ZeroObservers.count ∧
      Factors encode ZeroObservers.zeroTest ∧
      Factors encode ZeroObservers.firstAnswer) ∧
    (¬ Factors ZeroObservers.count encode ∧
      ¬ Factors ZeroObservers.zeroTest encode ∧
      ¬ Factors ZeroObservers.firstAnswer encode) :=
  ⟨⟨ZeroObservers.reify_determines_count, ZeroObservers.reify_determines_zeroTest,
      ZeroObservers.reify_determines_firstAnswer⟩,
    ZeroObservers.count_not_determines_reify,
    ZeroObservers.zeroTest_not_determines_reify,
    ZeroObservers.firstAnswer_not_determines_reify⟩

/-! ## Superposition is the universal constructor

The dual statement, with the retraction used in the other direction. -/

/-- **Every construction of an answer bag factors through superposition.**
Whatever produces a bag from data can be presented as: build a collection,
then superpose it. -/
theorem superpose_universal {Source : Type} (build : Source → List Datum) :
    ∃ present : Source → Datum, ∀ source, decode (present source) = build source :=
  ⟨fun source => encode (build source), fun source => decode_encode (build source)⟩

/-- And the presentation is unique wherever it matters: two presentations
agreeing after superposition are equal after normalization. -/
theorem superpose_presentation_unique {Source : Type}
    {first second : Source → Datum}
    (agree : ∀ source, decode (first source) = decode (second source))
    (source : Source) :
    encode (decode (first source)) = encode (decode (second source)) := by
  rw [agree source]

/-- **The pair, stated together.**  Superposition is universal among ways
into the answer algebra, reification universal among ways out, and the
retraction is what makes both true.  The two operators are one structure. -/
theorem superpose_collapse_are_a_universal_pair :
    (∀ (Source : Type) (build : Source → List Datum),
        ∃ present : Source → Datum, ∀ source, decode (present source) = build source) ∧
      (∀ (View : Type) (observer : List Datum → View), Factors encode observer) ∧
      (∀ bag : List Datum, decode (encode bag) = bag) :=
  ⟨fun _ build => superpose_universal build, fun _ observer => reify_universal observer,
    bags_retract_of_data⟩

end Mettapedia.Languages.MeTTa.Universality
