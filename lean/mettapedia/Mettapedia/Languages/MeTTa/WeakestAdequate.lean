import Mathlib.Data.Finset.Basic
import Mettapedia.Languages.MeTTa.OrderObservability

/-!
# Weakest adequate carriers: is a set weaker than a bag?

"Weakest" in the sense of ruling out least, subject to still doing the job.
Formally: **the coarsest carrier through which every required distinction
still factors**.  That makes the question decidable case by case instead of
arguable, and it has an answer that is not the one either slogan gives.

The confusion is that the comparison **reverses** depending on what is being
called weak, and both readings are true at once:

* **As an observation** a set is weaker than a bag — it rules out less,
  because it makes fewer distinctions.  `bag_determines_set` shows the set
  view factors through the bag view, so it is strictly coarser.
* **As a requirement on implementations** a set is *stronger* — its choice
  operator must satisfy an extra equation.  `set_view_is_idempotent` and
  `bag_view_is_not_idempotent` are that gap, compiled.

Those two are the same fact seen from opposite ends: more equations on the
operator is exactly fewer distinctions in the carrier.  So "weaker" must be
said of the observation, and the conformance burden then moves the other way.

With that fixed, the design question has a definite answer.  If multiplicity
is among the required distinctions — and it must be, or one derivation and
two identical derivations become the same thing — then:

* the set carrier is **inadequate**: `set_not_determines_multiplicity`;
* the bag carrier is **adequate**: `bag_determines_multiplicity`;
* and the bag carrier is **coarsest among adequate ones**:
  `bag_is_coarsest_for_multiplicity`.

So the bag is the weakest adequate carrier, not merely the preferred one.
`weakestAdequate_unique` supplies the accompanying universal property: a
weakest adequate carrier is unique up to mutual determination, so "choose the
weakest" names a specific object rather than a direction.
-/

namespace Mettapedia.Languages.MeTTa.Weakness

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.OrderObservability
open Mettapedia.GSLT.Core.NonFactorization

/-! ## Three carriers and the distinction at stake -/

/-- The finest carrier: answers in order. -/
def listView : List Datum → List Datum := id

/-- Forget the order (already defined; named here for the ladder). -/
def bagOf : List Datum → Multiset Datum := bagView

/-- Forget the multiplicity too. -/
def setView (answers : List Datum) : Finset Datum := answers.toFinset

/-- How many times a given answer occurred.  This is the distinction the
choice of carrier is really about. -/
def multiplicityOf (target : Datum) (answers : List Datum) : Nat :=
  answers.count target

/-! ## The ladder, as factorizations -/

theorem list_determines_bag : Factors listView bagOf :=
  ⟨fun answers => bagView answers, fun _ => rfl⟩

/-- **A set is a coarser observation than a bag.**  In the "rules out less"
sense, the set view really is the weaker of the two. -/
theorem bag_determines_set : Factors bagOf setView :=
  ⟨Multiset.toFinset, fun _ => rfl⟩

/-- Counting inside the bag is counting in the run. -/
@[simp] theorem count_bagOf (target : Datum) (answers : List Datum) :
    Multiset.count target (bagOf answers) = multiplicityOf target answers := by
  simp [bagOf, bagView, multiplicityOf]

/-- A bag reports multiplicity. -/
theorem bag_determines_multiplicity (target : Datum) :
    Factors bagOf (multiplicityOf target) :=
  ⟨fun bag => Multiset.count target bag, fun answers => count_bagOf target answers⟩

/-- Two runs with the same answers present and different multiplicities. -/
def multiplicityFiber : NonTrivialFiber setView (multiplicityOf .unit) where
  left := [.unit]
  right := [.unit, .unit]
  sameShadow := by decide
  differentValue := by decide

/-- **A set does not report multiplicity.**  So if one derivation and two
identical derivations must differ, the set carrier is inadequate — and no
later library can repair it, because the information is gone. -/
theorem set_not_determines_multiplicity :
    ¬ Factors setView (multiplicityOf .unit) :=
  multiplicityFiber.not_factors

/-! ## The reversal, compiled

More equations on the operator is fewer distinctions in the carrier.  These
two theorems are that statement. -/

/-- The set view satisfies idempotence: repeating a run changes nothing. -/
theorem set_view_is_idempotent (answers : List Datum) :
    setView (answers ++ answers) = setView answers := by
  ext datum
  simp [setView]

/-- The bag view does not.  So the set carrier's extra law is exactly the
distinction it gave up — a stronger demand on implementations bought with a
weaker observation. -/
theorem bag_view_is_not_idempotent :
    bagOf ([Datum.unit] ++ [Datum.unit]) ≠ bagOf [Datum.unit] := by
  decide

/-! ## Weakest adequate, and its universal property -/

/-- A carrier is **adequate** for a family of required distinctions when each
of them factors through it. -/
def AdequateFor {Carrier Index : Type} {View : Index → Type}
    (carrier : List Datum → Carrier) (required : ∀ index, List Datum → View index) :
    Prop :=
  ∀ index, Factors carrier (required index)

/-- A carrier is **weakest adequate** when it is adequate and every adequate
carrier determines it — that is, nothing adequate is coarser. -/
def WeakestAdequate {Carrier Index : Type} {View : Index → Type}
    (carrier : List Datum → Carrier) (required : ∀ index, List Datum → View index) :
    Prop :=
  AdequateFor carrier required ∧
    ∀ (Other : Type) (other : List Datum → Other),
      AdequateFor other required → Factors other carrier

/-- **The weakest adequate carrier is unique up to mutual determination.**
So "take the weakest version" identifies an object rather than pointing in a
direction. -/
theorem weakestAdequate_unique {Carrier Another Index : Type} {View : Index → Type}
    {required : ∀ index, List Datum → View index}
    {first : List Datum → Carrier} {second : List Datum → Another}
    (firstWeakest : WeakestAdequate first required)
    (secondWeakest : WeakestAdequate second required) :
    Factors first second ∧ Factors second first :=
  ⟨secondWeakest.2 Carrier first firstWeakest.1,
    firstWeakest.2 Another second secondWeakest.1⟩

/-! ## The answer for multiplicity -/

/-- **No adequate carrier is coarser than the bag.**  Anything that reports
every multiplicity already separates whatever the bag separates, because a
multiset is determined by its counts. -/
theorem bag_is_coarsest_for_multiplicity {Other : Type} (other : List Datum → Other)
    (adequate : ∀ target, Factors other (multiplicityOf target)) :
    ConstantOnFibers other bagOf := by
  intro left right sameShadow
  refine Multiset.ext.mpr fun target => ?_
  rw [count_bagOf, count_bagOf]
  exact (adequate target).constantOnFibers left right sameShadow

/-- **The bag is the weakest adequate carrier once multiplicity is
required.**  Adequate, coarsest among adequate carriers, and the coarser
alternative is refuted — all three, which is what settles the question rather
than trading slogans. -/
theorem bag_is_weakest_adequate_for_multiplicity :
    (∀ target, Factors bagOf (multiplicityOf target)) ∧
      (∀ (Other : Type) (other : List Datum → Other),
        (∀ target, Factors other (multiplicityOf target)) →
          ConstantOnFibers other bagOf) ∧
      ¬ Factors setView (multiplicityOf .unit) :=
  ⟨bag_determines_multiplicity,
    fun _ other adequate => bag_is_coarsest_for_multiplicity other adequate,
    set_not_determines_multiplicity⟩

/-- And the bag is strictly coarser than the list, so requiring multiplicity
does not force order: the ladder stops exactly where it should. -/
theorem bag_strictly_below_list :
    Factors listView bagOf ∧ ¬ Factors bagView ZeroObservers.firstAnswer :=
  ⟨list_determines_bag, bagView_not_determines_firstAnswer⟩

end Mettapedia.Languages.MeTTa.Weakness
