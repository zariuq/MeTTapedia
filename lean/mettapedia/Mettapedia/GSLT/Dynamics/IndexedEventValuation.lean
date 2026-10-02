import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mettapedia.GSLT.Core.Composition

/-!
# Compositional valuations of proof-relevant events

Cost, evidence, provenance, authority, and resource claims may decorate the
same exact events while using different algebras.  This module is independent
of any particular transition system.  A valuation assigns optional grades to
events in a `PartialMonoid`; chronological histories fold through that
algebra.  Independent valuations combine by product, and valuations pull back
along event encodings.
-/

namespace Mettapedia.GSLT.Dynamics.IndexedEventValuation

open Mettapedia.GSLT

universe uEvent uSourceEvent uGrade uLeft uRight

/-- One algebra-indexed valuation of an arbitrary event type. -/
structure Valuation (Event : Type uEvent) where
  Grade : Type uGrade
  algebra : PartialMonoid Grade
  grade : Event -> Option Grade

namespace Valuation

/-- Combine independently chosen valuation axes without conflating them. -/
abbrev prod {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) : Valuation Event where
  Grade := left.Grade × right.Grade
  algebra := left.algebra.prod right.algebra
  grade := fun event =>
    (left.grade event).bind fun leftGrade =>
      (right.grade event).bind fun rightGrade =>
        some (leftGrade, rightGrade)

/-- Pull a valuation back through an event encoding. -/
abbrev pullback {SourceEvent : Type uSourceEvent} {Event : Type uEvent}
    (valuation : Valuation Event) (encode : SourceEvent -> Event) :
    Valuation SourceEvent where
  Grade := valuation.Grade
  algebra := valuation.algebra
  grade := valuation.grade ∘ encode

/-- Fold a chronological event history through the selected partial algebra. -/
def historyGrade {Event : Type uEvent} (valuation : Valuation Event) :
    List Event -> Option valuation.Grade :=
  valuation.algebra.foldOption valuation.grade

@[simp] theorem historyGrade_nil {Event : Type uEvent}
    (valuation : Valuation Event) :
    valuation.historyGrade [] = some valuation.algebra.unit :=
  rfl

@[simp] theorem historyGrade_cons {Event : Type uEvent}
    (valuation : Valuation Event) (event : Event) (events : List Event) :
    valuation.historyGrade (event :: events) =
      (valuation.grade event).bind fun head =>
        (valuation.historyGrade events).bind fun tail =>
          valuation.algebra.op head tail :=
  rfl

/-- Chronological concatenation is valued by algebra composition. -/
theorem historyGrade_append {Event : Type uEvent}
    (valuation : Valuation Event) (first second : List Event) :
    valuation.historyGrade (first ++ second) =
      (valuation.historyGrade first).bind fun left =>
        (valuation.historyGrade second).bind fun right =>
          valuation.algebra.op left right :=
  valuation.algebra.foldOption_append valuation.grade first second

/-- Partial resource composition of two actual events. -/
def combine? {Event : Type uEvent} (valuation : Valuation Event)
    (first second : Event) : Option valuation.Grade := do
  let firstGrade ← valuation.grade first
  let secondGrade ← valuation.grade second
  valuation.algebra.op firstGrade secondGrade

def Compatible {Event : Type uEvent} (valuation : Valuation Event)
    (first second : Event) : Prop := (valuation.combine? first second).isSome

/-- Pairwise composition is the two-event case of the same chronological fold. -/
theorem combine_eq_historyGrade {Event : Type uEvent} (valuation : Valuation Event)
    (first second : Event) :
    valuation.combine? first second = valuation.historyGrade [first, second] := by
  simp [combine?, historyGrade_cons, historyGrade_nil, valuation.algebra.op_unit]

/-- Product valuation is exactly the product of the two independent history
valuations.  In particular, neither coordinate may silently stand in for a
failure of the other. -/
theorem prod_historyGrade {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) (events : List Event) :
    (left.prod right).historyGrade events =
      (left.historyGrade events).bind fun leftGrade =>
        (right.historyGrade events).bind fun rightGrade =>
          some (leftGrade, rightGrade) := by
  induction events with
  | nil => rfl
  | cons event events inductionHypothesis =>
      simp only [historyGrade_cons]
      rw [inductionHypothesis]
      cases hLeftHead : left.grade event <;>
        cases hRightHead : right.grade event <;>
        cases hLeftTail : left.historyGrade events <;>
        cases hRightTail : right.historyGrade events <;>
        simp [PartialMonoid.prod]

/-- Every resource coordinate must accept before their product accepts. -/
theorem prod_compatible {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event) (right : Valuation.{uEvent, uRight} Event)
    (first second : Event)
    (leftCompatible : left.Compatible first second)
    (rightCompatible : right.Compatible first second) :
    (left.prod right).Compatible first second := by
  change ((left.prod right).combine? first second).isSome = true
  rw [combine_eq_historyGrade, prod_historyGrade]
  rw [← combine_eq_historyGrade, ← combine_eq_historyGrade]
  obtain ⟨leftGrade, leftEquation⟩ := Option.isSome_iff_exists.mp leftCompatible
  obtain ⟨rightGrade, rightEquation⟩ := Option.isSome_iff_exists.mp rightCompatible
  simp [leftEquation, rightEquation]

/-- A total valuation cannot reject an event or a composition of grades. -/
structure IsTotal {Event : Type uEvent} (valuation : Valuation Event) : Prop where
  grade_some : forall event, Exists fun grade => valuation.grade event = some grade
  op_some : forall left right,
    Exists fun result => valuation.algebra.op left right = some result

theorem IsTotal.historyGrade_some {Event : Type uEvent}
    {valuation : Valuation Event} (total : IsTotal valuation)
    (events : List Event) :
    Exists fun grade => valuation.historyGrade events = some grade := by
  induction events with
  | nil => exact ⟨valuation.algebra.unit, rfl⟩
  | cons event events inductionHypothesis =>
      obtain ⟨head, headEquation⟩ := total.grade_some event
      obtain ⟨tail, tailEquation⟩ := inductionHypothesis
      obtain ⟨result, resultEquation⟩ := total.op_some head tail
      exact ⟨result, by
        simp only [historyGrade_cons, headEquation, tailEquation, Option.bind_some]
        exact resultEquation⟩

/-- Erasing a total right-hand coordinate recovers the left valuation exactly.
This is the non-vacuous condition needed for provenance or telemetry erasure
to preserve acceptance. -/
theorem map_fst_prod_historyGrade_of_right_total {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) (total : IsTotal right)
    (events : List Event) :
    Option.map Prod.fst ((left.prod right).historyGrade events) =
      left.historyGrade events := by
  rw [prod_historyGrade]
  obtain ⟨rightGrade, rightEquation⟩ := total.historyGrade_some events
  rw [rightEquation]
  cases left.historyGrade events <;> rfl

@[simp] theorem pullback_historyGrade
    {SourceEvent : Type uSourceEvent} {Event : Type uEvent}
    (valuation : Valuation Event) (encode : SourceEvent -> Event)
    (events : List SourceEvent) :
    (valuation.pullback encode).historyGrade events =
      valuation.historyGrade (events.map encode) := by
  induction events with
  | nil => rfl
  | cons event events inductionHypothesis =>
      rw [historyGrade_cons, List.map_cons, historyGrade_cons]
      change
        (valuation.grade (encode event)).bind
            (fun head =>
              ((valuation.pullback encode).historyGrade events).bind
                fun tail => valuation.algebra.op head tail) = _
      rw [inductionHypothesis]

end Valuation

/-- Every additive monoid gives a total partial-composition algebra. -/
def additivePartialMonoid (Grade : Type uGrade) [AddMonoid Grade] :
    PartialMonoid Grade where
  unit := 0
  op := fun first second => some (first + second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [add_assoc]

/-- Attach a total additive grade to every event. -/
abbrev additive {Event : Type uEvent} {Grade : Type uGrade} [AddMonoid Grade]
    (grade : Event -> Grade) : Valuation Event where
  Grade := Grade
  algebra := additivePartialMonoid Grade
  grade := fun event => some (grade event)

/-- Chronological concatenation, used for provenance histories where order and
repetition are observable. -/
def chronologicalListPartialMonoid (Item : Type uGrade) :
    PartialMonoid (List Item) where
  unit := []
  op := fun first second => some (first ++ second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [List.append_assoc]

/-- Attach a singleton chronological history to every event. -/
abbrev chronological {Event : Type uEvent} {Item : Type uGrade}
    (item : Event -> Item) : Valuation Event where
  Grade := List Item
  algebra := chronologicalListPartialMonoid Item
  grade := fun event => some [item event]

/-- An additive valuation computes the ordered sum of the actual event grades. -/
@[simp] theorem additive_historyGrade {Event : Type uEvent} {Grade : Type uGrade}
    [AddMonoid Grade] (grade : Event → Grade) (events : List Event) :
    (additive grade).historyGrade events = some ((events.map grade).sum) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [Valuation.historyGrade_cons, ih]
      rfl

/-- A chronological valuation keeps every event in order, including repetitions. -/
@[simp] theorem chronological_historyGrade {Event : Type uEvent} {Item : Type uGrade}
    (item : Event → Item) (events : List Event) :
    (chronological item).historyGrade events = some (events.map item) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [Valuation.historyGrade_cons, ih]
      rfl

theorem additive_isTotal {Event : Type uEvent} {Grade : Type uGrade}
    [AddMonoid Grade] (grade : Event -> Grade) :
    (additive grade).IsTotal := by
  constructor
  · intro event
    change Exists fun result : Grade => some (grade event) = some result
    exact ⟨grade event, rfl⟩
  · change forall left right : Grade, Exists fun result : Grade =>
      (additivePartialMonoid Grade).op left right = some result
    intro left right
    exact ⟨left + right, rfl⟩

theorem chronological_isTotal {Event : Type uEvent} {Item : Type uGrade}
    (item : Event -> Item) :
    (chronological item).IsTotal := by
  constructor
  · intro event
    change Exists fun result : List Item => some [item event] = some result
    exact ⟨[item event], rfl⟩
  · change forall left right : List Item, Exists fun result : List Item =>
      (chronologicalListPartialMonoid Item).op left right = some result
    intro left right
    exact ⟨left ++ right, rfl⟩

end Mettapedia.GSLT.Dynamics.IndexedEventValuation
