import Mettapedia.GSLT.Core.FiniteOccurrenceLookup

/-!
# Finite list membership with a reverse cursor

Finite membership is the unit-valued specialization of occurrence lookup.
This module lowers the chronological visited prefix of
`FiniteOccurrenceLookup` to a reverse prefix, so each executable advance is
one constant-size list constructor rather than an append.

The lowering is a covered GSLT translation: every source step maps to one
reverse-cursor step, and every step leaving a translated state lifts back to
an exact source step.  Both machines are interpreted through OSLF before the
native modal transport is exposed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.FiniteListMembership

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {Value : Type}

/-- A list member represented as the key of a unit-valued occurrence. -/
def entry (value : Value) : Entry Value Unit :=
  { key := value, value := () }

/-- Unit-valued entries retain exactly their ordered keys. -/
def values (entries : List (Entry Value Unit)) : List Value :=
  entries.map Entry.key

@[simp] theorem values_map_entry (items : List Value) :
    values (items.map entry) = items := by
  simp [values, Function.comp_def, entry]

/-- Public membership observations retain the exact first occurrence or the
explicit end position reached by a missing query. -/
inductive Observation where
  | found (position : Nat)
  | missing (endPosition : Nat)
deriving DecidableEq, Repr

/-- Executable membership cursor.  `visitedRev` makes one advance a `cons`;
the represented chronological inventory is recovered by reversing it. -/
structure Scan (Value : Type) where
  target : Value
  visitedRev : List Value
  remaining : List Value
deriving DecidableEq, Repr

namespace Scan

def inventory (scan : Scan Value) : List Value :=
  scan.visitedRev.reverse ++ scan.remaining

def position (scan : Scan Value) : Nat :=
  scan.visitedRev.length

end Scan

/-- Reverse-cursor states retain the complete inventory at termination. -/
inductive State (Value : Type) where
  | scanning (scan : Scan Value)
  | finished (target : Value) (inventory : List Value)
      (observation : Observation)
deriving DecidableEq, Repr

namespace State

def inventory : State Value → List Value
  | .scanning scan => scan.inventory
  | .finished _ inventory _ => inventory

end State

/-- One constant-work reverse-cursor membership step. -/
inductive Step : State Value → State Value → Prop where
  | hit (target : Value) (visitedRev : List Value)
      (next : Value) (remaining : List Value)
      (same : next = target) :
      Step
        (.scanning ⟨target, visitedRev, next :: remaining⟩)
        (.finished target (visitedRev.reverse ++ next :: remaining)
          (.found visitedRev.length))
  | advance (target : Value) (visitedRev : List Value)
      (next : Value) (remaining : List Value)
      (different : next ≠ target) :
      Step
        (.scanning ⟨target, visitedRev, next :: remaining⟩)
        (.scanning ⟨target, next :: visitedRev, remaining⟩)
  | miss (target : Value) (visitedRev : List Value) :
      Step
        (.scanning ⟨target, visitedRev, []⟩)
        (.finished target visitedRev.reverse
          (.missing visitedRev.length))

/-- Reverse-cursor finite membership as a GSLT. -/
def gslt (Value : Type) : GSLT where
  Term := State Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The chronological source is the existing unit-valued occurrence lookup. -/
abbrev ChronologicalState (Value : Type) :=
  FiniteOccurrenceLookup.State Value Unit

def chronologicalGSLT (Value : Type) : GSLT :=
  FiniteOccurrenceLookup.gslt Value Unit

def observation : FiniteOccurrenceLookup.Observation Unit → Observation
  | .found position _ => .found position
  | .missing endPosition => .missing endPosition

@[simp] theorem observation_found (position : Nat) :
    observation (.found position ()) = .found position := by
  rfl

@[simp] theorem observation_missing (position : Nat) :
    observation (.missing position) = .missing position := by
  rfl

/-- Lower a chronological cursor to its constant-work reverse representation. -/
def lowerState : ChronologicalState Value → State Value
  | .scanning scan =>
      .scanning
        { target := scan.target
          visitedRev := (values scan.visited).reverse
          remaining := values scan.remaining }
  | .finished target inventory result =>
      .finished target (values inventory) (observation result)

@[simp] theorem lowerState_scanning (target : Value)
    (visited remaining : List (Entry Value Unit)) :
    lowerState (.scanning ⟨target, visited, remaining⟩) =
      .scanning
        ⟨target, (values visited).reverse, values remaining⟩ := by
  rfl

@[simp] theorem lowerState_finished_found (target : Value)
    (inventory : List (Entry Value Unit)) (position : Nat) :
    lowerState (.finished target inventory (.found position ())) =
      .finished target (values inventory) (.found position) := by
  rfl

@[simp] theorem lowerState_finished_missing (target : Value)
    (inventory : List (Entry Value Unit)) (position : Nat) :
    lowerState (.finished target inventory (.missing position)) =
      .finished target (values inventory) (.missing position) := by
  rfl

/-- Every chronological occurrence step becomes exactly one constant-work
reverse-cursor step. -/
theorem lower_step
    {source target : ChronologicalState Value}
    (step : FiniteOccurrenceLookup.Step source target) :
    Step (lowerState source) (lowerState target) := by
  cases step with
  | hit target visited next remaining same =>
      rcases next with ⟨next, value⟩
      cases value
      simpa [lowerState, values, List.map_append] using
        (Step.hit target (values visited).reverse next
          (values remaining) same)
  | advance target visited next remaining different =>
      simpa [lowerState, values, List.map_append] using
        (Step.advance target (values visited).reverse next.key
          (values remaining) different)
  | miss target visited =>
      simpa [lowerState, values, observation] using
        (Step.miss target (values visited).reverse)

/-- No reverse-cursor transition is invented at a lowered chronological
state: it lifts to an exact occurrence-lookup transition. -/
theorem lift_step
    {source : ChronologicalState Value} {target : State Value}
    (step : Step (lowerState source) target) :
    ∃ sourceTarget,
      FiniteOccurrenceLookup.Step source sourceTarget ∧
        lowerState sourceTarget = target := by
  cases source with
  | finished sourceTarget inventory result =>
      cases step
  | scanning scan =>
      rcases scan with ⟨sourceTarget, visited, remaining⟩
      cases remaining with
      | nil =>
          cases step with
          | miss _ _ =>
              refine
                ⟨.finished sourceTarget visited
                    (.missing visited.length),
                  FiniteOccurrenceLookup.Step.miss sourceTarget visited, ?_⟩
              simp [lowerState, values]
      | cons next remaining =>
          cases step with
          | hit _ _ _ _ same =>
              refine
                ⟨.finished sourceTarget (visited ++ next :: remaining)
                    (.found visited.length ()),
                  FiniteOccurrenceLookup.Step.hit sourceTarget visited next
                    remaining same, ?_⟩
              simp [lowerState, values, List.map_append]
          | advance _ _ _ _ different =>
              refine
                ⟨.scanning
                    ⟨sourceTarget, visited ++ [next], remaining⟩,
                  FiniteOccurrenceLookup.Step.advance sourceTarget visited next
                    remaining different, ?_⟩
              simp [lowerState, values, List.map_append]

/-- Exact GSLT-to-GSLT lowering from chronological lookup to the reverse
cursor used by the executable list machine. -/
def lowering (Value : Type) :
    CoveredTranslation (chronologicalGSLT Value) (gslt Value) where
  mapTerm := lowerState
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  cover :=
    { mapStep := lower_step
      liftStep := lift_step }

/-- OSLF-derived native theory of chronological membership. -/
def chronologicalNTT (Value : Type) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (chronologicalGSLT Value)

/-- OSLF-derived native theory of constant-work reverse membership. -/
def membershipNTT (Value : Type) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (gslt Value)

/-- OSLF sends the exact lowering to the native-modal predicate transport. -/
def loweringNTT (Value : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (membershipNTT Value) (chronologicalNTT Value) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
    (lowering Value).toOperational

/-- Possibility transport is exact because the lowering has local step
reflection, not merely forward preservation. -/
theorem lowering_diamond_exact (Value : Type)
    (predicate : Set (State Value)) :
    Set.preimage lowerState (gsltDiamond (gslt Value) predicate) =
      gsltDiamond (chronologicalGSLT Value)
        (Set.preimage lowerState predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    (lowering Value) predicate

/-- Initial reverse-cursor state for one finite list query. -/
def initial (target : Value) (items : List Value) : State Value :=
  .scanning ⟨target, [], items⟩

/-- The existing executable first-occurrence result specialized to unit
payloads agrees with ordinary membership positions. -/
def lookup [DecidableEq Value] (target : Value) (items : List Value) :
    Observation :=
  observation
    (FiniteOccurrenceLookup.lookup target (items.map entry))

private def occurrenceCanary : List Nat := [4, 7, 7, 9]

example : lookup 7 occurrenceCanary = .found 1 := by decide

example : lookup 8 occurrenceCanary = .missing 4 := by decide

/-- Repeated equal members remain distinct occurrences; lookup selects the
first occurrence rather than quotienting the list to a set. -/
example :
    Step (.scanning ⟨7, [4], [7, 7, 9]⟩)
      (.finished 7 ([4].reverse ++ [7, 7, 9]) (.found 1)) := by
  exact Step.hit 7 [4] 7 [7, 9] rfl

#print axioms values_map_entry
#print axioms lower_step
#print axioms lift_step
#print axioms lowering_diamond_exact

end Mettapedia.GSLT.FiniteListMembership
