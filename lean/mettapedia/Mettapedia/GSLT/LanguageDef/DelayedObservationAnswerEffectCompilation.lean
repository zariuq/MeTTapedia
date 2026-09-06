import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

/-!
# Delayed observations inside answer-effect programs

A delayed term observer and an answer-effect interpreter solve independent
problems.  The observer avoids constructing a complete value when a direct
observation is exact.  The answer effect describes zero, choice, and ordered
or unordered answer production.  This module composes those interfaces
without choosing a term representation, evaluator, dialect, or scheduler.

The semantic operation always means materialize-then-observe.  A physical
provider may execute the proved direct observer when its local capability
predicate admits the closure, or decline otherwise.  Decline remains distinct
from semantic zero: the ordinary evaluator must handle the program when the
provider returns `none`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DelayedObservationAnswerEffectCompilation

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

universe u

/-- A response-indexed deterministic operation which observes one closure. -/
inductive ObservationOp (Closure Result : Type) : Type → Type where
  | observe (closure : Closure) : ObservationOp Closure Result Result

/-- Authoritative meaning: construct the complete value, then observe it. -/
def semantics
    {Closure Materialized Result : Type}
    (observation : DelayedObservation Closure Materialized Result) :
    {Response : Type} → ObservationOp Closure Result Response → Response
  | _, .observe closure =>
      observation.observeMaterialized closure (observation.materialize closure)

/-- The direct observation is exactly the authoritative operation meaning. -/
theorem semantics_observe_eq_direct
    {Closure Materialized Result : Type}
    (observation : DelayedObservation Closure Materialized Result)
    (closure : Closure) :
    semantics observation (ObservationOp.observe closure) =
      observation.observeDirect closure := by
  exact (observation.commutes closure).symm

/-- A capability-indexed physical provider.  Admission controls only whether
the optimized operation is available; it cannot change the returned result. -/
def admittedRealizer
    {Closure Materialized Result : Type}
    (observation : DelayedObservation Closure Materialized Result)
    (admitted : Closure → Bool) :
    Realizer (ObservationOp Closure Result) (semantics observation) where
  run?
    | .observe closure =>
        if admitted closure then some (observation.observeDirect closure)
        else none
  sound := by
    intro Response operation response executed
    cases operation with
    | observe closure =>
        simp only at executed
        split at executed
        · injection executed with directEqualsResponse
          rw [← directEqualsResponse]
          exact (semantics_observe_eq_direct observation closure).symm
        · contradiction

@[simp] theorem admittedRealizer_run_of_admitted
    {Closure Materialized Result : Type}
    (observation : DelayedObservation Closure Materialized Result)
    (admitted : Closure → Bool) (closure : Closure)
    (available : admitted closure = true) :
    (admittedRealizer observation admitted).run?
        (ObservationOp.observe closure) =
      some (observation.observeDirect closure) := by
  simp [admittedRealizer, available]

@[simp] theorem admittedRealizer_run_of_declined
    {Closure Materialized Result : Type}
    (observation : DelayedObservation Closure Materialized Result)
    (admitted : Closure → Bool) (closure : Closure)
    (unavailable : admitted closure = false) :
    (admittedRealizer observation admitted).run?
        (ObservationOp.observe closure) = none := by
  simp [admittedRealizer, unavailable]

/-- A delayed Boolean observation controls answer production without becoming
part of the answer-effect semantics itself. -/
def guardedProgram
    {Closure : Type} {Answer : Type u}
    (closure : Closure) (answer : Answer) :
    Program (ObservationOp Closure Bool) Answer :=
  Program.guard (ObservationOp.observe closure) (.pure answer)

/-- When admitted, direct observation executes the guard with the same answer
as materialize-then-observe and reports one deterministic operation. -/
theorem execute_guard_of_admitted
    {Closure Materialized : Type} {Answer : Type u}
    (observation : DelayedObservation Closure Materialized Bool)
    (admitted : Closure → Bool) (closure : Closure) (answer : Answer)
    (available : admitted closure = true) :
    (admittedRealizer observation admitted).executeWithCost?
        listEffect (guardedProgram closure answer) =
      some
        (Program.denote listEffect (semantics observation)
          (guardedProgram closure answer), 1) := by
  cases direct : observation.observeDirect closure <;>
    simp [Realizer.executeWithCost?, guardedProgram, Program.guard,
      admittedRealizer, available, semantics_observe_eq_direct, direct]

/-- Declining an observation whose semantic result is true cannot be
interpreted as an empty answer.  The physical route declines while the
authoritative denotation still contains the answer. -/
theorem declined_true_observation_is_not_zero
    {Closure Materialized : Type} {Answer : Type u}
    (observation : DelayedObservation Closure Materialized Bool)
    (admitted : Closure → Bool) (closure : Closure) (answer : Answer)
    (unavailable : admitted closure = false)
    (accepted : observation.observeDirect closure = true) :
    (admittedRealizer observation admitted).executeWithCost?
        listEffect (guardedProgram closure answer) = none ∧
      Program.denote listEffect (semantics observation)
        (guardedProgram closure answer) = [answer] := by
  constructor
  · simp [Realizer.executeWithCost?, guardedProgram, Program.guard,
      admittedRealizer, unavailable]
  · simp [guardedProgram, Program.denote_guard,
      semantics_observe_eq_direct, accepted, listEffect]

/-! ## Executable controls -/

/-- The complete value deliberately differs from the closure representation;
direct observation returns the parity fact without allocating that value. -/
def oddObservation : DelayedObservation Bool Nat Bool where
  materialize closure := if closure then 7 else 4
  observeMaterialized _ value := value % 2 == 1
  observeDirect closure := closure
  commutes := by
    intro closure
    cases closure <;> decide

def admitTrueOnly : Bool → Bool := id

/-- Positive: an admitted direct observation retains the answer. -/
example :
    (admittedRealizer oddObservation admitTrueOnly).executeWithCost?
        listEffect (guardedProgram true ("answer" : String)) =
      some (["answer"], 1) := by
  rfl

/-- Positive zero: an admitted false observation produces semantic zero. -/
example :
    (admittedRealizer oddObservation (fun _ => true)).executeWithCost?
        listEffect (guardedProgram false ("answer" : String)) =
      some ([], 1) := by
  rfl

/-- Negative boundary: a true but unavailable observation declines; it does
not silently become the empty answer list. -/
example :
    (admittedRealizer oddObservation (fun _ => false)).executeWithCost?
        listEffect (guardedProgram true ("answer" : String)) = none ∧
      Program.denote listEffect (semantics oddObservation)
        (guardedProgram true ("answer" : String)) = ["answer"] := by
  exact declined_true_observation_is_not_zero oddObservation
    (fun _ => false) true "answer" rfl rfl

#print axioms semantics_observe_eq_direct
#print axioms execute_guard_of_admitted
#print axioms declined_true_observation_is_not_zero

end Mettapedia.GSLT.LanguageDef.DelayedObservationAnswerEffectCompilation
