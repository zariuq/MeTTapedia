import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Actual firing runs and the existing operational path interface

The successor theory forgets which admitted firing produced an edge. Its
finite paths have actual runs with the same endpoint and length. Event paths
retain the firing itself and convert back to the original dependent run.
Neither construction enumerates rules, chooses a solver or requires finite
branching. Recovering a successor path supplies a run, not a unique run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Execution

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open LogicOverTheStep.StepSpan FragmentsOfTheStep.TransitionMaps

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- The existing discrete successor theory of the actual admitted step. -/
abbrev theory : GSLT := theoryOf State (Succ P)

/-- Edges are the interface's admitted effects, including their firings. -/
abbrev EventPath (first last : State) :=
  Route (P.toEffectCore.Event P.eventAdmission) first last

def toEvents : {s : State} → (run : P.Run s) → EventPath P s run.last
  | _, .nil s => .refl s
  | _, .cons firing admitted rest => .cons (P.event firing admitted) (toEvents rest)

def prependEvent {s t : State} (edge : P.toEffectCore.Event P.eventAdmission s t)
    (run : P.Run t) : P.Run s := by
  rcases edge with ⟨firing, prepared, admitted, endpoint⟩
  cases endpoint
  exact .cons firing admitted run

theorem prependEvent_last {s t : State} (edge : P.toEffectCore.Event P.eventAdmission s t)
    (run : P.Run t) : (prependEvent P edge run).last = run.last := by
  rcases edge with ⟨firing, prepared, admitted, rfl⟩
  rfl

def fromEvents : {s t : State} → EventPath P s t → {run : P.Run s // run.last = t}
  | _, _, .refl s => ⟨.nil s, rfl⟩
  | _, _, .cons edge rest =>
      let later := fromEvents rest;
      ⟨prependEvent P edge later.1, (prependEvent_last P edge later.1).trans later.2⟩

theorem fromEvents_toEvents {s : State} (run : P.Run s) :
    (fromEvents P (toEvents P run)).1 = run := by
  induction run with
  | nil => rfl
  | cons firing admitted rest ih =>
      change Step.Run.cons firing admitted (fromEvents P (toEvents P rest)).1 = _
      rw [ih]

def eventWord : {s t : State} → EventPath P s t → List ((s : State) × Firing s)
  | _, _, .refl _ => []
  | s, _, .cons edge rest => ⟨s, edge.firing⟩ :: eventWord rest

theorem fromEvents_word {s t : State} (path : EventPath P s t) :
    (fromEvents P path).1.word = eventWord P path := by
  induction path with
  | refl => rfl
  | cons edge rest ih =>
      rcases edge with ⟨firing, prepared, admitted, rfl⟩
      exact congrArg (List.cons _) ih

theorem eventWord_toEvents {s : State} (run : P.Run s) :
    eventWord P (toEvents P run) = run.word := by
  induction run with
  | nil => rfl
  | cons firing admitted rest ih => exact congrArg (List.cons _) ih

def toPath : {s : State} → (run : P.Run s) → ExecutionPath (theory P) s run.last
  | _, .nil s => .refl s
  | _, .cons firing admitted rest =>
      .cons ⟨⟨firing, admitted, rfl⟩⟩ (toPath rest)

theorem toPath_length {s : State} (run : P.Run s) :
    (toPath P run).length = run.word.length := by
  induction run with
  | nil => rfl
  | cons firing admitted rest ih => exact congrArg (· + 1) ih

/-- Recover an actual run from a supplied successor path. Different
firings with the same endpoints are not identified by this assertion. -/
theorem path_has_run {s t : State} (path : ExecutionPath (theory P) s t) :
    ∃ run : P.Run s, run.last = t ∧ run.word.length = path.length := by
  induction path with
  | refl => exact ⟨.nil _, rfl, rfl⟩
  | cons edge rest ih =>
      obtain ⟨firing, admitted, same⟩ := edge.down
      subst same
      obtain ⟨run, endpoint, length⟩ := ih
      exact ⟨.cons firing admitted run, endpoint, congrArg (· + 1) length⟩

theorem multiStep_iff_run {s t : State} :
    (theory P).MultiStep s t ↔ ∃ run : P.Run s, run.last = t := by
  constructor
  · intro steps
    obtain ⟨path⟩ := (executionPath_nonempty_iff_multiStep (theory P) s t).mpr steps
    obtain ⟨run, endpoint, _⟩ := path_has_run P path
    exact ⟨run, endpoint⟩
  · rintro ⟨run, rfl⟩
    exact executionPathToMultiStep (toPath P run)

/-- A readout of a reachable state is a readout of an actual firing run. -/
theorem reachable_iff_run (observes : State → Prop) (s : State) :
    (∃ t, (theory P).MultiStep s t ∧ observes t) ↔
      ∃ run : P.Run s, observes run.last := by
  constructor
  · rintro ⟨t, steps, observed⟩
    obtain ⟨run, rfl⟩ := (multiStep_iff_run P).mp steps
    exact ⟨run, observed⟩
  · rintro ⟨run, observed⟩
    exact ⟨run.last, (multiStep_iff_run P).mpr ⟨run, rfl⟩, observed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Execution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Execution.fromEvents_toEvents
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Execution.path_has_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Execution.reachable_iff_run
