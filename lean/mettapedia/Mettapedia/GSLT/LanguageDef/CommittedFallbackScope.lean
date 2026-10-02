import Mettapedia.GSLT.LanguageDef.CommittedFallbackNative
import Mettapedia.Machines.EquationCut

/-!
# Locality of nested committed queries

Each live query owns one frame. Its cursor includes its pending alternatives
and logical checkpoint; its success marker is not part of that checkpoint.
The performed world belongs to the running stack, not to saved frames.

`Step` describes an excursion above a saved stack height. Queries can enter
other queries, poll their own frame, and return after normal completion.
Faults remain explicit and cannot be silently returned as normal exhaustion.
The stack-height condition is a delimiter, not an assumption that a step
preserves its caller. `excursion_locality` derives that property for arbitrary
finite nesting, including suspension and query faults.

This is a frame/control theorem. It does not establish the ownership or
liveness of pointers in a C realization, nor implement answer consumers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CommittedFallbackScope

open CommittedFallback
open CommittedFallbackNative
open Mettapedia.Machines.EquationCut (trunc)

variable {Cursor Answer World Fault : Type}

/-- Saved query control contains no backtrackable copy of the performed world. -/
structure Frame (Cursor Answer Fault : Type) where
  cursor : Option Cursor
  useFallback : Bool
  succeeded : Bool
  error : Option Fault
  answers : List Answer
  deriving DecidableEq, Repr

def Frame.withWorld (frame : Frame Cursor Answer Fault) (world : World) :
    Native Cursor Answer World Fault :=
  ⟨frame.cursor, frame.useFallback, frame.succeeded, frame.error, world, frame.answers⟩

def frameOf (native : Native Cursor Answer World Fault) : Frame Cursor Answer Fault :=
  ⟨native.cursor, native.useFallback, native.succeeded, native.error, native.answers⟩

@[simp] theorem frameOf_withWorld (frame : Frame Cursor Answer Fault) (world : World) :
    frameOf (frame.withWorld world) = frame := by cases frame; rfl

@[simp] theorem withWorld_frameOf (native : Native Cursor Answer World Fault) :
    (frameOf native).withWorld native.world = native := by cases native; rfl

structure Stack (Cursor Answer World Fault : Type) where
  frames : List (Frame Cursor Answer Fault)
  world : World
  deriving DecidableEq, Repr

def enter (cursor : Cursor) (stack : Stack Cursor Answer World Fault) :
    Stack Cursor Answer World Fault :=
  ⟨⟨some cursor, false, false, none, []⟩ :: stack.frames, stack.world⟩

/-- Only the currently active query is polled. The saved frames are not
passed to the provider, so their markers cannot be updated by an inner poll. -/
def poll (queries : Queries Cursor Answer World Fault) :
    Stack Cursor Answer World Fault → Option (Stack Cursor Answer World Fault)
  | ⟨[], _⟩ => none
  | ⟨active :: callers, world⟩ =>
      (next queries (active.withWorld world)).map fun native =>
        ⟨frameOf native :: callers, native.world⟩

/-- Completion returns the inner query's occurrences, without assigning them
to its caller's cursor or rolling back the world. Faults do not take this path. -/
def leave : Stack Cursor Answer World Fault →
    Option (List Answer × Stack Cursor Answer World Fault)
  | ⟨⟨none, false, false, none, answers⟩ :: callers, world⟩ =>
      some (answers, ⟨callers, world⟩)
  | _ => none

inductive Step (queries : Queries Cursor Answer World Fault) (barrier : Nat) :
    Stack Cursor Answer World Fault → Stack Cursor Answer World Fault → Prop where
  | enter (cursor : Cursor) (stack : Stack Cursor Answer World Fault) :
      Step queries barrier stack (enter cursor stack)
  | poll {stack nextStack} : barrier < stack.frames.length →
      poll queries stack = some nextStack → Step queries barrier stack nextStack
  | leave {stack nextStack answers} : barrier < stack.frames.length →
      leave stack = some (answers, nextStack) → Step queries barrier stack nextStack

abbrev Reaches (queries : Queries Cursor Answer World Fault) (barrier : Nat) :=
  Relation.ReflTransGen (Step queries barrier)

theorem poll_callers {queries : Queries Cursor Answer World Fault}
    {active : Frame Cursor Answer Fault} {callers : List (Frame Cursor Answer Fault)}
    {world : World} {result : Stack Cursor Answer World Fault}
    (polled : poll queries ⟨active :: callers, world⟩ = some result) :
    ∃ active', result.frames = active' :: callers := by
  unfold poll at polled
  cases response : next queries (active.withWorld world) with
  | none => simp [response] at polled
  | some native =>
      simp only [response, Option.map_some, Option.some.injEq] at polled
      subst result
      exact ⟨frameOf native, rfl⟩

theorem leave_callers {active : Frame Cursor Answer Fault}
    {callers : List (Frame Cursor Answer Fault)} {world : World}
    {result : Stack Cursor Answer World Fault} {answers : List Answer}
    (returned : leave ⟨active :: callers, world⟩ = some (answers, result)) :
    result = ⟨callers, world⟩ := by
  rcases active with ⟨cursor, useFallback, succeeded, error, trace⟩
  cases cursor <;> cases useFallback <;> cases succeeded <;> cases error <;>
    simp [leave] at returned
  exact returned.2.symm

theorem leave_world {stack result : Stack Cursor Answer World Fault} {answers : List Answer}
    (returned : leave stack = some (answers, result)) : result.world = stack.world := by
  rcases stack with ⟨frames, world⟩
  cases frames with
  | nil => simp [leave] at returned
  | cons active callers => rw [leave_callers returned]

/-- A nested step retains every older marker, cursor, checkpoint and ordered
alternative, not merely an equal set of eventual answers. -/
theorem Step.locality {queries : Queries Cursor Answer World Fault} {barrier : Nat}
    {stack result : Stack Cursor Answer World Fault} (step : Step queries barrier stack result)
    (bounded : barrier ≤ stack.frames.length) :
    barrier ≤ result.frames.length ∧ trunc barrier result.frames = trunc barrier stack.frames := by
  cases step with
  | enter cursor stack =>
      constructor
      · simp only [CommittedFallbackScope.enter, List.length_cons]; omega
      · exact Mettapedia.Machines.EquationCut.trunc_cons _ bounded
  | poll above polled =>
      rcases stack with ⟨frames, world⟩
      cases frames with
      | nil => simp at above
      | cons active callers =>
          obtain ⟨active', unchanged⟩ := poll_callers polled
          rw [unchanged]
          constructor
          · simpa only [List.length_cons] using bounded
          · have bound : barrier ≤ callers.length := by simp only [List.length_cons] at above; omega
            rw [Mettapedia.Machines.EquationCut.trunc_cons _ bound,
              Mettapedia.Machines.EquationCut.trunc_cons _ bound]
  | leave above returned =>
      rcases stack with ⟨frames, world⟩
      cases frames with
      | nil => simp at above
      | cons active callers =>
          have bound : barrier ≤ callers.length := by simp only [List.length_cons] at above; omega
          rw [leave_callers returned]
          exact ⟨bound, (Mettapedia.Machines.EquationCut.trunc_cons active bound).symm⟩

theorem excursion_locality {queries : Queries Cursor Answer World Fault} {barrier : Nat}
    {stack result : Stack Cursor Answer World Fault}
    (route : Reaches queries barrier stack result) (bounded : barrier ≤ stack.frames.length) :
    barrier ≤ result.frames.length ∧ trunc barrier result.frames = trunc barrier stack.frames := by
  induction route with
  | refl => exact ⟨bounded, rfl⟩
  | tail _ step ih =>
      obtain ⟨bound, unchanged⟩ := step.locality ih.1
      exact ⟨bound, unchanged.trans ih.2⟩

/-- Returning all the way to the delimiter restores the actual saved frames. -/
theorem excursion_returns_saved_frames {queries : Queries Cursor Answer World Fault}
    (saved nested : List (Frame Cursor Answer Fault)) {world : World}
    {result : Stack Cursor Answer World Fault}
    (route : Reaches queries saved.length ⟨nested ++ saved, world⟩ result)
    (returned : result.frames.length = saved.length) : result.frames = saved := by
  have locality := excursion_locality route (by simp)
  have initial : trunc saved.length (nested ++ saved) = saved := by simp [trunc]
  have final : trunc saved.length result.frames = result.frames := by
    rw [← returned, Mettapedia.Machines.EquationCut.trunc_length]
  have unchanged : trunc saved.length result.frames = trunc saved.length (nested ++ saved) :=
    locality.2
  rw [final, initial] at unchanged
  exact unchanged

def committedFrame (cursor : Cursor) (answers : List Answer) : Frame Cursor Answer Fault :=
  ⟨some cursor, false, true, none, answers⟩

/-- Inner work cannot re-open an outer committed query on resumption. The
resumed query receives the final performed world, not its entry world. -/
theorem outer_commit_survives {queries : Queries Cursor Answer World Fault}
    (cursor : Cursor) (answers : List Answer) (older nested : List (Frame Cursor Answer Fault))
    {world : World} {result : Stack Cursor Answer World Fault}
    (route : Reaches queries (older.length + 1)
      ⟨nested ++ committedFrame cursor answers :: older, world⟩ result)
    (returned : result.frames.length = older.length + 1)
    {finish : State Cursor Answer World Fault}
    (resumed : Relation.ReflTransGen (TargetStep queries)
      ((committedFrame cursor answers).withWorld result.world) (encode finish)) :
    result.frames = committedFrame cursor answers :: older ∧ ¬ IsFallback finish.phase := by
  constructor
  · apply excursion_returns_saved_frames _ nested route
    simpa using returned
  · exact native_committed_never_fallback resumed

namespace Controls

open CommittedFallbackNative.Controls (listQueries run)

def outer : Stack (List Nat) Nat Nat String :=
  ⟨[committedFrame [] [7]], 1⟩

def completedInner : Stack (List Nat) Nat Nat String :=
  ⟨[frameOf (run listQueries 3 (encode ⟨.probing [3, 3], 1, []⟩)),
    committedFrame [] [7]], 4⟩

private def control (phase : Phase (List Nat) String) (answers : List Nat) :
    Frame (List Nat) Nat String := frameOf (encode ⟨phase, (), answers⟩)

/-- Two actual nested queries run and return through the stack operations.
All five inner polls remain in the world, while the outer choice is untouched. -/
theorem two_nested_queries_return_to_the_saved_choice :
    Reaches listQueries 1 outer ⟨[committedFrame [] [7]], 6⟩ := by
  let saved : List (Frame (List Nat) Nat String) := [committedFrame [] [7]]
  let first := control (.probing [3, 3]) []
  let middle : Stack (List Nat) Nat Nat String := ⟨first :: saved, 1⟩
  let deep := enter [4] middle
  let yielded : Stack (List Nat) Nat Nat String :=
    ⟨control (.committed []) [4] :: first :: saved, 2⟩
  let finished : Stack (List Nat) Nat Nat String :=
    ⟨control .done [4] :: first :: saved, 3⟩
  let returned : Stack (List Nat) Nat Nat String := ⟨first :: saved, 3⟩
  let firstYield : Stack (List Nat) Nat Nat String :=
    ⟨control (.committed [3]) [3] :: saved, 4⟩
  let secondYield : Stack (List Nat) Nat Nat String :=
    ⟨control (.committed []) [3, 3] :: saved, 5⟩
  let firstFinished : Stack (List Nat) Nat Nat String :=
    ⟨control .done [3, 3] :: saved, 6⟩
  have started : Reaches listQueries 1 outer middle :=
    Relation.ReflTransGen.single (.enter [3, 3] outer)
  have entered : Reaches listQueries 1 outer deep := started.tail (.enter [4] middle)
  have delivered : Reaches listQueries 1 outer yielded :=
    entered.tail (.poll (by decide) (by decide))
  have completed : Reaches listQueries 1 outer finished :=
    delivered.tail (.poll (by decide) (by decide))
  have back : Reaches listQueries 1 outer returned :=
    completed.tail (.leave (answers := [4]) (by decide) (by decide))
  have deliveredFirst : Reaches listQueries 1 outer firstYield :=
    back.tail (.poll (by decide) (by decide))
  have deliveredSecond : Reaches listQueries 1 outer secondYield :=
    deliveredFirst.tail (.poll (by decide) (by decide))
  have completedFirst : Reaches listQueries 1 outer firstFinished :=
    deliveredSecond.tail (.poll (by decide) (by decide))
  exact completedFirst.tail (.leave (answers := [3, 3]) (by decide) (by decide))

theorem returning_inner_retains_duplicates_marker_and_world :
    leave completedInner = some ([3, 3], ⟨[committedFrame [] [7]], 4⟩) := by decide

theorem restored_outer_does_not_fall_back :
    (run listQueries 3 ((committedFrame (Fault := String) [] [7]).withWorld 4)).answers = [7] :=
  by decide

/-- A trail restore that clears the caller's marker invents a fallback answer. -/
theorem restoring_a_backtrackable_marker_is_wrong :
    (run listQueries 3 { (committedFrame (Fault := String) [] [7]).withWorld 4 with
      succeeded := false }).answers = [7, 99] := by decide

theorem copying_an_inner_cursor_loses_outer_alternatives :
    (run listQueries 2 ((committedFrame (Fault := String) [8] [7]).withWorld 4)).answers = [7, 8] ∧
    (run listQueries 2 ((committedFrame (Fault := String) [] [7]).withWorld 4)).answers = [7] :=
  by decide

theorem a_fault_cannot_return_as_normal_completion :
    leave (⟨[⟨none, false, false, some "inner fault", []⟩,
      committedFrame [] [7]], 4⟩ : Stack (List Nat) Nat Nat String) = none := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.CommittedFallbackScope
