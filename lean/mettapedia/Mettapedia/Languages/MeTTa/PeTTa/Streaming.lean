import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
import Mettapedia.Data.List.FirstSelection

/-!
# Streaming source continuations over the existing unifying phases

Alternatives retain their own controls and return continuations, while effects,
input, output and the allocation supply belong to one shared world. Collection,
first demand and runtime exception scopes have distinct closing markers.
Returning from a call does not put the caller inside the callee's handler.

Unifying.step supplies the existing primitive and dispatch phases. This module
changes their control composition; it does not claim equal schedules with the
completed-operand profile or full SWI translator adequacy. In particular,
functional-pattern preparation and backward output constraints are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Unifying (Answer Control)

/-- The actual source world's fields, shared by all pending alternatives. -/
structure World where
  state : Effects.State
  input : List Atom := []
  output : List Atom := []
  uses : Nat := 0
  privateCode : List SpaceSemantics.Equation := []

def World.configuration (world : World) (control : Control)
    (frames : List Unifying.Frame := []) : Unifying.Configuration :=
  {state := world.state,control,frames,input := world.input,output := world.output,
    uses := world.uses,privateCode := world.privateCode}

def World.fromConfiguration (configuration : Unifying.Configuration) : World :=
  ⟨configuration.state,configuration.input,configuration.output,configuration.uses,configuration.privateCode⟩

inductive Frame where
  | source (frame : Unifying.Frame)
  | collection (key : Nat)
  | handler (key : Nat)
  | first (key : Nat)

structure Task where
  control : Control
  frames : List Frame := []

inductive Job where
  | execute (task : Task)
  | collect (key : Nat) (bindings : Subst) (caller : List Frame) (answers : List Answer)
  | handler (key : Nat)
  | first (key : Nat)

structure State where
  world : World
  agenda : List Job
  answers : List Answer := []
  nextBoundary : Nat := 0

def handlerMarker (key : Nat) : Job → Bool
  | .handler found => found == key
  | _ => false

def firstMarker (key : Nat) : Job → Bool
  | .first found => found == key
  | _ => false

/-- The accumulator lives in its closing marker, so cutting a scope also
releases its private collection. No independent receipt table is maintained. -/
def collectionChange (key : Nat) (answer : Answer) : Job → Option Job
  | .collect found bindings caller answers =>
      if found == key then some (.collect found bindings caller (answers ++ [answer])) else none
  | _ => none

def collectAnswer (key : Nat) (answer : Answer) (agenda : List Job) : Option (List Job) :=
  List.FirstSelection.change? (collectionChange key answer) agenda

def nearestHandler : List Frame → Option Nat
  | [] => none
  | .handler key :: _ => some key
  | _ :: rest => nearestHandler rest

def openCollection (state : State) (bindings : Subst) (control : Control)
    (caller : List Frame) (older : List Job) : State :=
  {state with
    agenda := .execute ⟨control,.collection state.nextBoundary :: caller⟩ ::
      .collect state.nextBoundary bindings caller [] :: older
    nextBoundary := state.nextBoundary + 1}

def openHandler (state : State) (control : Control)
    (caller : List Frame) (older : List Job) : State :=
  {state with
    agenda := .execute ⟨control,.handler state.nextBoundary :: caller⟩ ::
      .handler state.nextBoundary :: older
    nextBoundary := state.nextBoundary + 1}

def openFirst (state : State) (control : Control)
    (caller : List Frame) (older : List Job) : State :=
  {state with
    agenda := .execute ⟨control,.first state.nextBoundary :: caller⟩ ::
      .first state.nextBoundary :: older
    nextBoundary := state.nextBoundary + 1}

/-- Import one existing source phase, including its actually reached world.
The ordinary source phase produces at most one waiting frame. Old batched
sequence frames are not silently interpreted as streaming continuations. -/
def enqueuePhase (state : State) (after : Unifying.Configuration)
    (caller : List Frame) (older : List Job) : Option State :=
  let reached := {state with world := World.fromConfiguration after}
  match after.frames with
  | [] => some {reached with agenda := .execute ⟨after.control,caller⟩ :: older}
  | [.collect bindings] => some (openCollection reached bindings after.control caller older)
  | [.dynamicCall] => some (openHandler reached after.control caller older)
  | [.sequence _ _] => none
  | [frame] => some {reached with agenda := .execute ⟨after.control,.source frame :: caller⟩ :: older}
  | _ => none

def laterAnswers (answers : List Answer) (frames : List Frame) (older : List Job) : List Job :=
  match answers with
  | [] => older
  | _ => .execute ⟨.returned answers,frames⟩ :: older

/-- One returned packet runs its continuation before any remaining packet.
Only a collection marker accumulates answers without continuing its caller. -/
def returnAnswer (registry : SpaceSemantics.Program) (state : State)
    (answer : Answer) (frames : List Frame) (older : List Job) : Option State :=
  match frames with
  | [] => some {state with agenda := older,answers := state.answers ++ [answer]}
  | .source frame :: caller => do
      let after ← Unifying.step registry (state.world.configuration (.returned [answer]) [frame])
      enqueuePhase state after caller older
  | .collection key :: _ =>
      (collectAnswer key answer older).map fun agenda => {state with agenda}
  | .handler _ :: caller =>
      some {state with agenda := .execute ⟨.returned [answer],caller⟩ :: older}
  | .first key :: caller =>
      (List.FirstSelection.after? (firstMarker key) older).map fun remaining =>
        {state with agenda := .execute ⟨.returned [answer],caller⟩ :: remaining}

def step (registry : SpaceSemantics.Program) (state : State) : Option State :=
  match state.agenda with
  | [] => none
  | .collect _ bindings caller answers :: older =>
      some {state with
        world := {state.world with uses := state.world.uses + answers.length}
        agenda := .execute ⟨.returned
          [⟨.expression (Unifying.copies state.world.uses answers),bindings⟩],caller⟩ :: older}
  | .handler _ :: older | .first _ :: older => some {state with agenda := older}
  | .execute task :: older =>
      match task.control with
      | .returned [] => some {state with agenda := older}
      | .returned (answer :: answers) =>
          returnAnswer registry state answer task.frames (laterAnswers answers task.frames older)
      | .sequence controls answers =>
          some {state with
            agenda := laterAnswers answers task.frames
              ((controls.map fun control => .execute ⟨control,task.frames⟩) ++ older)}
      | .evaluate bindings (.expression [.symbol "collapse",expression]) =>
          some (openCollection state bindings (.evaluate bindings expression) task.frames older)
      | .evaluate bindings (.expression [.symbol "once",expression]) =>
          some (openFirst state (.evaluate bindings expression) task.frames older)
      | .fault _ => do
          let key ← nearestHandler task.frames
          let remaining ← List.FirstSelection.after? (handlerMarker key) older
          some {state with agenda := remaining}
      | _ => do
          let after ← Unifying.step registry (state.world.configuration task.control)
          enqueuePhase state after task.frames older

/-- The complete paid residual, including pending alternatives and markers. -/
def advance (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) : State :=
  Mettapedia.Machines.BoundedDeterministicRun.run (step registry) fuel state

inductive Outcome where
  | complete (state : State)
  | suspended (state : State)
  | fault (reason : Effects.Fault) (state : State)

def observe (state : State) : Outcome :=
  match state.agenda with
  | [] => .complete state
  | .execute ⟨.fault reason,frames⟩ :: _ =>
      if (nearestHandler frames).isNone then .fault reason state else .suspended state
  | _ => .suspended state

def run (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) : Outcome :=
  observe (advance registry fuel state)

/-- A fresh request shares the reached world and allocates its source scope.
Closing an earlier request is required before calling this entry operation. -/
def enter (world : World) (expression : Atom) : State :=
  {world := {world with uses := world.uses + 1},
   agenda := [.execute ⟨.evaluate [] (Unifying.rename world.uses expression),[]⟩]}

def values (state : State) : List Atom :=
  state.answers.map fun answer => Unifying.resolve answer.bindings answer.value

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
