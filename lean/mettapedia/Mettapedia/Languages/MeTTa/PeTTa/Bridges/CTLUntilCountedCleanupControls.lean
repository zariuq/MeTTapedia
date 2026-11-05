import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup

/-! Duplicate producer counts, round/label separation, exact copy capacity,
and allocation handoff after live removal effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open CountedSourceEntry (Input)
open CTLUntilMixedStore (Row render)
open CTLUntilSourceRows (number)

def rows : List (Row Int) := [.frontier 10 0 1, .frontier 10 0 1, .frontier 10 0 2,
  .frontier 10 1 3, .frontier 20 0 4, .edge 1 2]
def kept : List (Row Int) := [.frontier 10 1 3, .frontier 20 0 4, .edge 1 2]
def atoms := rows.map (render FlatQueryRowCodec.integers)

def input (capacity : Nat) : Input Unit := {
  program := {equations := [], declarations := []}
  state := {
    allocator := Allocator.empty capacity 8
    world := ⟨NamedSpaces.Store.new atoms [], [], []⟩
    scope := ⟨[], [], none⟩, parents := [] }
  caller := {bindings := [(.var "f", number 10), (.var "k", number 0)], goals := [], destination := .var "answer"}
  context := (), origins := [9], pending := [], destination := .var "answer"
  body := body .self "f" "k" "x" }

def sourceRun (input : Input Unit) := (ScopedQuerySource.machine .relational input.program).run 100 input.before
def sourceRows (input : Input Unit) :=
  (EagerDFSStreaming.Scoped.readback (sourceRun input).2).bind fun cursor => cursor.2.world.state.read .self
def allocationStopped (input : Input Unit) : Bool := match (sourceRun input).2 with
  | .suspended .allocation _ => true
  | _ => false

#guard (sourceRun (input 3)).1.map CollectedAnswer.value == [number 3]
#guard sourceRows (input 3) == some (kept.map (render FlatQueryRowCodec.integers))
#guard (childExecution (input 0) .self "f" "k" "x").events.isEmpty
#guard allocationStopped (input 2)
#guard (sourceRun (input 2)).1.isEmpty
#guard sourceRows (input 2) == sourceRows (input 3)

def empty : Input Unit := {input 0 with state := {(input 0).state with
  world := ⟨NamedSpaces.Store.new (kept.map (render FlatQueryRowCodec.integers)) [], [], []⟩}}
#guard (sourceRun empty).1.map CollectedAnswer.value == [number 0]
#guard !allocationStopped empty

theorem producer_count_is_not_distinct_count :
    (rows.filterMap (CTLUntilMixedStore.frontSelect 10 0)).length = 3 ∧
      (rows.filterMap (CTLUntilMixedStore.frontSelect 10 0)).toFinset.card = 2 := by decide +kernel

theorem wrong_round_changes_cleanup :
    CTLUntilCleanup.remaining 10 0 rows ≠ CTLUntilCleanup.remaining 10 1 rows := by decide +kernel

def namedProgram : SpaceSemantics.Program := {
  equations := [⟨"drop", [.var "f", .var "k"], CTLUntilNamedCleanup.source .self "f" "k" "x"⟩]
  declarations := [] }
def namedRun (capacity : Nat) (arguments : List Atom) :=
  (ScopedQuerySource.machine .relational namedProgram).run 120
    (ScopedMatchEntry.entrance (.expression (.symbol "drop" :: arguments)) (.var "answer")
      (input capacity).caller (input capacity).state () [9] [])

#guard (namedRun 3 [number 10, number 0]).1.map CollectedAnswer.value == [number 3]
#guard ((EagerDFSStreaming.Scoped.readback (namedRun 3 [number 10, number 0]).2).bind
  fun cursor => cursor.2.world.state.read .self) == some (kept.map (render FlatQueryRowCodec.integers))
#guard (match (namedRun 2 [number 10, number 0]).2 with
  | .suspended .allocation _ => true
  | _ => false)
#guard (namedRun 3 [number 10, number 0, number 1]).1.map CollectedAnswer.value != [number 3]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup.Controls
