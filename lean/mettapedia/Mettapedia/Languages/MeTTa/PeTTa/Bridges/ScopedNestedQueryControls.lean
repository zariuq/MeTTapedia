import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource

/-! Complete nested source prefixes, changing query worlds, duplicate rows,
late reference handoff and resource suspension. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ScopedQuerySource.Controls (call number)

def template : GuardedNestedQuerySource.Template := {
  formulaName := "f", nodeName := "x", satisfactionHandle := .self
  body := ⟨"answer", "ignored", .self, call "sat" [.var "f", .var "x"],
    call "fr" [.var "f", .var "k1", .var "x"]⟩ }
def request := CTLUntilPublicationSource.request FlatQueryRowCodec.integers .self 10 1
def program : SpaceSemantics.Program := {equations := [NamedPresenceSource.declaration request], declarations := []}
def caller : Control := {
  bindings := [(.var "f", number 10), (.var "a", number 20), (.var "k", number 0), (.var "k1", number 1)]
  goals := [], destination := .var "answer" }
def initial : State Unit := {
  allocator := Allocator.empty 32 8
  world := ⟨NamedSpaces.Store.new CTLUntilMixedStore.Controls.atoms [], [], []⟩
  scope := ⟨[], [], none⟩, parents := [] }
def legs : List NestedQuerySource.Leg := [
  (.self, call "fr" [.var "f", .var "k", .var "y"]),
  (.self, call "rt" [.var "y", .var "x"]),
  (.self, call "sat" [.var "a", .var "x"])]
def execute (plan : List NestedQuerySource.Leg) (proposal : GuardedNestedQuerySource.Template)
    (state : State Unit) := run program (GuardedNestedQuerySource.leaf program proposal Unit) plan caller state () [9] []
def reference (plan : List NestedQuerySource.Leg) (proposal : GuardedNestedQuerySource.Template)
    (state : State Unit) (budget : Nat) :=
  (ScopedQuerySource.machine .relational program).run budget
    (ScopedMatchEntry.entrance (source plan proposal.source) (.var proposal.body.result) caller state () [9] [])
def saved (execution : Execution Unit) := EagerDFSStreaming.Scoped.readback (execution.observation []).2
def rows (execution : Execution Unit) := (saved execution).bind (fun cursor => cursor.2.world.state.read .self)
def completed (execution : Execution Unit) : Bool := match execution.stop with
  | .complete _ => true
  | _ => false
def packet (answer : CollectedAnswer) := (answer.value, answer.bindings, answer.occurrences, answer.associated)

def full := execute legs template initial
def fullReference := reference legs template initial full.budget
#guard completed full
#guard full.budget == 285
#guard full.events.map CollectedAnswer.value == [Effects.boolean true]
#guard fullReference.1.map packet == full.events.map packet
#guard rows full == some (CTLUntilMixedStore.Controls.atoms ++
  [call "sat" [number 10, number 1], call "fr" [number 10, number 1, number 1]])
#guard full.events.map (fun answer => answer.occurrences.take 4) == [[9, 1, 3, 2]]

def noCopy := execute legs template {initial with allocator := Allocator.empty 0 8}
def stoppedCopy : Bool := match noCopy.stop with
  | .suspended .allocation _ => true
  | _ => false
#guard stoppedCopy
#guard noCopy.events.map CollectedAnswer.value == [Effects.boolean true]
#guard rows noCopy == rows full

def collecting : State Unit := {initial with
  scope := ⟨[], [], some ({bindings := [], goals := [], destination := .var "outer"}, .var "outer", (), [])⟩
  parents := [⟨[], [], none⟩] }
def localRun := execute legs template collecting
#guard completed localRun
#guard localRun.events.isEmpty
#guard (saved localRun).map (fun cursor => cursor.2.scopes.head?.map
  (fun scope => scope.collected.map CollectedAnswer.value)) == some (some [Effects.boolean true])

-- The second inner query sees the first one's new row. Within either query,
-- its already captured worklist does not grow from its own publication.
def seeds : List Atom := [call "seed" [], call "seed" [], call "fr" [number 10, number 0, number 1]]
def changingTemplate : GuardedNestedQuerySource.Template := {template with
  body := {template.body with secondCode := call "fr" [.var "f", number 1, number 2]}}
def changingState : State Unit := {initial with world := ⟨NamedSpaces.Store.new seeds [], [], []⟩}
def changingLegs : List NestedQuerySource.Leg := [(.self, call "seed" []), (.self, call "fr" [.var "f", .var "round", .var "x"])]
def changing := execute changingLegs changingTemplate changingState
def changingReference := reference changingLegs changingTemplate changingState changing.budget
#guard completed changing
#guard changing.budget == 123
#guard changing.events.map CollectedAnswer.value == [Effects.boolean true, Effects.boolean true]
#guard changingReference.1.map packet == changing.events.map packet
#guard rows changing == some (seeds ++ [call "sat" [number 10, number 1], call "fr" [number 10, number 1, number 2],
  call "sat" [number 10, number 2], call "fr" [number 10, number 1, number 2]])
#guard changing.events.map (fun answer => answer.occurrences.take 3) == [[9, 0, 2], [9, 1, 4]]

def frozenCandidates := (FlatQueryRelationCompilation.sourceScan [] (call "seed" []) 0 seeds).flatMap fun _ =>
  (FlatQueryRelationCompilation.sourceScan [] (call "fr" [number 10, .var "round", .var "x"]) 0 seeds).map
    (fun row => Mettapedia.Languages.ProcessCalculi.MORK.applySubst row.2 (.var "x"))
#guard frozenCandidates == [number 1, number 1]
#guard frozenCandidates.eraseDups.length == 1
#guard changing.events.length == 2

-- A captured payload that is not the actual guard key must decline. Earlier
-- effects stay committed, and reference continuation must not repeat them.
def jobs := [call "job" [number 1, call "sat" [number 10, number 1]],
  call "job" [number 2, call "different-key" []]]
def payloadTemplate : GuardedNestedQuerySource.Template := {template with
  body := {template.body with firstCode := .var "payload"}}
def jobsState : State Unit := {initial with world := ⟨NamedSpaces.Store.new jobs [], [], []⟩}
def jobLegs : List NestedQuerySource.Leg := [(.self, call "job" [.var "x", .var "payload"])]
def late := execute jobLegs payloadTemplate jobsState
def lateSaved : Option (ScopedCursor Unit) := match late.stop with
  | .reference cursor => some cursor
  | _ => none
#guard lateSaved.isSome
#guard late.budget == 44
#guard late.events.map CollectedAnswer.value == [Effects.boolean true]
#guard rows late == some (jobs ++ [call "sat" [number 10, number 1], call "fr" [number 10, number 1, number 1]])
def resumedLate := lateSaved.map (fun cursor => (ScopedQuerySource.machine .relational program).run 200 cursor)
#guard resumedLate.map (fun result => (late.events ++ result.1).map CollectedAnswer.value) ==
  some [Effects.boolean true, Effects.boolean true]
#guard (resumedLate.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun cursor => cursor.2.world.state.read .self) ==
  some (jobs ++ [call "sat" [number 10, number 1], call "fr" [number 10, number 1, number 1],
    call "different-key" [], call "fr" [number 10, number 1, number 2]])

-- A relevant open row causes handoff after the handle has been prepared.
def openState : State Unit := {initial with world := ⟨NamedSpaces.Store.new
  (CTLUntilMixedStore.Controls.atoms ++ [call "rt" [number 2, .var "open"]]) [], [], []⟩}
def openRun := execute legs template openState
def openHandoff : Bool := match openRun.stop with
  | .reference cursor => match cursor.2.scopes.head?.bind (fun scope => scope.frontier.head?) with
    | some (control, _, _) => match control.goals.head? with
      | some (.invoke "match" _ _) => true
      | _ => false
    | none => false
  | _ => false
#guard openHandoff
#guard openRun.budget == 7
#guard openRun.events.isEmpty
#guard rows openRun == openState.world.state.read .self

-- A missing later query target retains all earlier preparation/capture work.
def missingLegs : List NestedQuerySource.Leg := [(.self, call "fr" [.var "f", .var "k", .var "y"]),
  (.privateSpace 99, call "rt" [.var "y", .var "x"])]
def missing := execute missingLegs template initial
#guard missing.budget == 7
#guard !completed missing
#guard missing.events.isEmpty

#print axioms ScopedMatchEntry.execute_exact
#print axioms ScopedNestedQueryExecution.visit_exact
#print axioms GuardedNestedQuerySource.run_exact
#print axioms ScopedNestedQueryExecution.reached_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution.Controls
