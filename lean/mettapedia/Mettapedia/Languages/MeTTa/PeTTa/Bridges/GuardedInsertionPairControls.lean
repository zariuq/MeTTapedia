import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSourceControls

/-! Fresh-event counts, retained candidate occurrences, dynamic membership
and a copy refusal after an earlier candidate has already published effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number program)
open CapturedOnceSource.Controls (request raw frame)

def second : Atom := call "fr" [.var "tag", number 1, .var "captured_node_name"]
def secondValue : Atom := call "fr" [number 1, number 1, number 7]
def caller : Control := {bindings := (frame 7).bindings, goals := [], destination := .var "answer"}
def work : Control := entry caller "answer" (request 7) .self "ignored" raw second

def execute (capacity : Nat) (facts : List Atom) (candidates : Nat := 1) (fuel : Nat := 200) :=
  let frontier : List (CollectionWork Unit) := (List.range candidates).map fun index => (work, (), [index])
  (ScopedQuerySource.machine .relational program).run fuel
    (Allocator.empty capacity 8, ⟨⟨NamedSpaces.Store.new facts [], [], []⟩, [⟨frontier, [], none⟩]⟩)

def finalRows (capacity : Nat) (facts : List Atom) (candidates : Nat := 1) (fuel : Nat := 200) :=
  (EagerDFSStreaming.Scoped.readback (execute capacity facts candidates fuel).2).bind
    fun saved => saved.2.world.state.read .self

def complete (capacity : Nat) (facts : List Atom) (candidates : Nat := 1) : Bool :=
  match (execute capacity facts candidates).2 with
  | .finished _ => true
  | _ => false

#guard (execute 8 [] 1 32).1.isEmpty
#guard (execute 8 [] 1 33).1.map CollectedAnswer.value == [Effects.boolean true]
#guard finalRows 8 [] == some [(request 7).pattern, secondValue]
#guard (execute 8 [(request 7).pattern] 1 24).1.isEmpty
#guard finalRows 8 [(request 7).pattern] == some [(request 7).pattern]
#guard complete 8 [(request 7).pattern]

-- A second captured candidate observes the first candidate's insertion.
#guard (execute 8 [] 2).1.map CollectedAnswer.value == [Effects.boolean true]
#guard finalRows 8 [] 2 == some [(request 7).pattern, secondValue]
#guard complete 8 [] 2

-- Absence needs no witness copy; a later held candidate does.
#guard complete 0 []
def laterCopyRefused : Bool := match (execute 0 [] 2).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard laterCopyRefused
#guard (execute 0 [] 2).1.map CollectedAnswer.value == [Effects.boolean true]
#guard finalRows 0 [] 2 == some [(request 7).pattern, secondValue]
#guard !complete 0 [] 2

def heldCopyRefused : Bool := match (execute 0 [(request 7).pattern]).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard heldCopyRefused
#guard !complete 0 [(request 7).pattern]

def paused := EagerDFSStreaming.Scoped.readback (execute 8 [] 2 27).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 200 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some [(request 7).pattern, secondValue]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]

namespace SeparateSpaces

def request : LiteralQuerySource.Request := {(CapturedOnceSource.Controls.request 7) with handle := .privateSpace 0}
def sentinel : Atom := .symbol "outside"
def initial : Effects.State :=
  (((NamedSpaces.Store.new [sentinel, request.pattern] [] : Effects.State).allocate []).2.allocate []).2

def execute (state : Effects.State := initial) (target : NamedSpaces.Handle := .privateSpace 1) (fuel : Nat := 200) :=
  (ScopedQuerySource.machine .relational program).run fuel
    (Allocator.empty 8 8, ⟨⟨state, [], []⟩,
      [(⟨[(entry caller "answer" request target "ignored" raw second, (), [3])], [], none⟩ : CollectionScope Unit)]⟩)

def finalState (state : Effects.State := initial) (target : NamedSpaces.Handle := .privateSpace 1) (fuel : Nat := 200) :=
  (EagerDFSStreaming.Scoped.readback (execute state target fuel).2).map (fun saved => saved.2.world.state)

-- A row in &self is not a witness for the private satisfaction space.
#guard (execute initial).1.map CollectedAnswer.value == [Effects.boolean true]
#guard (finalState initial).bind (fun state => state.read (.privateSpace 0)) == some [request.pattern]
#guard (finalState initial).bind (fun state => state.read (.privateSpace 1)) == some [secondValue]
#guard (finalState initial).bind (fun state => state.read .self) == some [sentinel, request.pattern]

def held : Effects.State := (initial.write (.privateSpace 0) [request.pattern]).getD initial
#guard (execute held).1.isEmpty
#guard (finalState held).bind (fun state => state.read (.privateSpace 1)) == some []

-- Missing second target: first publication remains at the reference boundary.
def unavailable : Bool := match (execute initial (.privateSpace 2)).2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard unavailable
#guard (execute initial (.privateSpace 2)).1.isEmpty
#guard (finalState initial (.privateSpace 2)).bind (fun state => state.read (.privateSpace 0)) == some [request.pattern]
#guard (finalState initial (.privateSpace 2)).bind (fun state => state.read (.privateSpace 1)) == some []
#guard (finalState initial (.privateSpace 2)).bind (fun state => state.read (.privateSpace 2)) == none

-- Pause after the first insertion; resume against the retained second target.
#guard (finalState initial (.privateSpace 1) 27).bind (fun state => state.read (.privateSpace 0)) == some [request.pattern]
#guard (finalState initial (.privateSpace 1) 27).bind (fun state => state.read (.privateSpace 1)) == some []
def paused := EagerDFSStreaming.Scoped.readback (execute initial (.privateSpace 1) 27).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 200 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 1)) == some [secondValue]

end SeparateSpaces

#print axioms fresh_prefix
#print axioms held_prefix
#print axioms fresh_return
#print axioms ScopedInsertionSequence.returned_consistent
#print axioms ScopedInsertionSequence.separate_store_receipt

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource.Controls
