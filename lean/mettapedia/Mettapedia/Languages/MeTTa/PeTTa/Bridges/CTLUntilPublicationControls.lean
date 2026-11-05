import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairControls

/-! Source publication to separate and aliased targets, pause/resume, and
an unavailable second handle after the first write has already occurred. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open CTLUntilMixedStore (render)

def first : Atom := render FlatQueryRowCodec.integers (.satisfaction 10 1)
def second : Atom := render FlatQueryRowCodec.integers (.frontier 10 1 1)
def caller : Control := {bindings := [], goals := [], destination := .var "answer"}
def program : SpaceSemantics.Program := {equations := [], declarations := []}
def initial : Effects.State :=
  (((NamedSpaces.Store.new CTLUntilMixedStore.Controls.atoms [] : Effects.State).allocate []).2.allocate []).2

def start (state : Effects.State) (target : NamedSpaces.Handle) : ScopedCursor Unit :=
  (Allocator.empty 16 8, ⟨⟨state, [], []⟩,
    [⟨[(ScopedInsertionSequence.entry caller "answer" "ignored" (.privateSpace 0) target first second, (), [9])], [], none⟩]⟩)
def execute (state : Effects.State := initial) (target : NamedSpaces.Handle := .privateSpace 1) (fuel : Nat := 100) :=
  (ScopedQuerySource.machine .relational program).run fuel (start state target)
def finalState (state : Effects.State := initial) (target : NamedSpaces.Handle := .privateSpace 1) (fuel : Nat := 100) :=
  (EagerDFSStreaming.Scoped.readback (execute state target fuel).2).map (fun saved => saved.2.world.state)

#guard (execute initial).1.map CollectedAnswer.value == [Effects.boolean true]
#guard (finalState initial).bind (fun state => state.read (.privateSpace 0)) == some [first]
#guard (finalState initial).bind (fun state => state.read (.privateSpace 1)) == some [second]
#guard (finalState initial).bind (fun state => state.read .self) == some CTLUntilMixedStore.Controls.atoms
#guard (execute initial (.privateSpace 0)).1.map CollectedAnswer.value == [Effects.boolean true]
#guard (finalState initial (.privateSpace 0)).bind (fun state => state.read (.privateSpace 0)) == some [first, second]
#guard (finalState initial (.privateSpace 0)).bind (fun state => state.read (.privateSpace 1)) == some []

def paused := EagerDFSStreaming.Scoped.readback (execute initial (.privateSpace 1) 8).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 100 saved
def resumedState := (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map (fun saved => saved.2.world.state)
#guard paused.bind (fun saved => saved.2.world.state.read (.privateSpace 0)) == some [first]
#guard paused.bind (fun saved => saved.2.world.state.read (.privateSpace 1)) == some []
#guard resumedState.bind (fun state => state.read (.privateSpace 0)) == some [first]
#guard resumedState.bind (fun state => state.read (.privateSpace 1)) == some [second]

-- Re-entering the body with its old caller is not resumption.
def restarted := paused.map fun saved => execute saved.2.world.state
#guard (restarted.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 0)) == some [first, first]

def blocked := execute initial (.privateSpace 2) 12
def suspended : Bool := match blocked.2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard suspended
#guard blocked.1.isEmpty
#guard (finalState initial (.privateSpace 2) 12).bind (fun state => state.read (.privateSpace 0)) == some [first]
#guard (finalState initial (.privateSpace 2) 12).bind (fun state => state.read (.privateSpace 2)) == none

-- A host supplies the missing target, then resumes the exact saved request.
def supplied := (EagerDFSStreaming.Scoped.readback blocked.2).map fun saved =>
  (saved.1, {saved.2 with world := {saved.2.world with state := (saved.2.world.state.allocate []).2}})
def suppliedRun := supplied.map fun saved => (ScopedQuerySource.machine .relational program).run 100 saved
#guard suppliedRun.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (suppliedRun.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 0)) == some [first]
#guard (suppliedRun.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 2)) == some [second]

def guarded (state : Effects.State) (target : NamedSpaces.Handle := .privateSpace 1) :=
  (ScopedQuerySource.machine .relational program).run 200
    (Allocator.empty 16 8, ⟨⟨state, [], []⟩,
      [(⟨[(GuardedInsertionPairSource.entry caller "answer"
        (request FlatQueryRowCodec.integers (.privateSpace 0) 10 1) target "ignored" first second, (), [])], [], none⟩ : CollectionScope Unit)]⟩)
#guard (guarded initial).1.map CollectedAnswer.value == [Effects.boolean true]
def guardedAfter := (EagerDFSStreaming.Scoped.readback (guarded initial).2).map (fun saved => saved.2.world.state)
#guard guardedAfter.map (fun state => (guarded state).1.isEmpty) == some true
#guard guardedAfter.bind (fun state => state.read (.privateSpace 0)) == some [first]
#guard guardedAfter.bind (fun state => state.read (.privateSpace 1)) == some [second]

-- Restarting the whole guard after partial publication can lose the frontier.
def guardedBlocked := guarded initial (.privateSpace 2)
def guardedSupplied := (EagerDFSStreaming.Scoped.readback guardedBlocked.2).map fun saved =>
  (saved.1, {saved.2 with world := {saved.2.world with state := (saved.2.world.state.allocate []).2}})
def guardedResumed := guardedSupplied.map fun saved => (ScopedQuerySource.machine .relational program).run 200 saved
def guardedRestarted := guardedSupplied.map fun saved => guarded saved.2.world.state (.privateSpace 2)
#guard guardedBlocked.1.isEmpty
#guard guardedResumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (guardedResumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 2)) == some [second]
#guard guardedRestarted.map (fun result => result.1.isEmpty) == some true
#guard (guardedRestarted.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 0)) == some [first]
#guard (guardedRestarted.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 2)) == some []

#print axioms ScopedInsertionSource.unavailable_prefix
#print axioms ScopedInsertionSequence.second_unavailable_prefix
#print axioms ScopedInsertionSequence.pair_store_receipt
#print axioms body_prefix
#print axioms satisfaction_membership
#print axioms fresh_candidate_prefix
#print axioms capture_view_after_writes
#print axioms fresh_known_cardinality

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource.Controls
