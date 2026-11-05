import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls

/-! Named candidate admission, one-packet delivery, held/copy refusal and
partial-publication resumption. Duplicate guard clauses are not collapsed. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedPresenceConditional (Input)
open ScopedQuerySource.Controls (call number)

def request := CTLUntilPublicationSource.request FlatQueryRowCodec.integers (.privateSpace 0) 10 1
def firstCode : Atom := call "sat" [.var "f", .var "x"]
def secondCode : Atom := call "fr" [.var "f", number 1, .var "x"]
def first : Atom := request.pattern
def second : Atom := call "fr" [number 10, number 1, number 1]
def body (target : NamedSpaces.Handle := .privateSpace 1) : Body :=
  ⟨"answer", "ignored", target, firstCode, secondCode⟩
def state : Effects.State :=
  (((NamedSpaces.Store.new CTLUntilMixedStore.Controls.atoms [] : Effects.State).allocate []).2.allocate []).2
def base (target : NamedSpaces.Handle := .privateSpace 1) : Input Unit := {
  program := {equations := [NamedPresenceSource.declaration request], declarations := []}
  allocator := Allocator.empty 16 8
  world := ⟨state, [], []⟩
  scope := ⟨[], [], none⟩
  parents := []
  caller := {bindings := [(.var "f", number 10), (.var "x", number 1)], goals := [], destination := .var "answer"}
  context := (), origins := [3], pending := []
  destination := .var "answer", formulaName := "f", nodeName := "x"
  yes := empty
  no := ScopedInsertionSequence.source "ignored" request.handle target firstCode secondCode
  request }

def admitted (input : Input Unit) (proposal : Body := body) : Bool :=
  match NamedPresenceConditional.prepare input with
  | none => false
  | some guard => (prepare input guard proposal).isSome
def execute (input : Input Unit) (fuel : Nat := 200) :=
  (ScopedQuerySource.machine .relational input.program).run fuel input.before
def finalState (input : Input Unit) (fuel : Nat := 200) :=
  (EagerDFSStreaming.Scoped.readback (execute input fuel).2).map (fun saved => saved.2.world.state)

#guard admitted (base)
#guard (execute (base) 39).1.isEmpty
#guard (execute (base) 40).1.map CollectedAnswer.value == [Effects.boolean true]
#guard (finalState (base)).bind (fun stored => stored.read (.privateSpace 0)) == some [first]
#guard (finalState (base)).bind (fun stored => stored.read (.privateSpace 1)) == some [second]
#guard (finalState (base)).bind (fun stored => stored.read .self) == some CTLUntilMixedStore.Controls.atoms

-- An unbound principal representative is not syntactic freshness: its name
-- can already occur in retained equations. The narrow body route refuses it.
def selfConstrainedOutput : Input Unit := {base with
  caller := {(base).caller with bindings := (base).caller.bindings ++ [(.var "answer", .var "answer")]}}
#guard (NamedPresenceConditional.prepare selfConstrainedOutput).isSome
#guard !admitted selfConstrainedOutput
#guard (execute selfConstrainedOutput).1.map CollectedAnswer.value == [Effects.boolean true]

-- Reusing a captured name as the first insertion's let destination must not
-- receive the fresh-two-write certificate. The partial source machine retains
-- the constrained primitive request before either insertion.
def capturedTemporaryBody : Body := {body with temporary := "f"}
def capturedTemporary : Input Unit := {base with
  no := ScopedInsertionSequence.source "f" request.handle (.privateSpace 1) firstCode secondCode}
#guard !admitted capturedTemporary capturedTemporaryBody
#guard (execute capturedTemporary).1.isEmpty
def capturedTemporarySuspended : Bool := match (execute capturedTemporary).2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard capturedTemporarySuspended
#guard (finalState capturedTemporary).bind (fun stored => stored.read (.privateSpace 0)) == some []
#guard (finalState capturedTemporary).bind (fun stored => stored.read (.privateSpace 1)) == some []

def heldState : Effects.State := (state.write (.privateSpace 0) [first, first]).getD state
def held : Input Unit := {base with world := ⟨heldState, [], []⟩}
#guard admitted held
#guard (execute held).1.isEmpty
#guard (finalState held).bind (fun stored => stored.read (.privateSpace 0)) == some [first, first]
#guard (finalState held).bind (fun stored => stored.read (.privateSpace 1)) == some []

def noCapacity : Input Unit := {held with allocator := Allocator.empty 0 8}
def copyingRefused : Bool := match (execute noCapacity 31).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard admitted noCapacity
#guard copyingRefused
#guard (execute noCapacity 31).1.isEmpty

def aliasTarget := base (.privateSpace 0)
#guard admitted aliasTarget (body (.privateSpace 0))
#guard (finalState aliasTarget).bind (fun stored => stored.read (.privateSpace 0)) == some [first, second]

def missing := base (.privateSpace 2)
def blocked := execute missing 38
def missingRefused : Bool := match blocked.2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard admitted missing (body (.privateSpace 2))
#guard missingRefused
#guard blocked.1.isEmpty
#guard (finalState missing 38).bind (fun stored => stored.read (.privateSpace 0)) == some [first]

def supplied := (EagerDFSStreaming.Scoped.readback blocked.2).map fun saved =>
  (saved.1, {saved.2 with world := {saved.2.world with state := (saved.2.world.state.allocate []).2}})
def resumed := supplied.map fun saved => (ScopedQuerySource.machine .relational missing.program).run 200 saved
def restarted := supplied.map fun saved => execute {missing with world := saved.2.world}
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 2)) == some [second]
#guard restarted.map (fun result => result.1.isEmpty) == some true
#guard (restarted.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read (.privateSpace 2)) == some []

-- Same completed answer count does not permit dropping a later copy refusal.
def duplicated : Input Unit := {base with
  allocator := Allocator.empty 0 8
  program := {equations := [NamedPresenceSource.declaration request, NamedPresenceSource.declaration request], declarations := []}}
#guard (NamedPresenceConditional.prepare duplicated).isSome
#guard !admitted duplicated
#guard (execute duplicated).1.map CollectedAnswer.value == [Effects.boolean true]
def laterCopyRefused : Bool := match (execute duplicated).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard laterCopyRefused

def collecting : Input Unit := {base with
  scope := ⟨[], [], some ({bindings := [], goals := [], destination := .var "outer"}, .var "outer", (), [])⟩
  parents := [⟨[], [], none⟩] }
#guard admitted collecting
#guard (execute collecting 40).1.isEmpty
#guard ((EagerDFSStreaming.Scoped.readback (execute collecting 40).2).bind fun saved => saved.2.scopes.head?).map
  (fun scope => scope.collected.map CollectedAnswer.value) == some [Effects.boolean true]

#print axioms fresh_prefix
#print axioms fresh_return
#print axioms held_prefix
#print axioms second_unavailable_prefix
#print axioms NamedGuardedInsertionAdmission.evidence_constructed
#print axioms NamedGuardedInsertionAdmission.prepare_accepts
#print axioms NamedGuardedInsertionAdmission.canonical_admission

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource.Controls
