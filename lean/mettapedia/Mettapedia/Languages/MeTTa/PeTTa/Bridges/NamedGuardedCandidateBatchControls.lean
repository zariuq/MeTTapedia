import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionControls

/-! Live duplicate guards, late refusal, partial writes, local collection and
actual mixed-store query entry. Budgets are supplied source budgets. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open NamedGuardedInsertionSource.Controls (base first second)
open ScopedQuerySource.Controls (call number)

def program := (base).program
def candidate : Candidate Unit := {
  caller := (base).caller, context := (), origins := [3], formulaName := "f", nodeName := "x",
  request := (base).request, body := NamedGuardedInsertionSource.Controls.body }
def initial : State Unit := {
  allocator := (base).allocator, world := (base).world, scope := (base).scope, parents := (base).parents }
def duplicate : Candidate Unit := {candidate with origins := [4]}
def two := run program [candidate, duplicate] initial []

def saved (execution : Execution Unit) := EagerDFSStreaming.Scoped.readback (execution.observation []).2
def stored (execution : Execution Unit) (handle : NamedSpaces.Handle) :=
  (saved execution).bind fun cursor => cursor.2.world.state.read handle
def completed (execution : Execution Unit) : Bool := match execution.stop with
  | .complete _ => true
  | _ => false

#guard completed two
#guard two.budget == 71
#guard two.events.map CollectedAnswer.value == [Effects.boolean true]
#guard stored two (.privateSpace 0) == some [first]
#guard stored two (.privateSpace 1) == some [second]

-- The second equal candidate sees the first one's publication, and its held
-- witness still needs copying. A scalar fresh-count cannot hide this refusal.
def noCopy := run program [candidate, duplicate] {initial with allocator := Allocator.empty 0 8} []
#guard !completed noCopy
#guard noCopy.events.map CollectedAnswer.value == [Effects.boolean true]
#guard stored noCopy (.privateSpace 0) == some [first]
#guard stored noCopy (.privateSpace 1) == some [second]
def copyStopped : Bool := match noCopy.stop with
  | .suspended remaining .allocation _ => remaining.length == 1
  | _ => false
#guard copyStopped

-- A late admission failure retains the already changed world and does not
-- consume the refused source control.
def wrongOutput : Candidate Unit := {duplicate with body := {duplicate.body with result := "other"}}
def lateRefusal := run program [candidate, wrongOutput] initial []
def referenceStopped : Bool := match lateRefusal.stop with
  | .reference remaining _ => remaining.map Candidate.control == [wrongOutput.control]
  | _ => false
#guard referenceStopped
#guard lateRefusal.budget == 40
#guard lateRefusal.events.map CollectedAnswer.value == [Effects.boolean true]
#guard stored lateRefusal (.privateSpace 0) == some [first]
#guard (saved lateRefusal).map (fun cursor =>
  cursor.2.scopes.head?.map (fun scope => scope.frontier.map (fun work => work.1))) == some (some [wrongOutput.control])

def oldPacket : CollectedAnswer := ⟨.symbol "older", [(.var "kept", number 7)], [66], [.var "live"]⟩
def tailWork : CollectionWork Unit :=
  ({bindings := [], goals := [.evaluate (call "quote" [.symbol "unrelated"]) (.var "tail")],
    destination := .var "tail", reserved := {"tail-live"}, cutBoundary := 9}, (), [99])
def reachedState : State Unit := {initial with
  scope := {initial.scope with frontier := [candidate.work, wrongOutput.work, tailWork], collected := [oldPacket]}}
def withTail := run program [candidate, wrongOutput] reachedState [tailWork]
def savedTail := EagerDFSStreaming.Scoped.readback (withTail.observation [tailWork]).2
#guard withTail.events.map CollectedAnswer.value == [Effects.boolean true]
#guard savedTail.map (fun cursor => cursor.2.scopes.head?.map (fun scope => scope.frontier)) ==
  some (some [wrongOutput.work, tailWork])
#guard savedTail.map (fun cursor => cursor.2.scopes.head?.map
  (fun scope => scope.collected.map CollectedAnswer.value)) == some (some [.symbol "older", Effects.boolean true])
#guard ((savedTail.bind fun cursor => cursor.2.scopes.head?).bind (fun scope => scope.collected.head?)).map
  (fun answer => (answer.value, answer.bindings, answer.occurrences, answer.associated)) ==
  some (oldPacket.value, oldPacket.bindings, oldPacket.occurrences, oldPacket.associated)

-- The universal source theorem covers full residual equality, not merely the
-- visible packet/store projections checked above.
theorem retained_tail_full_source :
    (ScopedQuerySource.machine .relational program).run withTail.budget
      (reachedState.allocator, ⟨reachedState.world, reachedState.scope :: reachedState.parents⟩) =
      withTail.observation [tailWork] :=
  reached_exact program [candidate, wrongOutput] reachedState [tailWork] rfl

def retainedCaller : Candidate Unit := {candidate with caller := {candidate.caller with
  goals := [.evaluate (call "quote" [.symbol "pending"]) (.var "answer")]}}
def retainedRefusal := run program [retainedCaller] initial []
#guard retainedRefusal.budget == 0
#guard (saved retainedRefusal).map (fun cursor =>
  cursor.2.scopes.head?.map (fun scope => scope.frontier.map (fun work => work.1))) == some (some [retainedCaller.control])

-- Missing second target: no packet, first write retained, both the active
-- descriptor and the unvisited sibling remain associated with the stop.
def missing : Candidate Unit := {candidate with body := {candidate.body with secondHandle := .privateSpace 2}}
def partialWrite := run program [missing, duplicate] initial []
def secondStopped : Bool := match partialWrite.stop with
  | .suspended remaining (.branch (.invoke "add-atom" _ _)) _ => remaining.length == 2
  | _ => false
#guard secondStopped
#guard partialWrite.budget == 38
#guard partialWrite.events.isEmpty
#guard stored partialWrite (.privateSpace 0) == some [first]
#guard stored partialWrite (.privateSpace 1) == some []

def other : Candidate Unit := {candidate with
  caller := {candidate.caller with bindings := [(.var "f", number 10), (.var "x", number 2)]}
  origins := [5]
  request := CTLUntilPublicationSource.request FlatQueryRowCodec.integers (.privateSpace 0) 10 2 }
def localState : State Unit := {initial with
  scope := ⟨[], [], some ({bindings := [], goals := [], destination := .var "outer"}, .var "outer", (), [])⟩
  parents := [⟨[], [], none⟩] }
def collectedBatch := run program [candidate, other] localState []
#guard completed collectedBatch
#guard collectedBatch.budget == 80
#guard collectedBatch.events.isEmpty
#guard (saved collectedBatch).map (fun cursor => cursor.2.scopes.head?.map
  (fun scope => scope.collected.map CollectedAnswer.value)) == some (some [Effects.boolean true, Effects.boolean true])
#guard stored collectedBatch (.privateSpace 0) == some [first, other.request.pattern]

-- The actual inner match uses original mixed-store occurrence positions.
def positions := CTLUntilSourceRows.located (CTLUntilMixedStore.satSelect (20 : Int) 1) 0 CTLUntilMixedStore.Controls.rows
def fromQuery := CTLUntilCandidateBatchSource.captured candidate positions
#guard fromQuery.map Candidate.origins == [[3, 2], [3, 7]]
def query := CTLUntilCandidateBatchSource.queryControl candidate (Effects.handleValue .self) CTLUntilMixedStore.Controls.operand
def queryState : State Unit := {initial with scope := {initial.scope with frontier := [(query, (), candidate.origins)]}}
def queryBatch := run program fromQuery queryState []
def actualQuery := (ScopedQuerySource.machine .relational program).run (1 + queryBatch.budget)
  (queryState.allocator, ⟨queryState.world, queryState.scope :: queryState.parents⟩)
#guard actualQuery.1.map CollectedAnswer.value == queryBatch.events.map CollectedAnswer.value
#guard queryBatch.events.map (fun answer => answer.occurrences.take 2) == [[3, 2]]
#guard (EagerDFSStreaming.Scoped.readback actualQuery.2).bind
  (fun cursor => cursor.2.world.state.read (.privateSpace 0)) == some [first]

-- Authored match preparation contributes a real retained handle equation.
def preparedCandidate := CTLUntilCandidateBatchSource.preparedCandidate candidate .self CTLUntilMixedStore.Controls.operand
def preparedControl := ScopedMatchPreparation.ready candidate.caller (.var candidate.body.result) .self
  CTLUntilMixedStore.Controls.operand candidate.source
def preparedState : State Unit := {initial with
  scope := {initial.scope with frontier := [(preparedControl, (), candidate.origins)]}}
def preparedBatch := run program (CTLUntilCandidateBatchSource.captured preparedCandidate positions) preparedState []
def authoredQuery := (ScopedQuerySource.machine .relational program).run (4 + preparedBatch.budget)
  (ClosedOnceQueryFrame.placed initial.allocator initial.world initial.scope initial.parents
    (ScopedMatchPreparation.entry candidate.caller (.var candidate.body.result) .self
      CTLUntilMixedStore.Controls.operand candidate.source) () candidate.origins [])
def location := ScopedMatchPreparation.location candidate.caller (.var candidate.body.result) .self
  CTLUntilMixedStore.Controls.operand candidate.source
#guard authoredQuery.1.map CollectedAnswer.value == [Effects.boolean true]
#guard preparedBatch.events.map CollectedAnswer.value == [Effects.boolean true]
#guard authoredQuery.1.head?.map (fun answer => answer.bindings.contains (Effects.handleValue .self, .var location)) == some true
#guard authoredQuery.1.head?.map (fun answer => answer.bindings.length) ==
  queryBatch.events.head?.map (fun answer => answer.bindings.length + 1)
#guard (EagerDFSStreaming.Scoped.readback authoredQuery.2).bind
  (fun cursor => cursor.2.world.state.read (.privateSpace 0)) == some [first]

def names : CTLUntilCandidateAdmission.Names := ⟨"f", "k1", "next", "prior", "answer", "ignored"⟩
def seed : Control := {bindings := [(.var "f", number 10), (.var "k1", number 1)], goals := [], destination := .var "answer"}
def capturedCandidate := CTLUntilCandidateAdmission.candidate FlatQueryRowCodec.integers 10 2 1
  (.privateSpace 0) (.privateSpace 1) seed names [] () [8] 3 6
def capturedRun := run program [capturedCandidate] initial []
#guard completed capturedRun
#guard capturedRun.events.map CollectedAnswer.value == [Effects.boolean true]
#guard stored capturedRun (.privateSpace 0) == some [first]
#guard stored capturedRun (.privateSpace 1) == some [second]
def aliasedCandidate := CTLUntilCandidateAdmission.candidate FlatQueryRowCodec.integers 10 2 1
  (.privateSpace 0) (.privateSpace 1) seed {names with prior := names.next} [] () [8] 3 6
def aliasedRun := run program [aliasedCandidate] initial []
#guard aliasedRun.budget == 0
#guard !completed aliasedRun
#guard stored aliasedRun (.privateSpace 0) == some []

#print axioms NamedGuardedCandidateExecution.execute_exact
#print axioms run_exact
#print axioms reached_exact
#print axioms CTLUntilCandidateBatchSource.capture_then_batch
#print axioms run_budget
#print axioms retained_tail_full_source
#print axioms ScopedMatchPreparation.preparation
#print axioms CTLUntilCandidateBatchSource.prepare_capture_then_batch
#print axioms CTLUntilCandidateAdmission.captured_admission
#print axioms CTLUntilCandidateAdmission.decoded_not_reference

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch.Controls
