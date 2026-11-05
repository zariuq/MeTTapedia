import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedFrame
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQuerySilence

/-!
# Resource-complete counted EU source execution

Entry evidence concerns only the actual source syntax, original caller and
initial store. The generated collapse child, completed traversal, copy receipt
and numeric return are derived. The original continuation is retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open EagerDFS.Destination
open FlatQueryRowCodec (Codec)
open ClosedOnceQueryFrame (FreshFor placed)
open GuardedCountSource (Input)
open CTLUntilScopedRound (Query Decoded)
open CTLUntilMixedStore (Row decodeRows graphView satisfactionView frontSelect)
open CTLUntilLeafAdmission (GuardProfile)
open CTLUntilCountedFrame (childQuery)
open CTLUntilSourceRows (number)

variable {Context Label : Type} [DecidableEq Label]

structure Entry (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query) (input : Input Context) where
  template : input.template = query.template
  legs : input.legs = query.legs
  principal : Environment
  resolved : resolve input.caller.bindings = some principal
  formula : read principal (.var query.names.formula) = codec.encode label
  holds : read principal (.var query.operand) = codec.encode operand
  current : read principal (.var query.currentRound) = number round
  nextRound : read principal (.var query.names.nextRound) = number (round + 1)
  nextFresh : FreshFor query.names.next input.caller.bindings
  priorFresh : FreshFor query.names.prior input.caller.bindings
  temporaryFresh : FreshFor query.names.temporary input.caller.bindings
  distinct : [query.names.next, query.names.prior, query.names.temporary].Nodup
  profile : GuardProfile codec label query input.program
  decoded : Decoded codec query.handles input.state
  frontAtoms : List Atom
  graphAtoms : List Atom
  factAtoms : List Atom
  fronts : List (Row Label)
  graph : List (Row Label)
  facts : List (Row Label)
  frontRead : input.state.world.state.read query.frontierHandle = some frontAtoms
  frontDecode : decodeRows codec frontAtoms = some fronts
  graphRead : input.state.world.state.read query.edgeHandle = some graphAtoms
  graphDecode : decodeRows codec graphAtoms = some graph
  factRead : input.state.world.state.read query.operandHandle = some factAtoms
  factDecode : decodeRows codec factAtoms = some facts
  initialKnown : List Nat
  initialFrontier : List Nat
  knownRead : CTLUntilRoundPublication.known codec label query input.state.world.state = some initialKnown
  frontierRead : CTLUntilRoundPublication.frontier codec label round query input.state.world.state = some initialFrontier

def Entry.word {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query} {input : Input Context}
    (entry : Entry codec label operand round query input) : List Nat :=
  Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView entry.graph) (satisfactionView operand entry.facts)
    (entry.fronts.filterMap (frontSelect label round))

def Entry.added {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query} {input : Input Context}
    (entry : Entry codec label operand round query input) : List Nat :=
  Mettapedia.Machines.CTLUntilCandidateBag.fresh entry.word entry.initialKnown.toFinset

theorem child_completed {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query} {input : Input Context}
    (entry : Entry codec label operand round query input) (separate : label ≠ operand)
    (reserve : entry.word.length ≤ input.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator) (copies : List (Token × (Atom × List Atom))),
      input.childExecution.stop = .complete after ∧ input.copies after = some (next, copies) ∧
      after.scope.collected.length = entry.added.length ∧
      CTLUntilRoundPublication.known codec label query after.world.state = some (entry.initialKnown ++ entry.added) ∧
      CTLUntilRoundPublication.frontier codec label round query after.world.state = some (entry.initialFrontier ++ entry.added) ∧
      next.usableCount + entry.word.length = input.state.allocator.usableCount := by
  obtain ⟨admitted, distinct⟩ := CTLUntilCountedFrame.child_admission codec label operand round input query entry.template entry.legs
    entry.principal entry.resolved entry.formula entry.holds entry.current entry.nextRound
    entry.nextFresh entry.priorFresh entry.temporaryFresh entry.distinct
  have childTemplate := CTLUntilCountedFrame.child_template input query entry.template
  have childLegs : (childQuery input query).legs = input.legs := (CTLUntilCountedFrame.child_legs input query).trans entry.legs.symm
  have childReady : GuardedQueryPackets.CollectedReady input.childState := by
    intro packet member
    cases member
  obtain ⟨after, completed, _decoded, _stable, updated, copyAvailable⟩ :=
    CTLUntilRoundCompletion.round_and_copy codec label operand separate round (childQuery input query) distinct
      entry.fronts entry.graph entry.facts input.program (CTLUntilCountedFrame.childProfile codec label input query entry.profile)
      input.childCaller input.childState input.context input.origins [] admitted
      (CTLUntilCountedFrame.child_decoded codec input query entry.decoded) childReady
      entry.frontAtoms entry.graphAtoms entry.factAtoms entry.frontRead entry.frontDecode entry.graphRead entry.graphDecode
      entry.factRead entry.factDecode (by simpa only [Entry.word, GuardedCountSource.Input.childState, List.length_nil, Nat.add_zero] using reserve)
  have done : input.childExecution.stop = .complete after := by
    simpa only [childTemplate, childLegs, GuardedCountSource.Input.childExecution] using completed
  have observations := updated.observations entry.initialKnown entry.initialFrontier entry.knownRead entry.frontierRead
  obtain ⟨next, copies, copied, balance⟩ := copyAvailable (collectionSupport (after.cursor []).2)
  refine ⟨after, next, copies, done, copied, ?_, observations.1, observations.2.1, ?_⟩
  · simpa only [Entry.added, Entry.word, GuardedCountSource.Input.childState, List.length_nil, Nat.zero_add] using observations.2.2
  · simpa only [Entry.word, GuardedCountSource.Input.childState, List.length_nil, Nat.add_zero] using balance

/-- The authored size/collapse expression returns the mathematical fresh
count to an actually unbound destination, including an alias, while keeping
the older caller goals and reached world. -/
theorem counted_prefix {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query} {input : Input Context}
    (entry : Entry codec label operand round query input) (separate : label ≠ operand)
    (reserve : entry.word.length ≤ input.state.allocator.usableCount) (representative : String)
    (unbound : read entry.principal input.destination = .var representative) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      CTLUntilRoundPublication.known codec label query after.world.state = some (entry.initialKnown ++ entry.added) ∧
      CTLUntilRoundPublication.frontier codec label round query after.world.state = some (entry.initialFrontier ++ entry.added) ∧
      next.usableCount + entry.word.length = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination entry.added.length)
          input.context (input.origins ++ [0]) input.pending)) := by
  obtain ⟨after, next, copies, completed, copied, count, known, frontier, capacity⟩ := child_completed entry separate reserve
  refine ⟨after, next, known, frontier, capacity, ?_⟩
  have returned := GuardedCountSource.counted_prefix input after next copies entry.principal representative
    entry.resolved unbound completed copied
  rw [GuardedQuerySilence.childExecution_events input, count] at returned
  exact returned

/-- A numerically constrained destination keeps the reached reference
invocation after the actual query and copy. Completion/copy success are
derived from entry capacity; no query effects are replayed on handoff. -/
theorem constrained_prefix {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query} {input : Input Context}
    (entry : Entry codec label operand round query input) (separate : label ≠ operand)
    (reserve : entry.word.length ≤ input.state.allocator.usableCount) (expected : Nat)
    (constrained : read entry.principal input.destination = GuardedCountReturn.value expected) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      CTLUntilRoundPublication.known codec label query after.world.state = some (entry.initialKnown ++ entry.added) ∧
      CTLUntilRoundPublication.frontier codec label round query after.world.state = some (entry.initialFrontier ++ entry.added) ∧
      (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 2) input.before =
        ([], .suspended (.branch (.invoke "size-atom" [.var input.slot] input.destination))
          (placed next after.world input.state.scope input.state.parents
            (GuardedCountReturn.ready input.caller input.slot input.destination entry.added.length)
            input.context input.origins input.pending)) := by
  obtain ⟨after, next, copies, completed, copied, count, known, frontier, _capacity⟩ := child_completed entry separate reserve
  have refined := GuardedCountReturn.tuple_refined input.caller input.slot input.destination after.scope.collected.length
    (GuardedCountSource.slot_fresh input) ⟨entry.principal, resolve_sound entry.resolved⟩
  obtain ⟨principal, resolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have inherited : Solves principal input.caller.bindings := by
    intro pair member
    exact resolve_sound resolved pair (List.mem_append_left _ member)
  have reading := CapturedQueryOperands.resolved_forces entry.resolved input.destination (GuardedCountReturn.value expected)
    constrained (fun environment => ConstantQuerySource.Scalar.read (.grounded _) environment) principal inherited
  have noVariable : ∀ name, read principal input.destination ≠ .var name := by
    intro name
    rw [reading]
    intro impossible
    cases impossible
  have returned := GuardedCountSource.constrained_prefix input after next copies principal completed copied resolved noVariable
  rw [GuardedQuerySilence.childExecution_events input, count] at returned
  exact ⟨after, next, known, frontier, returned⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource
