import Mettapedia.GSLT.LanguageDef.CollectionNestedBatchControls
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceCoverage
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariantsControls
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
import Mettapedia.OSLF.MeTTaIL.Complete.Graph

/-!
# Authored nested workflow through joint retained matching and guard work

The driver begins with source-derived jobs, rather than a precomputed match
list. Its controls inspect retained allocations, complete source histories,
guard results, interruption and the original outer-context receipt operation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionOccurrenceMachineControls

open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher

def initial (permitted : Bool) (source : Pattern) (bound : List TypeExpr := []) :=
  CollectionOccurrenceMachine.begin (CollectionNestedConsumerControls.plan permitted)
    bound (.base "Workspace") source

def run (permitted : Bool) (source : Pattern) (work : Nat) (bound : List TypeExpr := []) :=
  CollectionOccurrenceMachine.run 0 work (initial permitted source bound)

def source := CollectionNestedConsumerControls.source

theorem guarded_workflow_fragment :
    CollectionOccurrenceMachine.checkNullaryFragment (CollectionNestedConsumerControls.plan true) = true := by
  cbv

/-- The actual authored workflow satisfies the generic source-coverage
hypotheses. The runtime controls below separately exercise successful and
denied guards, distinct equal-token occurrences, and interrupted execution. -/
theorem guarded_workflow_receipt_covered {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid (CollectionNestedConsumerControls.plan true) [] (.base "Workspace") source)
    (depth : Nat) (bounded : StructuralDescent.eventsDepth receipt.premiseHistory ≤ depth) :
    ∃ work packet result,
      packet ∈ (CollectionOccurrenceMachine.run depth work
        (CollectionOccurrenceMachine.begin (CollectionNestedConsumerControls.plan true)
          [] (.base "Workspace") (CanonicalBags.canon source))).batch.log ∧
      packet.finish? (CollectionNestedConsumerControls.plan true) [] (.base "Workspace") = some result ∧
      result.premiseHistory = receipt.premiseHistory ∧
      result.job.ordinal = receipt.job.ordinal ∧ result.job.declaration = receipt.job.declaration ∧
      CanonicalBags.Same receipt.target result.target := by
  have hypotheses := CollectionOccurrenceMachine.checkNullaryFragment_sound guarded_workflow_fragment
    receipt.job.declaration (List.fst_mem_of_mem_zipIdx valid.1.1)
  exact CollectionOccurrenceMachine.receipt_eventually_published valid hypotheses.2.2 hypotheses.1
    (.nullary hypotheses.2.1) depth bounded

#guard !GeneralPremise.checkNullaryGuards [.relationQuery "inspect" [.fvar "facts"]]
#guard !GeneralPremise.checkNullaryGuards [.congruence (.fvar "x") (.fvar "y")]

/-- The existing authored set-context module now runs through the joint
matcher and continuation, rather than only enumerating context variants. -/
def contextRun (source : Pattern) :=
  CollectionOccurrenceMachine.run 0 200
    (CollectionOccurrenceMachine.begin CollectionSelection.ContextControls.plan [] (.base "Proc")
      (CanonicalBags.canon source))

def contextTargets (source : Pattern) : List Pattern :=
  ((contextRun source).batch.log.filterMap fun packet =>
    packet.finish? CollectionSelection.ContextControls.plan [] (.base "Proc")).map
      (fun receipt => CanonicalBags.canon receipt.target)

def checkControls : IO Unit := do
  for permitted in [true, false] do
    let begun := initial permitted source
    unless begun.batch.frames.isEmpty && begun.batch.log.isEmpty do
      throw (IO.userError "Source matching began with precomputed allocations")
    let done := run permitted source 200
    unless done.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) do
      throw (IO.userError "Joint workflow matching remains pending at its control allowance")
    unless done.batch.frames.length == 2 &&
        (done.matchers.flatMap (Lane.account 0)).length == 2 do
      throw (IO.userError "Joint workflow installed an allocation twice or lost an occurrence")
    unless (done.batch.frames.map (fun frame => frame.allocation.answer.trace)).eraseDups.length == 2 do
      throw (IO.userError "Joint workflow erased physical token identities")
    unless done.batch.log.length == (if permitted then 2 else 0) do
      throw (IO.userError "Joint workflow guard produced the wrong receipt account")
    unless done.batch.frames.all (fun frame =>
        frame.state.agenda.isEmpty && frame.state.unresolved.isEmpty) do
      throw (IO.userError "Joint workflow retained unresolved conditional work")
    unless done.batch.log.all (fun packet =>
        match packet.finish? (CollectionNestedConsumerControls.plan permitted) [] (.base "Workspace") with
        | none => false
        | some receipt => CanonicalBags.canon receipt.target == CollectionNestedConsumerControls.expected) do
      throw (IO.userError "Joint workflow lost its outer context or changed token multiplicity")
    let resumed := CollectionOccurrenceMachine.run 0 120
      (CollectionOccurrenceMachine.run 0 80 begun)
    unless resumed.batch.log.map CollectionNestedBatchControls.readout ==
        done.batch.log.map CollectionNestedBatchControls.readout &&
        resumed.matchers.map (fun lane => (lane.spent, lane.state.answers)) ==
          done.matchers.map (fun lane => (lane.spent, lane.state.answers)) do
      throw (IO.userError "Joint workflow interruption restarted matching or changed publications")
    let search := CollectionOccurrenceSearch.search (CollectionNestedConsumerControls.plan permitted)
      [] (.base "Workspace") 0
    let complete := search.run source 200
    unless decide (search.status complete = .complete) &&
        (search.publication complete).map reprStr ==
          (search.publication (search.resume (search.run source 80) 120)).map reprStr do
      throw (IO.userError "Shared nested search lost its completion or retained receipt account")
    let graph := Complete.Explore.explore search (CanonicalBags.canon source) 400
    let edges := Complete.Graph.edges search graph
    unless Complete.Settled.settled search graph &&
        graph.nodes.length == (if permitted then 3 else 1) &&
        edges.length == (if permitted then 3 else 0) do
      throw (IO.userError "Generic explorer lost a nested workflow node or receipt-bearing edge")
    if permitted then
      unless (graph.nodes.map (·.state)).contains
          (CanonicalBags.canon (CollectionNestedConsumerControls.boxed
            [CollectionNestedConsumerControls.token "B", CollectionNestedConsumerControls.token "B",
              CollectionNestedConsumerControls.token "B"])) do
        throw (IO.userError "Generic explorer failed to reach the completed nested workflow")
  let missing := run true (CollectionNestedConsumerControls.boxed
    [CollectionNestedConsumerControls.token "B"]) 200
  unless missing.batch.frames.isEmpty && missing.batch.log.isEmpty do
    throw (IO.userError "Missing source token created a joint allocation")
  let ambient := CollectionNestedConsumerControls.boxed
    [CollectionNestedConsumerControls.token "A", .bvar 0, CollectionNestedConsumerControls.token "A",
      CollectionNestedConsumerControls.token "B"]
  let underBinder := run true ambient 200 [.base "Place"]
  unless underBinder.batch.frames.length == 2 && underBinder.batch.log.length == 2 do
    throw (IO.userError "Joint workflow lost its ambient binder context")
  let a := CollectionSelection.ContextControls.atom "A"
  let b := CollectionSelection.ContextControls.atom "B"
  let setOf := CollectionSelection.ContextControls.setOf
  let bagOf := CollectionSelection.ContextControls.bagOf
  for (input, expected) in [
      (setOf [a], [setOf [b], setOf [a, b]]),
      (bagOf [a], [bagOf [b]]),
      (setOf [a, b], [setOf [b], setOf [a, b]]),
      (setOf [setOf [a]],
        [setOf [setOf [b]], setOf [setOf [a], setOf [b]],
          setOf [setOf [a, b]], setOf [setOf [a], setOf [a, b]]]),
      (.apply "Wrap" [setOf [a]],
        [.apply "Wrap" [setOf [b]], .apply "Wrap" [setOf [a, b]]])] do
    unless decide ((contextTargets input).Perm (expected.map CanonicalBags.canon)) do
      throw (IO.userError "Joint context execution missed consumption, retention or nested set collapse")
  let duplicateBag := contextRun (bagOf [a, a])
  unless duplicateBag.batch.log.length == 2 &&
      (duplicateBag.batch.log.map (fun packet => packet.job.origin.site.address)).eraseDups.length == 2 do
    throw (IO.userError "Joint context execution conflated equal physical bag occurrences")
  unless (contextTargets (setOf [b])).isEmpty do
    throw (IO.userError "Joint context execution invented an unmatched source redex")
  IO.println "CollectionOccurrenceMachineControls: source jobs, incremental allocation, guards and resumption passed"

#eval checkControls

end Mettapedia.GSLT.LanguageDef.CollectionOccurrenceMachineControls
