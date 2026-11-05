import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundRefinement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity

/-!
# Resource-sufficient completion of actual live EU rounds

Candidate occurrence words account for both consumed witness identities and
reserved output copies. The existing traversal completes when its usable
identities cover the remaining occurrences plus already collected packets.
The invariant follows actual intermediate states; raw array capacity is not
used as a substitute for free, non-retired identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows graphView satisfactionView frontSelect)
open CTLUntilScopedRound
open CTLUntilRoundViews (Stable)
open CTLUntilCandidateWords (WordFrame)
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilLeafAdmission (GuardProfile)

variable {Context Label : Type} [DecidableEq Label]

def AdmittedWord (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (fronts graph facts : List (Row Label)) (legs : List NestedQuerySource.Leg) (caller : Control) (word : List Nat) : Prop :=
  AdmissionFrame codec label operand round query legs caller ∧
    WordFrame codec label operand round query fronts graph facts legs caller word

theorem completes (codec : Codec Label) (label operand : Label) (separate : label ≠ operand)
    (round : Nat) (query : Query)
    (distinct : [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup)
    (fronts graph facts : List (Row Label)) (program : SpaceSemantics.Program)
    (profile : GuardProfile codec label query program) (initial : Effects.State)
    (frontAtoms graphAtoms factAtoms : List Atom)
    (frontRead : initial.read query.frontierHandle = some frontAtoms) (frontDecode : decodeRows codec frontAtoms = some fronts)
    (graphRead : initial.read query.edgeHandle = some graphAtoms) (graphDecode : decodeRows codec graphAtoms = some graph)
    (factRead : initial.read query.operandHandle = some factAtoms) (factDecode : decodeRows codec factAtoms = some facts)
    (legs : List NestedQuerySource.Leg) :
    ScopedQueryWordCompletion.Completes (AdmittedWord codec label operand round query fronts graph facts legs)
      (fun state : State Context => Decoded codec query.handles state ∧
        Stable codec label operand round query initial state.world.state)
      (fun state => state.allocator.usableCount) (fun state => state.scope.collected.length)
      (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context) legs) := by
  have names := distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
  apply ScopedQueryWordCompletion.run_completes program
    (GuardedNestedQuerySource.leaf program query.template Context)
    (AdmittedWord codec label operand round query fronts graph facts)
    (fun state : State Context => Decoded codec query.handles state ∧
      Stable codec label operand round query initial state.world.state)
    (fun state => state.allocator.usableCount) (fun state => state.scope.collected.length)
  · intro caller before context origins pending word described valid reserve
    obtain ⟨admission, framed⟩ := described
    cases framed with
    | leaf _ resolved fixed node bound =>
      have positive : 0 < before.allocator.usableCount := by
        change 1 + before.scope.collected.length ≤ before.allocator.usableCount at reserve
        omega
      obtain ⟨after, completed⟩ := CTLUntilLeafCompletion.worker_completes codec label operand round query program profile
        (by tauto) caller before context origins pending admission valid.1 positive
      have decoded := leaf_preserves codec label operand round query program query.handles
        caller before context origins pending after admission.frame valid.1 completed
      have stable := CTLUntilRoundViews.leaf_stable codec label operand separate round query program
        caller before after context origins pending admission.frame completed
      have ledger := GuardedQueryCapacity.invoke_conservation program query.template caller before context origins pending after completed
      exact ⟨after, completed, ⟨decoded, valid.2.trans stable⟩, ledger⟩
  · intro leg rest caller state context origins pending word described valid
    exact CTLUntilCaptureAdmission.phase_capture_exists codec label operand round query program leg rest
      caller state context origins pending described.1.frame valid.1
  · intro leg rest caller state context origins pending word selected described valid captured
    obtain ⟨assigned, children, joined⟩ := CTLUntilCandidateWords.capture_words codec label operand round query
      fronts graph facts (by tauto) program initial frontAtoms graphAtoms factAtoms frontRead frontDecode graphRead graphDecode
      factRead factDecode leg rest caller state context origins pending word selected described.2 valid.1 valid.2 captured
    have admitted := CTLUntilCaptureAdmission.capture_admission_frame codec label operand round query distinct program
      leg rest caller state context origins pending selected described.1 valid.1 captured
    refine ⟨assigned, ?_, joined⟩
    exact (List.forall₂_and_left selected.choices assigned).mpr ⟨admitted, children⟩

/-- A whole canonical round completes and leaves enough capacity to copy
all ready packets. The exact total charge is the number of candidate
occurrences plus the initial ready-packet count, not the number of distinct
new nodes. This is a logical copy-identity bound, not a physical RAM bound. -/
theorem round_and_copy (codec : Codec Label) (label operand : Label) (separate : label ≠ operand)
    (round : Nat) (query : Query)
    (distinct : [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup)
    (fronts graph facts : List (Row Label)) (program : SpaceSemantics.Program)
    (profile : GuardProfile codec label query program) (caller : Control) (before : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (admission : AdmissionFrame codec label operand round query query.legs caller)
    (valid : Decoded codec query.handles before) (ready : GuardedQueryPackets.CollectedReady before)
    (frontAtoms graphAtoms factAtoms : List Atom)
    (frontRead : before.world.state.read query.frontierHandle = some frontAtoms) (frontDecode : decodeRows codec frontAtoms = some fronts)
    (graphRead : before.world.state.read query.edgeHandle = some graphAtoms) (graphDecode : decodeRows codec graphAtoms = some graph)
    (factRead : before.world.state.read query.operandHandle = some factAtoms) (factDecode : decodeRows codec factAtoms = some facts)
    (reserve : (Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts)
      (fronts.filterMap (frontSelect label round))).length + before.scope.collected.length ≤ before.allocator.usableCount) :
    let word := Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts)
      (fronts.filterMap (frontSelect label round))
    ∃ after,
      (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
        query.legs caller before context origins pending).stop = .complete after ∧
      Decoded codec query.handles after ∧
      Stable codec label operand round query before.world.state after.world.state ∧
      CTLUntilWordUpdate.Update codec label round query word before after ∧
      (∀ protectedNames, ∃ next copies,
        EagerDFS.Collection.copyOwnedAnswers? after.allocator protectedNames
          (after.scope.collected.map (fun packet => (packet.value, packet.associated))) = some (next, copies) ∧
        next.usableCount + word.length + before.scope.collected.length = before.allocator.usableCount) := by
  dsimp only
  let word := Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts)
    (fronts.filterMap (frontSelect label round))
  have described : WordFrame codec label operand round query fronts graph facts query.legs caller word := by
    have recover : ∀ {legs current}, Frame codec label operand round query legs current → legs.length = 3 →
        WordFrame codec label operand round query fronts graph facts query.legs current word := by
      intro legs current frame length
      cases frame with
      | frontier _ resolved fixed nextFresh priorFresh => exact .frontier _ resolved fixed nextFresh priorFresh
      | edge | satisfaction | publish => simp at length
    exact recover admission.frame rfl
  obtain ⟨after, completed, afterValid, ledger⟩ := completes codec label operand separate round query distinct
    fronts graph facts program profile before.world.state frontAtoms graphAtoms factAtoms
    frontRead frontDecode graphRead graphDecode factRead factDecode query.legs
    caller before context origins pending word ⟨admission, described⟩
    ⟨valid, Stable.refl codec label operand round query before.world.state⟩ reserve
  change after.allocator.usableCount + word.length + before.scope.collected.length =
    before.allocator.usableCount + after.scope.collected.length at ledger
  change word.length + before.scope.collected.length ≤ before.allocator.usableCount at reserve
  have names := distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
  have updated := CTLUntilRoundRefinement.refines codec label operand separate round query (by tauto)
    fronts graph facts program before.world.state frontAtoms graphAtoms factAtoms
    frontRead frontDecode graphRead graphDecode factRead factDecode query.legs
    caller before context origins pending after word described
    ⟨valid, Stable.refl codec label operand round query before.world.state⟩ completed
  have afterReady := ScopedNestedQueryExecution.run_preserves program
    (GuardedNestedQuerySource.leaf program query.template Context) GuardedQueryPackets.CollectedReady
    (GuardedQueryPackets.leaf_preserves program query.template) query.legs
    caller before context origins pending after ready completed
  have capacity : after.scope.collected.length ≤ after.allocator.usableCount := by omega
  refine ⟨after, completed, afterValid.1, afterValid.2, updated.2, ?_⟩
  intro protectedNames
  obtain ⟨next, copies, copied, remaining⟩ := GuardedQueryCopyCapacity.copy_ready after.allocator protectedNames
    after.scope.collected afterReady capacity
  refine ⟨next, copies, copied, ?_⟩
  change next.usableCount + word.length + before.scope.collected.length = before.allocator.usableCount
  omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion
