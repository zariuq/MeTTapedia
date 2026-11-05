import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity

/-!
# Resource-sufficient completion of a reached EU publication leaf

Readable source targets construct both insertion receipts, including aliased
targets. A usable copy identity services a held witness. Static admission is
constructed from the actual guard declaration and reached principal frame;
no completed source execution or successful future publication is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafCompletion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound (Query Decoded)
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilLeafAdmission (GuardProfile)
open CTLUntilMixedStore (render)
open CTLUntilSourceRows (number)
open NamedGuardedCandidateBatch (State)
open NamedGuardedCandidateExecution (Advance executeAdmitted)

variable {Context Label : Type}

theorem admitted_completes (input : NamedPresenceConditional.Input Context)
    (guard : NamedPresenceConditional.Evidence input) (body : NamedGuardedInsertionSource.Body)
    (receipt : NamedGuardedInsertionSource.Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (rows secondRows : List Atom)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (ready : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (secondSnapshot : input.world.state.read body.secondHandle = some secondRows)
    (copyAvailable : ∃ next, PresenceGuardSource.copyAllocator input.allocator true = some next) :
    ∃ advance : Advance, (executeAdmitted input guard body receipt finished output).result = .advanced advance := by
  unfold executeAdmitted
  split
  next unavailable =>
    have impossible := unavailable.symm.trans snapshot
    cases impossible
  next actual found =>
    have same := Option.some.inj (found.symm.trans snapshot)
    subst actual
    split
    next closed =>
      split
      next present =>
        obtain ⟨next, copied⟩ := copyAvailable
        split
        next unavailable =>
          have impossible := unavailable.symm.trans copied
          cases impossible
        next allocated copiedActual => exact ⟨_, rfl⟩
      next absent =>
        obtain ⟨middle, after, first, second⟩ := ScopedInsertionSequence.pair_exists input.world.state
          input.request.handle body.secondHandle input.request.pattern receipt.secondValue
          rows secondRows snapshot secondSnapshot
        split
        next unavailable =>
          have impossible := unavailable.symm.trans first
          cases impossible
        next actualMiddle firstActual =>
          have same := Option.some.inj (firstActual.symm.trans first)
          subst actualMiddle
          split
          next unavailable =>
            have impossible := unavailable.symm.trans second
            cases impossible
          next actualAfter secondActual => exact ⟨_, rfl⟩
    next rejected => exact (rejected ready).elim

/-- Positive usable capacity suffices for either live guard outcome. The
fresh branch constructs its writes from availability rather than spending a
copy identity; the held branch uses the actual finite allocator search. -/
theorem leaf_completes (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (distinct : query.names.temporary ≠ query.names.result)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (admitted : AdmissionFrame codec label operand round query [] caller)
    (valid : Decoded codec query.handles state) (capacity : 0 < state.allocator.usableCount) :
    ∃ after, (GuardedNestedQuerySource.invoke program query.template caller state context origins pending).execution.stop =
      .complete after := by
  obtain ⟨frame, resultFresh, temporaryFresh, finished, output⟩ := admitted
  cases frame with
  | publish _ resolved fixed node bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have nodeRead := bound principal (resolve_sound resolved)
    obtain ⟨firstRead, secondRead⟩ := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
      readings.1 readings.2.2.2 nodeRead
    let request := CTLUntilPublicationSource.request codec query.satisfactionHandle label node
    let input := (query.template.candidate caller context origins request).input program state pending
    have requested := CTLUntilLeafAdmission.request_from_reading codec label node query principal firstRead
    obtain ⟨guard, receipt, guardPrepared, bodyPrepared, _secondValue⟩ :=
      NamedGuardedInsertionAdmission.canonical_admission input query.template.body principal (codec.encode label) (number node)
        (render codec (.frontier label (round + 1) node)) profile.occurrence
        resolved readings.1 nodeRead (codec.literal label) (.grounded _) rfl
        (profile.row_for node) profile.otherHeads profile.leftEvaluated profile.rightEvaluated rfl rfl rfl
        temporaryFresh resultFresh distinct firstRead secondRead
        (CTLUntilPublicationSource.frontier_literal codec label (round + 1) node)
        (CTLUntilPublicationSource.satisfaction_ordinary codec label node)
        (CTLUntilPublicationSource.frontier_ordinary codec label (round + 1) node)
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.satisfactionHandle (by simp [Query.handles])
    obtain ⟨frontAtoms, _frontRows, frontSnapshot, _frontDecoded⟩ :=
      valid query.nextFrontierHandle (by simp [Query.handles])
    obtain ⟨actual, rowsReady⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
    have ready : ClosedQueryAdmission.rowsReady input.request.pattern atoms = true := by
      change ClosedQueryAdmission.rowsReady (render codec (.satisfaction label node)) atoms = true
      rw [← actual]
      exact CTLUntilMixedStore.rows_ready codec "sat" [codec.encode label, number node] (by simp) rows rowsReady
    have copyAvailable := (ScalarCopyCapacity.copyAllocator_true_exists_iff state.allocator).mpr capacity
    obtain ⟨advance, ran⟩ := admitted_completes input guard query.template.body receipt finished output
      atoms frontAtoms snapshot ready frontSnapshot copyAvailable
    change input.caller.goals = [] at finished
    change input.caller.destination = .var query.template.body.result at output
    have advanced : (NamedGuardedCandidateExecution.execute input query.template.body).result = .advanced advance := by
      simpa only [NamedGuardedCandidateExecution.execute, dif_pos finished, dif_pos output,
        guardPrepared, bodyPrepared] using ran
    refine ⟨state.advance advance, ?_⟩
    unfold GuardedNestedQuerySource.invoke
    dsimp only
    split
    next inconsistent => simp [resolved] at inconsistent
    next actualPrincipal actualResolved =>
      have same := Option.some.inj (actualResolved.symm.trans resolved)
      subst actualPrincipal
      split
      next unavailable =>
        have impossible : (none : Option LiteralQuerySource.Request) = some request :=
          unavailable.symm.trans requested
        cases impossible
      next actualRequest actualRequested =>
        have same := Option.some.inj (actualRequested.symm.trans requested)
        subst actualRequest
        dsimp only
        rw [advanced]

theorem worker_completes (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (distinct : query.names.temporary ≠ query.names.result)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (admitted : AdmissionFrame codec label operand round query [] caller)
    (valid : Decoded codec query.handles state) (capacity : 0 < state.allocator.usableCount) :
    ∃ after, ((GuardedNestedQuerySource.leaf program query.template Context).execute
      caller state context origins pending).stop = .complete after :=
  leaf_completes codec label operand round query program profile distinct caller state context origins pending admitted valid capacity

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafCompletion
