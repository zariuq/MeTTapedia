import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchPreparation

/-!
# Actual satisfaction-query entry followed by guarded candidate execution

The innermost query captures its physical occurrence positions in the current
decoded mixed store. Its original body controls become the exact contiguous
leaf batch. World updates remain live during that batch; later nested source
work stays pending. No flattened all-round frontier is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateBatchSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (Candidate State)
open CTLUntilMixedStore (Row render satSelect decodeRows)

variable {Context Label : Type} [DecidableEq Label]

def queryControl (candidate : Candidate Context) (spaceCode patternCode : Atom) : Control :=
  {candidate.caller with
    goals := .invoke "match" [spaceCode, patternCode, candidate.source]
      (.var candidate.body.result) :: candidate.caller.goals}

def captured (candidate : Candidate Context) (positions : List (Nat × Unit)) : List (Candidate Context) :=
  positions.map fun entry => {candidate with origins := candidate.origins ++ [entry.1]}

theorem captured_work (candidate : Candidate Context) (spaceCode patternCode : Atom)
    (positions : List (Nat × Unit)) :
    (captured candidate positions).map Candidate.work =
      ScopedQuerySource.work candidate.context candidate.origins (positions.map fun entry =>
        (entry.1, ScopedQuerySource.bodyControl (queryControl candidate spaceCode patternCode) []
          candidate.source (.var candidate.body.result) candidate.caller.goals)) := by
  simp only [captured, ScopedQuerySource.work, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry _
  simp only [Candidate.work, Candidate.control, ScopedQuerySource.bodyControl,
    ScopedQuerySource.extend, List.map_nil, List.append_nil, queryControl, Candidate.source]

/-- One actual query-entry step followed by the exact live-world leaf batch.
Rows and complete matching come from the decoder and source capture theorem.
The result may be a retained reference request or an allocation suspension. -/
theorem capture_then_batch (codec : FlatQueryRowCodec.Codec Label) (program : SpaceSemantics.Program)
    (candidate : Candidate Context) (state : State Context) (pending : List (CollectionWork Context))
    (spaceCode patternCode : Atom) (principal : Environment) (label : Label) (node : Nat)
    (atoms : List Atom) (rows : List (Row Label))
    (frontier : state.scope.frontier =
      (queryControl candidate spaceCode patternCode, candidate.context, candidate.origins) :: pending)
    (resolved : resolve candidate.caller.bindings = some principal)
    (patternRead : read principal patternCode = CTLUntilMixedCapture.preparedSatisfaction codec label node)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= state.world.state.read) = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    let candidates := captured candidate (CTLUntilSourceRows.located (satSelect label node) 0 rows)
    let execution := NamedGuardedCandidateBatch.run program candidates state pending
    (ScopedQuerySource.machine .relational program).run (1 + execution.budget)
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) = execution.observation pending := by
  dsimp only
  have first := CTLUntilMixedCapture.satisfaction_entry codec .relational program state.allocator state.world state.scope
    state.parents (queryControl candidate spaceCode patternCode) candidate.context candidate.origins pending
    spaceCode patternCode candidate.source (.var candidate.body.result) candidate.caller.goals principal label node atoms rows
    frontier rfl resolved patternRead (by rfl) snapshot decoded
  rw [← captured_work candidate spaceCode patternCode] at first
  change (ScopedQuerySource.machine .relational program).step
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) =
    some (.silent (state.cursor
      ((captured candidate (CTLUntilSourceRows.located (satSelect label node) 0 rows)).map Candidate.work ++ pending))) at first
  have continued := (ScopedQuerySource.machine .relational program).run_succ_silent
    (fuel := (NamedGuardedCandidateBatch.run program
      (captured candidate (CTLUntilSourceRows.located (satSelect label node) 0 rows)) state pending).budget) first
  rw [NamedGuardedCandidateBatch.run_exact] at continued
  simpa only [Nat.add_comm] using continued

/-- The query's evaluated handle equation belongs to every captured body
frame, even though pattern and body syntax themselves remain unchanged. -/
def preparedCandidate (candidate : Candidate Context) (handle : NamedSpaces.Handle) (pattern : Atom) : Candidate Context :=
  {candidate with caller := {
    ScopedMatchPreparation.ready candidate.caller (.var candidate.body.result) handle pattern candidate.source with
      goals := candidate.caller.goals}}

theorem prepared_source (candidate : Candidate Context) (handle : NamedSpaces.Handle) (pattern : Atom) :
    (preparedCandidate candidate handle pattern).source = candidate.source := rfl

theorem prepared_control (candidate : Candidate Context) (handle : NamedSpaces.Handle) (pattern : Atom) :
    ScopedMatchPreparation.ready candidate.caller (.var candidate.body.result) handle pattern candidate.source =
      queryControl (preparedCandidate candidate handle pattern)
        (.var (ScopedMatchPreparation.location candidate.caller (.var candidate.body.result) handle pattern candidate.source)) pattern := rfl

/-- Authored match, including its three operand-preparation steps, followed
by actual capture and live candidate execution. The reached principal solver
and handle reading are constructed rather than supplied. -/
theorem prepare_capture_then_batch (codec : FlatQueryRowCodec.Codec Label) (program : SpaceSemantics.Program)
    (candidate : Candidate Context) (state : State Context) (pending : List (CollectionWork Context))
    (handle : NamedSpaces.Handle) (pattern : Atom) (principal : Environment) (label : Label) (node : Nat)
    (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve candidate.caller.bindings = some principal)
    (patternRead : read principal pattern = CTLUntilMixedCapture.preparedSatisfaction codec label node)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let prepared := preparedCandidate candidate handle pattern
    let readyState : State Context := {state with scope := {state.scope with frontier :=
      [(ScopedMatchPreparation.ready candidate.caller (.var candidate.body.result) handle pattern candidate.source,
        candidate.context, candidate.origins)] ++ pending}}
    let candidates := captured prepared (CTLUntilSourceRows.located (satSelect label node) 0 rows)
    let execution := NamedGuardedCandidateBatch.run program candidates readyState pending
    (ScopedQuerySource.machine .relational program).run (4 + execution.budget)
      (ClosedOnceQueryFrame.placed state.allocator state.world state.scope state.parents
        (ScopedMatchPreparation.entry candidate.caller (.var candidate.body.result) handle pattern candidate.source)
        candidate.context candidate.origins pending) = execution.observation pending := by
  dsimp only
  let prepared := preparedCandidate candidate handle pattern
  let location := ScopedMatchPreparation.location candidate.caller (.var candidate.body.result) handle pattern candidate.source
  let readyState : State Context := {state with scope := {state.scope with frontier :=
    [(ScopedMatchPreparation.ready candidate.caller (.var candidate.body.result) handle pattern candidate.source,
      candidate.context, candidate.origins)] ++ pending}}
  obtain ⟨after, afterResolved⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent candidate.caller (.var candidate.body.result) handle pattern candidate.source
      ⟨principal, resolve_sound resolved⟩)
  have reading := ScopedMatchPreparation.closed_reading candidate.caller (.var candidate.body.result) handle pattern candidate.source
    principal after pattern (CTLUntilMixedCapture.preparedSatisfaction codec label node) resolved afterResolved patternRead
    (LiteralQuerySource.read_literal _ (by
      apply SpaceSemantics.Literal.constructor "sat" _ (by decide)
      intro atom member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact codec.literal label
      · exact .grounded _))
  have handleRead := ScopedMatchPreparation.ready_location candidate.caller (.var candidate.body.result) handle pattern candidate.source
    after afterResolved
  have queried := capture_then_batch codec program prepared readyState pending (.var location) pattern after label node atoms rows
    (by rfl)
    afterResolved reading (by
      change (Effects.readHandle (read after (.var location)) >>= state.world.state.read) = some atoms
      rw [handleRead, Effects.readHandle_handleValue]
      exact snapshot) decoded
  dsimp only at queried
  have first := ScopedMatchPreparation.preparation program state.allocator state.world state.scope state.parents
    candidate.caller candidate.context candidate.origins pending (.var candidate.body.result) handle pattern candidate.source
    ⟨principal, resolve_sound resolved⟩
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 3
    (1 + (NamedGuardedCandidateBatch.run program
      (captured prepared (CTLUntilSourceRows.located (satSelect label node) 0 rows)) readyState pending).budget) _ _ [] first
  change (ScopedQuerySource.machine .relational program).run _ _ =
    ([] ++ ((ScopedQuerySource.machine .relational program).run _
      (readyState.allocator, ⟨readyState.world, readyState.scope :: readyState.parents⟩)).1,
      ((ScopedQuerySource.machine .relational program).run _
      (readyState.allocator, ⟨readyState.world, readyState.scope :: readyState.parents⟩)).2) at joined
  rw [queried] at joined
  simpa only [← Nat.add_assoc, List.nil_append, Nat.reduceAdd, Prod.mk.eta, prepared, readyState] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateBatchSource
