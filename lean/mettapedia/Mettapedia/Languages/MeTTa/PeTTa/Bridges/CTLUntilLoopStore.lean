import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedViews

/-!
# Exact all-self store views between EU iterations

The invariant retains ordered occurrence lists for graph, operand, known
facts and current frontier. A completed round leaves its old frontier in
place and appends the fresh next frontier. Actual cleanup removes precisely
the old frontier, establishing the existing candidate-bag transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows graphView satisfactionView frontSelect)
open CTLUntilScopedRound (Query Decoded)
open CTLUntilRoundPublication (observe)
open Mettapedia.Machines.CTLUntilCandidateBag (candidates fresh advance)

variable {Context Label : Type} [DecidableEq Label]

structure Views (label operand : Label) (edges : List (Nat × Nat)) (holds : List Nat) (round : Nat)
    (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat) (rows : List (Row Label)) : Prop where
  separate : label ≠ operand
  admitted : ∀ row ∈ rows, row.admitted
  graph : graphView rows = edges
  holding : satisfactionView operand rows = holds
  known : satisfactionView label rows = bag.known
  current : rows.filterMap (frontSelect label round) = bag.delta
  other : ∀ step, step ≠ round → rows.filterMap (frontSelect label step) = []

def Stored (codec : Codec Label) (label operand : Label) (edges : List (Nat × Nat)) (holds : List Nat)
    (round : Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat) (world : Effects.State) : Prop :=
  ∃ atoms rows, world.read .self = some atoms ∧ decodeRows codec atoms = some rows ∧
    Views label operand edges holds round bag rows

structure RoundViews (label operand : Label) (edges : List (Nat × Nat)) (holds : List Nat) (round : Nat)
    (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat) (rows : List (Row Label)) : Prop where
  separate : label ≠ operand
  admitted : ∀ row ∈ rows, row.admitted
  graph : graphView rows = edges
  holding : satisfactionView operand rows = holds
  known : satisfactionView label rows = (advance edges holds bag).known
  current : rows.filterMap (frontSelect label round) = bag.delta
  next : rows.filterMap (frontSelect label (round + 1)) = (advance edges holds bag).delta
  other : ∀ step, step ≠ round → step ≠ round + 1 → rows.filterMap (frontSelect label step) = []

def RoundStored (codec : Codec Label) (label operand : Label) (edges : List (Nat × Nat)) (holds : List Nat)
    (round : Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat) (world : Effects.State) : Prop :=
  ∃ atoms rows, world.read .self = some atoms ∧ decodeRows codec atoms = some rows ∧
    RoundViews label operand edges holds round bag rows

theorem next_frontier_empty {label operand : Label} {edges : List (Nat × Nat)} {holds : List Nat}
    {round : Nat} {bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat} {rows : List (Row Label)}
    (views : Views label operand edges holds round bag rows) :
    rows.filterMap (frontSelect label (round + 1)) = [] := views.other _ (by omega)

theorem seeded_views (label operand : Label) (separate : label ≠ operand)
    (edges : List (Nat × Nat)) (holds goals : List Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) (graph : graphView rows = edges)
    (holding : satisfactionView operand rows = holds) (emptyKnown : satisfactionView label rows = [])
    (emptyFrontiers : ∀ step, rows.filterMap (frontSelect label step) = []) :
    Views label operand edges holds 0 ⟨goals, goals⟩ (rows ++ goals.flatMap (CTLUntilSeedSource.seedRows label)) := by
  refine ⟨separate, CTLUntilSeedViews.admitted_append label goals rows admitted, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CTLUntilSeedViews.graph_unchanged label goals rows).trans graph
  · exact (CTLUntilSeedViews.satisfaction_other label operand separate goals rows).trans holding
  · simp only [CTLUntilSeedViews.satisfaction_output, emptyKnown, List.nil_append]
  · simp only [CTLUntilSeedViews.frontier_zero, emptyFrontiers, List.nil_append]
  · intro step nonzero
    exact (CTLUntilSeedViews.frontier_other_round label step nonzero goals rows).trans (emptyFrontiers step)

theorem seeded_stored (codec : Codec Label) (label operand : Label) (separate : label ≠ operand)
    (edges : List (Nat × Nat)) (holds goals : List Nat) (rows : List (Row Label)) (world : Effects.State)
    (admitted : ∀ row ∈ rows, row.admitted) (graph : graphView rows = edges)
    (holding : satisfactionView operand rows = holds) (emptyKnown : satisfactionView label rows = [])
    (emptyFrontiers : ∀ step, rows.filterMap (frontSelect label step) = [])
    (snapshot : world.read .self = some ((rows ++ goals.flatMap (CTLUntilSeedSource.seedRows label)).map (render codec))) :
    Stored codec label operand edges holds 0 ⟨goals, goals⟩ world := by
  refine ⟨_, _, snapshot, CTLUntilMixedStore.decode_rows_complete codec _
    (CTLUntilSeedViews.admitted_append label goals rows admitted), ?_⟩
  exact seeded_views label operand separate edges holds goals rows admitted graph holding emptyKnown emptyFrontiers

theorem cleanup_views {label operand : Label} {edges : List (Nat × Nat)} {holds : List Nat}
    {round : Nat} {bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat} {rows : List (Row Label)}
    (views : RoundViews label operand edges holds round bag rows) :
    Views label operand edges holds (round + 1) (advance edges holds bag) (CTLUntilCleanup.remaining label round rows) := by
  refine ⟨views.separate, CTLUntilCleanup.remaining_admitted label round rows views.admitted, ?_, ?_, ?_, ?_, ?_⟩
  · exact (CTLUntilCleanup.remaining_graph label round rows).trans views.graph
  · exact (CTLUntilCleanup.remaining_satisfaction label operand round rows).trans views.holding
  · exact (CTLUntilCleanup.remaining_satisfaction label label round rows).trans views.known
  · exact (CTLUntilCleanup.remaining_next_frontier label round rows).trans views.next
  · intro step different
    by_cases current : step = round
    · subst step
      exact CTLUntilCleanup.remaining_frontier_empty label round rows
    · exact (CTLUntilCleanup.remaining_other_frontier label label round step (Or.inr current) rows).trans
        (views.other step current different)

theorem cleanup_count {label operand : Label} {edges : List (Nat × Nat)} {holds : List Nat}
    {round : Nat} {bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat} {rows : List (Row Label)}
    (views : RoundViews label operand edges holds round bag rows) :
    (rows.filterMap (frontSelect label round)).length = bag.delta.length := congrArg List.length views.current

theorem cleanup_stored (codec : Codec Label) (label operand : Label) (edges : List (Nat × Nat))
    (holds : List Nat) (round : Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (rows : List (Row Label)) (world : Effects.State) (views : RoundViews label operand edges holds round bag rows)
    (snapshot : world.read .self = some ((CTLUntilCleanup.remaining label round rows).map (render codec))) :
    Stored codec label operand edges holds (round + 1) (advance edges holds bag) world :=
  ⟨_, _, snapshot, CTLUntilMixedStore.decode_rows_complete codec _
    (CTLUntilCleanup.remaining_admitted label round rows views.admitted), cleanup_views views⟩

omit [DecidableEq Label] in
theorem decoded_self_unique (codec : Codec Label) (world : Effects.State) (atoms otherAtoms : List Atom)
    (rows otherRows : List (Row Label)) (snapshot : world.read .self = some atoms)
    (otherSnapshot : world.read .self = some otherAtoms) (decoded : decodeRows codec atoms = some rows)
    (otherDecoded : decodeRows codec otherAtoms = some otherRows) : rows = otherRows := by
  have same : atoms = otherAtoms := Option.some.inj (snapshot.symm.trans otherSnapshot)
  subst otherAtoms
  exact Option.some.inj (decoded.symm.trans otherDecoded)

theorem evidence_views {codec : Codec Label} {label operand : Label} {round : Nat}
    {call : CTLUntilNamedRound.Call Context} (evidence : CTLUntilNamedRound.Evidence codec label operand round call)
    (allSelf : ∀ handle ∈ call.query.handles, handle = .self)
    (edges : List (Nat × Nat)) (holds : List Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (stored : Stored codec label operand edges holds round bag call.state.world.state) :
    evidence.word = candidates edges holds bag.delta ∧ evidence.initialKnown = bag.known ∧
      evidence.initialFrontier = [] ∧ evidence.added = (advance edges holds bag).delta := by
  obtain ⟨atoms, rows, snapshot, decoded, views⟩ := stored
  have frontSelf := allSelf call.query.frontierHandle (by simp [Query.handles])
  have edgeSelf := allSelf call.query.edgeHandle (by simp [Query.handles])
  have operandSelf := allSelf call.query.operandHandle (by simp [Query.handles])
  have knownSelf := allSelf call.query.satisfactionHandle (by simp [Query.handles])
  have nextSelf := allSelf call.query.nextFrontierHandle (by simp [Query.handles])
  have frontRows : evidence.fronts = rows := decoded_self_unique codec call.state.world.state _ _ _ _
    (by simpa only [frontSelf] using evidence.frontRead) snapshot evidence.frontDecode decoded
  have edgeRows : evidence.graph = rows := decoded_self_unique codec call.state.world.state _ _ _ _
    (by simpa only [edgeSelf] using evidence.graphRead) snapshot evidence.graphDecode decoded
  have operandRows : evidence.facts = rows := decoded_self_unique codec call.state.world.state _ _ _ _
    (by simpa only [operandSelf] using evidence.factRead) snapshot evidence.factDecode decoded
  have word : evidence.word = candidates edges holds bag.delta := by
    simp only [CTLUntilNamedRound.Evidence.word, frontRows, edgeRows, operandRows, views.graph, views.holding, views.current]
  have known := evidence.knownRead
  change observe codec (satisfactionView label) call.query.satisfactionHandle call.state.world.state = some evidence.initialKnown at known
  rw [knownSelf, CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded, views.known] at known
  have knownEq : evidence.initialKnown = bag.known := (Option.some.inj known).symm
  have frontier := evidence.frontierRead
  change observe codec (List.filterMap (frontSelect label (round + 1))) call.query.nextFrontierHandle call.state.world.state =
    some evidence.initialFrontier at frontier
  rw [nextSelf, CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded, next_frontier_empty views] at frontier
  have frontierEq : evidence.initialFrontier = [] := (Option.some.inj frontier).symm
  refine ⟨word, knownEq, frontierEq, ?_⟩
  simp only [CTLUntilNamedRound.Evidence.added, word, knownEq, advance]

/-- Interpret the projection fields returned by the same actual named-round
receipt. No second execution or independently assumed final store is used. -/
theorem round_views (codec : Codec Label) (label operand : Label) (edges : List (Nat × Nat))
    (holds : List Nat) (round : Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (query : Query) (before after : NamedGuardedCandidateBatch.State Context)
    (allSelf : ∀ handle ∈ query.handles, handle = .self)
    (stored : Stored codec label operand edges holds round bag before.world.state)
    (decodedAfter : Decoded codec query.handles after)
    (preserved : CTLUntilRoundData.Preserved codec operand query before.world.state after.world.state)
    (other : CTLUntilRoundData.OtherFrontiers codec label round before.world.state after.world.state)
    (known : CTLUntilRoundPublication.known codec label query after.world.state = some (advance edges holds bag).known)
    (next : CTLUntilRoundPublication.frontier codec label round query after.world.state = some (advance edges holds bag).delta) :
    RoundStored codec label operand edges holds round bag after.world.state := by
  obtain ⟨atoms, rows, snapshot, decoded, views⟩ := stored
  have selfMember : NamedSpaces.Handle.self ∈ query.handles := by
    have first := allSelf query.frontierHandle (by simp [Query.handles])
    rw [← first]
    simp [Query.handles]
  obtain ⟨nextAtoms, nextRows, nextRead, nextDecode⟩ := decodedAfter .self selfMember
  have admitted := (CTLUntilMixedStore.decode_rows_sound codec nextAtoms nextRows nextDecode).2
  have graph := preserved.graph
  change observe codec graphView query.edgeHandle after.world.state = observe codec graphView query.edgeHandle before.world.state at graph
  rw [allSelf query.edgeHandle (by simp [Query.handles]),
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ nextRead nextDecode,
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded] at graph
  have holding := preserved.operand
  change observe codec (satisfactionView operand) query.operandHandle after.world.state =
    observe codec (satisfactionView operand) query.operandHandle before.world.state at holding
  rw [allSelf query.operandHandle (by simp [Query.handles]),
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ nextRead nextDecode,
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded] at holding
  change observe codec (satisfactionView label) query.satisfactionHandle after.world.state = some (advance edges holds bag).known at known
  rw [allSelf query.satisfactionHandle (by simp [Query.handles]),
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ nextRead nextDecode] at known
  change observe codec (List.filterMap (frontSelect label (round + 1))) query.nextFrontierHandle after.world.state =
    some (advance edges holds bag).delta at next
  rw [allSelf query.nextFrontierHandle (by simp [Query.handles]),
    CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ nextRead nextDecode] at next
  have old (step : Nat) (different : step ≠ round + 1) :
      nextRows.filterMap (frontSelect label step) = rows.filterMap (frontSelect label step) := by
    have same := other .self step different
    rw [CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ nextRead nextDecode,
      CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded] at same
    exact Option.some.inj same
  exact ⟨nextAtoms, nextRows, nextRead, nextDecode,
    views.separate, admitted, (Option.some.inj graph).trans views.graph,
    (Option.some.inj holding).trans views.holding, Option.some.inj known,
    (old round (by omega)).trans views.current, Option.some.inj next,
    fun step notCurrent notNext => (old step notNext).trans (views.other step notCurrent)⟩

namespace Controls

def initialRows : List (Row Nat) := [.edge 0 1, .edge 0 1, .satisfaction 20 0, .satisfaction 20 0]
def seededRows : List (Row Nat) := initialRows ++ [1, 1].flatMap (CTLUntilSeedSource.seedRows 10)

theorem duplicate_initial_frontier_is_admitted : Views 10 20 [(0, 1), (0, 1)] [0, 0] 0 ⟨[1, 1], [1, 1]⟩ seededRows := by
  apply seeded_views 10 20 (by decide) _ _ _ initialRows
  · intro row member
    simp only [initialRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  · rfl
  · rfl
  · rfl
  · intro step
    rfl

theorem future_frontier_is_not_empty :
    ¬ Views 10 20 [(0, 1), (0, 1)] [0, 0] 0 ⟨[1, 1], [1, 1]⟩ (seededRows ++ [.frontier 10 1 99]) := by
  intro views
  have impossible := views.other 1 (by decide)
  have actual : (seededRows ++ [Row.frontier 10 1 99]).filterMap (frontSelect 10 1) = [99] := rfl
  rw [actual] at impossible
  cases impossible

end Controls

#print axioms evidence_views
#print axioms round_views
#print axioms cleanup_views

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore
