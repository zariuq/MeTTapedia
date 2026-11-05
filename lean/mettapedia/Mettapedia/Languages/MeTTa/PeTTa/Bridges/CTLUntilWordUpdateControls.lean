import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRoundControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundRefinement

/-! Ordered source publication, repeated producers, and a reversed-word
negative control. These executable controls do not replace the general
candidate-word decomposition proof. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate.Controls

open NamedGuardedCandidateBatch (State)
open ScopedNestedQueryExecution (Execution)
open CTLUntilScopedRound.Controls (query)
open CTLUntilMixedStore (Row)
open ScopedNestedQueryExecution.Controls renaming initial → fixtureInitial,
  caller → fixtureCaller, program → fixtureProgram, legs → fixtureLegs,
  template → fixtureTemplate, full → fixtureFull, execute → fixtureExecute

def observesWord (word : List Nat) (before : State Unit) (execution : Execution Unit) : Bool :=
  match execution.stop,
      CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query before.world.state,
      CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query before.world.state with
  | .complete after, some known, some next =>
    let added := Mettapedia.Machines.CTLUntilCandidateBag.fresh word known.toFinset
    CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query after.world.state == some (known ++ added) &&
    CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query after.world.state == some (next ++ added) &&
    after.scope.collected.length == before.scope.collected.length + added.length
  | _, _, _ => false

def candidateWord (rows : List (Row Int)) : List Nat :=
  Mettapedia.Machines.CTLUntilCandidateBag.candidates (CTLUntilMixedStore.graphView rows)
    (CTLUntilMixedStore.satisfactionView 20 rows) (rows.filterMap (CTLUntilMixedStore.frontSelect 10 0))

#guard observesWord (candidateWord CTLUntilMixedStore.Controls.rows) fixtureInitial fixtureFull
#guard !observesWord [3] fixtureInitial fixtureFull

def twoRows : List (Row Int) := CTLUntilMixedStore.Controls.rows ++ [.edge 3 2, .satisfaction 20 3]
def twoInitial : State Unit := {fixtureInitial with world :=
  ⟨NamedSpaces.Store.new (twoRows.map (CTLUntilMixedStore.render FlatQueryRowCodec.integers)) [], [], []⟩}
def twoRun := fixtureExecute fixtureLegs fixtureTemplate twoInitial

#guard candidateWord twoRows == [1, 1, 1, 1, 3, 1, 1, 1, 1, 3]
#guard observesWord (candidateWord twoRows) twoInitial twoRun
#guard observesWord [1, 3] twoInitial twoRun
#guard !observesWord [3, 1] twoInitial twoRun

-- Resource suspension cannot be read as a completed empty candidate word.
#guard !observesWord [] fixtureInitial ScopedNestedQueryExecution.Controls.noCopy

theorem full_refines_word (after : State Unit) (completed : fixtureFull.stop = .complete after) :
    Update FlatQueryRowCodec.integers 10 0 query
      (candidateWord CTLUntilMixedStore.Controls.rows) fixtureInitial after := by
  have result := CTLUntilRoundRefinement.completed_word FlatQueryRowCodec.integers 10 20 (by decide)
    0 query (by decide) CTLUntilMixedStore.Controls.rows CTLUntilMixedStore.Controls.rows CTLUntilMixedStore.Controls.rows
    fixtureProgram fixtureCaller fixtureInitial after () [9] []
    CTLUntilScopedRound.Controls.initial_resolved_fixed.1 CTLUntilScopedRound.Controls.initial_resolved_fixed.2
    CTLUntilScopedRound.Controls.next_fresh CTLUntilScopedRound.Controls.prior_fresh CTLUntilScopedRound.Controls.initial_decoded
    CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.atoms
    rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
    rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
    rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
  exact (result (by
    simpa only [CTLUntilScopedRound.Controls.query_template, CTLUntilScopedRound.Controls.query_legs,
      fixtureFull, fixtureExecute] using completed)).2

/-- The observed ordered outputs are obtained from the general source
refinement theorem; only the finite input candidate list is reduced here. -/
theorem full_ordered_outputs (after : State Unit) (completed : fixtureFull.stop = .complete after) :
    CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query after.world.state = some [1] ∧
    CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query after.world.state = some [9, 1] ∧
    after.scope.collected.length = 1 := by
  have observed := (full_refines_word after completed).observations [] [9]
    CTLUntilScopedRound.Controls.initial_known CTLUntilScopedRound.Controls.initial_next_frontier
  have added : Mettapedia.Machines.CTLUntilCandidateBag.fresh
      (candidateWord CTLUntilMixedStore.Controls.rows) (∅ : Finset Nat) = [1] := by decide +kernel
  simpa only [List.toFinset_nil, added, List.nil_append, List.cons_append, List.length_singleton,
    fixtureInitial, List.length_nil, Nat.zero_add] using observed

#print axioms ScopedQueryWordRefinement.run_refines
#print axioms CTLUntilRoundPublication.leaf_decision
#print axioms Update.append
#print axioms leaf_update
#print axioms full_refines_word
#print axioms full_ordered_outputs

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate.Controls
