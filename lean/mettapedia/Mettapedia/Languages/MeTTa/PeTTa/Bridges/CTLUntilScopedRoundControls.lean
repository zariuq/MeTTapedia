import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowthControls

/-!
Typed preservation instantiated on the actual mixed-store EU fixture.
Initial resolution and readings are checked independently of the nested run.
Duplicate rows and an existing future frontier remain observable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ClosedOnceQueryFrame (FreshFor)
open ScopedQuerySource.Controls (call number)

open ScopedNestedQueryExecution.Controls renaming caller → fixtureCaller,
  template → fixtureTemplate, legs → fixtureLegs, program → fixtureProgram,
  initial → fixtureInitial, full → fixtureFull, execute → fixtureExecute,
  rows → fixtureRows, completed → fixtureCompleted

def query : Query := {
  names := ⟨"f", "k1", "y", "x", "answer", "ignored"⟩
  operand := "a", currentRound := "k"
  frontierHandle := .self, edgeHandle := .self, operandHandle := .self
  satisfactionHandle := .self, nextFrontierHandle := .self }

theorem query_template : query.template = fixtureTemplate := rfl
theorem query_legs : query.legs = fixtureLegs := rfl

def callerReadings : Bool := match resolve fixtureCaller.bindings with
  | none => false
  | some principal => decide (
      read principal (.var query.names.formula) = FlatQueryRowCodec.integers.encode 10 ∧
      read principal (.var query.operand) = FlatQueryRowCodec.integers.encode 20 ∧
      read principal (.var query.currentRound) = number 0 ∧
      read principal (.var query.names.nextRound) = number 1)

def initialModel : Environment := fun name =>
  if name = "f" then encode (number 10) else
  if name = "a" then encode (number 20) else
  if name = "k" then encode (number 0) else
  if name = "k1" then encode (number 1) else .var name

theorem initial_model_solves : Solves initialModel fixtureCaller.bindings := by
  intro pair member
  simp only [fixtureCaller, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [initialModel, EagerDFS.Destination.read, encode, decode, number]

theorem caller_principal : ∃ principal, resolve fixtureCaller.bindings = some principal ∧
    read principal (.var query.names.formula) = FlatQueryRowCodec.integers.encode 10 ∧
    read principal (.var query.operand) = FlatQueryRowCodec.integers.encode 20 ∧
    read principal (.var query.currentRound) = number 0 ∧
    read principal (.var query.names.nextRound) = number 1 := by
  obtain ⟨principal, resolved⟩ := resolve_complete ⟨initialModel, initial_model_solves⟩
  have forced (name : String) (value : Int)
      (member : (.var name, number value) ∈ fixtureCaller.bindings) :
      read principal (.var name) = number value :=
    (resolve_sound resolved (.var name, number value) member).trans
      (ConstantQuerySource.Scalar.read (.grounded _) principal)
  refine ⟨principal, resolved, ?_, ?_, ?_, ?_⟩
  · exact forced "f" 10 (by simp [fixtureCaller])
  · exact forced "a" 20 (by simp [fixtureCaller])
  · exact forced "k" 0 (by simp [fixtureCaller])
  · exact forced "k1" 1 (by simp [fixtureCaller])

theorem caller_readings_checked : callerReadings = true := by
  obtain ⟨principal, resolved, readings⟩ := caller_principal
  simpa only [callerReadings, resolved, decide_eq_true_eq] using readings

theorem initial_resolved_fixed :
    Resolved fixtureCaller ∧ Fixed FlatQueryRowCodec.integers 10 20 0 query fixtureCaller := by
  obtain ⟨principal, resolved, readings⟩ := caller_principal
  exact ⟨⟨principal, resolved⟩, fixed_of_readings FlatQueryRowCodec.integers 10 20 0 query
    fixtureCaller principal resolved readings.1 readings.2.1 readings.2.2.1 readings.2.2.2⟩

theorem next_fresh : FreshFor query.names.next fixtureCaller.bindings := by decide +kernel
theorem prior_fresh : FreshFor query.names.prior fixtureCaller.bindings := by decide +kernel

theorem initial_frame : Frame FlatQueryRowCodec.integers 10 20 0 query query.legs fixtureCaller :=
  .frontier fixtureCaller initial_resolved_fixed.1 initial_resolved_fixed.2 next_fresh prior_fresh

theorem initial_decoded : Decoded FlatQueryRowCodec.integers query.handles fixtureInitial := by
  intro handle member
  have same : handle = .self := by simpa [query, Query.handles] using member
  subst handle
  exact ⟨CTLUntilMixedStore.Controls.atoms, CTLUntilMixedStore.Controls.rows, rfl,
    CTLUntilMixedStore.Controls.raw_rows_decode_without_loss⟩

/-- Final schema preservation follows from the phase theorem, not reduction
of the complete execution or an assumed final decoder result. -/
theorem full_preserves_decoding (after : State Unit)
    (completed : fixtureFull.stop = .complete after) :
    Decoded FlatQueryRowCodec.integers query.handles after := by
  apply completed_decoded FlatQueryRowCodec.integers 10 20 0 query (by decide)
    fixtureProgram fixtureCaller fixtureInitial after () [9] []
    initial_resolved_fixed.1 initial_resolved_fixed.2 next_fresh prior_fresh initial_decoded
  simpa only [query_template, query_legs, fixtureFull, fixtureExecute] using completed

theorem full_preserves_views (after : State Unit)
    (completed : fixtureFull.stop = .complete after) :
    CTLUntilRoundViews.Stable FlatQueryRowCodec.integers 10 20 0 query
      fixtureInitial.world.state after.world.state := by
  have result := CTLUntilRoundViews.completed_stable FlatQueryRowCodec.integers 10 20 (by decide)
    0 query (by decide) fixtureProgram fixtureCaller fixtureInitial after () [9] []
    initial_resolved_fixed.1 initial_resolved_fixed.2 next_fresh prior_fresh initial_decoded
  exact (result (by
    simpa only [query_template, query_legs, fixtureFull, fixtureExecute] using completed)).2

theorem initial_known :
    CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query fixtureInitial.world.state = some [] := by
  have observed := CTLUntilRoundPublication.observe_decoded FlatQueryRowCodec.integers
    (CTLUntilMixedStore.satisfactionView (10 : Int)) .self fixtureInitial.world.state
    CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.rows rfl
    CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
  have values : CTLUntilMixedStore.satisfactionView (10 : Int) CTLUntilMixedStore.Controls.rows = [] := by
    decide +kernel
  exact observed.trans (congrArg some values)

theorem initial_next_frontier :
    CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query fixtureInitial.world.state = some [9] := by
  have observed := CTLUntilRoundPublication.observe_decoded FlatQueryRowCodec.integers
    (List.filterMap (CTLUntilMixedStore.frontSelect (10 : Int) 1)) .self fixtureInitial.world.state
    CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.rows rfl
    CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
  have values : CTLUntilMixedStore.Controls.rows.filterMap (CTLUntilMixedStore.frontSelect (10 : Int) 1) = [9] := by
    decide +kernel
  exact observed.trans (congrArg some values)

theorem full_publication (after : State Unit)
    (completed : fixtureFull.stop = .complete after) :
    CTLUntilRoundPublication.Published FlatQueryRowCodec.integers 10 0 query [] [9] 0 after := by
  have result := CTLUntilRoundPublication.completed_publication FlatQueryRowCodec.integers 10 20 0 query
    (by decide) fixtureProgram fixtureCaller fixtureInitial after () [9] []
    initial_resolved_fixed.1 initial_resolved_fixed.2 next_fresh prior_fresh initial_decoded
    [] [9] initial_known initial_next_frontier
  exact (result (by
    simpa only [query_template, query_legs, fixtureFull, fixtureExecute] using completed)).2

theorem full_fixed_label_count (after : State Unit)
    (completed : fixtureFull.stop = .complete after) (finalKnown : List Nat)
    (observed : CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query after.world.state = some finalKnown) :
    finalKnown.toFinset.card = after.scope.collected.length := by
  have counted := (full_publication after completed).fixed_label_count finalKnown observed
  simpa only [Nat.add_zero, List.toFinset_nil, Finset.card_empty, Nat.zero_add] using counted

-- Original duplicate occurrences remain in this completed fixture.
#guard (fixtureRows fixtureFull).map
  (fun atoms => atoms.count (call "fr" [number 10, number 0, number 2])) == some 2
#guard (fixtureRows fixtureFull).map
  (fun atoms => atoms.count (call "sat" [number 20, number 1])) == some 2

-- A pre-existing next-round row is retained, not replaced by the fresh delta.
#guard (fixtureRows fixtureFull).map
  (fun atoms => atoms.count (call "fr" [number 10, number 1, number 9])) == some 1
#guard ((fixtureRows fixtureFull).bind (CTLUntilMixedStore.decodeRows FlatQueryRowCodec.integers)).map
  (fun rows => rows.filterMap (CTLUntilMixedStore.frontSelect (10 : Int) 1)) == some [9, 1]

-- The output label cannot also be treated as an unchanged operand label.
theorem coincident_operand_query_changes :
    FlatQueryRelationCompilation.sourceScan [] CTLUntilMixedStore.Controls.output 0 CTLUntilMixedStore.Controls.after ≠
      FlatQueryRelationCompilation.sourceScan [] CTLUntilMixedStore.Controls.output 0 CTLUntilMixedStore.Controls.atoms := by
  have views := CTLUntilMixedStore.Controls.publication_keeps_inputs_but_changes_output_membership
  rw [views.2.2.2, views.2.2.1]
  decide

-- The generic raw worker can complete malformed publication; this is outside
-- the canonical typed-round template used by full_preserves_decoding.
#guard fixtureCompleted GuardedQueryGrowth.Controls.malformedFrRun
#guard ((GuardedQueryGrowth.Controls.after? GuardedQueryGrowth.Controls.malformedFrRun).bind
  (fun after => after.world.state.read .self)).bind
  (CTLUntilMixedStore.decodeRows FlatQueryRowCodec.integers) == none

def boundCapture : Query := {query with names := {query.names with next := query.names.formula}}

theorem bound_capture_reading : Bound fixtureCaller boundCapture.names.next 10 := by
  intro environment solved
  exact (initial_resolved_fixed.2 environment solved).1

theorem bound_capture_refuses_freshness : ¬FreshFor boundCapture.names.next fixtureCaller.bindings := by
  decide +kernel

#print axioms initial_resolved_fixed
#print axioms initial_frame
#print axioms full_preserves_decoding
#print axioms full_preserves_views
#print axioms full_publication
#print axioms full_fixed_label_count
#print axioms CTLUntilRoundPublication.completed_publication
#print axioms CTLUntilRoundPublication.Published.fixed_label_count
#print axioms bound_capture_refuses_freshness

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound.Controls
