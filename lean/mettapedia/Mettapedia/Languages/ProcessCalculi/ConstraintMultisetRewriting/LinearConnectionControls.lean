import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Physical connection controls: residuals, global solutions and cycles

The positive certificate uses the existing caller-binding example and keeps
its surviving occurrence. Negative controls separate an undeclared rule,
a wrong shared assignment, repeated physical consumption and a closed cycle
of otherwise complementary, linearly used occurrence ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls
open ConditionalComposite
open LinearConnectionLayout

def callEvent : Event (Term signature) Nat := (callRule, callSelection)
def callProgram : Set (RuleInstance (Term signature)) := {callRule}

theorem the_existing_call_is_a_static_connection_certificate :
    Certificate A callProgram zero label initial [callEvent] := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, A.models_nil zero, ?_⟩
  · intro event member
    have same : event = callEvent := List.mem_singleton.mp member
    subst event
    exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro event member
    have same : event = callEvent := List.mem_singleton.mp member
    subst event
    exact ⟨rfl, rfl⟩
  · intro event member
    have same : event = callEvent := List.mem_singleton.mp member
    subst event
    exact Set.mem_singleton _
  · apply (supplied_singleton_iff _ _).mpr
    decide
  · intro event member equation inConnections
    have sameEvent : event = callEvent := List.mem_singleton.mp member
    subst event
    have sameEquation : equation = (f (.const 0), f (.var 0)) := by
      simpa [callEvent, addedEquations, Selection.equations, callRule, callSelection, label] using inConnections
    subst equation
    rfl

theorem static_connections_execute_and_keep_the_residual_identity :
    ConditionalSchedule.Executable A label initial [callEvent] ∧
      (ConditionalSchedule.follow label initial [callEvent]).present = {1, 2} := by
  refine ⟨the_existing_call_is_a_static_connection_certificate.executes.1, ?_⟩
  rw [the_existing_call_is_a_static_connection_certificate.final_rows]
  decide

theorem every_residual_reader_sees_the_same_shared_solution :
    PositiveResourceProjection.realized A zero label 1 = .const 0 := rfl

theorem a_different_assignment_is_not_the_same_connection_proof :
    ¬ Certificate A callProgram one label initial [callEvent] := by
  intro layout
  exact caller_value_cannot_stay_arbitrary layout.executes.2

theorem an_unlisted_rule_is_not_a_logical_declaration :
    ¬ Certificate A (∅ : Set (RuleInstance (Term signature))) zero label initial [callEvent] := by
  intro layout
  exact layout.declared callEvent (List.mem_singleton_self _)

def groundLabel (identity : Nat) : Term signature := .const identity

def edgeRule (input output : Nat) : RuleInstance (Term signature) :=
  ⟨[.const input], [], [], [], [.const output]⟩

def edge (input output : Nat) : Event (Term signature) Nat :=
  (edgeRule input output, ⟨[input], [], [output]⟩)

def cycle : List (Event (Term signature) Nat) := [edge 1 0, edge 0 1]
def emptyBoundary : Configuration (Term signature) Nat := ⟨[], ∅⟩

theorem the_cycle_uses_every_physical_input_and_output_once :
    (cycle.flatMap fun event => event.2.made).Nodup ∧
      (cycle.flatMap fun event => event.2.taken).Nodup := by decide

theorem the_cycle_ports_all_match_under_one_assignment (assignment : Subst signature) :
    ∀ event ∈ cycle, A.Models assignment (addedEquations groundLabel event.1 event.2) := by
  intro event member
  rcases List.mem_cons.mp member with rfl | later
  · intro equation member
    have same : equation = (Term.const (σ := signature) 1, .const 1) := by
      simpa [edge, edgeRule, groundLabel, addedEquations, Selection.equations] using member
    subst equation
    rfl
  · have sameEvent : event = edge 0 1 := List.mem_singleton.mp later
    subst event
    intro equation member
    have same : equation = (Term.const (σ := signature) 0, .const 0) := by
      simpa [edge, edgeRule, groundLabel, addedEquations, Selection.equations] using member
    subst equation
    rfl

/-- Matching every port and using it once cannot bootstrap a cyclic net. -/
theorem the_cyclic_connections_have_no_topological_certificate (assignment : Subst signature) :
    ¬ Certificate A Set.univ assignment groundLabel emptyBoundary cycle := by
  intro layout
  have impossible := layout.supplied [] (edge 1 0) [edge 0 1] rfl (x := 1) (by decide)
  simp [emptyBoundary] at impossible

theorem no_reordering_bootstraps_the_cyclic_connections (assignment : Subst signature)
    (order : List (Event (Term signature) Nat)) (perm : cycle.Perm order) :
    ¬ Certificate A Set.univ assignment groundLabel emptyBoundary order := by
  intro layout
  cases order with
  | nil => have impossible := perm.length_eq; simp [cycle] at impossible
  | cons first rest =>
      have member : first ∈ cycle := perm.mem_iff.mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp member with rfl | other
      · have impossible := layout.supplied [] (edge 1 0) rest rfl (x := 1) (by decide)
        simp [emptyBoundary] at impossible
      · have same : first = edge 0 1 := List.mem_singleton.mp other
        subst first
        have impossible := layout.supplied [] (edge 0 1) rest rfl (x := 0) (by decide)
        simp [emptyBoundary] at impossible

def consume : Event (Term signature) Nat :=
  (⟨[.const 0], [], [], [], []⟩, ⟨[0], [], []⟩)

theorem one_physical_resource_cannot_supply_two_consuming_ports (assignment : Subst signature) :
    ¬ Certificate A Set.univ assignment groundLabel ⟨[], {0}⟩ [consume, consume] := by
  intro layout
  have distinct := layout.consumed_distinct
  exact (by decide : ¬ ([0, 0] : List Nat).Nodup) distinct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionControls
