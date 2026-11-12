import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures

/-!
# Argument production with older work and an actual collection parent

These instantiate the finite-run invariant on the authored mixed-host source
fixture, before any typed frame exists. The nested source starts with collapse;
the older frontier call has a different return type and remains unrestricted
by the selected call's return recipe.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentHostControls

open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay PettaArgumentProgress
open PettaInheritedFixtures

theorem initial_safe (nested bad : Bool) : Safe (initial nested bad) := by
  apply root_frontier_safe
  intro item member
  rcases List.mem_cons.mp member with rfl | other
  · rfl
  · cases List.mem_singleton.mp other
    rfl

theorem ready_safe (nested bad : Bool) (reached : State Unit)
    (produced : ready nested bad = some reached) : Safe reached := by
  have kept := run_retained services (program bad) (entryFuel nested) (initial nested bad) (initial_safe nested bad)
  unfold ready at produced
  cases observed : ((PettaOccurrenceOverlay.machine services .eagerValue (program bad)).run
      (entryFuel nested) (initial nested bad)).2 with
  | exhausted final =>
      simp only [observed] at produced
      cases Option.some.inj produced
      exact kept reached (by simp only [observed, PettaCallerReturnMachine.exitState])
  | finished final | stuck final | suspended request final | faulted =>
      simp only [observed] at produced
      cases produced

/-- No numerical answer or terminating run is needed: every body-phase frame
in the reached host has all its declared operand positions. -/
theorem ready_body_operand (nested bad : Bool) (reached : State Unit)
    (produced : ready nested bad = some reached)
    (current : Scope Unit) (member : current ∈ reached.2.scopes) (item : Work Unit)
    (present : item ∈ current.frontier) (frame : CallFrame) (called : frame ∈ item.2.1.calls)
    (phase : frame.phase = .body) (index : Nat) (within : index < frame.row.parameters.length) :
    ∃ recipe, frame.ready[index]? = some recipe := by
  have aligned := ((ready_safe nested bad reached produced).2 current member).work item present frame called
  exact ready_index_available aligned phase index within

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentHostControls
