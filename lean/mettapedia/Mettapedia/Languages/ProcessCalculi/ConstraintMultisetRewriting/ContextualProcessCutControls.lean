import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCutCertificates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference

/-!
# Checking event cuts in reverse does not reverse the physical execution

The certificate creates a row and then consumes it. Its two guards and cuts
may be inspected in either enumeration, while the reversed resource word
fails. Earlier questions keep their own equations; the final conjunction is
used for final consistency, never to justify an earlier ask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCutControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualProcessCatalogue
open ContextualSelectionViews.Controls (base locals atom)
open ContextualGuardedExecutionControls (initial)
open ContextualSchedulePromotionControls (combinedCertificate combined_checked production consumption)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def process := cutProcess combinedCertificate
def first : Fin process.size := ⟨0, by decide⟩
def second : Fin process.size := ⟨1, by decide⟩

theorem the_two_events_retain_different_cuts_and_worlds :
    process.cut first = [] ∧ process.cut second = [first] ∧
      (process.event first).guardWorld = {7} ∧
      (process.event second).guardWorld = {7, 99} := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide +kernel

theorem each_cut_retains_exactly_its_own_equations :
    process.problem first = [] ∧
      process.problem second = [(atom consumption.target.declarations, atom consumption.target.declarations)] := by
  constructor <;> with_unfolding_all rfl

theorem reverse_checking_is_accepted : process.CheckEnumeration [second, first] := by
  have accepted := (cut_process_acceptance_exact combinedCertificate).mpr combined_checked
  intro identity _member
  exact accepted identity

theorem reverse_resource_execution_refuses :
    ResourceOccupation.runs
      [(ResourceProcess.ports (process.event second).selection),
       (ResourceProcess.ports (process.event first).selection)] initial.inventory.configuration.present = none := by
  change ResourceOccupation.runs [([99], [], []), ([], [], [99])] ({7} : Finset Nat) = none
  decide +kernel

theorem accepted_cuts_recover_the_full_original_endpoint :
    ∃ path : Quiver.Path initial consumption.target,
      ContextualExecution.selections path = combinedCertificate.selections ∧
        ContextualExecution.fuels path = [0, 1] :=
  accepted_cut_process_has_original_execution combinedCertificate
    ((cut_process_acceptance_exact combinedCertificate).mpr combined_checked)

theorem unsupported_guard_is_still_refused_after_compiling_its_cut :
    ¬ (cutProcess (.snoc (.nil initial) ContextualSchedulePromotionControls.unsupported)).Admitted := by
  intro accepted
  have checks := (cut_process_acceptance_exact _).mp accepted
  apply ContextualSchedulePromotionControls.unsupported_guard_is_retained_and_refuses.2
  exact checks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCutControls
