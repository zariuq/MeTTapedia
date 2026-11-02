import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompletedPreservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointRestart

/-! A whole run may span any finite sequence of provider epochs. Each segment
uses the actual normalized runner; restarting preserves its final source
control point and independent source result in the new provider epoch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem advance_then_restart_preserves_source_result (program : OCaml.Program) (prepared : Prepared)
    (table nextTable : GeneralPremise.ProviderSnapshot) (ticks quantum : Nat)
    (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    {source : OCaml.MachineState} {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (point : ControlPoint program source machine.state rank) (completed : OCaml.run program budget source = .complete result) :
    let advanced := Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum machine
    let search := Complete.Normalized.search (epochPlan prepared nextTable) [] (.base "MlConfig") .canonical
    let fresh := Machine.begin search (Complete.Normalized.commit (epochPlan prepared nextTable) .canonical advanced.state)
    Reached search fresh ∧ ∃ source nextRank work,
      ControlPoint program source fresh.state nextRank ∧ OCaml.run program work source = .complete result := by
  obtain ⟨nextSource, nextRank, work, nextPoint, later⟩ := runner_advance_preserves_completed_source program prepared table ticks quantum
    machine built invariant.source reached point completed
  obtain ⟨freshReached, freshPoint⟩ := control_point_epoch_restart program prepared nextTable built nextPoint
  exact ⟨freshReached, nextSource, nextRank, work, freshPoint, later⟩

#print axioms advance_then_restart_preserves_source_result

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
