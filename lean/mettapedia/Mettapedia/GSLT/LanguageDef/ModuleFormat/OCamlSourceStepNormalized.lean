import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSourceEntry
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointCanonical

/-! Ordinary source-step entry through the actual equation-saturated and
canonical runner. A tick may keep searching; a committed step enters a
control point for the independently specified source successor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem prepared_source_step_entry (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source next : OCaml.MachineState) (config target : Pattern)
    (built : prepare program = .ok prepared) (encoded : state? (patterns program) source = some config)
    (sourceStep : OCaml.machineStep program source = .ok (some next))
    (step : (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target) :
    ∃ rank, ControlPoint program next target rank := by
  obtain ⟨receipt, valid, same⟩ := Complete.Run.valid_of_step (epochPlan prepared table) [] (.base "MlConfig")
    (epoch_compiled_equations_empty program prepared table built) step
  obtain ⟨position, firing⟩ := GeneralRuleJobs.rootOnly_receipt (plan := epochPlan prepared table) rfl valid
  rw [same] at firing
  exact prepared_source_firing_entry program prepared table source next config target built position encoded sourceStep firing

theorem prepared_source_normalized_entry (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source next : OCaml.MachineState) (config target : Pattern)
    (built : prepare program = .ok prepared) (encoded : state? (patterns program) source = some config)
    (sourceStep : OCaml.machineStep program source = .ok (some next))
    (step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target) :
    ∃ rank, ControlPoint program next target rank := by
  obtain ⟨raw, step, committed⟩ := step
  obtain ⟨rank, point⟩ := prepared_source_step_entry program prepared table source next config raw built encoded sourceStep step
  have fixed := control_point_commit program prepared table built point
  have same : raw = target := fixed.symm.trans committed
  subst raw
  exact ⟨rank, point⟩

theorem source_runner_tick (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (quantum : Nat) (source next : OCaml.MachineState)
    (built : prepare program = .ok prepared)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (encoded : state? (patterns program) source = some machine.state)
    (sourceStep : OCaml.machineStep program source = .ok (some next)) :
    let advanced := Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine quantum
    ControlPoint program source advanced.state 0 ∨ ∃ rank, ControlPoint program next advanced.state rank := by
  rcases tick_commit_or_keep (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
    reached quantum with kept | committed
  · exact .inl (kept.1 ▸ ControlPoint.state encoded)
  · obtain ⟨receipt, valid, same⟩ := committed
    have step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical
        machine.state (Complete.Normalized.commit (epochPlan prepared table) .canonical receipt.target) :=
      ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid, rfl⟩
    obtain ⟨rank, point⟩ := prepared_source_normalized_entry program prepared table source next _ _ built encoded sourceStep step
    exact .inr ⟨rank, same ▸ point⟩

#print axioms prepared_source_step_entry
#print axioms prepared_source_normalized_entry
#print axioms source_runner_tick

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
