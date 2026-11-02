import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardEvaluation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardReturn
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceStepNormalized

/-! Every encoded successful source step enables a genuine prepared step.
The target enters the successor's administrative control point, and its
canonical commitment is already fixed by that source relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_return_can_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (actual : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern) (next : OCaml.MachineState)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (sourceStep : OCaml.machineStep program (.returned actual rest) = .ok (some next)) :
    ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value actual, encodedRest]) target := by
  cases rest with
  | nil =>
    have same : encodedRest = node "MlKDone" := Option.some.inj resolved.symm
    subst encodedRest
    have point : ControlPoint program (.returned actual []) (node "MlReturn" [value actual, node "MlKDone"]) 0 := .state rfl
    have nextPoint : ControlPoint program (.halted (.ok actual)) (node "MlDone" [value actual]) 0 := .state rfl
    exact ⟨_, prepared_base_control_step program prepared table 0 (by decide +kernel) built signatures point nextPoint
      (return_done_instance _)⟩
  | cons frame rest =>
    simp only [continuation?, Option.bind_eq_bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨tail, tailResolved, framed⟩ := resolved
    exact prepared_frame_can_step program prepared table actual frame rest tail encodedRest next
      built signatures tailResolved framed sourceStep

theorem prepared_source_can_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source next : OCaml.MachineState) (config : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (encoded : state? (patterns program) source = some config)
    (sourceStep : OCaml.machineStep program source = .ok (some next)) :
    ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target := by
  cases source with
  | halted result => cases sourceStep
  | evaluate reference captured rest =>
    simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at encoded
    obtain ⟨encodedRest, resolved, rfl⟩ := encoded
    exact prepared_evaluation_can_step program prepared table reference captured rest encodedRest next built signatures resolved sourceStep
  | returned actual rest =>
    simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at encoded
    obtain ⟨encodedRest, resolved, rfl⟩ := encoded
    exact prepared_return_can_step program prepared table actual rest encodedRest next built signatures resolved sourceStep

theorem prepared_source_step_realized (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source next : OCaml.MachineState) (config : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (encoded : state? (patterns program) source = some config)
    (sourceStep : OCaml.machineStep program source = .ok (some next)) :
    ∃ target rank, Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target ∧
      ControlPoint program next target rank := by
  obtain ⟨target, step⟩ := prepared_source_can_step program prepared table source next config built signatures encoded sourceStep
  obtain ⟨rank, point⟩ := prepared_source_step_entry program prepared table source next config target built encoded sourceStep step
  exact ⟨target, rank, ⟨target, step, control_point_commit program prepared table built point⟩, point⟩

#print axioms prepared_return_can_step
#print axioms prepared_source_can_step
#print axioms prepared_source_step_realized

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
