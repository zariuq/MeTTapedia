import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointCanonical

/-! Canonical execution commits retain the independent administrative source
state. A reached runner tick either keeps its state or makes a strictly
rank-decreasing, source-preserving step while administration is pending.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem administrative_normalized_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config target : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (positive : 0 < rank)
    (step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target) :
    ∃ nextRank, ControlPoint program source target nextRank ∧ nextRank < rank := by
  obtain ⟨raw, step, committed⟩ := step
  obtain ⟨nextRank, nextPoint, smaller⟩ := administrative_step_preserves_source program prepared table built invariant point positive step
  have fixed := control_point_commit program prepared table built nextPoint
  have same : raw = target := fixed.symm.trans committed
  subst raw
  exact ⟨nextRank, nextPoint, smaller⟩

theorem administrative_runner_tick (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table))
      GeneralOccurrenceSemantics.Receipt) (quantum : Nat)
    {source : OCaml.MachineState} {rank : Nat}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (point : ControlPoint program source machine.state rank) (positive : 0 < rank) :
    let next := Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine quantum
    ∃ nextRank, ControlPoint program source next.state nextRank ∧ nextRank ≤ rank := by
  rcases tick_commit_or_keep (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
    reached quantum with kept | committed
  · exact ⟨rank, kept.1 ▸ point, Nat.le_refl _⟩
  · obtain ⟨receipt, valid, next⟩ := committed
    have step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical
        machine.state (Complete.Normalized.commit (epochPlan prepared table) .canonical receipt.target) :=
      ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid, rfl⟩
    obtain ⟨nextRank, nextPoint, smaller⟩ := administrative_normalized_step program prepared table built invariant point positive step
    exact ⟨nextRank, next ▸ nextPoint, Nat.le_of_lt smaller⟩

#print axioms administrative_normalized_step
#print axioms administrative_runner_tick

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
