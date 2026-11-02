import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompletedPreservation

/-! Actual normalized transitions strictly decrease the remaining source
work or, at equal source work, the administrative rank. The budget comes
from the independent source run rather than from target search fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem normalized_step_progress (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config target : Pattern}
    {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (completed : OCaml.run program budget source = .complete result)
    (step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target) :
    ∃ next nextRank work, ControlPoint program next target nextRank ∧ OCaml.run program work next = .complete result ∧
      (work < budget ∨ work = budget ∧ nextRank < rank) := by
  by_cases zero : rank = 0
  · subst rank
    have encoded := rank_zero_encodes_source point
    rcases OCaml.completed_run_cases completed with stopped | ⟨next, _, sourceStep, _⟩
    · subst source
      exact False.elim (prepared_terminal_no_normalized_step program prepared table result config target built encoded step)
    · obtain ⟨nextRank, nextPoint⟩ := prepared_source_normalized_entry program prepared table source next config target
        built encoded sourceStep step
      obtain ⟨work, smaller, later⟩ := OCaml.completed_run_successor_smaller completed sourceStep
      exact ⟨next, nextRank, work, nextPoint, later, .inl smaller⟩
  · obtain ⟨nextRank, nextPoint, smaller⟩ := administrative_normalized_step program prepared table built invariant point
      (Nat.pos_of_ne_zero zero) step
    exact ⟨source, nextRank, budget, nextPoint, completed, .inr ⟨rfl, smaller⟩⟩

#print axioms normalized_step_progress

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
