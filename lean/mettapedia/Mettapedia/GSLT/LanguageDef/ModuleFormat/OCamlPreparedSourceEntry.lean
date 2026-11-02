import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedReturnEntry
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedEvaluationEntry

/-! Every actual prepared firing from an ordinary encoded source state enters
an administrative control point for its independent successful source step.
All source-machine and continuation constructors are covered.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem prepared_source_firing_entry (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source next : OCaml.MachineState) (config target : Pattern)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (encoded : state? (patterns program) source = some config)
    (sourceStep : OCaml.machineStep program source = .ok (some next))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      config ordinal trace captured completed history target) :
    ∃ rank, ControlPoint program next target rank := by
  cases source with
  | halted result => cases sourceStep
  | evaluate reference sourceEnvironment rest =>
    simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at encoded
    obtain ⟨encodedRest, resolved, rfl⟩ := encoded
    exact prepared_evaluation_entry program prepared table reference sourceEnvironment rest encodedRest target next
      built position resolved sourceStep firing
  | returned actual rest =>
    simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at encoded
    obtain ⟨encodedContinuation, resolved, rfl⟩ := encoded
    cases rest with
    | nil =>
      have same : encodedContinuation = node "MlKDone" := Option.some.inj resolved.symm
      subst encodedContinuation
      obtain ⟨index, authored, member⟩ := enabled_return_continuation program prepared table "MlKDone" _ _ built position firing
      have candidates : returnCandidates "MlKDone" = [0] := by decide +kernel
      rw [candidates] at member
      have sameIndex := List.mem_singleton.mp member
      subst index
      have zero := prepared_selected_row_zero program prepared table built position
      obtain ⟨_, _, actualStep, readback⟩ := return_done_source_step (program := program) (pool := patterns program)
        position authored zero firing
      have sameNext := Option.some.inj (Except.ok.inj (actualStep.symm.trans sourceStep))
      subst next
      exact ⟨0, .state readback⟩
    | cons frame rest =>
      simp only [continuation?, Option.bind_eq_bind, Option.bind_eq_some_iff] at resolved
      obtain ⟨encodedRest, resolved, framed⟩ := resolved
      exact prepared_return_frame_entry program prepared table actual frame rest encodedRest encodedContinuation target next
        built position resolved framed sourceStep firing

#print axioms prepared_source_firing_entry

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
