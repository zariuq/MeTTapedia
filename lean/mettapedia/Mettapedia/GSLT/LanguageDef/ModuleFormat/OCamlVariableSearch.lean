import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableFiring
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

/-! Actual variable search publishes exactly source-authorized indexed
lookup results. Only a completed search can certify missing lookup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem variable_search_iff {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan}
    {ordinal reference index : Nat} {program : OCaml.Program} {items : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (declared : program.instruction? reference = some (.variable index))
    (formed : compileInstruction? (patterns program) reference (.variable index) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (∃ work firing, firing ∈ (Complete.DeepRoot.run
      ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
        node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩ work
      (Complete.DeepRoot.start
        ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
          node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩)).publication ∧ firing.target = target) ↔
      ∃ actual, items[index]? = some actual ∧ target = node "MlReturn" [value actual, encodedRest] := by
  let request : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
      node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩
  constructor
  · rintro ⟨work, firing, published, rfl⟩
    have valid := Complete.DeepRoot.sound request work firing published
    obtain ⟨_, _, actual, found, _, same, _⟩ :=
      variable_firing_source position terms types declared formed resolved valid
    exact ⟨actual, found, same⟩
  · rintro ⟨actual, found, rfl⟩
    obtain ⟨_, trace, captured, valid⟩ := variable_plan_step position terms types declared found formed resolved
    let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], node "MlReturn" [value actual, encodedRest]⟩
    obtain ⟨work, published⟩ := Complete.DeepRoot.complete_in_limit (request := request) (firing := firing) valid
    exact ⟨work, firing, published, rfl⟩

theorem completed_variable_search_failure {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan}
    {ordinal reference index work : Nat} {program : OCaml.Program} {items : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (declared : program.instruction? reference = some (.variable index))
    (formed : compileInstruction? (patterns program) reference (.variable index) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (done : (Complete.DeepRoot.run
      ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
        node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩ work
      (Complete.DeepRoot.start
        ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
          node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩)).complete = true) :
    items[index]? = none ↔ (Complete.DeepRoot.run
      ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
        node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩ work
      (Complete.DeepRoot.start
        ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
          node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩)).publication = [] := by
  let request : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
      node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩
  change items[index]? = none ↔ (Complete.DeepRoot.run request work (Complete.DeepRoot.start request)).publication = []
  constructor
  · intro failed
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro firing published
    have valid := Complete.DeepRoot.sound request work firing published
    obtain ⟨_, _, actual, found, _⟩ := variable_firing_source position terms types declared formed resolved valid
    rw [failed] at found
    cases found
  · intro empty
    cases found : items[index]? with
    | none => rfl
    | some actual =>
      obtain ⟨_, trace, captured, valid⟩ := variable_plan_step position terms types declared found formed resolved
      let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], node "MlReturn" [value actual, encodedRest]⟩
      have published := Complete.DeepRoot.exact_of_complete request work done (firing := firing) valid
      rw [empty] at published
      cases published

#print axioms variable_search_iff
#print axioms completed_variable_search_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
