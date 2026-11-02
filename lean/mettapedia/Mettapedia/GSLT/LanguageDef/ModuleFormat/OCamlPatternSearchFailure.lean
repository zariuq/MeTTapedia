import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

/-! Source pattern failure agrees with empty publication of a completed
actual root search. Pending work cannot certify failure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem completed_pattern_search_failure {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index work : Nat}
    {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {argument : OCaml.Value}
    {body : OCaml.Code} {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : row.authored = (patternRules index parameter)[0]'(by simp [patternRules]))
    (referenced : patternReference? pool parameter = some (patternId index))
    (resolved : continuation? pool rest = some encodedRest)
    (done : (Complete.DeepRoot.run
      ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
        node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest], ordinal⟩ work
      (Complete.DeepRoot.start
        ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
          node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest], ordinal⟩)).complete = true) :
    OCaml.matchPattern parameter argument = none ↔
      (Complete.DeepRoot.run
        ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
          node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest], ordinal⟩ work
        (Complete.DeepRoot.start
          ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
            node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest], ordinal⟩)).publication = [] := by
  let request : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions), [], .base "MlConfig",
      node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest], ordinal⟩
  change OCaml.matchPattern parameter argument = none ↔ (Complete.DeepRoot.run request work (Complete.DeepRoot.start request)).publication = []
  constructor
  · intro failed
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro firing present
    have valid := Complete.DeepRoot.sound request work firing present
    have impossible := (match_one_plan_failure (body := body) (capturedEnvironment := capturedEnvironment)
      position terms types authored referenced resolved).mp failed
    exact impossible ⟨firing.target, firing.trace, firing.captured, firing.completed, firing.history, valid⟩
  · intro empty
    apply (match_one_plan_failure (body := body) (capturedEnvironment := capturedEnvironment)
      position terms types authored referenced resolved).mpr
    rintro ⟨target, trace, captured, completed, history, valid⟩
    let firing : Complete.DeepRoot.Firing := ⟨trace, captured, completed, history, target⟩
    have present := Complete.DeepRoot.exact_of_complete request work done (firing := firing) valid
    rw [empty] at present
    cases present

#print axioms completed_pattern_search_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
