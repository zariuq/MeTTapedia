import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEvaluationEntry
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledFamilies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableFiring

/-! Every enabled evaluation row of a prepared program enters a control point
for the independently supplied successful source transition. Its instruction
and code reference are recovered from the actual selected row and firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem prepared_evaluation_entry (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (reference : OCaml.Code) (sourceEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest target : Pattern) (next : OCaml.MachineState) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (sourceStep : OCaml.machineStep program (.evaluate reference sourceEnvironment rest) = .ok (some next))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment sourceEnvironment, encodedRest]) ordinal trace captured completed history target) :
    ∃ rank, ControlPoint program next target rank := by
  obtain ⟨rowReference, instruction, declared, formed⟩ := enabled_evaluate_family program prepared table _ built position firing
  have zero := prepared_selected_row_zero program prepared table built position
  have same := instruction_firing_reference position formed zero firing
  subst rowReference
  cases instruction with
  | «variable» index =>
    obtain ⟨_, _, actual, _, step, _, encoded⟩ := variable_firing_source position
      (prepare_readback program prepared built).2.2.1 (prepare_readback program prepared built).2.2.2.1
      declared formed resolved firing
    have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
    subst next
    exact ⟨0, .state encoded⟩
  | tuple fields =>
    exact build_evaluation_entry program reference .tuple fields sourceEnvironment rest encodedRest target next
      position formed zero declared resolved sourceStep firing
  | variant typeId constructor fields =>
    exact build_evaluation_entry program reference (.variant typeId constructor) fields sourceEnvironment rest encodedRest target next
      position formed zero declared resolved sourceStep firing
  | primitive operator arguments =>
    exact build_evaluation_entry program reference (.primitive operator) arguments sourceEnvironment rest encodedRest target next
      position formed zero declared resolved sourceStep firing
  | _ => exact ⟨0, direct_evaluation_entry program reference _ sourceEnvironment rest encodedRest target next
      position formed zero (by trivial) declared resolved sourceStep firing⟩

#print axioms prepared_evaluation_entry

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
