import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSourceEntry
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointControls

/-! Actual prepared closure entry, nullary construction and wrong-code /
wrong-branch controls distinguish source-step preservation from rule order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.SourceEntryControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open ServiceControls

theorem closure_instruction_has_source_entry (prepared : Prepared) (built : prepare lambdaProgram = .ok prepared) :
    ∃ target ordinal trace captured,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared provider)) [] (.base "MlConfig")
        (node "MlEvaluate" [code 2, environment [number 99], encodedRest]) ordinal trace captured captured [] target ∧
      ∃ rank, ControlPoint lambdaProgram (.returned (.closure (.lambda 2) [number 99]) rest) target rank := by
  obtain ⟨ordinal, row, position, formed, _⟩ := whole_plan_instruction lambdaProgram prepared 2
    (.lambda (.literal (.integer 0)) 1) built rfl (prepared_plan_complete lambdaProgram prepared built)
  obtain ⟨next, target, trace, captured, step, _, firing⟩ := direct_instruction_plan_step
    (program := lambdaProgram) (capturedEnvironment := [number 99]) (rest := rest)
    position (prepare_readback lambdaProgram prepared built).2.2.1
    (prepare_readback lambdaProgram prepared built).2.2.2.1 rfl (by trivial) formed (show continuation? (patterns lambdaProgram) rest = some encodedRest from rfl)
  have source : OCaml.machineStep lambdaProgram (.evaluate 2 [number 99] rest) =
      .ok (some (.returned (.closure (.lambda 2) [number 99]) rest)) := rfl
  have sameNext := Option.some.inj (Except.ok.inj (step.symm.trans source))
  subst next
  refine ⟨target, ordinal, trace, captured, firing, ?_⟩
  exact prepared_source_firing_entry lambdaProgram prepared provider _ _ _ target built position (by rfl) source firing

def nullaryProgram : OCaml.Program where
  code := #[.variant 2 3 []]
  entry := 0
  constructors := [⟨2,3,0⟩]

theorem nullary_source_finishes_before_target_build :
    OCaml.machineStep nullaryProgram (OCaml.begin nullaryProgram) = .ok (some (.returned (.variant 2 3 []) [])) ∧
    ControlPoint nullaryProgram (.returned (.variant 2 3 []) [])
      (node "MlBuildConfig" [build (.variant 2 3), valueList [], node "MlKDone"]) 3 :=
  ⟨rfl, .build (kind := .variant 2 3) (items := []) (rest := []) rfl rfl⟩

theorem wrong_code_cannot_fire {plan : GeneralExecutionAdmission.Plan} {row : GeneralExecutionAdmission.RulePlan}
    {ordinal : Nat} (parameter : OCaml.MatchPattern) (pool : List OCaml.MatchPattern) (environment rest : Pattern)
    (position : plan.rules[ordinal]? = some row)
    (formed : compileInstruction? pool 0 (.lambda parameter 1) = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true) :
    ¬ ∃ target trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
        (node "MlEvaluate" [code 1, environment, rest]) ordinal trace captured completed history target := by
  rintro ⟨target, trace, captured, completed, history, firing⟩
  have impossible := instruction_firing_reference position formed zero firing
  omega

theorem true_cannot_take_false_branch (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    (inputs : List Pattern) (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (wrong : baseLanguage.rewrites[5]? = some row.authored) :
    ¬ ∃ target trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
        (node "MlReturn" [literal (.boolean true), node "MlKBranch" inputs]) ordinal trace captured completed history target := by
  rintro ⟨target, trace, captured, completed, history, firing⟩
  have correct := enabled_boolean_return program prepared table "MlKBranch" true inputs built position (by simp) firing
  have expected : baseLanguage.rewrites[4]? = some row.authored := correct
  have distinct : baseLanguage.rewrites[4]? ≠ baseLanguage.rewrites[5]? := by decide +kernel
  exact distinct (expected.trans wrong.symm)

#print axioms closure_instruction_has_source_entry
#print axioms nullary_source_finishes_before_target_build
#print axioms wrong_code_cannot_fire
#print axioms true_cannot_take_false_branch

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.SourceEntryControls
