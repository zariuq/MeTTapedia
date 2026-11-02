import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledKernelVariants
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowDependencies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternRowIdentity
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointDispatch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedOrderedSelection

/-! Every actual prepared administrative firing realizes the same independent
source state and strictly decreases its administrative rank. All declaration
families and pattern indices are recovered from the firing itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem administrative_firing_preserves_source (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config target : Pattern} {rank ordinal : Nat}
    {row : GeneralExecutionAdmission.RulePlan}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (positive : 0 < rank)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      config ordinal trace captured completed history target) :
    ∃ nextRank, ControlPoint program source target nextRank ∧ nextRank < rank := by
  have zero := prepared_selected_row_zero program prepared table built position
  cases point with
  | state _ => omega
  | application resolved applied =>
    obtain ⟨reference, instruction, rows, declared, compiled, authored⟩ :=
      enabled_apply_family program prepared table _ built position firing
    exact ⟨1, function_dispatch_lowers_rank program reference instruction rows _ _ _ _ target _
      position declared compiled authored zero resolved applied firing⟩
  | matchOne indexed resolved =>
    rcases enabled_match_one_family program prepared table _ built position firing with failed | matched
    · exact ⟨0, match_failure_lowers_rank program _ _ _ _ _ _ _ target
        position failed zero invariant indexed firing⟩
    · obtain ⟨rowIndex, parameter, poolAt, authored⟩ := matched
      have indexSame := match_one_row_index position authored zero firing
      subst rowIndex
      have parameterSame := Option.some.inj (poolAt.symm.trans indexed)
      subst parameter
      exact ⟨0, matched_pattern_lowers_rank program _ _ _ _ _ _ _ target
        position authored zero resolved firing⟩
  | @select clauses encodedClauses argument sourceEnvironment rest encodedRest _ listed resolved selected =>
    cases clauses with
    | nil =>
      have listSame : encodedClauses = node "MlClauseNil" :=
        (Option.some.inj ((clauseList?_nil _).symm.trans listed)).symm
      subst encodedClauses
      have authored := enabled_select_empty program prepared table built position _ _ _ firing
      exact ⟨0, select_empty_lowers_rank program _ _ _ _ target _ position authored zero selected firing⟩
    | cons clause clauses =>
      obtain ⟨index, later', _, patternAt, tailAt, listSame⟩ := clause_list_cons_readback listed
      subst encodedClauses
      have authored := enabled_select_clause program prepared table built position _ _ _ _ firing
      exact ⟨2 * clauses.length + 2, select_clause_lowers_rank program index clause clauses later' _ _ _ _ target _
        position authored zero patternAt tailAt resolved selected firing⟩
  | clause indexed listed resolved selected =>
    rcases enabled_clause_family program prepared table _ built position firing with failed | matched
    · exact ⟨_, clause_failure_lowers_rank program _ _ _ _ _ _ _ _ target _
        position failed zero invariant indexed listed resolved selected firing⟩
    · obtain ⟨rowIndex, parameter, poolAt, authored⟩ := matched
      have indexSame := clause_row_index position authored zero firing
      subst rowIndex
      have parameterSame := Option.some.inj (poolAt.symm.trans indexed)
      subst parameter
      exact ⟨0, matched_clause_lowers_rank program _ _ _ _ _ _ _ _ target _
        position authored zero resolved selected firing⟩
  | @build kind items rest encodedRest _ resolved finished =>
    cases kind with
    | tuple =>
      have authored := enabled_build_tuple program prepared table built position _ _ firing
      exact ⟨0, build_tuple_lowers_rank program items rest encodedRest target _ position authored zero resolved finished firing⟩
    | variant typeId constructor =>
      have authored := enabled_build_variant program prepared table built position typeId constructor _ _ firing
      exact ⟨0, build_variant_lowers_rank program typeId constructor items rest encodedRest target _
        position authored zero resolved finished firing⟩
    | primitive operator =>
      have authored := enabled_build_primitive program prepared table built position operator _ _ firing
      exact ⟨2, build_primitive_lowers_rank program operator items rest encodedRest target _
        position authored zero resolved finished firing⟩
  | primitive resolved evaluated =>
    have authored := enabled_primitive_family program prepared table _ built position firing
    exact ⟨1, primitive_query_lowers_rank program _ _ _ _ _ target position authored zero invariant resolved evaluated firing⟩
  | @answer result rest encodedRest resolved =>
    cases result with
    | ok actual =>
      have authored := enabled_answer_value program prepared table built position actual _ firing
      exact ⟨0, primitive_answer_lowers_rank program (.ok actual) rest encodedRest target position authored zero resolved firing⟩
    | error error =>
      have authored := enabled_answer_fault program prepared table built position error _ firing
      exact ⟨0, primitive_answer_lowers_rank program (.error error) rest encodedRest target position authored zero resolved firing⟩

#print axioms administrative_firing_preserves_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
