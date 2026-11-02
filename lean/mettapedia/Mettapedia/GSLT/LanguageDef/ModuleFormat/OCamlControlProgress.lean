import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardApplication
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlForwardPattern
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceServiceRequest
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSelectionSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedOrderedSelection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBuildSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitiveAnswers
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceEpochInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompletedPreservation

/-! Every source control point of a finite successful source evaluation can
step, request one of the existing services, or expose a terminal result.
An actually exhausted runner excludes the step case. All administrative
constructors are covered, including duplicate pattern occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem administrative_progress (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (point : ControlPoint program source config rank) (positive : 0 < rank) :
    (∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target) ∨
      SourceServiceRequest program config := by
  cases point with
  | state _ => omega
  | application resolved applied =>
    exact .inl (prepared_application_can_step program prepared table _ _ _ _ _ built signatures resolved applied)
  | @matchOne index parameter argument body captured rest encodedRest indexed resolved =>
    cases matched : OCaml.matchPattern parameter argument with
    | none => exact .inr (.matchFailure index parameter argument body captured rest encodedRest indexed resolved matched)
    | some bindings =>
      exact .inl ⟨_, prepared_match_success_step_any_index program prepared table index parameter argument body captured rest encodedRest
        bindings built signatures indexed resolved matched⟩
  | @select clauses encodedClauses argument captured rest encodedRest _ listed resolved _ =>
    cases clauses with
    | nil =>
      have same : encodedClauses = node "MlClauseNil" := (Option.some.inj ((clauseList?_nil _).symm.trans listed)).symm
      subst encodedClauses
      exact .inl ⟨_, prepared_select_empty_step program prepared table argument captured rest encodedRest built signatures resolved⟩
    | cons clause clauses =>
      obtain ⟨index, later, referenced, _, tailResolved, same⟩ := clause_list_cons_readback listed
      subst encodedClauses
      exact .inl ⟨_, prepared_select_first_step program prepared table clause clauses (patternId index) later argument captured rest encodedRest
        built signatures referenced tailResolved resolved⟩
  | @clause index clause clauses later argument captured rest encodedRest _ indexed listed resolved _ =>
    cases matched : OCaml.matchPattern clause.pattern argument with
    | none => exact .inr (.clauseFailure index clause clauses later argument captured rest encodedRest indexed listed resolved matched)
    | some bindings =>
      exact .inl ⟨_, prepared_clause_success_step_any_index program prepared table index clause clauses later argument captured rest encodedRest
        bindings built signatures indexed listed resolved matched⟩
  | @build kind items rest encodedRest _ resolved _ =>
    cases kind with
    | tuple => exact .inl ⟨_, prepared_tuple_build_step program prepared table items rest encodedRest built signatures resolved⟩
    | variant typeId constructor =>
      exact .inl ⟨_, prepared_variant_build_step program prepared table typeId constructor items rest encodedRest built signatures resolved⟩
    | primitive operator =>
      exact .inl ⟨_, prepared_primitive_build_step program prepared table operator items rest encodedRest built signatures resolved⟩
  | @primitive operator arguments result rest encodedRest resolved evaluated =>
    exact .inr (.primitive operator arguments result rest encodedRest resolved evaluated)
  | answer resolved =>
    obtain ⟨target, _, step⟩ := prepared_primitive_answer_step program prepared table _ _ _ built signatures resolved
    exact .inl ⟨target, step⟩

theorem control_point_progress (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (point : ControlPoint program source config rank) (completed : OCaml.run program budget source = .complete result) :
    (∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target) ∨
      SourceServiceRequest program config ∨ state? (patterns program) (.halted result) = some config := by
  by_cases zero : rank = 0
  · subst rank
    have encoded := rank_zero_encodes_source point
    rcases OCaml.completed_run_cases completed with terminal | ⟨next, _, sourceStep, _⟩
    · subst source
      exact .inr (.inr encoded)
    · exact .inl (prepared_source_can_step program prepared table source next config built signatures encoded sourceStep)
  · rcases administrative_progress program prepared table built signatures point (Nat.pos_of_ne_zero zero) with step | service
    · exact .inl step
    · exact .inr (.inl service)

theorem settled_control_point_cases (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    {source : OCaml.MachineState} {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (point : ControlPoint program source runner.state rank) (completed : OCaml.run program budget source = .complete result)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done) :
    SourceServiceRequest program runner.state ∨ state? (patterns program) (.halted result) = some runner.state := by
  rcases control_point_progress program prepared table built invariant.source.signatures point completed with ⟨target, step⟩ | cases
  · have checked := Complete.Predecessors.equationsChecked_of_complete (invariant.complete built)
    exact False.elim (Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig") checked reached done target step)
  · exact cases

#print axioms administrative_progress
#print axioms control_point_progress
#print axioms settled_control_point_cases

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
