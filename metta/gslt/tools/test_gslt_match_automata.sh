#!/usr/bin/env bash
set -euo pipefail

script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$script_root"
cetta_bin=${CETTA_BIN:-./cetta}
petta_runner=${PETTA_RUNNER:-}

run_metta() {
  # Program composition loads every source into the same evaluation space.
  if [[ -n "$petta_runner" ]]; then
    cat "$@" | bash "$petta_runner" --silent /dev/stdin
  else
    cat "$@" | CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet /dev/stdin
  fi
}

check_controls() {
  local family=$1 expected=$2
  awk -v family="$family" -v expected="$expected" '
    {
      selected = family == "normalized" ? $1 ~ /^\(normalized-/ : $1 == "(" family
      if (selected) {
        count++
        wanted = family == "AutomataControl" ? " true true\\)$" : " true\\)$"
        if ($0 !~ wanted) bad++
        key = family == "normalized" ? $1 : $2
        if (seen[key]++) bad++
      }
    }
    END {
      if (count != expected || bad != 0) {
        printf "%s gate: expected %d exact controls, got %d with %d failures\n", family, expected, count, bad > "/dev/stderr"
        exit 1
      }
    }'
}

output=$(run_metta lib/gslt_match_automata.metta tests/petta/gslt_match_automata_controls.metta)
printf '%s\n' "$output"
printf '%s\n' "$output" | check_controls AutomataControl 62

rule_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta \
  tests/petta/gslt_rule_execution_controls.metta)
printf '%s\n' "$rule_output"
printf '%s\n' "$rule_output" | check_controls RuleExecutionControl 273
printf '%s\n' "$rule_output" | check_controls ScopedMetadataControl 54
printf '%s\n' "$rule_output" | check_controls ScopedMatcherControl 45
printf '%s\n' "$rule_output" | check_controls ScopedContextControl 11

normalized_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta lib/gslt_match_normalized.metta \
  tests/petta/gslt_match_normalized_controls.metta)
printf '%s\n' "$normalized_output"
printf '%s\n' "$normalized_output" | check_controls normalized 22
printf '%s\n' "$normalized_output" | check_controls NormalizedDispatchControl 18

module_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta \
  lib/gslt_module.metta tests/petta/gslt_module_controls.metta)
printf '%s\n' "$module_output"
printf '%s\n' "$module_output" | check_controls ModuleExecutionControl 94

premise_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta tests/petta/gslt_premise_operations_controls.metta)
printf '%s\n' "$premise_output"
printf '%s\n' "$premise_output" | check_controls PremiseOperationControl 85
printf '%s\n' "$premise_output" | check_controls OpenAdmissionControl 200

equation_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta \
  lib/gslt_equation_execution.metta tests/petta/gslt_equation_execution_controls.metta)
printf '%s\n' "$equation_output"
printf '%s\n' "$equation_output" | check_controls EquationExecutionControl 21

context_output=$(run_metta lib/gslt_match_automata.metta lib/gslt_rule_execution.metta \
  lib/gslt_premise_operations.metta \
  lib/gslt_equation_execution.metta lib/gslt_equation_contexts.metta \
  tests/petta/gslt_equation_contexts_controls.metta)
printf '%s\n' "$context_output"
printf '%s\n' "$context_output" | check_controls EquationContextControl 70
printf '%s\n' "$context_output" | check_controls EquationAcquisitionControl 20

driver_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_execution_driver.metta lib/gslt_rule_readout_cache.metta lib/gslt_program_driver.metta \
  tests/petta/gslt_typed_sites_controls.metta tests/petta/gslt_rule_readout_cache_controls.metta \
  tests/petta/gslt_program_driver_controls.metta)
printf '%s\n' "$driver_output"
printf '%s\n' "$driver_output" | check_controls TypedSitesControl 10
printf '%s\n' "$driver_output" | check_controls ReadoutCacheControl 11
printf '%s\n' "$driver_output" | check_controls ProgramDriverControl 24

resumption_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_execution_driver.metta lib/gslt_rule_readout_cache.metta lib/gslt_program_driver.metta \
  lib/gslt_program_resumption.metta tests/petta/gslt_program_resumption_controls.metta)
printf '%s\n' "$resumption_output"
printf '%s\n' "$resumption_output" | check_controls ProgramResumptionControl 13

rho_lex_output=$(run_metta lib/gslt_rho_lex_canonical.metta tests/petta/gslt_rho_lex_canonical_controls.metta)
printf '%s\n' "$rho_lex_output"
printf '%s\n' "$rho_lex_output" | check_controls RhoLexCanonicalControl 12

rho_runner_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_execution_driver.metta lib/gslt_rule_readout_cache.metta lib/gslt_program_driver.metta \
  lib/gslt_program_resumption.metta lib/gslt_rho_lex_canonical.metta lib/gslt_rho_runner.metta \
  tests/petta/gslt_rho_runner_controls.metta)
printf '%s\n' "$rho_runner_output"
printf '%s\n' "$rho_runner_output" | check_controls RhoRunControl 5
printf '%s\n' "$rho_runner_output" | check_controls RhoSearchControl 8
printf '%s\n' "$rho_runner_output" | check_controls RhoProcessControl 9
printf '%s\n' "$rho_runner_output" | check_controls RhoPublicationControl 9
printf '%s\n' "$rho_runner_output" | check_controls RhoCellControl 8

live_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_execution_driver.metta lib/gslt_rule_readout_cache.metta lib/gslt_program_driver.metta \
  lib/gslt_program_resumption.metta lib/gslt_live_runner.metta tests/petta/gslt_live_runner_controls.metta)
printf '%s\n' "$live_output"
printf '%s\n' "$live_output" | check_controls LiveRunControl 12

emitted_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_execution_driver.metta lib/gslt_rule_readout_cache.metta lib/gslt_program_driver.metta \
  lib/gslt_program_resumption.metta lib/gslt_live_runner.metta tests/petta/emitted/arith.metta \
  tests/petta/emitted/cycle.metta tests/petta/emitted/partrec.metta tests/petta/gslt_emitted_module_controls.metta)
printf '%s\n' "$emitted_output"
printf '%s\n' "$emitted_output" | check_controls EmittedRunControl 6

reflection_output=$(run_metta lib/gslt_scoped_execution.metta tests/petta/gslt_scoped_reflection_controls.metta)
printf '%s\n' "$reflection_output"
printf '%s\n' "$reflection_output" | check_controls ScopedReflectionControl 30

descent_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_descent_execution.metta \
  tests/petta/gslt_descent_controls.metta)
printf '%s\n' "$descent_output"
printf '%s\n' "$descent_output" | check_controls DescentControl 58

descent_state_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_descent_execution.metta \
  tests/petta/gslt_descent_state_controls.metta)
printf '%s\n' "$descent_state_output"
printf '%s\n' "$descent_state_output" | check_controls DescentStateControl 21

canonical_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta \
  tests/petta/gslt_canonical_controls.metta)
printf '%s\n' "$canonical_output"
printf '%s\n' "$canonical_output" | check_controls CanonicalControl 22

complete_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/gslt_complete_controls.metta)
printf '%s\n' "$complete_output"
printf '%s\n' "$complete_output" | check_controls StepControl 12
printf '%s\n' "$complete_output" | check_controls PredecessorControl 2
printf '%s\n' "$complete_output" | check_controls LimitControl 2
printf '%s\n' "$complete_output" | check_controls ClassControl 12
printf '%s\n' "$complete_output" | check_controls RunnerControl 8
printf '%s\n' "$complete_output" | check_controls ExploreControl 4
printf '%s\n' "$complete_output" | check_controls VariantControl 5
printf '%s\n' "$complete_output" | check_controls LawsControl 8

complete_module_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta \
  lib/gslt_collection_selection.metta lib/gslt_collection_machine.metta lib/gslt_collection_logged_search.metta \
  lib/gslt_collection_backend.metta lib/gslt_collection_contexts.metta lib/gslt_recursive_collection.metta \
  lib/gslt_collection_presentation.metta lib/gslt_collection_handoff.metta lib/gslt_collection_continuation.metta \
  lib/gslt_collection_occurrences.metta lib/gslt_collection_install.metta lib/gslt_collection_match_lanes.metta \
  lib/gslt_collection_collector.metta lib/gslt_collection_occurrence_machine.metta \
  lib/gslt_collection_occurrence_discovery.metta lib/gslt_collection_occurrence_search.metta lib/gslt_runner.metta \
  tests/petta/emitted/complete_lambda.metta \
  tests/petta/emitted/complete_guarded.metta tests/petta/emitted/complete_sealed.metta \
  tests/petta/emitted/complete_branching.metta tests/petta/emitted/complete_unstratified.metta \
  tests/petta/emitted/complete_petri.metta tests/petta/emitted/complete_graph.metta \
  tests/petta/emitted/complete_produced.metta tests/petta/emitted/complete_produced_empty.metta \
  tests/petta/gslt_complete_module_controls.metta)
printf '%s\n' "$complete_module_output"
printf '%s\n' "$complete_module_output" | check_controls CompleteModuleControl 24

rho_module_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rho.metta tests/petta/emitted/rho_standard.metta tests/petta/gslt_rho_module_controls.metta)
printf '%s\n' "$rho_module_output"
printf '%s\n' "$rho_module_output" | check_controls RhoModuleControl 12

rho_quotedrop_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rho.metta tests/petta/emitted/rho_quotedrop.metta tests/petta/gslt_rho_quotedrop_controls.metta)
printf '%s\n' "$rho_quotedrop_output"
printf '%s\n' "$rho_quotedrop_output" | check_controls RhoQuoteDropControl 10

rho_model_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rho_quotedrop.metta tests/petta/emitted/rho_model.metta tests/petta/gslt_rho_model_controls.metta)
printf '%s\n' "$rho_model_output"
printf '%s\n' "$rho_model_output" | check_controls RhoModelControl 14

rholang_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rholang.metta tests/petta/gslt_rholang_module_controls.metta)
printf '%s\n' "$rholang_output"
printf '%s\n' "$rholang_output" | check_controls RholangModuleControl 4

rholang_closure_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rholang_closure.metta tests/petta/gslt_rholang_closure_controls.metta)
printf '%s\n' "$rholang_closure_output"
printf '%s\n' "$rholang_closure_output" | check_controls RholangClosureControl 3

rholang_freeze_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/rholang_freeze.metta tests/petta/gslt_rholang_freeze_controls.metta)
printf '%s\n' "$rholang_freeze_output"
printf '%s\n' "$rholang_freeze_output" | check_controls RholangFreezeControl 3

ambient_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/ambient.metta tests/petta/gslt_ambient_controls.metta)
printf '%s\n' "$ambient_output"
printf '%s\n' "$ambient_output" | check_controls AmbientControl 29

upstream_lambda_output=$(run_metta lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta \
  lib/gslt_descent_execution.metta lib/gslt_complete.metta lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta \
  tests/petta/emitted/upstream_lambda.metta tests/petta/gslt_upstream_lambda_controls.metta)
printf '%s\n' "$upstream_lambda_output"
printf '%s\n' "$upstream_lambda_output" | check_controls LambdaControl 14
