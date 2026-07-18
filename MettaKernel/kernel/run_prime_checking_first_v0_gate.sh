#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

"$ROOT/run_prime_minimal_checking_package_v0_gate.sh"
"$ROOT/run_prime_raw_checking_worked_metta_programs_v0_gate.sh"
"$ROOT/run_prime_metta_hotg_program_v0_gate.sh"
"$ROOT/run_prime_minimal_checking_package_v0_lean_gate.sh"
"$ROOT/run_prime_package_identity_v1_gate.sh"
"$ROOT/run_prime_subject_ref_v1_gate.sh"
"$ROOT/run_prime_fragment_adequacy_v1_gate.sh"
"$ROOT/run_prime_certificate_boundary_v1_gate.sh"
"$ROOT/run_prime_pettachainer_dag_replay_v1_gate.sh"

echo "PRIME CHECKING-FIRST V0 GATE: PASS (minimal package, worked programs, HOTG bridge, authenticated package and subject identities, source-derived fragment adequacy, cross-runtime certificate correspondence, real PeTTaChainer DAG replay, Megalodon differentials, and Lean witnesses)"
