#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$REPOSITORY/.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
PETTA_ROOT="${PETTA_ROOT:-$AIHUB/hyperon/PeTTa}"
PETTACHAINER_ROOT="${PETTACHAINER_ROOT:-$AIHUB/repos/PeTTaChainer}"
LEAN_ROOT="${PRIME_LEAN_ROOT:-$REPOSITORY/lean/mettapedia}"
SOURCE="$ROOT/prime_pettachainer_dag_replay_v1.metta"
PRODUCER="$ROOT/pettachainer_prime_dag_export_v1.metta"
LEAN_REL="Mettapedia/Languages/MeTTa/Prime/PeTTaChainerDAGReplayV1.lean"
LEAN_SOURCE="$LEAN_ROOT/$LEAN_REL"
LOGDIR="$ROOT/parity_logs"
CETTA_LOG="$LOGDIR/prime_pettachainer_dag_replay_v1_cetta.log"
PRODUCER_LOG="$LOGDIR/prime_pettachainer_dag_replay_v1_producer.log"
LEAN_LOG="$LOGDIR/prime_pettachainer_dag_replay_v1_lean.log"
EXPECTED_ASSERTIONS=27

mkdir -p "$LOGDIR"

if [[ "$(grep -c '^!(assertEqual' "$SOURCE")" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (assertion census changed)"
  exit 1
fi

replay_started_ns="$(date +%s%N)"
if ! "$CETTA" --lang prime "$SOURCE" >"$CETTA_LOG" 2>&1; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (CeTTa replay failed; log: $CETTA_LOG)"
  exit 1
fi
replay_finished_ns="$(date +%s%N)"
replay_milliseconds="$(( (replay_finished_ns - replay_started_ns) / 1000000 ))"
if grep -q 'Error\|❌' "$CETTA_LOG"; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (CeTTa assertion failed; log: $CETTA_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimePeTTaChainerDAGReplaySummaryV1 27 27 0)' "$CETTA_LOG")" -ne 1 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (CeTTa summary absent or duplicated)"
  exit 1
fi

if grep -Eq '\b(sorry|admit|axiom|native_decide|theorem_wanted)\b|_wanted' \
    "$LEAN_SOURCE"; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (forbidden Lean proof token)"
  exit 1
fi
if ! (cd "$LEAN_ROOT" && lake env lean "$LEAN_REL") >"$LEAN_LOG" 2>&1; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (Lean replay failed; log: $LEAN_LOG)"
  exit 1
fi
if grep -Eq '(^|[[:space:]])(error:|warning:)' "$LEAN_LOG"; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (Lean diagnostic found; log: $LEAN_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimePeTTaChainerDAGReplayLeanSummaryV1 24 24 0)' "$LEAN_LOG")" -ne 1 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (Lean summary absent or duplicated)"
  exit 1
fi
if [[ "$(grep -Fc 'depends on axioms: [propext,' "$LEAN_LOG")" -ne 3 ]] ||
   [[ "$(grep -Fxc ' Classical.choice,' "$LEAN_LOG")" -ne 3 ]] ||
   [[ "$(grep -Fxc ' Quot.sound]' "$LEAN_LOG")" -ne 3 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (Lean axiom footprint changed)"
  exit 1
fi

if [[ ! -f "$PETTA_ROOT/src/metta.pl" ]] ||
   [[ ! -d "$PETTACHAINER_ROOT/pettachainer/metta" ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (PeTTa or PeTTaChainer source unavailable)"
  exit 1
fi

python_libdir=""
if command -v python3.12 >/dev/null 2>&1; then
  python_libdir="$(python3.12 - <<'PY'
import sysconfig
print(sysconfig.get_config_var("LIBDIR") or "")
PY
)"
fi

(
  cd "$PETTACHAINER_ROOT/pettachainer/metta"
  if [[ -n "$python_libdir" ]] &&
     [[ -r "$python_libdir/libpython3.12.so.1.0" ]]; then
    export LD_LIBRARY_PATH="$python_libdir${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  fi
  if [[ -f "$PETTA_ROOT/mork_ffi/target/release/libmork_ffi.so" ]]; then
    export LD_PRELOAD="$PETTA_ROOT/mork_ffi/target/release/libmork_ffi.so"
  fi
  swipl --stack_limit=8g --no-pce -q \
    -s "$PETTA_ROOT/src/metta.pl" \
    -g "assertz(working_dir('$PETTACHAINER_ROOT/pettachainer/metta')),load_metta_file('$PRODUCER',_),halt" \
    -- --silent
) >"$PRODUCER_LOG" 2>&1

if [[ "$(grep -Fxc '(PeTTaChainerPrimeProducerSummaryV1 1 1 0)' "$PRODUCER_LOG")" -ne 1 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (producer summary absent or duplicated; log: $PRODUCER_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '((PeTTaForwardProofV1 (pathReachWitness (rule-proof conjunction (edgeToPath edgeAB) (edgeToReach edgeAB))) (STV 1.0 1.0)))' "$PRODUCER_LOG")" -ne 1 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (real proof-store result changed; log: $PRODUCER_LOG)"
  exit 1
fi

extract_payload() {
  local begin="$1"
  local end="$2"
  local log="$3"
  awk -v begin="$begin" -v end="$end" '
    $0 == begin { active = 1; next }
    $0 == end { active = 0; exit }
    active { print }
  ' "$log"
}

producer_dag="$(extract_payload '"PETTACHAINER_PRIME_DAG_BEGIN"' \
  '"PETTACHAINER_PRIME_DAG_END"' "$PRODUCER_LOG")"
cetta_dag="$(extract_payload PRIME_PETTACHAINER_DAG_BEGIN \
  PRIME_PETTACHAINER_DAG_END "$CETTA_LOG")"
cetta_digest="$(extract_payload PRIME_PETTACHAINER_DAG_DIGEST_BEGIN \
  PRIME_PETTACHAINER_DAG_DIGEST_END "$CETTA_LOG")"
certificate_bytes="$(extract_payload PRIME_PETTACHAINER_CERTIFICATE_BEGIN \
  PRIME_PETTACHAINER_CERTIFICATE_END "$CETTA_LOG")"
lean_dag="$(extract_payload PRIME_PETTACHAINER_DAG_BEGIN \
  PRIME_PETTACHAINER_DAG_END "$LEAN_LOG")"
lean_digest="$(extract_payload PRIME_PETTACHAINER_DAG_DIGEST_BEGIN \
  PRIME_PETTACHAINER_DAG_DIGEST_END "$LEAN_LOG")"
lean_certificate_bytes="$(extract_payload PRIME_PETTACHAINER_CERTIFICATE_BEGIN \
  PRIME_PETTACHAINER_CERTIFICATE_END "$LEAN_LOG")"

if [[ -z "$producer_dag" ]] || [[ "$producer_dag" != "$cetta_dag" ]] ||
   [[ "$producer_dag" != "$lean_dag" ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (producer, CeTTa, and Lean DAG bytes differ)"
  exit 1
fi
if [[ "$(grep -o 'PeTTaProofNodeV1' <<<"$producer_dag" | wc -l)" -ne 4 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (producer did not emit the expected four-node DAG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimePeTTaChainerDAGMetricsV1 4 4 1 5 "5/4")' "$CETTA_LOG")" -ne 1 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (sharing metrics changed)"
  exit 1
fi

producer_digest="$(printf '%s' "$producer_dag" | sha256sum | awk '{print $1}')"
if [[ -z "$cetta_digest" ]] || [[ "$producer_digest" != "$cetta_digest" ]] ||
   [[ "$producer_digest" != "$lean_digest" ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (cross-runtime artifact digest mismatch)"
  exit 1
fi
if [[ -z "$certificate_bytes" ]] ||
   [[ "$certificate_bytes" != *PrimePeTTaDAGCertificateV1* ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (canonical certificate serialization absent)"
  exit 1
fi
if [[ "$certificate_bytes" != "$lean_certificate_bytes" ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (CeTTa and Lean certificate bytes differ)"
  exit 1
fi
certificate_size="$(printf '%s' "$certificate_bytes" | wc -c)"
if [[ "$certificate_size" -le 256 ]]; then
  echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: FAIL (certificate metric captured an unevaluated placeholder)"
  exit 1
fi

echo "PRIME PETTACHAINER DAG REPLAY V1 GATE: PASS (real PeTTaChainer proof store exported 4 shared nodes for 5 tree occurrences; sharing ratio 5/4; certificate $certificate_size bytes; CeTTa replay gate ${replay_milliseconds}ms; producer/CeTTa/Lean bytes and digests agreed; 27 MeTTa and 24 Lean graph, serialization, authority, coverage, evidence, and support checks passed)"
