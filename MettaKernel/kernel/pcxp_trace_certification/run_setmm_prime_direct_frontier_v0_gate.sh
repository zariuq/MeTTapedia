#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
SETMM="${SETMM:?set SETMM to the pinned set.mm source file}"
SETMM_REVISION="${SETMM_REVISION:-47e6e06b87581cd630d210dc41cf83b02eea78ea}"
SETMM_SHA256="${SETMM_SHA256:-3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a}"
OUT="${OUT:-$ROOT/parity_logs/direct_frontier_v0}"

actual_setmm_sha256="$(sha256sum "$SETMM" | awk '{print $1}')"
if [[ "$actual_setmm_sha256" != "$SETMM_SHA256" ]]; then
  echo "SET.MM PRIME DIRECT FRONTIER V0 GATE: FAIL (set.mm SHA-256 mismatch)" >&2
  exit 1
fi

run_case() {
  local label="$1"
  local fuel="$2"
  local expected="$3"
  local case_dir="$OUT/$label"
  local fixture="$case_dir/setmm_prime_atp_guided_181_183_v0.metta"

  mkdir -p "$case_dir"
  python3 "$ROOT/setmm_prime_atp_tools.py" \
    --setmm "$SETMM" \
    --source-revision "$SETMM_REVISION" \
    --output-dir "$case_dir" \
    --targets "$label" \
    --depth 12 \
    --fuel "$fuel"

  local output
  output="$($CETTA --lang prime "$fixture" 2>&1)"
  printf '%s\n' "$output"

  if printf '%s\n' "$output" | grep -Fq '(Error '; then
    echo "SET.MM PRIME DIRECT FRONTIER V0 GATE: FAIL ($label assertion error)" >&2
    exit 1
  fi

  case "$expected" in
    checked)
      if ! printf '%s\n' "$output" | grep -Fq 'typing-search more-possible'; then
        echo "SET.MM PRIME DIRECT FRONTIER V0 GATE: FAIL ($label did not produce a checked answer)" >&2
        exit 1
      fi
      ;;
    incomplete)
      if ! printf '%s\n' "$output" | grep -Fq 'typing-search resource-incomplete'; then
        echo "SET.MM PRIME DIRECT FRONTIER V0 GATE: FAIL ($label did not preserve bounded incompleteness)" >&2
        exit 1
      fi
      ;;
    *)
      echo "SET.MM PRIME DIRECT FRONTIER V0 GATE: FAIL (bad expected outcome $expected)" >&2
      exit 1
      ;;
  esac
}

run_case pm2.61nii 250000 checked
run_case pm2.61iii 250000 incomplete
run_case ja 10000000 checked

echo 'SET.MM PRIME DIRECT FRONTIER V0 GATE: PASS (full-prior 181 checked, 182 bounded-incomplete, 183 checked)'
