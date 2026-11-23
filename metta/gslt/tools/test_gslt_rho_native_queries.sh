#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: test_gslt_rho_native_queries.sh OUTPUT_DIRECTORY" >&2
  exit 2
fi

script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lean_root=$(cd -- "$script_root/../../lean/mettapedia" && pwd)
mkdir -p -- "$1"
output_root=$(cd -- "$1" && pwd)
cetta_bin=${CETTA_BIN:-$script_root/../../../hyperon/cetta-mm0-metta-20261004/cetta}
petta_runner=${PETTA_RUNNER:-}
lean_runner=${LEAN_RUNNER:-}

run_lean() {
  if [[ -n "$lean_runner" ]]; then
    "$lean_runner" --run "$@"
  else
    lake env lean --run "$@"
  fi
}

cd "$lean_root"
run_lean "$script_root/tools/generate_rho_native_queries.lean" \
  "$output_root/rho-native-module.metta" "$output_root/rho-native-first.metta"

cd "$script_root"
runtime_sources=(
  lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta
  lib/gslt_descent_execution.metta lib/gslt_complete.metta
  lib/gslt_collection_laws.metta lib/gslt_canonical.metta lib/gslt_runner.metta
)
sha256sum "${runtime_sources[@]}" > "$output_root/runtime-source-sha256.txt"

run_metta() {
  if [[ -n "$petta_runner" ]]; then
    cat "${runtime_sources[@]}" "$output_root/rho-native-module.metta" "$1" \
      | bash "$petta_runner" --silent /dev/stdin > "$2" 2> "$3"
  else
    cat "${runtime_sources[@]}" "$output_root/rho-native-module.metta" "$1" \
      | CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet /dev/stdin > "$2" 2> "$3"
  fi
}

run_metta "$output_root/rho-native-first.metta" "$output_root/rho-native-first.out" "$output_root/rho-native-first.err"
cd "$lean_root"
run_lean "$script_root/tools/generate_rho_native_queries.lean" resume \
  "$output_root/rho-native-first.out" "$output_root/rho-native-resume.metta"
cd "$script_root"
run_metta "$output_root/rho-native-resume.metta" "$output_root/rho-native-resume.out" "$output_root/rho-native-resume.err"
cat "$output_root/rho-native-first.out" "$output_root/rho-native-resume.out" > "$output_root/rho-native.out"
cd "$lean_root"
run_lean "$script_root/tools/check_rho_native_query_output.lean" "$output_root/rho-native.out" \
  | tee "$output_root/rho-native.check"
cd "$script_root"
sha256sum -c "$output_root/runtime-source-sha256.txt" > "$output_root/runtime-source-unchanged.txt"
sha256sum "$output_root/rho-native.out"
