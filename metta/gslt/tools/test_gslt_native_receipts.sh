#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: test_gslt_native_receipts.sh OUTPUT_DIRECTORY" >&2
  exit 2
fi

script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lean_root=$(cd -- "$script_root/../../lean/mettapedia" && pwd)
mkdir -p -- "$1"
output_root=$(cd -- "$1" && pwd)
cetta_bin=${CETTA_BIN:-$script_root/../../../hyperon/cetta-mm0-metta-20261004/cetta}
petta_runner=${PETTA_RUNNER:-}

cd "$lean_root"
lake env lean --run "$script_root/tools/generate_native_receipts.lean" "$output_root/native-receipts.metta"

cd "$script_root"
run_metta() {
  if [[ -n "$petta_runner" ]]; then
    cat lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta lib/gslt_descent_execution.metta "$1" \
      | bash "$petta_runner" --silent /dev/stdin > "$2" 2> "$3"
  else
    cat lib/gslt_scoped_execution.metta lib/gslt_typed_sites.metta lib/gslt_descent_execution.metta "$1" \
      | CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet /dev/stdin > "$2" 2> "$3"
  fi
}

run_metta "$output_root/native-receipts.metta" "$output_root/native-receipts.first.out" "$output_root/native-receipts.first.err"
cd "$lean_root"
lake env lean --run "$script_root/tools/generate_native_receipts.lean" \
  "$output_root/native-receipts.first.out" "$output_root/native-receipts.resume.metta"
cd "$script_root"
run_metta "$output_root/native-receipts.resume.metta" "$output_root/native-receipts.resume.out" "$output_root/native-receipts.resume.err"
cat "$output_root/native-receipts.first.out" "$output_root/native-receipts.resume.out" > "$output_root/native-receipts.out"

cd "$lean_root"
lake env lean --run "$script_root/tools/check_native_receipt_output.lean" "$output_root/native-receipts.out" \
  | tee "$output_root/native-receipts.check"
sha256sum "$output_root/native-receipts.out"
