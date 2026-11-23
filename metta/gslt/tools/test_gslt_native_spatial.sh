#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo 'usage: test_gslt_native_spatial.sh OUTPUT_DIRECTORY' >&2
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
  if [[ -n "$lean_runner" ]]; then "$lean_runner" --run "$@"; else lake env lean --run "$@"; fi
}
run_metta() {
  if [[ -n "$petta_runner" ]]; then
    cat "$script_root/lib/gslt_native_spatial.metta" "$1" | bash "$petta_runner" --silent /dev/stdin > "$2" 2> "$3"
  else
    cat "$script_root/lib/gslt_native_spatial.metta" "$1" | CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet /dev/stdin > "$2" 2> "$3"
  fi
}
cd "$script_root"
sha256sum lib/gslt_native_spatial.metta > "$output_root/runtime-source-sha256.txt"
cd "$lean_root"
run_lean "$script_root/tools/generate_native_spatial_queries.lean" "$output_root/first.metta"
run_metta "$output_root/first.metta" "$output_root/first.out" "$output_root/first.err"
run_lean "$script_root/tools/generate_native_spatial_queries.lean" resume "$output_root/first.out" "$output_root/resume.metta"
run_metta "$output_root/resume.metta" "$output_root/resume.out" "$output_root/resume.err"
cat "$output_root/first.out" "$output_root/resume.out" > "$output_root/native-spatial.out"
python3 - "$output_root/native-spatial.out" <<'PY'
import pathlib, re, sys
lines=pathlib.Path(sys.argv[1]).read_text().splitlines()
controls=[]
for line in lines:
    if line.startswith('(NativeSpatialCursor '): continue
    match=re.fullmatch(r'\(NativeSpatialControl "([^"]+)" (NativePass|NativeFail)\)', line)
    if not match: raise SystemExit('unexpected output: '+line)
    controls.append(match.groups())
if len(controls)!=24: raise SystemExit(f'expected 24 controls, got {len(controls)}')
if len({name for name,_ in controls})!=24: raise SystemExit('duplicate control names')
failed=[name for name,value in controls if value!='NativePass']
if failed: raise SystemExit('failed: '+', '.join(failed))
print('Native spatial checker: 24 controls passed')
PY
cd "$script_root"
sha256sum -c "$output_root/runtime-source-sha256.txt" > "$output_root/runtime-source-unchanged.txt"
sha256sum "$output_root/native-spatial.out"
