#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo 'usage: test_gslt_native_fixed_points.sh OUTPUT_DIRECTORY' >&2
  exit 2
fi
script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lean_root=$(cd -- "$script_root/../../lean/mettapedia" && pwd)
mkdir -p -- "$1"
output_root=$(cd -- "$1" && pwd)
cetta_bin=${CETTA_BIN:-$script_root/../../../hyperon/cetta-mm0-metta-20261004/cetta}
cetta_lang=${CETTA_LANG:-petta}
petta_runner=${PETTA_RUNNER:-}
lean_runner=${LEAN_RUNNER:-}
run_lean() {
  if [[ -n "$lean_runner" ]]; then "$lean_runner" --run "$@"; else lake env lean --run "$@"; fi
}
cd "$script_root"
sha256sum lib/gslt_native_fixed_points.metta tools/generate_native_fixed_points.lean \
  "$lean_root/Mettapedia/Languages/MeTTa/PeTTa/Bridges/NativeTypes/NaturalCounterExecution.lean" \
  > "$output_root/source-sha256.txt"
cd "$lean_root"
run_lean "$script_root/tools/generate_native_fixed_points.lean" "$output_root/controls.metta"
cat "$script_root/lib/gslt_native_fixed_points.metta" "$output_root/controls.metta" > "$output_root/workload.metta"
if [[ -n "$petta_runner" ]]; then
  runtime_mode=petta
  bash "$petta_runner" --silent "$output_root/workload.metta" > "$output_root/native-fixed-points.out" 2> "$output_root/native-fixed-points.err"
else
  runtime_mode=$cetta_lang
  CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang "$cetta_lang" --quiet "$output_root/workload.metta" > "$output_root/native-fixed-points.out" 2> "$output_root/native-fixed-points.err"
fi
python3 - "$output_root/controls.metta" "$output_root/native-fixed-points.out" "$runtime_mode" <<'PY'
import pathlib, re, sys
source=pathlib.Path(sys.argv[1]).read_text()
expected=re.findall(r'NativeFixedPointControl "([^"]+)"',source)
if len(expected)!=112 or len(set(expected))!=112:
    raise SystemExit(f'expected 112 unique generated controls, found {len(expected)}')
controls=[]
pattern=r'\(NativeFixedPointControl "([^"]+)" (NativePass|NativeFail)\)'
if sys.argv[3]=='prime': pattern=r'\['+pattern+r'\]'
for line in pathlib.Path(sys.argv[2]).read_text().splitlines():
    match=re.fullmatch(pattern,line)
    if not match: raise SystemExit('unexpected output: '+line)
    controls.append(match.groups())
if [name for name,_ in controls]!=expected:
    raise SystemExit('missing, additional, duplicate or reordered control output')
failed=[name for name,result in controls if result!='NativePass']
if failed: raise SystemExit('failed: '+', '.join(failed))
pathlib.Path(sys.argv[2]).with_suffix('.packets').write_text(''.join(
    f'(NativeFixedPointControl "{name}" {verdict})\n' for name,verdict in controls))
print('Native finite fixed points: 112 differential controls passed')
PY
cd "$script_root"
sha256sum -c "$output_root/source-sha256.txt" > "$output_root/source-unchanged.txt"
sha256sum "$output_root/native-fixed-points.out"
