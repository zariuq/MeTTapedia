#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: test_gslt_collections.sh OUTPUT_DIRECTORY" >&2
  exit 2
fi

script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lean_root=$(cd -- "$script_root/../../lean/mettapedia" && pwd)
mkdir -p -- "$1"
output_root=$(cd -- "$1" && pwd)
cetta_bin=${CETTA_BIN:-$script_root/../../../hyperon/cetta-prime-2.0-draft-20260910/cetta}
petta_runner=${PETTA_RUNNER:-$script_root/../../../hyperon/PeTTa/run.sh}

cd "$lean_root"
lake --wfail build Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachineControls \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec \
  Mettapedia.GSLT.LanguageDef.CettaWireEquality \
  Mettapedia.GSLT.LanguageDef.CollectionConsumers \
  Mettapedia.GSLT.LanguageDef.CollectionConsumerControls \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution \
  > "$output_root/proof-build.log" 2>&1
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_collection_controls.lean" \
  "$output_root/collection-controls.metta" > "$output_root/generation.log" 2>&1
cat "$script_root/lib/gslt_scoped_execution.metta" \
  "$script_root/lib/gslt_typed_sites.metta" \
  "$script_root/lib/gslt_descent_execution.metta" \
  "$script_root/lib/gslt_complete.metta" \
  "$script_root/lib/gslt_collection_selection.metta" \
  "$script_root/lib/gslt_collection_machine.metta" \
  "$script_root/lib/gslt_collection_backend.metta" \
  "$output_root/collection-controls.metta" > "$output_root/collections.metta"

CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet "$output_root/collections.metta" \
  > "$output_root/cetta.first.out" 2> "$output_root/cetta.first.err"
bash "$petta_runner" --silent "$output_root/collections.metta" \
  > "$output_root/petta.first.out" 2> "$output_root/petta.first.err"

for engine in cetta petta; do
  lake env lean -DwarningAsError=true --run "$script_root/tools/generate_collection_controls.lean" resume \
    "$output_root/$engine.first.out" "$output_root/$engine.resume-controls.metta" \
    > "$output_root/$engine.resume-generation.log" 2>&1
  cat "$script_root/lib/gslt_scoped_execution.metta" \
    "$script_root/lib/gslt_typed_sites.metta" \
    "$script_root/lib/gslt_descent_execution.metta" \
    "$script_root/lib/gslt_complete.metta" \
    "$script_root/lib/gslt_collection_selection.metta" \
    "$script_root/lib/gslt_collection_machine.metta" \
    "$script_root/lib/gslt_collection_backend.metta" \
    "$output_root/$engine.resume-controls.metta" > "$output_root/$engine.resume.metta"
  if [[ "$engine" == cetta ]]; then
    CETTA_PETTA_SEARCH_MACHINE=1 "$cetta_bin" --lang petta --quiet "$output_root/$engine.resume.metta" \
      > "$output_root/$engine.resume.out" 2> "$output_root/$engine.resume.err"
  else
    bash "$petta_runner" --silent "$output_root/$engine.resume.metta" \
      > "$output_root/$engine.resume.out" 2> "$output_root/$engine.resume.err"
  fi
  cat "$output_root/$engine.first.out" "$output_root/$engine.resume.out" > "$output_root/$engine.out"
  lake env lean -DwarningAsError=true --run "$script_root/tools/generate_collection_controls.lean" check \
    "$output_root/$engine.out" > "$output_root/$engine.check.log" 2>&1
done

python3 - "$output_root" "$cetta_bin" "$petta_runner" "$script_root" <<'PY'
from pathlib import Path
import hashlib
import json
import re
import sys

root = Path(sys.argv[1])
source_root = Path(sys.argv[4])
source = (root / "collection-controls.metta").read_text() + (root / "cetta.resume-controls.metta").read_text()
labels = re.findall(r'\(CollectionControl "([^"]+)"', source)
if not labels or len(labels) != len(set(labels)):
    raise SystemExit("Missing or repeated generated control labels")
outputs = {}
for engine in ("cetta", "petta"):
    text = (root / f"{engine}.out").read_text()
    rows = re.findall(r'\(CollectionControl "([^"]+)" (True|False|true|false)\)', text)
    if [name for name, _ in rows] != labels:
        raise SystemExit(f"{engine}: missing, reordered or additional controls")
    failed = [name for name, answer in rows if answer.lower() != "true"]
    if failed:
        raise SystemExit(f"{engine}: failed controls: {failed}")
    remaining = re.sub(r'\(CollectionControl "[^"]+" (?:True|False|true|false)\)', "", text)
    remaining = "\n".join(line for line in remaining.splitlines()
                          if not line.startswith(("(CollectionSnapshot ", "(CollectionPacket ",
                                                  "(CollectionFiringPacket ",
                                                  "(CollectionPlanSnapshot ",
                                                  "(CollectionPlanPacket ")))
    if any(line.strip().lower() != "true" for line in remaining.splitlines() if line.strip()):
        raise SystemExit(f"{engine}: unexpected output")
    outputs[engine] = text
if outputs["cetta"] != outputs["petta"]:
    raise SystemExit("Engine outputs differ")
record = {
    "controls": len(labels),
    "all_passed": True,
    "byte_identical": True,
    "workload_sha256": hashlib.sha256((root / "collections.metta").read_bytes()).hexdigest(),
    "output_sha256": hashlib.sha256(outputs["cetta"].encode()).hexdigest(),
    "cetta_binary_sha256": hashlib.sha256(Path(sys.argv[2]).read_bytes()).hexdigest(),
    "petta_runner_sha256": hashlib.sha256(Path(sys.argv[3]).read_bytes()).hexdigest(),
    "source_sha256": {
        str(path.relative_to(source_root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [
            source_root / "lib/gslt_scoped_execution.metta",
            source_root / "lib/gslt_typed_sites.metta",
            source_root / "lib/gslt_descent_execution.metta",
            source_root / "lib/gslt_complete.metta",
            source_root / "lib/gslt_collection_selection.metta",
            source_root / "lib/gslt_collection_machine.metta",
            source_root / "lib/gslt_collection_backend.metta",
            source_root / "module/CollectionPetri.module",
            source_root / "module/CollectionReachability.module",
            source_root / "tools/generate_collection_controls.lean",
            source_root / "tools/test_gslt_collections.sh",
        ]
    },
    "independent_receipt_checks": {engine: (root / f"{engine}.check.log").read_text().strip()
                                   for engine in ("cetta", "petta")},
    "scope": "finite plan-ordered root-collection batches plus the ordinary complete scoped matcher on arranged carriers; Petri and graph-closure frontiers run through the shared generic scheduled continuation, while collection allocation remains a separate scheduler",
}
(root / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"Collection controls: {len(labels)}/{len(labels)} on both engines; byte-identical output")
PY
