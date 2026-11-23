#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: test_gslt_complete.sh OUTPUT_DIRECTORY" >&2
  exit 2
fi

script_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lean_root=$(cd -- "$script_root/../../lean/mettapedia" && pwd)
mkdir -p -- "$1"
output_root=$(cd -- "$1" && pwd)
cetta_bin=${CETTA_BIN:-$script_root/../../../hyperon/cetta-prime-2.0-draft-20260910/cetta}
petta_runner=${PETTA_RUNNER:-$script_root/../../../hyperon/PeTTa/run.sh}

cd "$lean_root"
python3 - "$script_root" > "$output_root/generator-targets.txt" <<'PYTARGETS'
from pathlib import Path
import re
import sys
root = Path(sys.argv[1])
modules = []
for name in ("generate_complete_controls.lean", "generate_collection_runner_controls.lean",
             "generate_complete_modules.lean", "generate_constructor_scan_controls.lean",
             "generate_retained_operation_controls.lean", "generate_retained_transition_controls.lean",
             "generate_allocation_advance_controls.lean", "generate_allocation_children_controls.lean",
             "generate_datalog_projection_controls.lean"):
    modules.extend(re.findall(r"^import (Mettapedia\.[A-Za-z0-9_.]+)$",
                              (root / "tools" / name).read_text(), re.M))
print("\n".join(dict.fromkeys(modules)))
PYTARGETS
mapfile -t generator_targets < "$output_root/generator-targets.txt"
lake --wfail build Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution \
  Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionControls \
  Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntimeExecution \
  "${generator_targets[@]}" > "$output_root/proof-build.log" 2>&1
python3 - "$lean_root" "$script_root" "$output_root" <<'PYPINS'
from pathlib import Path
import hashlib
import json
import re
import sys

lean, source, output = map(Path, sys.argv[1:])
repo = lean.parent.parent
modules = (output / "generator-targets.txt").read_text().splitlines()
files = {lean / name for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean")}
local_modules = set(modules)
for module in modules:
    relative = Path(*module.split("."))
    setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
    files.add(setup)
    for name, groups in json.loads(setup.read_text())["importArts"].items():
        if name.startswith("Mettapedia."):
            local_modules.add(name)
            files.update(Path(path) for group in groups for path in group)
for module in local_modules:
    relative = Path(*module.split("."))
    source_file = lean / relative.with_suffix(".lean")
    files.add(source_file)
    for authored in re.findall(r'^\s*#module_file "([^"]+)"', source_file.read_text(), re.M):
        files.add((source_file.parent / authored).resolve())
    files.add(lean / ".lake/build/lib/lean" / relative.with_suffix(".olean"))
    for suffix in (".olean.server", ".olean.private", ".ir", ".ir.sig"):
        path = lean / ".lake/build/lib/lean" / relative.with_suffix(suffix)
        if path.is_file():
            files.add(path)
for name in ("generate_complete_controls.lean", "generate_collection_runner_controls.lean",
             "generate_complete_modules.lean", "generate_constructor_scan_controls.lean",
             "generate_retained_operation_controls.lean", "generate_retained_transition_controls.lean",
             "generate_allocation_advance_controls.lean", "generate_allocation_children_controls.lean",
             "generate_datalog_projection_controls.lean", "test_gslt_complete.sh"):
    files.add(source / "tools" / name)

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

record = {"local_modules": sorted(local_modules),
          "source_and_artifact_sha256": {str(path.relative_to(repo)): digest(path)
                                        for path in sorted(files)}}
(output / "lean-inputs-before.json").write_text(json.dumps(record, indent=2) + "\n")
PYPINS
lake env lean "$script_root/tools/generate_complete_controls.lean" -DwarningAsError=true \
  > "$output_root/class-controls.metta" 2> "$output_root/class-generation.log"
lake env lean "$script_root/tools/generate_collection_runner_controls.lean" -DwarningAsError=true \
  > "$output_root/collection-controls.metta" 2> "$output_root/collection-generation.log"
lake env lean "$script_root/tools/generate_complete_modules.lean" -DwarningAsError=true \
  > "$output_root/emission-controls.metta" 2> "$output_root/emission-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_constructor_scan_controls.lean" \
  > "$output_root/constructor-scan-controls.metta" 2> "$output_root/constructor-scan-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_retained_operation_controls.lean" \
  > "$output_root/retained-operation-controls.metta" 2> "$output_root/retained-operation-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_retained_transition_controls.lean" \
  > "$output_root/retained-transition-controls.metta" 2> "$output_root/retained-transition-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_allocation_advance_controls.lean" \
  > "$output_root/allocation-advance-controls.metta" 2> "$output_root/allocation-advance-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_allocation_children_controls.lean" \
  > "$output_root/allocation-children-controls.metta" 2> "$output_root/allocation-children-generation.log"
lake env lean -DwarningAsError=true --run "$script_root/tools/generate_datalog_projection_controls.lean" \
  "$output_root/datalog-projection" > "$output_root/datalog-projection-generation.log" 2>&1

libraries=(
  gslt_scoped_execution gslt_schema_typing gslt_collection_constructor_typing gslt_collection_constructor_scan gslt_collection_retained_operations gslt_collection_allocation_advance gslt_collection_allocation_children
  gslt_typed_sites gslt_descent_execution gslt_complete
  gslt_collection_laws gslt_canonical gslt_collection_selection
  gslt_collection_machine gslt_collection_logged_search gslt_collection_backend gslt_collection_contexts gslt_recursive_collection gslt_collection_presentation gslt_collection_handoff gslt_collection_continuation gslt_collection_occurrences gslt_collection_install gslt_collection_match_lanes gslt_collection_collector gslt_collection_occurrence_machine gslt_collection_occurrence_discovery gslt_collection_occurrence_search gslt_runner
)
source_files=()
for library in "${libraries[@]}"; do
  source_files+=("$script_root/lib/$library.metta")
done
modules=(complete_produced complete_produced_empty complete_petri complete_graph complete_lambda complete_guarded complete_sealed complete_branching complete_unstratified complete_workflow complete_workflow_denied complete_workflow_ambient complete_set_context complete_collection_input complete_collection_input_duplicates complete_collection_input_missing complete_collection_query complete_collection_query_duplicates complete_collection_query_missing complete_collection_query_wrong complete_named_replacement complete_named_replacement_arrow complete_quantified_local complete_quantified_duplicate complete_quantified_missing complete_quantified_empty complete_quantified_nested)
module_files=()
for module in "${modules[@]}"; do
  module_files+=("$script_root/tests/petta/emitted/$module.metta")
done
authored_files=()
for module in CollectionPetri CollectionReachability CollectionNestedGuardedPetri CollectionNestedInputPetri CollectionNestedOutputPetri CollectionQuantifiedWorkflow CollectionNestedControl NamedReplacementControl BinaryCollectionJoin; do
  authored_files+=("$script_root/module/$module.module")
done
python3 - "$cetta_bin" "$output_root" "$script_root" "$petta_runner" \
  "${source_files[@]}" "${module_files[@]}" "${authored_files[@]}" \
  "$script_root/tools/generate_complete_controls.lean" \
  "$script_root/tools/generate_collection_runner_controls.lean" \
  "$script_root/tools/generate_complete_modules.lean" \
  "$script_root/tools/generate_constructor_scan_controls.lean" \
  "$script_root/tools/generate_retained_operation_controls.lean" \
  "$script_root/tools/generate_retained_transition_controls.lean" \
  "$script_root/tools/generate_allocation_advance_controls.lean" \
  "$script_root/tools/generate_allocation_children_controls.lean" \
  "$script_root/tools/generate_datalog_projection_controls.lean" "$script_root/tools/test_gslt_complete.sh" <<'PY'
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
digest = hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest()
expected = os.environ.get("CETTA_EXPECTED_SHA256")
if expected and digest != expected:
    raise SystemExit("CeTTa binary does not match CETTA_EXPECTED_SHA256")
output, source = map(Path, sys.argv[2:4])
(output / "cetta-before.sha256").write_text(digest + "\n")
inputs = {str(path.resolve().relative_to(source)):
          hashlib.sha256(path.read_bytes()).hexdigest()
          for path in map(Path, sys.argv[5:])}
(output / "inputs-before.json").write_text(json.dumps(inputs, indent=2) + "\n")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

runner = Path(sys.argv[4]).absolute()
petta_root = runner.parent.resolve()
runner = petta_root / runner.name
sources = [runner, *sorted((petta_root / "src").glob("*.pl")),
           petta_root / "mork_ffi/morkspaces.pl"]
if petta_root / "src/main.pl" not in sources:
    raise SystemExit("PeTTa entry-point sources were not found")
optional = [petta_root / "mork_ffi/target/release/libmork_ffi.so",
            petta_root / "mork_ffi/morklib.so"]
swi = Path(shutil.which("swipl")).resolve()
variables = subprocess.check_output([str(swi), "--dump-runtime-variables"], text=True)
library = re.search(r'^PLLIBSWIPL="([^"]+)";', variables, re.M)
runtime = {
    "source_sha256": {str(path.relative_to(petta_root)): sha(path) for path in sources},
    "optional_native_sha256": {str(path.relative_to(petta_root)): sha(path) if path.is_file() else None
                               for path in optional},
    "swi_executable_sha256": sha(swi),
    "swi_runtime_library_sha256": sha(Path(library.group(1))) if library else None,
    "swi_version": subprocess.check_output([str(swi), "--version"], text=True).strip(),
}
(output / "petta-before.json").write_text(json.dumps(runtime, indent=2) + "\n")
PY

cat "${source_files[@]}" "${module_files[@]}" "$output_root/class-controls.metta" \
  "$output_root/collection-controls.metta" "$output_root/emission-controls.metta" \
  "$output_root/constructor-scan-controls.metta" \
  "$output_root/retained-operation-controls.metta" "$output_root/retained-transition-controls.metta" \
  "$output_root/allocation-advance-controls.metta" \
  "$output_root/allocation-children-controls.metta" \
  "$output_root/datalog-projection/projector.metta" "$output_root/datalog-projection/controls.metta" \
  > "$output_root/complete.metta"

python3 - "$output_root" "$cetta_bin" "$petta_runner" <<'PY'
from pathlib import Path
import json
import os
import subprocess
import sys
import time

root, cetta, petta = map(Path, sys.argv[1:])
measurements = []
for engine, command in (
    ("cetta", [str(cetta), "--lang", "petta", "--quiet", str(root / "complete.metta")]),
    ("petta", ["bash", str(petta), "--silent", str(root / "complete.metta")]),
):
    started = time.monotonic()
    with (root / f"{engine}.out").open("w") as out, (root / f"{engine}.err").open("w") as err:
        result = subprocess.run(command, stdout=out, stderr=err,
                                env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
    measurements.append({"engine": engine, "exit_code": result.returncode,
                         "seconds": time.monotonic() - started})
    (root / "runtime-measurements.json").write_text(json.dumps(measurements, indent=2) + "\n")
    if result.returncode:
        raise SystemExit(f"{engine}: execution failed with {result.returncode}")
PY

python3 - "$output_root" "$script_root" "$cetta_bin" "$petta_runner" <<'PY'
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

root, source_root, cetta, petta = map(Path, sys.argv[1:])
source = "".join((root / name).read_text() for name in
                 ("class-controls.metta", "collection-controls.metta", "emission-controls.metta", "constructor-scan-controls.metta",
                  "retained-operation-controls.metta", "retained-transition-controls.metta", "allocation-advance-controls.metta",
                  "allocation-children-controls.metta", "datalog-projection/controls.metta"))
labels = re.findall(r'\(([A-Za-z]+(?:Control|Negative)) "([^"]+)"', source)
if not labels or not any(kind == "CollectionRunnerControl" for kind, _ in labels):
    raise SystemExit("Missing class or collection controls")
row_pattern = r'\(([A-Za-z]+(?:Control|Negative)) "([^"]+)" ((?:(?:true|false) ?)+)\)'
outputs = {}
checks = 0
for engine in ("cetta", "petta"):
    text = (root / f"{engine}.out").read_text()
    rows = re.findall(row_pattern, text)
    if [(kind, name) for kind, name, _ in rows] != labels:
        raise SystemExit(f"{engine}: missing, reordered or additional controls")
    for kind, name, answers in rows:
        expected = {"CollectionRunnerControl": 8, "CollectionStatusControl": 4, "CollectionHandoffControl": 6,
                    "CollectionRawHandoffControl": 9, "CollectionContinuationControl": 9,
                    "CollectionContextControl": 2, "RecursiveMatcherControl": 4, "CollectionPresentationControl": 1,
                    "RecursiveHandoffControl": 3, "CollectionRepresentationControl": 2, "NestedContinuationControl": 9,
                    "CollectionBatchControl": 8, "OccurrenceMachineFullControl": 7, "OccurrenceDiscoveryControl": 3,
                    "OccurrenceSearchControl": 7, "OccurrenceSearchStatusControl": 2,
                    "LocalQuantifierControl": 8, "CanonicalMatcherControl": 6,
                    "CanonicalPostmatchControl": 6, "CanonicalReadoutControl": 6,
                    "PublicOccurrenceControl": 7, "InterpretedNativeControl": 5,
                    "KnowledgeGraphProducerControl": 21, "KGProducerInvarianceControl": 15,
                    "KGDeclaredKeyControl": 9, "FiniteExplorerControl": 9, "ConstructorScanControl": 3,
                    "RetainedResumeControl": 6, "AllocationAdvanceControl": 7,
                    "DatalogProjectionControl": 4}.get(kind, 1)
        if answers.split() != ["true"] * expected:
            raise SystemExit(f"{engine}: failed or incomplete control {kind}/{name}")
    if re.sub(row_pattern, "", text).split() != ["true"] * len(labels):
        raise SystemExit(f"{engine}: unexpected output")
    if (root / f"{engine}.err").read_text():
        raise SystemExit(f"{engine}: runtime stderr is nonempty")
    outputs[engine] = text
    checks = sum(len(answers.split()) for _, _, answers in rows)
if outputs["cetta"] != outputs["petta"]:
    raise SystemExit("Engine outputs differ")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

if digest(cetta) != (root / "cetta-before.sha256").read_text().strip():
    raise SystemExit("CeTTa binary changed during the gate")
inputs_before = json.loads((root / "inputs-before.json").read_text())
if any(digest(source_root / path) != pin for path, pin in inputs_before.items()):
    raise SystemExit("Compiler or runtime source changed during the gate")

runtime = json.loads((root / "petta-before.json").read_text())
petta_root = petta.absolute().parent.resolve()
if any(digest(petta_root / path) != pin for path, pin in runtime["source_sha256"].items()):
    raise SystemExit("PeTTa interpreter sources changed during the gate")
for path, pin in runtime["optional_native_sha256"].items():
    artifact = petta_root / path
    if (digest(artifact) if artifact.is_file() else None) != pin:
        raise SystemExit("PeTTa native inputs changed during the gate")
swi = Path(shutil.which("swipl")).resolve()
variables = subprocess.check_output([str(swi), "--dump-runtime-variables"], text=True)
library = re.search(r'^PLLIBSWIPL="([^"]+)";', variables, re.M)
if digest(swi) != runtime["swi_executable_sha256"] or \
        (digest(Path(library.group(1))) if library else None) != runtime["swi_runtime_library_sha256"]:
    raise SystemExit("SWI runtime changed during the gate")

lean_inputs = json.loads((root / "lean-inputs-before.json").read_text())
repo = source_root.parent.parent
if any(digest(repo / path) != pin
       for path, pin in lean_inputs["source_and_artifact_sha256"].items()):
    raise SystemExit("Lean source or execution artifacts changed during generation or execution")

measurements = [json.loads(line.removeprefix("; GSLT-MEASUREMENT "))
                for line in source.splitlines() if line.startswith("; GSLT-MEASUREMENT ")]
if not measurements:
    raise SystemExit("Missing collection allocation/resumption measurements")
(root / "collection-measurements.json").write_text(json.dumps(measurements, indent=2) + "\n")

projection_measurements_path = root / "datalog-projection/projection-measurements.json"
projection_measurements = json.loads(projection_measurements_path.read_text())
projection_labels = [label for kind, label in labels if kind == "DatalogProjectionControl"]
if [row["label"] for row in projection_measurements] != projection_labels:
    raise SystemExit("Missing, reordered or additional projector measurements")

record = {
    "controls": len(labels), "checks": checks, "all_passed": True, "byte_identical": True,
    "constructor_readiness_controls": sum(kind == "ConstructorTypingControl" for kind, _ in labels),
    "constructor_scan_controls": sum(kind == "ConstructorScanControl" for kind, _ in labels),
    "retained_operation_controls": sum(kind == "RetainedOperationControl" for kind, _ in labels),
    "retained_transition_controls": sum(kind == "RetainedTransitionControl" for kind, _ in labels),
    "retained_resume_controls": sum(kind == "RetainedResumeControl" for kind, _ in labels),
    "datalog_projection_controls": sum(kind == "DatalogProjectionControl" for kind, _ in labels),
    "datalog_program_projection_controls": sum(kind == "DatalogProjectionControl" and label.startswith("program/") for kind, label in labels),
    "datalog_projection_measurement_count": len(projection_measurements),
    "datalog_projection_measurements_sha256": digest(projection_measurements_path),
    "datalog_projection_scope": "all 46 authored structural compiler rows have independent two-way reference agreement; whole programs and recursive constant tuples use the unchanged shared class emitter, runner, explorer, receipt-bearing edges and complete resumed machine; an ordinary source/certificate reading, grouped declarations, duplicate statements and clause/comparison syntax are exercised; raw reference finite-prefix selection agreement is proved for the program region; universal target typing, native forest coverage/selection, literal interpretation, full class-receipt translation and Datalog inference remain separate",
    "allocation_advance_controls": sum(kind == "AllocationAdvanceControl" for kind, _ in labels),
    "allocation_advance_scope": "one actual grouped-cursor tick, complete unpublished suffix, publication index and full retained continuation; residual sorting, child construction and full allocation expansion remain separate",
    "allocation_children_controls": sum(kind == "AllocationChildrenControl" for kind, _ in labels),
    "allocation_children_scope": "exact single and ordered-batch child construction from caller-ordered residual records; full typed scopes and continuations retained, missing-rest rejection and duplicate occurrences preserved; native residual normalization and whole allocation expansion remain separate",
    "retained_transition_scope": "exact returned/child/constructor state-step composition; complete outer zippers, typed contexts and continuations; ordered candidate prefix and prior pending work retained; resumed publication of a completed-candidate queue; no full producer or source firing admission",
    "constructor_scan_scope": "one actual retained constructor transition with complete child requests, original declaration ordinals, pending full rows, typed focuses and dependent continuations; full producer and source firing coverage remain separate",
    "constructor_readiness_scope": "actual retained row predicate with distinct target/schema contexts and bare/wrapped representations; declaration membership, formation and full recursive producer qualification remain separate",
    "inputs_current": True,
    "scope": "one native runner, explorer and emitter over class, certified root and certified occurrence searches; emitted Petri and graph modules retain their canonical root profiles; authored nested workflows and set contexts use the recognized nullary or mixed provider-query profile with checked object input templates and canonical provider values, with source-to-emitted graph correspondence and settled outgoing successor-class coverage; the default class admission set guard remains unchanged",
    "additional_scope": "recursive typed contexts and retained recursive matching components, including full allocation histories, interrupted states, resumption, exact binder contexts and source receipt coverage, ordinary presentation reconstruction, and prepared ordinary matching handoff; prepared conditional continuation states and outer-context receipts; chronological batches with per-allocation suffix drains, including a delayed earlier allocation; retained recursive matching plus conditional execution from encoded source-derived lanes, with complete joint states and receipt accounts, guards, set retention/collapse, binder contexts, missing redexes and interruption; native current-source typed job discovery, binding elaboration, residual context variants and exact initialization; native retained Search run/resume, canonical target selection, pending/blocked/completed status and cached finished receipts from the complete raw machine; admission-selected emitted begin/run/explore/edges for nested workflows with positive/negative guards, ambient binder context, missing redex, set consumption/retention/collapse, nested retained copies and distinct bag occurrences; named heterogeneous replacement consumers retain reordered arguments through nested terms and binder contexts, with a wrong-order control; whole-capture collection input guards retain provider-row indices, including duplicate rows, with negative missing-input and noncanonical-row controls; mixed input/output queries retain structured input reads, nested ordinary output allocation traces and original provider-row occurrences; binary replacement typing follows bare/wrapped declaration representations through the existing native checker; single and nested lexical finite-vector quantifiers run through the existing class profile, retaining complete body events, independent local outputs, empty-range behavior and missing-row negatives; the shared interpreted native premise machine additionally realizes finite-provider queries, directed child steps and recursive finite quantifiers with exact retained states and histories under its selected matching interpretation; actual RSum step-premise and native graph-producer key observations are exercised separately from admission; quotient-aware source transport, child-step collection admission, additional authored equations and complete logical derivation enumeration remain separate",
    "quantifier_scope": {"carrier": "finite vectors", "profile": "existing class search",
        "body_outputs": "local to each body", "history": "complete raw validation events",
        "text_module_quantifier_lowering_qualified": True,
        "quotient_collection_quantifier_admission_qualified": False},
    "source_algebra_scope": {
        "defined_first_order_fold_interpretations": True,
        "canonical_lowering_interpretation_qualified": True,
        "native_declared_law_normalization_correspondence": True,
        "arbitrary_source_theory_reflection_qualified": False,
        "independent_collection_data_identification_licensed": False,
    },
    "canonical_matching_scope": {
        "cached_request_start_tick_status_readout_and_input": True,
        "exact_partial_states_and_allocation_histories": True,
        "native_full_interpreted_premises_qualified": True,
        "native_full_interpreted_premises_scope": "finite providers, represented name footprints, selected ordinary or intrinsic canonical matching, exact retained states and ordered histories at the supplied child depth; no admission or equational-source-policy change",
        "presented_source_gslt_agreement_qualified": False,
    },
    "workload_sha256": digest(root / "complete.metta"),
    "output_sha256": hashlib.sha256(outputs["cetta"].encode()).hexdigest(),
    "cetta_binary_sha256": digest(cetta), "petta_runner_sha256": digest(petta),
    "petta_runtime_cohort": runtime,
    "runtime_measurements": json.loads((root / "runtime-measurements.json").read_text()),
    "collection_measurement_count": len(measurements),
    "collection_measurements_sha256": digest(root / "collection-measurements.json"),
    "measurement_scope": "Source-model allocation, publication and budget accounts checked by exact native-state comparisons; timings are whole-workload measurements and supply no asymptotic bounds",
    "source_sha256": inputs_before,
    "lean_local_module_count": len(lean_inputs["local_modules"]),
    "lean_source_and_artifact_count": len(lean_inputs["source_and_artifact_sha256"]),
    "lean_input_manifest_sha256": digest(root / "lean-inputs-before.json"),
}
(root / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"Complete controls: {checks}/{checks} on both engines; byte-identical output")
PY
