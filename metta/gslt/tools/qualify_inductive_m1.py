#!/usr/bin/env python3
"""Run the available M1 links on one source and one selected CeTTa binary.

Run with the project's Lean environment after building GSLTInductiveM1Qualification.
The grammar reader uses HE/extended; program execution uses Prime and PeTTa modes.
These are different dialect stages, even when they share an executable.

Exit 0 means the complete milestone is qualified, 1 means a stage failed, and
2 means available stages passed but required milestone obligations remain open.
Missing native kernel and production-adapter evidence cannot yield a green M1.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from qualify_inductive_native_facts import project_source_pins


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_annotations(records):
    """Check exact intake of the proved emitter's subjects and permissions.

    This validates the qualification record; it is not a native proof checker.
    The Lean emitter's output_sound theorem supplies the typing derivation.
    """
    if (not isinstance(records, list) or any(not isinstance(r, dict) for r in records) or
            [r.get("case") for r in records] != ["valid", "alpha"]):
        raise RuntimeError("annotated source coverage differs")
    policies = [
        {"permissions": [0, 1], "nil_certificate_accepted": False, "cons_certificate_accepted": False},
        {"permissions": [0, 1, 2], "nil_certificate_accepted": True, "cons_certificate_accepted": False},
        {"permissions": [0, 1, 2, 3], "nil_certificate_accepted": True, "cons_certificate_accepted": True},
    ]
    subjects = ("source_function", "annotated_function", "expected_type")
    for row in records:
        if (row.get("judgment") != "CumulativePiSigmaId.CTyped" or
                json.dumps(row.get("typing_permissions")) != "[0, 1]"):
            raise RuntimeError("annotated typing judgment or permissions differ")
        if any(row.get(name) is not True for name in
               ("erasure_matches_source", "annotation_matches_independent", "type_matches_independent")):
            raise RuntimeError("annotated source correspondence failed")
        if json.dumps(row.get("computation_policies"), sort_keys=True) != json.dumps(policies, sort_keys=True):
            raise RuntimeError("annotated computation permissions differ")
        if any(not isinstance(row.get(name), str) or not row[name] for name in subjects):
            raise RuntimeError("missing annotated checking subject")
    if any(records[0][name] != records[1][name] for name in subjects):
        raise RuntimeError("alpha-renamed source changed the annotated checking subject")
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--petta", required=True, type=Path)
    parser.add_argument("--cetta-tree", type=Path,
                        help="also qualify the production Atom/GMP source with sanitizers")
    parser.add_argument("--cetta-build-manifest", type=Path,
                        help="bind the chosen binary to its private native build and run array lifetime coverage")
    parser.add_argument("--cetta-sanitized-build-manifest", type=Path,
                        help="also qualify an ASan/UBSan artifact with the same sources and generated configuration")
    parser.add_argument("--native-facts-config", type=Path,
                        help="replay the available HOL Light, MM0 and Megalodon facts on this CeTTa binary")
    parser.add_argument("--native-cc", default=os.environ.get("CC", "clang"),
                        help="C compiler for the production probe; an absolute path avoids lake PATH changes")
    args = parser.parse_args()
    if args.cetta_sanitized_build_manifest and not (args.cetta_build_manifest and args.cetta_tree):
        parser.error("the sanitizer companion needs --cetta-build-manifest and --cetta-tree")
    root = Path(__file__).resolve().parents[1]
    lean = root.parents[1] / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cetta, petta = args.cetta.resolve(), args.petta.resolve()
    cetta_tree = args.cetta_tree.resolve() if args.cetta_tree else None
    adjacent_library_root = cetta.parent / "lib"
    source_library_root = cetta_tree / "lib" if cetta_tree else adjacent_library_root
    expected_library_names = ("lib_lbnf.metta", "langdef.metta", "holkernel.metta",
                              "mm0kernel.metta", "megalodon.metta")
    cetta_library_root = (adjacent_library_root
                          if all((adjacent_library_root / name).is_file()
                                 for name in expected_library_names)
                          else source_library_root)
    cetta_library_inputs = [cetta_library_root / "lib_lbnf.metta",
                            cetta_library_root / "langdef.metta"]
    if any(not path.is_file() for path in cetta_library_inputs):
        raise RuntimeError("CeTTa LBNF/langdef library root is incomplete")
    source = root / "module/IndexedNatVecAppend.module"
    emitter = root / "tools/emit_checked_append_source.lean"
    selected_inputs = root / "tools/check_inductive_selected_inputs.lean"
    reader_script = root / "tools/test_append_source_reader.py"
    runtime_script = root / "tools/test_inductive_append.py"
    fixed_gate = root / "tools/test_gslt_native_fixed_points.sh"
    counter = lean / "Mettapedia/OSLF/NativeTypes/Instances/Natural/RetainedCounterControls.lean"
    own_inputs = [Path(__file__).resolve(), root / "tools/qualify_inductive_native_facts.py",
                  cetta, petta, source, emitter, selected_inputs, reader_script,
                  runtime_script, fixed_gate, counter, root / "tools/test_inductive_annotations.py",
                  *cetta_library_inputs,
                  root / "module/module_v1.cf",
                  root / "tools/generate_native_fixed_points.lean",
                  root / "lib/gslt_native_fixed_points.metta",
                  root / "module/NativeNaturalCounter.module",
                  lean / "Mettapedia/Languages/MeTTa/PeTTa/Bridges/IndexedInductiveAppendPolicy.lean",
                  lean / "Mettapedia/Languages/MeTTa/PeTTa/Bridges/IndexedInductiveAppendAnnotated.lean",
                  lean / "Mettapedia/OSLF/NativeTypes/Instances/Natural/RetainedCounter.lean"]
    profile_contract = (lean /
        "Mettapedia/TypeTheory/Calculi/CumulativePiSigmaId/Declarations/NativeNaturalVectorCheckingProfiles.lean")
    own_inputs += [lean / "Mettapedia/TypeTheory/Calculi/CumulativePiSigmaId/Declarations" / name
                   for name in ("NativeNaturalVectorAnnotatedAppend.lean",
                                "NativeNaturalVectorAnnotatedPrograms.lean",
                                "NativeNaturalVectorAnnotatedChecking.lean",
                                "NativeNaturalVectorAnnotatedEvidence.lean",
                                "NativeNaturalVectorAnnotated.lean",
                                "NativeNaturalVectorComputationProfiles.lean",
                                "NativeNaturalVectorCheckingProfiles.lean")]
    own_inputs += [lean / "Mettapedia" / name for name in (
        "OSLF/NativeTypes/Instances/Natural/Counter.lean",
        "OSLF/NativeTypes/Instances/Natural/Authored.lean",
        "GSLT/LanguageDef/Examples/NativeNaturalCounter.lean",
        "GSLT/LanguageDef/IntegerRepresentationRetainedCall.lean",
        "GSLT/LanguageDef/IntegerRepresentationPublication.lean",
        "GSLT/LanguageDef/IntegerRepresentationPublicationControls.lean",
        "Languages/MeTTa/PeTTa/Bridges/NativeTypes/FiniteMuCalculusWire.lean",
        "Languages/MeTTa/PeTTa/Bridges/NativeTypes/FiniteMuCalculusSource.lean",
        "Languages/MeTTa/PeTTa/Bridges/NativeTypes/NaturalCounterExecution.lean")]
    native_obligation = "Three selected native natural-law routes and their authored meanings"
    production_obligation = "Paired retained GMP/array production, ownership and failure contracts"
    profile_obligation = "Exact natural checking, scoped logical and full raw operational profile fork"
    record = {"m1_qualified": False, "available_stages_qualified": False, "status": "running",
              "stages": [], "open_obligations": [
                  native_obligation, production_obligation, profile_obligation],
              "scope": "Selected textual Nat/Vec append with natural-integer payloads; certified counter-query execution, finite-model differential controls and conditional retained-provider path theorem",
              "non_claims": ["No proof of linked C/GMP or packed-parser completeness",
                             "No unrestricted raw-to-annotated typing reflection or full logical-profile identification",
                             "No general MeTTa fixed-point execution theorem",
                             "No native infinite-resource or scheduler-fairness certificate",
                             "Selected HOL law interpretation is not full source definition-history refinement"]}
    records_file = output / "qualification.json"

    def close_obligation(obligation):
        record["open_obligations"] = [item for item in record["open_obligations"]
                                      if item != obligation]

    def save():
        records_file.write_text(json.dumps(record, indent=2) + "\n")

    save()

    def run(label, command, *, environment=None, expected=0):
        started = time.monotonic()
        result = subprocess.run(command, cwd=lean, env=environment or os.environ.copy(),
                                text=True, capture_output=True, timeout=1200)
        (output / (label + ".stdout")).write_text(result.stdout)
        (output / (label + ".stderr")).write_text(result.stderr)
        passed = result.returncode == expected if expected is not None else result.returncode != 0
        record["stages"].append({"name": label, "passed": passed, "returncode": result.returncode,
                                 "seconds": round(time.monotonic() - started, 6)})
        save()
        if not passed:
            raise RuntimeError(f"{label} failed; see its captured output")
        print(f"{label}: passed", flush=True)
        return result.stdout

    try:
        pins = {str(path): digest(path) for path in own_inputs}
        record["input_pins"] = pins

        def merge_pins(new):
            for path, value in new.items():
                if path in pins and pins[path] != value:
                    raise RuntimeError(f"stages used different versions of {Path(path).name}")
            pins.update(new)

        merge_pins(project_source_pins((path for path in own_inputs if path.suffix == ".lean"), lean))

        if args.cetta_build_manifest:
            manifest = args.cetta_build_manifest.resolve()
            native_build = json.loads(manifest.read_text())
            if (native_build.get("qualified") is not True or native_build.get("status") != "passed" or
                    native_build.get("binary_sha256") != pins[str(cetta)]):
                raise RuntimeError("selected binary is not the qualified native build")
            expected_staged = {f"lib/{name}" for name in expected_library_names}
            staged = native_build.get("runtime_libraries")
            if not isinstance(staged, dict) or set(staged) != expected_staged:
                raise RuntimeError("qualified native build lacks the selected runtime libraries")
            for relative, evidence in staged.items():
                staged_path = cetta.parent / relative
                if (not staged_path.is_file() or digest(staged_path) != evidence.get("sha256") or
                        native_build["inputs"].get(evidence.get("source")) != evidence.get("sha256")):
                    raise RuntimeError("staged runtime library differs from its pinned source")
            merge_pins(native_build["inputs"])
            pins[str(manifest)] = digest(manifest)
            record["native_build"] = native_build
            if args.cetta_sanitized_build_manifest:
                companion_path = args.cetta_sanitized_build_manifest.resolve()
                companion = json.loads(companion_path.read_text())
                if (companion.get("qualified") is not True or companion.get("status") != "passed" or
                        "-fsanitize=address,undefined" not in companion["configuration"]["CFLAGS"] or
                        "-fsanitize=" in native_build["configuration"]["CFLAGS"] or
                        "-O3" not in native_build["configuration"]["CFLAGS"]):
                    raise RuntimeError("expected an optimized primary and ASan/UBSan companion")
                if native_build["configuration"]["SRC"] != companion["configuration"]["SRC"]:
                    raise RuntimeError("native build source inventories differ")
                companion_staged = companion.get("runtime_libraries")
                if not isinstance(companion_staged, dict) or set(companion_staged) != expected_staged:
                    raise RuntimeError("sanitized native build lacks the selected runtime libraries")
                if ({relative: evidence.get("sha256") for relative, evidence in staged.items()} !=
                    {relative: evidence.get("sha256") for relative, evidence in
                     companion_staged.items()}):
                    raise RuntimeError("native build runtime libraries differ")

                def generated_pin(build, key):
                    suffix = "/" + build["configuration"][key]
                    found = [value for path, value in build["inputs"].items() if path.endswith(suffix)]
                    if len(found) != 1:
                        raise RuntimeError("generated native input is not uniquely pinned")
                    return found[0]

                for key in ("BUILD_CONFIG_HEADER", "PARSER_BAKED_HEADER"):
                    if generated_pin(native_build, key) != generated_pin(companion, key):
                        raise RuntimeError("generated native configurations differ")
                # Shared source/header paths must have identical contents.
                merge_pins(companion["inputs"])
                pins[str(companion_path)] = digest(companion_path)
                record["sanitized_native_build"] = companion

        run("selected-input-policy", ["lean", "-DwarningAsError=true", "--run", str(selected_inputs)])
        record["selected_input_contract"] = {
            "checking_policy": "natural-only", "operational_policy": "original-four-iota",
            "typed_endpoints": True, "arbitrary_contextual_preservation": False}
        run("checking-profile-contract", ["lean", "-DwarningAsError=true", str(profile_contract)])
        record["checking_profile_contract"] = {
            "minimal": "retained receipts, no iota conversion",
            "checking": "natural-only annotated/raw conversion",
            "logical_child": "opaque proposition and function extensionality",
            "operational_child": "original four raw iota rows",
            "operational_preserves_checking": True,
            "unrestricted_full_annotation_lift": False}
        close_obligation(profile_obligation)
        run("source-checking", [sys.executable, str(reader_script), "--cetta", str(cetta),
                                "--cetta-library-root", str(cetta_library_root),
                                "--output", str(output / "reader")])
        reader = json.loads((output / "reader/qualification.json").read_text())
        if (reader["binary_sha256"] != pins[str(cetta)] or
                reader["source_sha256"] != pins[str(source)] or
                reader["permitted_rows"] != [0, 1] or not reader["raw_reader_agreement"]):
            raise RuntimeError("reader source, binary or selected checking policy differs")
        merge_pins(reader["receipt_sources"])
        packet = output / "reader/packet.metta"
        library = output / "checked-append.metta"
        annotation_file = output / "append-annotations.json"
        emitted = run("source-emission", ["lean", "--run", str(emitter), str(packet), str(library),
                                          str(annotation_file)])
        expected = [(label, "NativeEmitted" if label in ("valid", "alpha") else "NativeRefused")
                    for label in ("valid", "alpha", "wrong-child", "omitted-recursion", "wrong-index",
                                  "unbound", "missing-clause", "extra-block", "negative-field", "wrong-entry")]
        actual = []
        for line in emitted.splitlines():
            match = re.fullmatch(r'\(AppendSourceEmission "([^"]+)" (NativeEmitted|NativeRefused)\)', line)
            if not match:
                raise RuntimeError("unexpected source-emission output")
            actual.append(match.groups())
        if actual != expected:
            raise RuntimeError("source-emission coverage or verdict differs")
        annotations = validate_annotations(json.loads(annotation_file.read_text()))
        record["annotated_source"] = annotations
        run("annotation-intake-refusals", [sys.executable,
            str(root / "tools/test_inductive_annotations.py"), str(annotation_file)])
        pins[str(packet)] = digest(packet)
        pins[str(library)] = digest(library)
        pins[str(annotation_file)] = digest(annotation_file)
        run("append-and-observations", [sys.executable, str(runtime_script), str(output / "runtime"),
                                       "--cetta", str(cetta), "--petta", str(petta),
                                       "--library", str(library)])
        runtime = json.loads((output / "runtime/qualification.json").read_text())
        if (not runtime["qualified"] or runtime["source_pins"][str(cetta)] != pins[str(cetta)] or
                runtime["source_pins"][str(source)] != pins[str(source)] or
                runtime["source_pins"][str(library)] != pins[str(library)] or
                runtime["artifact_pins"]["append-library.metta"] != pins[str(library)]):
            raise RuntimeError("runtime did not qualify the same checked emission")
        merge_pins(runtime["source_pins"])

        # A changed emission must be refused before it can supply either workload.
        altered = output / "altered-emission.metta"
        altered.write_text(library.read_text() + "\n(= (unlicensed) 1)\n")
        for name in ("qualify_inductive_append.lean", "qualify_inductive_append_observations.lean"):
            log = run("refuse-" + name, ["lean", "--run", str(root / "tools" / name),
                      "emit-library", str(altered), str(output / "refused")], expected=None)
            error = (output / ("refuse-" + name + ".stderr")).read_text()
            if "submitted emission differs from the proved library" not in log + error:
                raise RuntimeError("changed emission failed for an unrelated reason")

        run("retained-counter-contract", ["lean", "-DwarningAsError=true", str(counter)])
        publication = lean / "Mettapedia/GSLT/LanguageDef/IntegerRepresentationPublicationControls.lean"
        run("integer-publication-contract", ["lean", "-DwarningAsError=true", str(publication)])
        if args.cetta_tree:
            atom_gate = lean / "scripts/conformance/check_exact_integer_atoms.py"
            run("retained-atom-production", [sys.executable, str(atom_gate),
                "--cetta-tree", str(args.cetta_tree.resolve()),
                "--output", str(output / "retained-atoms"), "--compiler", args.native_cc, "--sanitize"])
            atom_evidence = json.loads((output / "retained-atoms/qualification.json").read_text())
            if not atom_evidence["qualified"]:
                raise RuntimeError("production Atom/GMP probe did not qualify")
            merge_pins(atom_evidence["inputs"])
            record["retained_atom_probe"] = atom_evidence
            record["retained_atom_probe_boundary"] = (
                "Source-helper qualification is separate from the supplied CeTTa binary; "
                "no binary/source build provenance or array adapter is certified by this probe.")
        else:
            record["retained_atom_probe"] = {"qualified": False, "status": "not_requested"}
        if args.cetta_build_manifest:
            lifetime_gate = root / "tools/test_inductive_array_lifetime.py"
            builds = [("array-lifetime", args.cetta_build_manifest.resolve(), native_build)]
            if args.cetta_sanitized_build_manifest:
                builds.append(("array-lifetime-sanitized", args.cetta_sanitized_build_manifest.resolve(), companion))
            for label, manifest, build in builds:
                run(label, [sys.executable, str(lifetime_gate), "--build-manifest", str(manifest),
                    "--library", str(library), "--output", str(output / label)])
                lifetime = json.loads((output / label / "qualification.json").read_text())
                if (not lifetime["qualified"] or lifetime["binary_sha256"] != build["binary_sha256"] or
                        lifetime["source_pins"][str(library)] != pins[str(library)]):
                    raise RuntimeError("array lifetime gate used a different binary or checked emission")
                merge_pins(lifetime["source_pins"])
                record[label.replace("-", "_")] = lifetime
                if args.cetta_tree:
                    fault_gate = lean / "scripts/conformance/check_cetta_allocation_failure.py"
                    fault_label = label + "-failure"
                    run(fault_label, [sys.executable, str(fault_gate), "--build-manifest", str(manifest),
                        "--cetta-tree", str(args.cetta_tree.resolve()), "--library", str(library),
                        "--output", str(output / fault_label)])
                    fault = json.loads((output / fault_label / "qualification.json").read_text())
                    if not fault["qualified"] or fault["original_binary_sha256"] != build["binary_sha256"]:
                        raise RuntimeError("allocation failure evidence differs from selected build")
                    merge_pins(fault["inputs"])
                    record[fault_label.replace("-", "_")] = fault
            if args.cetta_sanitized_build_manifest:
                record["native_profile_qualified"] = True
                record["native_failure_policy"] = "Fail-stop process; no completed answer, no resumable provider fault"
                close_obligation(production_obligation)
            else:
                record["production_profile_boundary"] = (
                    "Paired optimized/sanitizer qualification remains required")
        else:
            record["array_lifetime"] = {"qualified": False, "status": "not_requested"}
        if args.native_facts_config:
            facts_gate = root / "tools/qualify_inductive_native_facts.py"
            config = args.native_facts_config.resolve()
            pins[str(facts_gate)] = digest(facts_gate)
            pins[str(config)] = digest(config)
            run("native-fact-routes", [sys.executable, str(facts_gate), "--cetta", str(cetta),
                "--config", str(config), "--output", str(output / "native-facts")])
            facts = json.loads((output / "native-facts/qualification.json").read_text())
            if (facts.get("qualified") is not True or facts.get("m1_qualified") is not False or
                    facts["binary_sha256"] != pins[str(cetta)]):
                raise RuntimeError("native fact routes differ from the selected binary or overstate M1")
            merge_pins(facts["input_pins"])
            merge_pins(facts["artifacts"])
            record["native_fact_routes"] = facts
            facts_controls = root / "tools/test_inductive_native_facts.py"
            pins[str(facts_controls)] = digest(facts_controls)
            run("native-fact-join-refusals", [sys.executable, str(facts_controls),
                str(output / "native-facts/qualification.json"), "--output",
                str(output / "native-facts/join-refusals.json")])
            close_obligation(native_obligation)
        else:
            record["native_fact_routes"] = {"qualified": False, "status": "not_requested"}
        fixed_streams = []
        for mode in ("prime", "petta", "reference-petta"):
            environment = dict(os.environ, LEAN_RUNNER="lean", CETTA_BIN=str(cetta),
                               CETTA_LANG=mode if mode != "reference-petta" else "petta",
                               PETTA_RUNNER=str(petta) if mode == "reference-petta" else "")
            directory = output / ("fixed-points-" + mode)
            run("fixed-points-" + mode, ["bash", str(fixed_gate), str(directory)],
                environment=environment)
            fixed_streams.append((directory / "native-fixed-points.packets").read_bytes())
        if not fixed_streams[0] == fixed_streams[1] == fixed_streams[2]:
            raise RuntimeError("fixed-point parsed packet streams differ")
        if any(digest(Path(path)) != value for path, value in pins.items()):
            raise RuntimeError("qualification inputs changed during the run")
        complete = not record["open_obligations"]
        record.update(status="passed" if complete else "incomplete",
                      m1_qualified=complete, available_stages_qualified=True,
                      input_pins=pins, emission_cases=actual, reader=reader, runtime=runtime,
                      fixed_point_controls_per_mode=112,
                      counter_source="NativeNaturalCounter.module, a separately authored companion with proved natural/parity comparison",
                      artifact_pins={str(path.relative_to(output)): digest(path)
                                     for path in (packet, library, annotation_file)},
                      retained_provider_scope="Selected retained addition-by-one calls, payloads, ownership, lifetimes and fail-stop allocation are qualified; universal availability and fairness are not claimed")
        save()
        if complete:
            print("M1 selected Nat/Vec append profile qualified on one source and artifact set.")
            return 0
        print("Available source/checking/emission/observation stages passed; M1 remains incomplete.")
        return 2
    except (OSError, subprocess.SubprocessError, RuntimeError, KeyError, ValueError) as error:
        record.update(status="failed", error=str(error))
        save()
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
