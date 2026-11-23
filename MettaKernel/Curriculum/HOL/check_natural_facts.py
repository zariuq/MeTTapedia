#!/usr/bin/env python3
"""Qualify source-produced natural facts through the existing native HOL service.

The expected statements come from the independently checked intrinsic HOL
presentation. Existing source export and HOLR adapters remain untrusted
producers. This gate compares exact statements and artifact identities; it
does not implement proof checking or prove the linked native implementation.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


ROOTS = ["num_RECURSION", "num_INDUCTION", "NOT_SUC", "SUC_INJ", "NAT_CARRIER_INFINITY"]
BOOLEAN_ROOTS = ["BOOL_DATA_RECURSION", "BOOL_DATA_INDUCTION", "BOOL_DATA_DISTINCT",
                 "BOOL_DATA_CASES", "BOOL_DATA_FINITE"]
GUARDED_ROOTS = ["GUARDED_FORALL_TRANSPORT", "GUARDED_EXISTS_TRANSPORT"]

FAMILIES = {
    "natural": (ROOTS, "IndexedInductiveNaturalHOL.NativeFacts.all_models", "HOLLightNaturalFacts.ml"),
    "boolean": (BOOLEAN_ROOTS, "IndexedInductiveBooleanHOL.NativeMeaning.all_models", "HOLLightBooleanFacts.ml"),
    "guarded": (GUARDED_ROOTS, "HOL.GuardedQuantifierTransport.all_models", "HOLLightGuardedQuantifierTransport.ml"),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def exact_output(output, statements, records):
    return output.splitlines() == statements + [f"(hol:accepted {records} {len(statements)})"]


def main(family="natural", entrypoint=None):
    if family not in FAMILIES:
        raise ValueError("unknown structural fact family")
    roots, meaning, proof_filename = FAMILIES[family]
    profile = "sealed" if family == "guarded" else "standard"
    parser = argparse.ArgumentParser(description=__doc__.replace("natural facts", family + " facts"))
    for option in ["cetta", "source", "closure-helper", "source-tools", "stream-tools", "adapter", "expected", "output"]:
        parser.add_argument("--" + option, type=Path, required=True)
    args = parser.parse_args()
    for key, value in vars(args).items():
        setattr(args, key, value.resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    report = dict(qualified=False, m1_qualified=False, family=family, profile=profile, stages=[], input_pins={})

    def save():
        report["wall_seconds"] = round(time.monotonic() - started, 4)
        report["aggregate_child_peak_rss_kib"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        (args.output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")

    def pin(path):
        require(path.is_file(), "missing input: " + str(path))
        report["input_pins"][str(path)] = digest(path)

    def run(label, command, code=0, diagnostic=None):
        before = time.monotonic()
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run(list(map(str, command)), text=True, capture_output=True, env=environment)
        (args.output / (label + ".stdout")).write_text(result.stdout)
        (args.output / (label + ".stderr")).write_text(result.stderr)
        report["stages"].append(dict(label=label, returncode=result.returncode,
                                      seconds=round(time.monotonic() - before, 4)))
        save()
        require(result.returncode == code, label + " returned " + str(result.returncode))
        if diagnostic:
            require(diagnostic in result.stdout + result.stderr, label + " lacks refusal diagnostic")
        return result

    try:
        source_proof = Path(__file__).with_name(proof_filename).resolve()
        exporter = args.source_tools / "hol_light_proof_export_v1.py"
        for path in [Path(__file__).resolve(), source_proof, args.cetta, args.expected, args.adapter,
                     args.closure_helper, exporter, args.source_tools / "hol_light_prepare_export_v1.py",
                     args.stream_tools / "holr.py", args.source / "ocaml-hol"]:
            pin(path)
        if entrypoint is not None:
            pin(Path(entrypoint).resolve())
        if family in ("boolean", "guarded"):
            repository = Path(__file__).resolve().parents[3]
            lean = repository / "lean/mettapedia"
            source_inventory = repository / "metta/gslt/tools/qualify_inductive_native_facts.py"
            pin(source_inventory)
            spec = importlib.util.spec_from_file_location("native_fact_source_inventory", source_inventory)
            inventory = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(inventory)
            model_roots = ([lean / "Mettapedia/GSLT/LanguageDef/IndexedInductiveBooleanHOL.lean",
                            lean / "Mettapedia/Languages/HOLLight/BooleanFacts.lean",
                            lean / "scripts/emit_hol_boolean_facts.lean"] if family == "boolean" else
                           [lean / "Mettapedia/Logic/HOL/GuardedQuantifierTransport.lean",
                            lean / "Mettapedia/Languages/HOLLight/GuardedQuantifierTransport.lean",
                            lean / "scripts/emit_hol_guarded_quantifier_transport.lean"])
            retained = inventory.project_source_pins(model_roots, lean)
            for path, value in retained.items():
                require(digest(Path(path)) == value, "model source changed during inventory")
                report["input_pins"][path] = value
            report["model_project_source_count"] = len(retained)
            report["compiled_model_correspondence_established_by_source_pins"] = False
            model_files = ([
                    lean / "Mettapedia/Logic/HOL/BooleanFacts.lean",
                    lean / "Mettapedia/GSLT/LanguageDef/IndexedInductiveBooleanHOL.lean",
                    lean / "Mettapedia/Languages/HOLLight/BooleanFacts.lean",
                    lean / "scripts/emit_hol_boolean_facts.lean"] if family == "boolean" else model_roots)
            for path in [*model_files, lean / "lean-toolchain", lean / "lake-manifest.json"]:
                pin(path)
        for path in sorted(args.source.glob("*.cmo")):
            pin(path)
        expected = json.loads(args.expected.read_text())
        require(expected.get("profile") == profile, "wrong requested axiom policy")
        require(expected.get("authored_meaning") == meaning,
                "wrong authored interpretation interface")
        require([row["name"] for row in expected["facts"]] == roots, "wrong typed root inventory")
        statements = [row["statement"] for row in expected["facts"]]
        require(len(set(statements)) == len(roots), "repeated typed statement")
        helper = args.output / "source-helper.ml"
        helper.write_text("loadt " + json.dumps(str(args.closure_helper)) + ";;\n" +
                          "loadt " + json.dumps(str(source_proof)) + ";;\n")
        pin(helper)
        source_output = args.output / "source"
        command = [sys.executable, exporter, "--source", args.source, "--closure-helper", helper,
                   "--output", source_output, "--library-through", "nums.ml"]
        for name in roots:
            command += ["--theorem", name]
        exported = json.loads(run("source-export", command).stdout)
        prefix = source_output / "closure"
        receipt = json.loads((source_output / "export.json").read_text())
        require([row["name"] for row in exported["roots"]] == roots, "wrong exported roots")
        require(len(set(row["id"] for row in exported["roots"])) == len(roots), "repeated source root")
        require((len(exported["axiom_nodes"]) == 3 if family == "natural" else
                 len(exported["axiom_nodes"]) == 0 if family == "guarded" else
                 len(exported["axiom_nodes"]) <= 3), "source introduced an additional axiom")
        require(receipt["source"]["closure_helper_sha256"] == digest(helper), "wrong source helper")
        for name, value in receipt["source"]["tracked_sources"].items():
            path = args.source / name
            require(digest(path) == value, "source changed after export")
            pin(path)
        for name, value in receipt["artifacts"].items():
            path = source_output / name
            require(digest(path) == value, "source artifact changed after export")
            pin(path)
        pin(source_output / "export.json")
        adapter = [sys.executable, args.adapter, "--stream-tools", args.stream_tools,
                   "--source-tools", args.source_tools, "--prefix", prefix]
        wire = args.output / (family + "-facts.holr")
        generated = json.loads(run("wire", [*adapter, "--output", wire]).stdout)
        pin(wire)
        records = generated["wire_records"]
        native = run("native", [args.cetta, "--lang", "hol-light", "--profile", profile, wire])
        require(not native.stderr.strip(), "native replay emitted diagnostics")
        require(exact_output(native.stdout, statements, records), "native/typed statements disagree")
        for label, flag, diagnostic in [("changed-root", "--changed-root", "expectation failed"),
                                       ("extra-axiom", "--extra-axiom", "axiom policy")]:
            altered = args.output / (label + ".holr")
            run(label + "-wire", [*adapter, flag, "--output", altered])
            run(label + "-native", [args.cetta, "--lang", "hol-light", "--profile", profile, altered],
                code=1, diagnostic=diagnostic)
        truncated = args.output / "truncated.holr"
        truncated.write_bytes(wire.read_bytes()[:-1])
        run("truncated-native", [args.cetta, "--lang", "hol-light", "--profile", profile, truncated],
            code=2, diagnostic="truncated")
        dropped = native.stdout.splitlines()
        del dropped[-2]
        changed = native.stdout.splitlines()
        changed_index = min(2, len(statements) - 1)
        old_token, new_token = {"natural": ('"SUC"', '"NUMERAL"'),
                                "boolean": ('"F"', '"T"'),
                                "guarded": ('"G"', '"H"')}[family]
        changed[changed_index] = changed[changed_index].replace(old_token, new_token, 1)
        require(changed != native.stdout.splitlines(), "packet mutation did not change its target")
        repeated = native.stdout.splitlines()
        repeated[min(3, len(statements) - 1)] = repeated[changed_index if len(statements) > 2 else 0]
        missing_label = {"natural": "missing-infinity-packet", "boolean": "missing-finiteness-packet",
                         "guarded": "missing-transport-packet"}[family]
        for label, altered in [(missing_label, dropped),
                               ("changed-operation-packet", changed),
                               ("repeated-root-packet", repeated)]:
            require(not exact_output("\n".join(altered), statements, records), label + " was accepted")
        packet_refusals = 3
        if family == "guarded":
            erased = expected.get("guard_erasure")
            require(isinstance(erased, str) and erased != statements[0], "missing typed guard-erasure control")
            require(not exact_output(native.stdout, [erased, *statements[1:]], records),
                    "guard-erasure claim packet was accepted")
            packet_refusals += 1
        for path, value in report["input_pins"].items():
            require(digest(Path(path)) == value, "input changed during qualification")
        report.update(qualified=True, selected_fact_interface_qualified=True,
                      release_provenance_qualified=False,
                      binary_sha256=digest(args.cetta), roots=expected["facts"],
                      source_revision=receipt["source"]["revision"], source_nodes=exported["nodes"],
                      source_axiom_nodes=exported["axiom_nodes"], source_axioms_added=0,
                      accepted_records=records, artifact_sha256=digest(wire), artifact_bytes=wire.stat().st_size,
                      native_refusals=3, packet_refusals=packet_refusals,
                      meaning=expected["authored_meaning"],
                      scope=("Selected typed guarded quantifier laws and their Henkin-model meaning" if family == "guarded" else
                             "Selected typed " + family + "-law signature and authored-carrier interpretation"),
                      trust="Untrusted producers; exact pinned native replay; linked C correctness and release provenance remain separate",
                      full_source_definition_history_refinement=False)
        save()
        print(json.dumps(dict(qualified=True, roots=len(roots), records=records,
                              source_axioms_added=0, native_refusals=3, packet_refusals=packet_refusals)))
        return 0
    except (RuntimeError, ValueError, KeyError, OSError) as error:
        report["error"] = str(error)
        save()
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
