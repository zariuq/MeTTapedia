#!/usr/bin/env python3
"""Prepare a qualified transform source export and run its typed Lean receiver.

Address selection and type-definition pairing are untrusted data adaptation.
The existing receiver checks every command, exact root formula and defining
theorem. This tool supplies no inference or axiom authority.
"""

import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


DEFINITIONS = [
    "T", "/\\", "==>", "!", "?", "\\/", "F", "~", "?!", "I",
    "tc_fire", "tc_models", "tc_solvable", "tc_map_store", "tc_frames", "tc_store",
    "tc_prepared_effect", "tc_semantic_effect", "tc_exact_knowledge", "tc_prepared_event",
    "tc_admitted_event", "tc_solution_preparation", "tc_guard_profile", "tc_profile_inclusion",
]
RUN_ROOTS = {
    "TC_RUN_LIST_SEPARATION", "TC_RUN_LIST_INJECTIVITY", "TC_RUN_LIST_INDUCTION",
    "TC_RUN_PATH_NIL", "TC_RUN_PATH_CONS", "TC_RUN_PULLBACK_NIL", "TC_RUN_PULLBACK_CONS",
}

WORD_ROOTS = {
    "TC_PREPARED_WORD_TARGET_NIL", "TC_PREPARED_WORD_TARGET_CONS",
    "TC_PREPARED_WORD_DOMAIN_NIL", "TC_PREPARED_WORD_DOMAIN_CONS",
}

TRACE_ROOTS = {"TC_TRACE_MEANING"}


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main():
    project = Path(__file__).resolve().parents[1]
    workspace = project.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path, help="completed check_theory.py output directory")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--lean-project", type=Path, default=project / "lean/mettapedia")
    parser.add_argument("--source-tools", type=Path,
                        default=workspace / "hyperon/cetta-prime-weights-parallel-20261001/tools")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--prepared-words", action="store_true",
                        help="also require the exact target/domain equations and their shared native model")
    parser.add_argument("--traces", action="store_true",
                        help="also require the exact trace meaning in the preparation/admission/word model")
    args = parser.parse_args()
    if args.traces:
        args.prepared_words = True
    bundle, output = args.bundle.resolve(), args.output.resolve()
    source = bundle / "source"
    qualified = json.loads((bundle / "qualification.json").read_text())
    if not qualified["qualified"]:
        raise ValueError("source proof bundle is not qualified")
    export = json.loads((source / "export.json").read_text())
    signature = json.loads((source / "closure.signature.json").read_text())
    definition_roots = set(signature["definition_roots"])
    normalizer_path = args.source_tools / "hol_light_prepare_export_v1.py"
    spec = importlib.util.spec_from_file_location("source_pairing", normalizer_path)
    normalizer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(normalizer)
    output.mkdir(parents=True, exist_ok=True)
    plain = source / "closure.nodes.jsonl"
    storage = plain if plain.exists() else Path(str(plain) + ".gz")
    before = storage.stat()
    source_hash, events_hash = hashlib.sha256(), hashlib.sha256()
    definitions = {}

    def records():
        opener = gzip.open if storage.suffix == ".gz" else open
        with opener(storage, "rb") as stream:
            for line in stream:
                source_hash.update(line)
                record = json.loads(line)
                if record["id"] in definition_roots and record["rule"] == "DEFINITION":
                    name = record["arguments"][1]
                    if name in definitions:
                        raise ValueError(f"duplicate defining record: {name}")
                    definitions[name] = record["id"]
                yield record

    count = 0
    with (output / "events.jsonl").open("wb") as target:
        for record in normalizer.group_type_definitions(records()):
            line = (json.dumps(record, separators=(",", ":")) + "\n").encode()
            target.write(line)
            events_hash.update(line)
            count += 1
    after = storage.stat()
    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
        raise ValueError("source changed during preparation")
    if source_hash.hexdigest() != export["artifacts"]["closure.nodes.jsonl"]:
        raise ValueError("source proof closure hash mismatch")
    addresses = [definitions[name] for name in DEFINITIONS]
    roots = [json.loads(line) for line in (source / "closure.roots.jsonl").read_text().splitlines()]
    required_roots = RUN_ROOTS | WORD_ROOTS if args.prepared_words else RUN_ROOTS
    if args.traces:
        required_roots |= TRACE_ROOTS
    roots = [root for root in roots if root["name"] in required_roots]
    if len(roots) != len(required_roots) or {root["name"] for root in roots} != required_roots:
        raise ValueError("run root inventory mismatch")
    (output / "definitions.json").write_text(json.dumps(addresses) + "\n")
    (output / "roots.jsonl").write_text("".join(json.dumps(root, separators=(",", ":")) + "\n" for root in roots))
    receiver = args.lean_project / "scripts/hol_light_run_export.lean"
    report = dict(prepared=True, qualified=False, events=count,
                  source_sha256=source_hash.hexdigest(), events_sha256=events_hash.hexdigest(),
                  definition_addresses=addresses, definition_names=DEFINITIONS,
                  receiver_sha256=digest(receiver), normalizer_sha256=digest(normalizer_path),
                  source_proof_bundle_sha256=qualified["holr_sha256"],
                  prepared_word_interpretation=args.prepared_words,
                  trace_interpretation=args.traces,
                  native_implementation_refinement=False,
                  closed_kernel_reduction_of_complete_replay=False)
    if not args.prepare_only:
        with (output / "receiver.log").open("w") as log:
            command = [
                "lake", "env", "lean", "--run", "scripts/hol_light_run_export.lean",
                str(output / "events.jsonl"), str(output / "roots.jsonl"), str(output / "definitions.json"),
            ]
            if args.traces:
                command.append("traces")
            elif args.prepared_words:
                command.append("prepared-words")
            result = subprocess.run(command, cwd=args.lean_project, stdout=log, stderr=subprocess.STDOUT)
        if digest(receiver) != report["receiver_sha256"]:
            raise ValueError("receiver source changed during qualification")
        if digest(output / "events.jsonl") != report["events_sha256"]:
            raise ValueError("prepared source changed during qualification")
        report["receiver_exit"] = result.returncode
        report["qualified"] = result.returncode == 0
        report["receiver_log_sha256"] = digest(output / "receiver.log")
    (output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ["prepared", "qualified", "events", "source_sha256"]}))
    if not args.prepare_only and not report["qualified"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
