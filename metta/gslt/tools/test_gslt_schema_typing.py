#!/usr/bin/env python3
"""Run typed matching and retained producer components in the scoped extension."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta", type=Path)
    parser.add_argument("--family", choices=("schema", "constructor", "scan", "operations", "transitions", "allocations", "allocation-children"), default="schema")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not args.cetta and not args.petta:
        parser.error("select --cetta, --petta, or both")
    args.output.mkdir(parents=True, exist_ok=True)
    case_files = {"schema": "schema_typing_cases.json", "constructor": "constructor_typing_cases.json",
                  "scan": "constructor_scan_cases.json", "operations": "retained_operation_cases.json",
                  "transitions": "retained_transition_cases.json",
                  "allocations": "allocation_advance_cases.json",
                  "allocation-children": "allocation_children_cases.json"}
    cases_path = ROOT / "tests" / case_files[args.family]
    cases = json.loads(cases_path.read_text())["cases"]
    sources = [ROOT / "lib/gslt_scoped_execution.metta", ROOT / "lib/gslt_schema_typing.metta"]
    if args.family in ("constructor", "scan", "operations", "transitions", "allocations", "allocation-children"):
        sources.append(ROOT / "lib/gslt_collection_constructor_typing.metta")
    if args.family in ("scan", "operations", "transitions", "allocations", "allocation-children"):
        sources.append(ROOT / "lib/gslt_collection_constructor_scan.metta")
    if args.family in ("operations", "transitions", "allocations", "allocation-children"):
        sources.extend([ROOT / "lib/gslt_complete.metta", ROOT / "lib/gslt_collection_retained_operations.metta"])
    if args.family in ("allocations", "allocation-children"):
        sources.extend([ROOT / "lib/gslt_collection_presentation.metta", ROOT / "lib/gslt_collection_allocation_advance.metta"])
    if args.family == "allocation-children":
        sources.append(ROOT / "lib/gslt_collection_allocation_children.metta")
    before = {str(p.relative_to(ROOT)): digest(p) for p in [*sources, cases_path]}
    fixture = args.output / (args.family + "-typing.metta")
    fixture.write_text("\n".join(p.read_text() for p in sources) + "\n" +
                       "\n".join("!" + case["call"] for case in cases) + "\n")
    commands = []
    if args.cetta:
        commands.append(("cetta", [str(args.cetta.resolve()), "--lang", "petta", "--quiet", str(fixture.resolve())]))
    if args.petta:
        commands.append(("petta", ["bash", str(args.petta.resolve()), "--silent", str(fixture.resolve())]))
    expected = [case["expected"] for case in cases]
    engines = []
    environment = os.environ.copy()
    environment["CETTA_PETTA_SEARCH_MACHINE"] = "1"
    for engine, command in commands:
        started = time.monotonic()
        result = subprocess.run(command, env=environment, capture_output=True, text=True, timeout=60)
        output = args.output / (engine + ".out")
        errors = args.output / (engine + ".err")
        output.write_text(result.stdout)
        errors.write_text(result.stderr)
        actual = [line for line in result.stdout.splitlines() if line.strip()]
        mismatches = [case["name"] for index, case in enumerate(cases)
                      if index >= len(actual) or actual[index] != expected[index]]
        passed = result.returncode == 0 and actual == expected and not result.stderr
        engines.append({"engine": engine, "exit_code": result.returncode, "passed": passed,
                        "answers": len(actual), "mismatches": mismatches,
                        "seconds": time.monotonic() - started,
                        "output_sha256": digest(output), "error_sha256": digest(errors),
                        "launcher_sha256": digest(Path(command[0] if engine == "cetta" else command[1]))})
    stable = all(digest(ROOT / path) == value for path, value in before.items())
    identical = len({row["output_sha256"] for row in engines}) == 1
    passed = stable and identical and all(row["passed"] for row in engines)
    receipt = {"passed": passed, "cases_per_engine": len(cases), "engines": engines,
               "sources": before, "sources_unchanged": stable, "outputs_identical": identical,
               "general_admission_changed": False,
               "family": args.family,
               "scope": "selected source component in the scoped extension; no full producer qualification"}
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
