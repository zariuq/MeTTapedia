#!/usr/bin/env python3
"""Replay calibration fixtures against an explicitly supplied CeTTa executable.

Classification: untrusted source adapter. Exact outputs are authored in the
expected files; the manifest associates observations with semantic contracts.
Passing these controls is not a C-correspondence or proof-checking claim.
This runner does not build or modify the runtime.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--manifest", type=Path,
                        help="use another compatible calibration manifest")
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--petta-reference", action="store_true",
                        help="run PeTTa cases with the authored transform library in the default profile")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    manifest_path = args.manifest.resolve(strict=True) if args.manifest else Path(__file__).resolve().parent / "cases.json"
    here = manifest_path.parent
    manifest = json.loads(manifest_path.read_text())
    assert manifest["schema"] in {"store-demand-contract-fixtures-v1", "contextual-transform-fixtures-v1"}
    requested = set(args.case)
    known = {case["name"] for case in manifest["cases"]}
    if requested - known:
        parser.error("unknown case: " + ", ".join(sorted(requested - known)))
    binary_before = digest(binary)
    observations = []
    environment = dict(os.environ)
    environment.pop("CETTA_TRANSFORM_TRACE", None)
    for case in manifest["cases"]:
        if requested and case["name"] not in requested:
            continue
        source = here / case["source"]
        for run in case["runs"]:
            if args.petta_reference and run["dialect"] != "petta":
                continue
            expected_file = here / run["expected"]
            expected = expected_file.read_text()
            record = {"case": case["name"], "dialect": run["dialect"],
                      "profile": run["profile"], "source_sha256": digest(source),
                      "expected_sha256": digest(expected_file)}
            command = [str(binary), "--lang", run["dialect"]]
            case_environment = dict(environment)
            if args.petta_reference:
                command += ["-e", "!(import! &self (library lib_transform_swi))\n" + source.read_text()]
                expected = "true\n" + expected
                case_environment["CETTA_TRANSFORM_TRACE"] = "1"
                record["reference"] = "lib_transform_swi"
                record["profile"] = "default"
            else:
                if run.get("profile") is not None:
                    command += ["--profile", run["profile"]]
                command.append(str(source))
            try:
                process = subprocess.run(
                    command, cwd=binary.parent, env=case_environment, text=True, capture_output=True,
                    timeout=args.timeout, check=False)
                record.update(returncode=process.returncode, stdout=process.stdout, stderr=process.stderr)
                record["passed"] = process.returncode == 0 and process.stdout == expected
                if args.petta_reference and "[transform]" in process.stderr:
                    record.update(passed=False, failure="authored reference entered native transform")
            except subprocess.TimeoutExpired:
                record.update(passed=False, failure="timeout")
            observations.append(record)
            if not record["passed"]:
                print(f"FAIL {case['name']} [{run['dialect']}]: {record}", file=sys.stderr)
                print(f"expected: {expected!r}", file=sys.stderr)
    unchanged = digest(binary) == binary_before
    passed = sum(record["passed"] for record in observations)
    report = {"schema": "store-demand-contract-replay-v1", "binary_sha256": binary_before,
              "binary_unchanged": unchanged, "passed": passed, "total": len(observations),
              "observations": observations}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    if not unchanged:
        print("FAIL: executable changed during replay; rerun against a stable executable", file=sys.stderr)
    print(f"{passed}/{len(observations)} observations passed; executable unchanged={unchanged}")
    return 0 if unchanged and passed == len(observations) and observations else 1


if __name__ == "__main__":
    raise SystemExit(main())
