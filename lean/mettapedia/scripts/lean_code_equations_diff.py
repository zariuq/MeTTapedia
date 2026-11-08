#!/usr/bin/env python3
"""Run an exported slice of Lean code equations in CeTTa's PeTTa dialect and
compare every answer with Lean's own evaluation.

Usage:
  python3 scripts/lean_code_equations_diff.py --cetta PATH [--slice core]
      [--timeout SECONDS] [--memory-mb MB] [--report PATH]

Each test runs alone, after the prelude and the slice's rules, with a timeout
and an optional memory limit, so one failing test cannot hide the rest.
The report records the binary, its version, its revision when it sits in a
git checkout, and each test's answer and time.  The exit status is zero only
when every answer equals Lean's.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PRELUDE = ROOT / "Mettapedia/Languages/Lean/CodeEquations/prelude.metta"


def binary_identity(binary: Path) -> dict:
    identity = {"name": binary.name, "sha256": hashlib.sha256(binary.read_bytes()).hexdigest()}
    try:
        version = subprocess.run([str(binary), "--version"], capture_output=True,
                                 text=True, timeout=30)
        identity["version"] = (version.stdout or version.stderr).strip().splitlines()[:2]
    except (OSError, subprocess.TimeoutExpired) as error:
        identity["version"] = [f"unavailable: {error}"]
    try:
        revision = subprocess.run(["git", "-C", str(binary.parent), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, timeout=30)
        if revision.returncode == 0:
            identity["revision"] = revision.stdout.strip()
        status = subprocess.run(["git", "-C", str(binary.parent), "status", "--porcelain",
                                 "--untracked-files=no"],
                                capture_output=True, text=True, timeout=60)
        if status.returncode == 0:
            identity["tracked_changes"] = len(status.stdout.splitlines())
    except (OSError, subprocess.TimeoutExpired):
        pass
    return identity


def limit_memory(megabytes: int):
    def apply() -> None:
        size = megabytes * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (size, size))
    return apply


def read_tests(slice_dir: Path) -> list[dict]:
    rows = (slice_dir / "tests.tsv").read_text().splitlines()
    header = rows[0].split("\t")
    tests = [dict(zip(header, row.split("\t"))) for row in rows[1:] if row]
    queries = [line for line in (slice_dir / "tests.metta").read_text().splitlines()
               if line.startswith("!")]
    if len(queries) != len(tests):
        raise SystemExit(f"tests.metta has {len(queries)} queries, tests.tsv {len(tests)} rows")
    for test, query in zip(tests, queries):
        test["query"] = query
    return tests


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--slice", default="core")
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--memory-mb", type=int,
                        help="optional address-space limit per test, in megabytes")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.memory_mb is not None and args.memory_mb <= 0:
        parser.error("--memory-mb must be positive")

    slice_dir = ROOT / "artifacts/lean-code-equations" / args.slice
    tests = read_tests(slice_dir)
    results = []
    with tempfile.TemporaryDirectory(prefix="queries-", dir=slice_dir) as scratch:
        for test in tests:
            query_file = Path(scratch) / f"test_{test['index']}.metta"
            query_file.write_text(test["query"] + "\n")
            command = [str(args.cetta), "--lang", "petta", str(PRELUDE),
                       str(slice_dir / "rules.metta"), str(query_file)]
            start = time.monotonic()
            returncode = None
            output = []
            try:
                run = subprocess.run(command, capture_output=True, text=True,
                                     timeout=args.timeout,
                                     preexec_fn=(limit_memory(args.memory_mb)
                                                 if args.memory_mb is not None else None))
                output = run.stdout.strip().splitlines()
                returncode = run.returncode
                answer = output[0] if output else ""
                if returncode != 0:
                    status = "crash" if returncode < 0 else "error"
                elif len(output) != 1:
                    status = "malformed-output"
                else:
                    status = "agree" if answer == test["petta_value"] else "differ"
                detail = "" if status == "agree" else (run.stderr.strip()[:400] or answer)
            except subprocess.TimeoutExpired:
                answer, status, detail = "", "timeout", f"no answer within {args.timeout} s"
            elapsed = time.monotonic() - start
            results.append({
                "index": int(test["index"]), "lean_source": test["lean_source"],
                "lean_value": test["lean_value"], "expected": test["petta_value"],
                "answer": answer, "status": status, "seconds": round(elapsed, 3),
                "detail": detail, "returncode": returncode, "stdout_lines": output,
            })

    agree = sum(1 for result in results if result["status"] == "agree")
    report = {
        "slice": args.slice,
        "binary": binary_identity(args.cetta.resolve()),
        "timeout_seconds": args.timeout,
        "memory_mb": args.memory_mb,
        "agree": agree,
        "total": len(results),
        "tests": results,
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    for result in results:
        mark = "ok  " if result["status"] == "agree" else result["status"].upper()
        print(f"{result['index']:3d} {mark:8s} {result['seconds']:8.3f}s  {result['lean_source']}")
        if result["status"] != "agree":
            print(f"      expected {result['expected']}\n      got      {result['answer'] or '-'}")
    print(f"{agree}/{len(results)} answers equal Lean's")
    return 0 if agree == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
