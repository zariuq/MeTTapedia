#!/usr/bin/env python3
"""Serial MORK qualification against a supplied Metamath suite and oracle.

Each registered case remains visible in the report. A timeout, step limit,
translation/tool error, or missing terminal is never a passing rejection.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from assemble import load_verifier, write_atomic
from run import run_case


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def registered(suite: Path) -> list[tuple[str, str, Path]]:
    entries: list[tuple[str, str, Path]] = []
    names: set[str] = set()
    for line in (suite / "reference/reference.txt").read_text().splitlines():
        content = line.split("#", 1)[0].strip()
        if not content:
            continue
        verdict, relative = content.split(maxsplit=1)
        relative_path = Path(relative)
        if (verdict not in {"ACCEPT", "REJECT"} or relative in names or
                relative_path.is_absolute() or ".." in relative_path.parts):
            raise ValueError(f"invalid or duplicate reference entry: {content}")
        names.add(relative)
        path = suite / "tests" / relative
        if not path.is_file():
            raise ValueError(f"registered fixture is missing: {relative}")
        entries.append((verdict, relative, path.resolve()))
    return entries


def suite_verdict(outcome: str) -> str | None:
    if outcome in {"accepted", "incomplete-proof"}:
        return "ACCEPT"
    if outcome == "rejected":
        return "REJECT"
    return None


def snapshot_verifier(destination: Path, manifest: Path | None = None) -> Path:
    """Freeze A for the whole qualification, independent of concurrent edits."""
    assembly = load_verifier() if manifest is None else load_verifier(manifest)
    destination.mkdir(parents=True, exist_ok=True)
    checks = {key: assembly.manifest[key] for key in
              ("forms", "top_level_exec", "parsed_sha256")}
    snapshot = {
        "schema": "mm2-verifier-manifest-v1", "profile": "zar",
        "source_data_schema": "mm2-source-data-v1", **checks,
        "fragments": [{"file": "verifier.mm2", **checks}],
    }
    write_atomic(destination / "verifier.mm2", assembly.text)
    path = destination / "manifest.json"
    write_atomic(path, json.dumps(snapshot, indent=2) + "\n")
    return path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", type=Path, required=True)
    parser.add_argument("--translator", type=Path, required=True)
    parser.add_argument("--mork", type=Path, required=True)
    parser.add_argument("--oracle", type=Path, required=True,
                        help="released mm-lean4 executable, tested explicitly in Zar mode")
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--steps", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--only", help="optional regex over registered paths; unselected cases are skipped")
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    if args.steps <= 0 or args.timeout <= 0:
        parser.error("step and time budgets must be positive")
    suite = args.suite.resolve()
    supplied_paths = {key: getattr(args, key).resolve() for key in ("translator", "mork", "oracle")}
    selected = re.compile(args.only) if args.only else None
    entries = registered(suite)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    session = Path(tempfile.mkdtemp(prefix="qualification-", dir=args.work_dir.resolve()))
    manifest = snapshot_verifier(session / "verifier", args.manifest)
    paths = {}
    for key, supplied in supplied_paths.items():
        copied = session / key
        shutil.copy2(supplied, copied)
        paths[key] = copied
    report: dict[str, object] = {
        "schema": "mm2-runtime-qualification-v1", "profile": "zar",
        "registered": len(entries), "selection": args.only,
        "steps_cap": args.steps, "timeout_seconds": args.timeout,
        "verifier_manifest": str(manifest),
        "reference_sha256": sha256(suite / "reference/reference.txt"),
        "binaries": {key: {"sha256": sha256(path)} for key, path in paths.items()},
        "cases": [],
    }
    try:
        identity = subprocess.run([str(paths["translator"]), "--identity"], capture_output=True,
                                  text=True, check=True, timeout=10)
        report["translator_identity"] = identity.stdout.strip()
    except (OSError, subprocess.SubprocessError) as error:
        report["translator_identity_error"] = str(error)
    passed = failed = skipped = 0
    cases: list[dict[str, object]] = []
    for index, (expected, relative, path) in enumerate(entries):
        if selected and not selected.search(relative):
            cases.append({"path": relative, "expected": expected, "status": "skipped"})
            skipped += 1
            continue
        case: dict[str, object] = {"path": relative, "expected": expected, "source_sha256": sha256(path)}
        try:
            oracle = subprocess.run([str(paths["oracle"]), "--mode=zar", str(path)],
                                    capture_output=True, text=True, timeout=args.timeout)
            case["oracle_exit"] = oracle.returncode
            case["oracle_verdict"] = {0: "ACCEPT", 1: "REJECT"}.get(oracle.returncode)
            outcome = run_case(input_path=path, translator=paths["translator"], mork=paths["mork"],
                               work_dir=session / f"{index:03}-{path.stem}",
                               steps=args.steps, timeout=args.timeout,
                               manifest=manifest)
            case["runtime"] = outcome
            case["runtime_verdict"] = suite_verdict(str(outcome["outcome"]))
            ok = case["oracle_verdict"] == expected and case["runtime_verdict"] == expected
            case["status"] = "passed" if ok else "failed"
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            case.update(status="failed", diagnostic=str(error))
        if case["status"] == "passed":
            passed += 1
        else:
            failed += 1
        cases.append(case)
        report.update(cases=cases, passed=passed, failed=failed, skipped=skipped,
                      complete=len(cases) == len(entries) and skipped == 0,
                      qualified=passed == len(entries))
        encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
        write_atomic(session / "qualification.json", encoded)
        write_atomic(args.work_dir / "qualification.json", encoded)
        print(json.dumps(case, sort_keys=True), flush=True)
    report.update(cases=cases, passed=passed, failed=failed, skipped=skipped,
                  complete=skipped == 0, qualified=passed == len(entries))
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    write_atomic(session / "qualification.json", encoded)
    write_atomic(args.work_dir / "qualification.json", encoded)
    print(json.dumps({key: report[key] for key in
                      ("registered", "passed", "failed", "skipped", "complete", "qualified")}), flush=True)
    return int(bool(failed) or bool(skipped))


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"qualification failed: {error}", file=sys.stderr)
        raise SystemExit(2)
