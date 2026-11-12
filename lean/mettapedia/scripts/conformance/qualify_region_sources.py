#!/usr/bin/env python3
"""Qualify durable region-source canaries against explicitly pinned PeTTa trees.

Reference trees are read-only inputs, verified against the supplied Git
repository. Every expected-output fixture is included unless --fixture names
an explicit subset. A failing comparison remains a failing process status.
The output directory must be new so prior receipts cannot be overwritten.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


FIXTURES = Path(__file__).resolve().parent / "region_sources"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_pins(repository: Path, revision: str, directory: Path) -> tuple[str, list[dict]]:
    commit = subprocess.check_output(
        ["git", "-C", str(repository), "rev-parse", "--verify", revision + "^{commit}"], text=True
    ).strip()
    raw = subprocess.check_output([
        "git", "-C", str(repository), "ls-tree", "-rz", commit, "--", "src", "lib", "run.sh"])
    pins = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, name = record.split(b"\t", 1)
        _, kind, wanted = metadata.split()
        if kind != b"blob":
            raise ValueError("Non-blob reference input")
        relative = name.decode()
        data = (directory / relative).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if actual != wanted.decode():
            raise ValueError("Reference input differs: " + relative)
        pins.append({"file": relative, "git_blob": actual, "sha256": sha256(data)})
    if not pins or not any(pin["file"] == "run.sh" for pin in pins):
        raise ValueError("Reference revision has no runnable source inventory")
    if (directory / "mork_ffi/target/release/libmork_ffi.so").exists():
        raise ValueError("Unpinned optional backend in reference tree")
    return commit, pins


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, required=True, help="PeTTa Git repository containing the revisions")
    parser.add_argument("--reference", nargs=3, action="append", required=True,
                        metavar=("NAME", "REVISION", "TREE"), help="Repeat for each read-only reference tree")
    parser.add_argument("--output", type=Path, required=True, help="New directory for receipts and process output")
    parser.add_argument("--fixture", action="append", help="Fixture stem; default is every paired fixture")
    parser.add_argument("--fixtures", type=Path, default=FIXTURES, help="Directory of source and expected-output pairs")
    parser.add_argument("--python", default="python3.12", help="Python executable used by the reference bridge")
    parser.add_argument("--timeout", type=float, default=30, help="Per-canary timeout in seconds")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    names = [reference[0] for reference in args.reference]
    if len(set(names)) != len(names) or any(not re.fullmatch(r"[A-Za-z0-9_-]+", name) for name in names):
        parser.error("reference names must be unique filename-safe identifiers")
    fixtures = args.fixtures.resolve()
    available = {path.stem for path in fixtures.glob("*.expected")}
    chosen = sorted(set(args.fixture) if args.fixture else available)
    if not chosen or set(chosen) - available:
        parser.error("unknown or empty fixture selection")
    references = []
    for name, revision, tree in args.reference:
        directory = Path(tree).resolve()
        commit, pins = source_pins(args.repository.resolve(), revision, directory)
        references.append((name, commit, pins, directory))

    environment = os.environ.copy()
    python_lib = subprocess.check_output([
        args.python, "-c", 'import sysconfig; print(sysconfig.get_config_var("LIBDIR"))'], text=True).strip()
    environment["LD_LIBRARY_PATH"] = python_lib + (
        ":" + environment["LD_LIBRARY_PATH"] if environment.get("LD_LIBRARY_PATH") else "")
    report = {
        "schema": "region-source-qualification-v1",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "runner_sha256": sha256(Path(__file__).read_bytes()),
        "swipl_version": subprocess.check_output(["swipl", "--version"], text=True).strip(),
        "python_version": subprocess.check_output([args.python, "--version"], text=True).strip(),
        "runtime_executables": {
            name: sha256(Path(shutil.which(command) or command).resolve().read_bytes())
            for name, command in (("swipl", "swipl"), ("python", args.python))
        },
        "fixture_selection": chosen,
        "profiles": [],
    }
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for name, commit, pins, directory in references:
        profile = {"name": name, "commit": commit, "source_pins": pins, "runs": []}
        for fixture in chosen:
            source = fixtures / (fixture + ".metta")
            source_bytes = source.read_bytes()
            expected = (fixtures / (fixture + ".expected")).read_bytes()
            try:
                process = subprocess.run(["bash", str(directory / "run.sh"), "--silent", str(source)],
                                         cwd=directory, env=environment, capture_output=True, timeout=args.timeout)
                stdout, stderr, status = process.stdout, process.stderr, process.returncode
                timed_out = False
            except subprocess.TimeoutExpired as timeout:
                stdout, stderr, status = timeout.stdout or b"", timeout.stderr or b"", None
                timed_out = True
            (output / (fixture + "-" + name + ".stdout")).write_bytes(stdout)
            (output / (fixture + "-" + name + ".stderr")).write_bytes(stderr)
            inputs_stable = source.read_bytes() == source_bytes and (fixtures / (fixture + ".expected")).read_bytes() == expected
            profile["runs"].append({
                "fixture": fixture, "exit": status, "timed_out": timed_out,
                "stdout_matches": stdout == expected, "stderr_empty": not stderr,
                "inputs_stable": inputs_stable,
                "qualified": status == 0 and stdout == expected and not stderr and not timed_out and inputs_stable,
                "source_sha256": sha256(source_bytes), "expected_sha256": sha256(expected),
                "stdout_sha256": sha256(stdout), "stderr_sha256": sha256(stderr),
            })
        _, final_pins = source_pins(args.repository.resolve(), commit, directory)
        profile["reference_inputs_stable"] = final_pins == pins
        profile["all_canaries_qualified"] = profile["reference_inputs_stable"] and all(run["qualified"] for run in profile["runs"])
        report["profiles"].append(profile)
    report["completed_at"] = datetime.now(timezone.utc).isoformat()
    report["qualified"] = all(profile["all_canaries_qualified"] for profile in report["profiles"])
    (output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"qualified": report["qualified"], "profiles": [
        {"name": profile["name"], "passed": sum(run["qualified"] for run in profile["runs"]),
         "total": len(profile["runs"]), "failures": [run["fixture"] for run in profile["runs"] if not run["qualified"]]}
        for profile in report["profiles"]]}, indent=2))
    return 0 if report["qualified"] else 1


if __name__ == "__main__":
    sys.exit(main())
