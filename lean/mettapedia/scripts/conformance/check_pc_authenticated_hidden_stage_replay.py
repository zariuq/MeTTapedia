#!/usr/bin/env python3
"""Check the authenticated trained-checkpoint hidden-stage replay boundary."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
THEOREM_ROOT = HERE.parent.parent
AIHUB_ROOT = THEOREM_ROOT.parents[2]
DEFAULT_SOURCE_ROOT = AIHUB_ROOT / "ml" / "gslt-synth"
FIXTURE = (
    THEOREM_ROOT
    / "artifacts"
    / "conformance"
    / "pc_authenticated_hidden_stage_replay_source_v1.json"
)
LEAN_TARGETS = (
    "Mettapedia.MachineLearning.NeuralNetworks.CreditTransport."
    "Float32AuthenticatedActivationReplaySite1Invocation0GeneratedFixture",
    "Mettapedia.MachineLearning.NeuralNetworks.CreditTransport."
    "Float32AuthenticatedHiddenStageReplaySite1Invocation0GeneratedFixture",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require_hashes(root: Path, entries: list[dict[str, Any]], label: str) -> None:
    for entry in entries:
        path = root / entry["file"]
        if not path.is_file():
            raise AssertionError(f"missing {label}: {entry['file']}")
        observed = sha256(path)
        if observed != entry["sha256"]:
            raise AssertionError(
                f"{label} hash mismatch for {entry['file']}: {observed}"
            )


def run_verifier(source_root: Path, python: str) -> dict[str, Any]:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(source_root)
    completed = subprocess.run(
        [
            python,
            str(
                source_root
                / "eval"
                / "verify_tgad_authenticated_hidden_stage_replay.py"
            ),
            "--json",
        ],
        cwd=source_root,
        env=environment,
        check=True,
        text=True,
        capture_output=True,
    )
    return json.loads(completed.stdout)


def require_expected(result: dict[str, Any], expected: dict[str, Any]) -> None:
    for key, value in expected.items():
        if result.get(key) != value:
            raise AssertionError(f"verification mismatch for {key}")


def check(source_root: Path, python: str, build: bool) -> dict[str, Any]:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    require_hashes(source_root, fixture["source_files"], "source file")
    require_hashes(THEOREM_ROOT, fixture["theorem_files"], "theorem file")
    require_hashes(THEOREM_ROOT, fixture["artifacts"], "replay artifact")
    result = run_verifier(source_root, python)
    require_expected(result, fixture["expected_verification"])
    if build:
        for target in LEAN_TARGETS:
            subprocess.run(
                ["lake", "build", target],
                cwd=THEOREM_ROOT,
                check=True,
            )
    return {
        "schema": fixture["schema"],
        "status": "PASS",
        "lean_build_requested": build,
        "trust_boundary": fixture["trust_boundary"],
        "non_claims": fixture["non_claims"],
        "verification": result,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, default=DEFAULT_SOURCE_ROOT)
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = check(args.source_root.resolve(), args.python, args.build)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("authenticated trained-checkpoint hidden-stage replay: PASS")


if __name__ == "__main__":
    main()
