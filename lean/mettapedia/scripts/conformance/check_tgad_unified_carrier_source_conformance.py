#!/usr/bin/env python3
"""Recompute the unified-carrier source-conformance artifact."""

from __future__ import annotations

import argparse
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
ARTIFACT = (
    THEOREM_ROOT
    / "artifacts"
    / "conformance"
    / "tgad_unified_carrier_source_conformance_v1.json"
)


def run_verifier(source_root: Path, python: str) -> dict[str, Any]:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(source_root)
    completed = subprocess.run(
        [
            python,
            str(source_root / "eval" / "verify_tgad_unified_carrier_source.py"),
        ],
        cwd=source_root,
        env=environment,
        check=True,
        text=True,
        capture_output=True,
    )
    return json.loads(completed.stdout)


def check(source_root: Path, python: str) -> dict[str, Any]:
    expected = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    generated_on = expected.pop("generated_on")
    observed = run_verifier(source_root, python)
    if observed != expected:
        raise AssertionError("unified-carrier source-conformance artifact is stale")
    return {
        "schema": expected["schema"],
        "status": "PASS",
        "generated_on": generated_on,
        "checks": len(expected["checks"]),
        "sources": len(expected["sources"]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, default=DEFAULT_SOURCE_ROOT)
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = check(args.source_root.resolve(), args.python)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("unified-carrier source conformance: PASS")


if __name__ == "__main__":
    main()
