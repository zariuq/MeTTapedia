#!/usr/bin/env python3
"""
Check that required ISO runtime-error probe cases are present and passing.

These probes correspond to Lean-side boundary declarations in
`Mettapedia/Logic/Prolog/RuntimeErrorSpec.lean`.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REQUIRED_IDS = [
    "iso_not_1_06_type_error_callable",
    "iso_not_1_07_instantiation_error",
    "iso_findall_3_07_instantiation_error",
    "iso_findall_3_08_type_error_callable",
]


def parse_results(path: Path) -> dict[str, dict]:
    out: dict[str, dict] = {}
    with path.open("r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{lineno}: invalid JSON: {exc}") from exc
            if row.get("suite") != "iso_probe":
                continue
            row_id = row.get("id")
            if isinstance(row_id, str):
                out[row_id] = row
    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check ISO runtime-error probe cases in SWI JSONL results."
    )
    parser.add_argument(
        "--results-file",
        default="artifacts/prolog/swi_fixture_results_latest.jsonl",
        help="Path to SWI JSONL results file",
    )
    args = parser.parse_args()

    results = parse_results(Path(args.results_file))

    missing = [cid for cid in REQUIRED_IDS if cid not in results]
    failing = [
        cid for cid in REQUIRED_IDS
        if cid in results and results[cid].get("status") != "pass"
    ]

    print("ISO probe runtime-error report")
    print(f"  required cases: {len(REQUIRED_IDS)}")
    print(f"  present: {len(REQUIRED_IDS) - len(missing)}")
    print("  missing: " + (", ".join(missing) if missing else "none"))
    print("  non-pass: " + (", ".join(failing) if failing else "none"))

    if missing or failing:
        print("Runtime-error probe check: FAIL")
        return 1

    print("Runtime-error probe check: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())

