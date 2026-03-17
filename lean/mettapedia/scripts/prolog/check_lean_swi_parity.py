#!/usr/bin/env python3
"""
Check parity between Lean fixture theorem IDs and SWI fixture run results.

This script enforces three invariants for `lean_aligned` fixtures:
1. Every SWI `lean_aligned` case ID has a matching Lean theorem name.
2. Every SWI `lean_aligned` case ID appears in the JSONL run results.
3. Every SWI `lean_aligned` case ID has status `pass`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path


THEOREM_RE = re.compile(r"^\s*theorem\s+([A-Za-z0-9_']+)\b")
CASE_RE = re.compile(r"fixture_case\(lean_aligned,\s*([A-Za-z0-9_]+)\s*,")


def parse_theorems(path: Path) -> set[str]:
    names: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = THEOREM_RE.match(line)
        if m:
            names.add(m.group(1))
    return names


def parse_lean_aligned_case_ids(path: Path) -> list[str]:
    ids: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = CASE_RE.search(line)
        if m:
            ids.append(m.group(1))
    return ids


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
            if row.get("suite") != "lean_aligned":
                continue
            row_id = row.get("id")
            if isinstance(row_id, str):
                out[row_id] = row
    return out


def format_ids(title: str, ids: list[str]) -> str:
    if not ids:
        return f"{title}: none"
    return f"{title} ({len(ids)}): " + ", ".join(ids)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Lean theorem IDs against SWI lean_aligned fixture results."
    )
    parser.add_argument(
        "--lean-file",
        default="Mettapedia/Logic/Prolog/FixtureCorpus.lean",
        help="Path to Lean fixture corpus file",
    )
    parser.add_argument(
        "--cases-file",
        default="scripts/prolog/swi_fixture_cases.pl",
        help="Path to SWI fixture cases file",
    )
    parser.add_argument(
        "--results-file",
        default="artifacts/prolog/swi_fixture_results_latest.jsonl",
        help="Path to SWI JSONL results file",
    )
    args = parser.parse_args()

    lean_file = Path(args.lean_file)
    cases_file = Path(args.cases_file)
    results_file = Path(args.results_file)

    theorem_names = parse_theorems(lean_file)
    case_ids = parse_lean_aligned_case_ids(cases_file)
    results = parse_results(results_file)

    id_counts = Counter(case_ids)
    duplicate_case_ids = sorted([cid for cid, n in id_counts.items() if n > 1])

    missing_theorems = sorted([cid for cid in case_ids if cid not in theorem_names])
    missing_results = sorted([cid for cid in case_ids if cid not in results])
    failing = sorted(
        [
            cid
            for cid in case_ids
            if cid in results and results[cid].get("status") != "pass"
        ]
    )
    extra_results = sorted([rid for rid in results if rid not in set(case_ids)])

    print("Lean/SWI parity report (suite=lean_aligned)")
    print(f"  Lean theorem count: {len(theorem_names)}")
    print(f"  lean_aligned case count: {len(case_ids)}")
    print(f"  lean_aligned result count: {len(results)}")
    print(format_ids("  Duplicate case IDs", duplicate_case_ids))
    print(format_ids("  Missing Lean theorem for case ID", missing_theorems))
    print(format_ids("  Missing SWI result for case ID", missing_results))
    print(format_ids("  Non-pass SWI status", failing))
    print(format_ids("  Extra SWI result IDs not in cases", extra_results))

    ok = not (
        duplicate_case_ids
        or missing_theorems
        or missing_results
        or failing
        or extra_results
    )
    if ok:
        print("Parity check: PASS")
        return 0

    print("Parity check: FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
