#!/usr/bin/env python3
"""
Validate that HE I/O fixtures are anchored to Lean theorems where required.

Policy:
- Fixtures with tier `core_anchor` must specify `lean_theorem`.
- Each required theorem must exist in the configured Lean file.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


THEOREM_RE = re.compile(r"^\s*theorem\s+([A-Za-z0-9_']+)\b")


def parse_theorems(path: Path) -> set[str]:
    names: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = THEOREM_RE.match(line)
        if m:
            names.add(m.group(1))
    return names


def main() -> int:
    parser = argparse.ArgumentParser(description="Check HE fixture -> Lean theorem anchors.")
    parser.add_argument(
        "--fixtures",
        default="scripts/conformance/he_io_fixtures.json",
        help="Fixture JSON path",
    )
    parser.add_argument(
        "--lean-file",
        default="Mettapedia/Conformance/SimpleHE.lean",
        help="Lean file containing theorem anchors",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    fixtures_path = root / args.fixtures
    lean_path = root / args.lean_file

    fixtures = json.loads(fixtures_path.read_text(encoding="utf-8"))
    if not isinstance(fixtures, list):
        raise ValueError("fixtures must be a list")

    theorem_names = parse_theorems(lean_path)

    missing_anchor_field: list[str] = []
    missing_theorem: list[tuple[str, str]] = []
    duplicate_ids: set[str] = set()
    seen_ids: set[str] = set()

    for row in fixtures:
        if not isinstance(row, dict):
            continue
        fid = str(row.get("id", "")).strip()
        if fid == "":
            continue
        if fid in seen_ids:
            duplicate_ids.add(fid)
        seen_ids.add(fid)
        tier = str(row.get("tier", "")).strip()
        theorem = str(row.get("lean_theorem", "")).strip()
        if tier == "core_anchor":
            if theorem == "":
                missing_anchor_field.append(fid)
            elif theorem not in theorem_names:
                missing_theorem.append((fid, theorem))

    print("HE I/O Lean anchor report")
    print(f"  fixture_count: {len(fixtures)}")
    print(f"  core_anchor_count: {sum(1 for r in fixtures if isinstance(r, dict) and r.get('tier') == 'core_anchor')}")
    print(f"  theorem_count_in_lean_file: {len(theorem_names)}")
    print(f"  duplicate_fixture_ids: {sorted(duplicate_ids)}")
    print(f"  missing_anchor_field: {missing_anchor_field}")
    print(f"  missing_theorem_targets: {missing_theorem}")

    ok = not duplicate_ids and not missing_anchor_field and not missing_theorem
    print(f"anchor_check: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
