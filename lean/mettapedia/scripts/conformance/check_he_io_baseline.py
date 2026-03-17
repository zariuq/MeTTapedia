#!/usr/bin/env python3
"""
Freeze/check HE I/O Hyperon baseline bags for regression drift detection.

Baseline schema:
{
  "suite": "he_io",
  "engine": "hyperon",
  "version": "metta-0.2.10",
  "generated_utc": "...",
  "cases": [
    {"id": "...", "bag": {"term": count, ...}}
  ]
}
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def load_results(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for ln in path.read_text(encoding="utf-8").splitlines():
        s = ln.strip()
        if not s:
            continue
        obj = json.loads(s)
        if not isinstance(obj, dict):
            raise ValueError("result row must be JSON object")
        rows.append(obj)
    return rows


def row_hyperon_terms(row: dict[str, Any]) -> list[str]:
    raw = row.get("actual_hyperon", row.get("actual", []))
    if not isinstance(raw, list) or not all(isinstance(x, str) for x in raw):
        raise ValueError(f"invalid actual_hyperon/actual terms for row id={row.get('id')}")
    return raw


def build_case_bags(rows: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for row in rows:
        fid = row.get("id")
        if not isinstance(fid, str) or not fid:
            raise ValueError("result row missing string id")
        bag = dict(Counter(row_hyperon_terms(row)))
        out[fid] = bag
    return out


def write_baseline(path: Path, rows: list[dict[str, Any]], version: str) -> None:
    case_bags = build_case_bags(rows)
    payload = {
        "suite": "he_io",
        "engine": "hyperon",
        "version": version,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "cases": [
            {"id": fid, "bag": case_bags[fid]}
            for fid in sorted(case_bags.keys())
        ],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")


def load_baseline(path: Path) -> dict[str, dict[str, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("baseline must be JSON object")
    cases = payload.get("cases")
    if not isinstance(cases, list):
        raise ValueError("baseline.cases must be a list")
    out: dict[str, dict[str, int]] = {}
    for case in cases:
        if not isinstance(case, dict):
            raise ValueError("baseline case row must be object")
        fid = case.get("id")
        bag = case.get("bag")
        if not isinstance(fid, str) or not fid:
            raise ValueError("baseline case missing id")
        if not isinstance(bag, dict):
            raise ValueError(f"baseline case bag must be object for id={fid}")
        parsed_bag: dict[str, int] = {}
        for k, v in bag.items():
            if not isinstance(k, str) or not isinstance(v, int):
                raise ValueError(f"baseline bag entry must be string->int for id={fid}")
            parsed_bag[k] = v
        out[fid] = parsed_bag
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Check/freeze HE I/O Hyperon baseline.")
    parser.add_argument(
        "--results",
        default="artifacts/conformance/he_io_results_latest.jsonl",
        help="HE I/O JSONL results file",
    )
    parser.add_argument(
        "--baseline",
        default="scripts/conformance/he_io_baseline_hyperon_0.2.10.json",
        help="Baseline JSON file",
    )
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="Write/overwrite baseline using current results",
    )
    parser.add_argument(
        "--version",
        default="metta-0.2.10",
        help="Engine version tag written into baseline metadata",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    results_path = root / args.results
    baseline_path = root / args.baseline

    rows = load_results(results_path)
    if not rows:
        raise ValueError(f"results empty: {results_path}")

    if args.write_baseline:
        write_baseline(baseline_path, rows, args.version)
        print(f"baseline written: {baseline_path}")
        return 0

    if not baseline_path.exists():
        raise FileNotFoundError(
            f"baseline file missing: {baseline_path} (run with --write-baseline once)"
        )

    current = build_case_bags(rows)
    baseline = load_baseline(baseline_path)

    cur_ids = set(current.keys())
    base_ids = set(baseline.keys())
    if cur_ids != base_ids:
        missing = sorted(base_ids - cur_ids)
        extra = sorted(cur_ids - base_ids)
        print("baseline drift: case id set mismatch")
        print(f"missing_in_results={missing}")
        print(f"extra_in_results={extra}")
        return 2

    drift: list[str] = []
    for fid in sorted(cur_ids):
        if current[fid] != baseline[fid]:
            drift.append(fid)

    if drift:
        print(f"baseline drift: {len(drift)} case(s) changed")
        for fid in drift:
            print(f"[drift] {fid}")
            print(f"  baseline={baseline[fid]}")
            print(f"  current={current[fid]}")
        return 3

    print(
        f"baseline check: PASS cases={len(cur_ids)} "
        f"baseline={baseline_path}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

