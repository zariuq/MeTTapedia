#!/usr/bin/env python3
"""
Report ISO test-id coverage against upstream Logtalk conformance files.

Source attribution:
- Logtalk Prolog conformance tests:
  https://github.com/LogtalkDotOrg/logtalk3/tree/master/tests/prolog
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ISO_RE = re.compile(r"\b(iso_[a-z0-9_]+)\b")
THEOREM_RE = re.compile(r"^\s*theorem\s+([A-Za-z0-9_']+)\b")
LEAN_CASE_RE = re.compile(r"fixture_case\(lean_aligned,\s*([A-Za-z0-9_]+)\s*,")

DEFAULT_REL_FILES = [
    "control/true_0/tests.lgt",
    "control/fail_0/tests.lgt",
    "control/conjunction_2/tests.lgt",
    "control/disjunction_2/tests.lgt",
    "predicates/once_1/tests.lgt",
    "predicates/not_1/tests.lgt",
    "predicates/unify_2/tests.lgt",
    "predicates/not_unifiable_2/tests.lgt",
    "predicates/findall_3/tests.lgt",
]


def parse_ids_from_text(text: str) -> set[str]:
    return set(ISO_RE.findall(text))


def parse_upstream_ids(logtalk_root: Path, rel_files: list[str]) -> set[str]:
    out: set[str] = set()
    for rel in rel_files:
        path = logtalk_root / rel
        if not path.exists():
            raise FileNotFoundError(f"Missing upstream file: {path}")
        out |= parse_ids_from_text(path.read_text(encoding="utf-8"))
    return out


def parse_theorem_ids(lean_file: Path) -> set[str]:
    out: set[str] = set()
    for line in lean_file.read_text(encoding="utf-8").splitlines():
        m = THEOREM_RE.match(line)
        if m:
            out.add(m.group(1))
    return {t for t in out if t.startswith("iso_")}


def parse_lean_case_ids(cases_file: Path) -> set[str]:
    out: set[str] = set()
    for line in cases_file.read_text(encoding="utf-8").splitlines():
        m = LEAN_CASE_RE.search(line)
        if m:
            cid = m.group(1)
            if cid.startswith("iso_"):
                out.add(cid)
    return out


def normalize_like(ids: set[str]) -> set[str]:
    out: set[str] = set()
    for cid in ids:
        out.add(cid[:-5] if cid.endswith("_like") else cid)
    return out


def fmt_list(name: str, items: list[str], limit: int) -> str:
    if not items:
        return f"{name}: none"
    shown = items[:limit]
    suffix = "" if len(items) <= limit else f" ... (+{len(items) - limit} more)"
    return f"{name} ({len(items)}): " + ", ".join(shown) + suffix


def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    default_logtalk_root = repo_root.parents[1] / "_ext/prolog-tests/logtalk3/tests/prolog"

    parser = argparse.ArgumentParser(description="Report Logtalk ISO coverage for Lean/SWI fixtures")
    parser.add_argument(
        "--logtalk-root",
        default=str(default_logtalk_root),
        help="Path to logtalk3/tests/prolog directory",
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
        "--list-limit",
        type=int,
        default=40,
        help="Maximum number of missing IDs to print",
    )
    parser.add_argument(
        "--require-lean-theorem-exact",
        type=int,
        default=None,
        help="Fail if exact Lean theorem ISO coverage is below this value",
    )
    parser.add_argument(
        "--require-lean-case-exact",
        type=int,
        default=None,
        help="Fail if exact lean_aligned ISO case coverage is below this value",
    )
    parser.add_argument(
        "--require-lean-theorem-normalized",
        type=int,
        default=None,
        help="Fail if normalized Lean theorem ISO coverage is below this value",
    )
    parser.add_argument(
        "--require-lean-case-normalized",
        type=int,
        default=None,
        help="Fail if normalized lean_aligned ISO case coverage is below this value",
    )
    args = parser.parse_args()

    logtalk_root = Path(args.logtalk_root)
    lean_file = Path(args.lean_file)
    cases_file = Path(args.cases_file)

    try:
        upstream_ids = parse_upstream_ids(logtalk_root, DEFAULT_REL_FILES)
    except FileNotFoundError as exc:
        print(f"ERROR: {exc}")
        return 2

    theorem_ids = parse_theorem_ids(lean_file)
    case_ids = parse_lean_case_ids(cases_file)

    theorem_ids_norm = normalize_like(theorem_ids)
    case_ids_norm = normalize_like(case_ids)

    exact_theorem_cov = sorted(upstream_ids & theorem_ids)
    exact_case_cov = sorted(upstream_ids & case_ids)
    norm_theorem_cov = sorted(upstream_ids & theorem_ids_norm)
    norm_case_cov = sorted(upstream_ids & case_ids_norm)

    missing_exact_theorems = sorted(upstream_ids - theorem_ids)
    missing_exact_cases = sorted(upstream_ids - case_ids)
    missing_norm_theorems = sorted(upstream_ids - theorem_ids_norm)
    missing_norm_cases = sorted(upstream_ids - case_ids_norm)

    n = len(upstream_ids)

    def pct(k: int) -> str:
        return f"{(100.0 * k / n):.1f}%" if n else "n/a"

    print("Logtalk ISO coverage report")
    print(f"  Upstream file set: {len(DEFAULT_REL_FILES)} files")
    print(f"  Upstream ISO IDs: {n}")
    print(f"  Lean theorem ISO IDs (exact): {len(exact_theorem_cov)}/{n} ({pct(len(exact_theorem_cov))})")
    print(f"  lean_aligned case ISO IDs (exact): {len(exact_case_cov)}/{n} ({pct(len(exact_case_cov))})")
    print(f"  Lean theorem ISO IDs (normalized _like): {len(norm_theorem_cov)}/{n} ({pct(len(norm_theorem_cov))})")
    print(f"  lean_aligned case ISO IDs (normalized _like): {len(norm_case_cov)}/{n} ({pct(len(norm_case_cov))})")

    print(fmt_list("  Missing upstream IDs in Lean theorems (exact)", missing_exact_theorems, args.list_limit))
    print(fmt_list("  Missing upstream IDs in lean_aligned cases (exact)", missing_exact_cases, args.list_limit))
    print(fmt_list("  Missing upstream IDs in Lean theorems (normalized)", missing_norm_theorems, args.list_limit))
    print(fmt_list("  Missing upstream IDs in lean_aligned cases (normalized)", missing_norm_cases, args.list_limit))

    checks: list[tuple[str, int | None, int]] = [
        ("exact Lean theorem ISO coverage", args.require_lean_theorem_exact, len(exact_theorem_cov)),
        ("exact lean_aligned ISO case coverage", args.require_lean_case_exact, len(exact_case_cov)),
        ("normalized Lean theorem ISO coverage", args.require_lean_theorem_normalized, len(norm_theorem_cov)),
        ("normalized lean_aligned ISO case coverage", args.require_lean_case_normalized, len(norm_case_cov)),
    ]

    failures: list[str] = []
    for label, required, actual in checks:
        if required is not None and actual < required:
            failures.append(f"{label}: required >= {required}, got {actual}")

    if failures:
        print("Coverage thresholds: FAIL")
        for row in failures:
            print(f"  - {row}")
        return 1

    if any(req is not None for _, req, _ in checks):
        print("Coverage thresholds: PASS")

    return 0


if __name__ == "__main__":
    sys.exit(main())
