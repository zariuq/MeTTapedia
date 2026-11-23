#!/usr/bin/env python3
"""Offline comparison of native B with the Lean passive-data reference.

This is a development gate, not a dependency of translation or execution.
MORK initial spaces are sets, so data-row order is not an execution order.
Each row is compared structurally; occurrence indices preserve ordered data.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from assemble import DEFAULT_MANIFEST, load_verifier
from mm2_atoms import atoms_equal, head, parse_atoms, render


def rows(path: Path, *, verifier_prefix: tuple | None = None) -> dict[str, str | None]:
    atoms = parse_atoms(path.read_text())
    if verifier_prefix is not None:
        if not atoms_equal(verifier_prefix, atoms[:len(verifier_prefix)]):
            raise ValueError("Reference program does not start with the pinned verifier")
        atoms = atoms[len(verifier_prefix):]
    return {render(atom): head(atom) for atom in atoms}


def compare(native: Path, reference: Path, *, verifier_prefix: tuple | None = None) -> dict[str, object]:
    actual, expected = rows(native), rows(reference, verifier_prefix=verifier_prefix)
    added = actual.keys() - expected.keys()
    missing = expected.keys() - actual.keys()
    return {
        "equal": not added and not missing,
        "native_rows": len(actual),
        "reference_rows": len(expected),
        "unexpected": [{"tag": actual[row], "row": row[:240]} for row in sorted(added)[:8]],
        "missing": [{"tag": expected[row], "row": row[:240]} for row in sorted(missing)[:8]],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--translator", type=Path, required=True)
    parser.add_argument("--source", type=Path, action="append", required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    reference = parser.add_mutually_exclusive_group(required=True)
    reference.add_argument("--reference", type=Path)
    reference.add_argument("--reference-program", type=Path,
                           help="Prior combined program; require exact A prefix and compare its B suffix")
    reference.add_argument("--lean-root", type=Path)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args()
    if (args.reference or args.reference_program) and len(args.source) != 1:
        parser.error("A saved reference takes exactly one --source")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    args.work_dir.mkdir(parents=True, exist_ok=True)
    translator = args.translator.resolve()
    verifier_prefix = load_verifier(args.manifest).atoms if args.reference_program else None
    failed = False
    for index, source in enumerate(args.source):
        source = source.resolve()
        native_path = args.work_dir.resolve() / f"{index:03}-{source.stem}.native.mm2"
        result = subprocess.run([str(translator), str(source), "--output", str(native_path)],
                                capture_output=True, text=True, timeout=args.timeout)
        native_status = result.returncode
        if args.reference or args.reference_program:
            reference_path = (args.reference or args.reference_program).resolve()
            reference_status = 0
        else:
            reference_path = args.work_dir.resolve() / f"{index:03}-{source.stem}.reference.mm2"
            env = {key: value for key, value in os.environ.items()
                   if not key.startswith("METTAPEDIA_MM2_")}
            env.update(METTAPEDIA_MM2_RAW_SOURCE=str(source),
                       METTAPEDIA_MM2_SOURCE_DATA_OUTPUT=str(reference_path),
                       METTAPEDIA_MM2_VERIFIER_OUTPUT=str(args.work_dir.resolve() / "reference-verifier.mm2"))
            lean = subprocess.run(
                ["nice", "-n", "19", args.lake, "env", "lean", "-M", "24576", "--stdin"],
                input="import Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit\n"
                      "#eval exportMetamathMM2RawUnitFromEnvironment\n",
                cwd=args.lean_root.resolve(), env=env, capture_output=True, text=True,
                timeout=args.timeout)
            last = lean.stdout.rstrip().splitlines()
            if lean.returncode or not last or last[-1] not in {"0", "1"}:
                print(lean.stdout + lean.stderr, file=sys.stderr)
                raise RuntimeError("Lean reference export did not finish normally")
            reference_status = int(last[-1])
        report: dict[str, object] = {
            "source": str(source), "native_status": native_status,
            "reference_status": reference_status,
        }
        if native_status != reference_status:
            report.update(equal=False, diagnostic=result.stderr.strip())
        elif native_status == 0:
            report.update(compare(native_path, reference_path, verifier_prefix=verifier_prefix))
        else:
            report["equal"] = native_status == 1
        failed |= not bool(report["equal"])
        print(json.dumps(report, sort_keys=True), flush=True)
    return int(failed)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"offline source agreement failed: {error}", file=sys.stderr)
        raise SystemExit(2)
