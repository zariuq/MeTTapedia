#!/usr/bin/env python3
"""Execute a prequalified A + B fixture with the ordinary source runner."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile

from assemble import load_verifier, write_atomic
from mm2_atoms import atoms_equal, parse_forms
from run import run_case


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program", type=Path, required=True)
    parser.add_argument("--result", type=Path, required=True)
    parser.add_argument("--mork", type=Path, required=True)
    parser.add_argument("--steps", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--owner", default="metamath-test-unit")
    parser.add_argument("--expect", choices=("accepted", "rejected", "incomplete-proof"))
    args = parser.parse_args(argv)
    try:
        assembly = load_verifier()
        text = args.program.read_text(encoding="utf-8")
        forms = parse_forms(text)
        count = len(assembly.atoms)
        if len(forms) <= count or not atoms_equal((form.atom for form in forms[:count]), assembly.atoms):
            raise ValueError("Prepared program does not begin with the exact current verifier")
        args.result.parent.mkdir(parents=True, exist_ok=True)
        # A persistent per-fixture work directory retains native diagnostics.
        work = args.result.parent / (args.result.stem + ".run")
        work.mkdir(parents=True, exist_ok=True)
        data_path = work / "prepared-source-data.mm2"
        write_atomic(data_path, text[forms[count].start:])
        receipt = run_case(data_path=data_path, mork=args.mork, work_dir=work,
                           steps=args.steps, timeout=args.timeout, owner=args.owner)
        print(json.dumps(receipt, sort_keys=True))
        if receipt["outcome"] == "execution-failure":
            return 2
        if args.expect and receipt["outcome"] != args.expect:
            print(f"Expected {args.expect}, observed {receipt['outcome']}", file=sys.stderr)
            return 1
        write_atomic(args.result, Path(receipt["artifacts"]["result.mm2"]).read_text(encoding="utf-8"))
        return 0
    except (OSError, ValueError, TypeError) as error:
        print(f"Prepared fixture execution failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
