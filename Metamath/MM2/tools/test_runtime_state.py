#!/usr/bin/env python3
"""Test fixed internal MM2 states, never the public passive-data interface.

These fixtures test specific verifier states. Reachability from a Metamath
source file is not established by this gate.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from assemble import Assembly, load_verifier, write_atomic
from mm2_atoms import Atom, Expr, Symbol, atom_digest, atoms_equal, head, parse_atoms, walk
from run import executable, performed_steps
from prepare import validate_output_paths


STATE_MANIFEST = Path(__file__).resolve().parents[1] / "tests" / "runtime-state" / "manifest.json"


def load_state(name: str, assembly: Assembly | None = None) -> tuple[str, dict]:
    assembly = assembly or load_verifier()
    manifest = json.loads(STATE_MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("schema") != "mm2-internal-state-fixtures-v1":
        raise ValueError("Unsupported internal-state fixture manifest")
    entry = next((case for case in manifest["cases"] if name in (case["name"], case["mode"])), None)
    if entry is None:
        raise ValueError("Unknown fixed internal-state fixture")
    path = STATE_MANIFEST.parent / entry["file"]
    text = path.read_text(encoding="utf-8")
    atoms = parse_atoms(text)
    if len(atoms) != entry["forms"] or atom_digest(atoms) != entry["parsed_sha256"]:
        raise ValueError(f"Internal-state fixture identity changed: {entry['name']}")
    dispatches = [node for atom in assembly.atoms for node in walk(atom)
                  if head(node) == "exec" and isinstance(node, Expr) and len(node.items) == 4
                  and isinstance(node.items[1], Expr)
                  and node.items[1].items == (Symbol("01"), Symbol("mm-source-event-dispatch"))]
    captured = [node for atom in atoms for node in walk(atom) if head(node) == "exec"]
    if not captured or any(not any(atoms_equal((node,), (reference,)) for reference in dispatches) for node in captured):
        raise ValueError("Fixture continuation is not the canonical source-event dispatcher")
    return text, entry


def check_state_result(atoms: list[Atom], entry: dict) -> None:
    counts = Counter(head(atom) for atom in atoms)
    for tag, expected in entry["counts"].items():
        if counts[tag] != expected:
            raise ValueError(f"{entry['name']}: expected {expected} {tag}, found {counts[tag]}")
    for tag in ("mm-source-current", "mm-source-object-lookup", "mm-source-object-found",
                "mm-source-object-missing", "mm-reload-source-object-lookup",
                "mm-source-floating-request", "mm-source-constant-commit", "mm-source-constant-abort",
                "mm-source-variable-commit", "mm-source-variable-abort", "mm-source-variable-stage-kind",
                "mm-internal-source-variable-typecode-found", "mm-internal-source-variable-typecode-missing",
                "mm-internal-source-active-floating-lookup", "mm-internal-source-active-floating-found",
                "mm-internal-source-active-floating-missing", "mm-reload-source-active-floating"):
        if counts[tag]:
            raise ValueError(f"{entry['name']}: unfinished {tag} transaction")
    if entry.get("reason"):
        rejections = [atom for atom in atoms if head(atom) == "mm-source-statement-rejected"]
        if len(rejections) != 1 or len(rejections[0].items) != 6 or rejections[0].items[4] != Symbol(entry["reason"]):
            raise ValueError(f"{entry['name']}: wrong rejection reason")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", required=True)
    parser.add_argument("--output", type=Path, required=True, help="Assembled test-only internal-state program")
    parser.add_argument("--assemble-only", action="store_true")
    parser.add_argument("--mork", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--steps", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=300.0)
    args = parser.parse_args(argv)
    try:
        assembly = load_verifier()
        state, entry = load_state(args.case, assembly)
        protected = [STATE_MANIFEST, STATE_MANIFEST.parent / entry["file"]]
        verifier_root = Path(__file__).resolve().parents[1] / "verifier"
        protected.extend(verifier_root / row["file"] for row in assembly.manifest["fragments"])
        outputs = [args.output] + ([args.result] if args.result else [])
        if args.mork is not None:
            protected.append(args.mork)
        validate_output_paths(outputs, protected)
        write_atomic(args.output, assembly.text + state)
        if args.assemble_only:
            return 0
        if args.mork is None or args.result is None:
            raise ValueError("Execution requires --mork and --result")
        if args.steps <= 0 or args.timeout <= 0:
            raise ValueError("Step limit and timeout must be positive")
        args.result.parent.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="internal-state-run-", dir=args.result.parent))
        result = work / "result.mm2"
        reply = subprocess.run([str(executable(args.mork)), "run", "--steps", str(args.steps), "--instrumentation", "0",
                                str(args.output), str(result)], capture_output=True, text=True, timeout=args.timeout)
        write_atomic(work / "mork.stdout", reply.stdout)
        write_atomic(work / "mork.stderr", reply.stderr)
        steps = performed_steps(reply.stdout)
        if reply.returncode or steps is None or steps >= args.steps:
            raise ValueError("Internal-state run failed or exhausted its budget")
        text = result.read_text(encoding="utf-8")
        check_state_result(parse_atoms(text), entry)
        write_atomic(args.result, text)
        print(json.dumps({"schema": "mm2-internal-state-receipt-v1", "case": entry["name"],
                          "steps": steps, "outcome": "passed", "reachability_claimed": False,
                          "artifacts": str(work)}))
        return 0
    except (OSError, ValueError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"Internal-state gate failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
