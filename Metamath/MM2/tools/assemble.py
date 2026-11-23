#!/usr/bin/env python3
"""Assemble the direct MM2 verifier in its manifest's fixed form order."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import os
import sys
import tempfile

from mm2_atoms import Atom, Expr, atom_digest, atoms_equal, head, parse_atoms, read_atoms


DEFAULT_MANIFEST = Path(__file__).resolve().parents[1] / "verifier" / "manifest.json"


@dataclass(frozen=True)
class Assembly:
    text: str
    atoms: tuple[Atom, ...]
    manifest: dict


def _check_atoms(atoms: list[Atom] | tuple[Atom, ...], expected: dict, label: str) -> None:
    if any(not isinstance(atom, Expr) for atom in atoms):
        raise ValueError(f"{label}: verifier forms must be expressions")
    actual = {
        "forms": len(atoms),
        "top_level_exec": sum(head(atom) == "exec" for atom in atoms),
        "parsed_sha256": atom_digest(atoms),
    }
    for key, value in actual.items():
        if expected.get(key) != value:
            raise ValueError(f"{label}: {key} mismatch (expected {expected.get(key)!r}, found {value!r})")


def load_verifier(manifest_path: str | Path = DEFAULT_MANIFEST) -> Assembly:
    path = Path(manifest_path)
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if manifest.get("schema") != "mm2-verifier-manifest-v1":
        raise ValueError("Unsupported verifier manifest schema")
    if manifest.get("source_data_schema") != "mm2-source-data-v1" or manifest.get("profile") != "zar":
        raise ValueError("This verifier requires mm2-source-data-v1, profile zar")
    fragments = manifest.get("fragments")
    if not isinstance(fragments, list) or not fragments:
        raise ValueError("Verifier manifest requires an ordered fragment list")
    texts: list[str] = []
    atoms: list[Atom] = []
    seen: set[str] = set()
    for fragment in fragments:
        name = fragment.get("file")
        if not isinstance(name, str) or Path(name).name != name or name in seen:
            raise ValueError("Fragment names must be distinct filenames within the manifest directory")
        seen.add(name)
        text = (path.parent / name).read_text(encoding="utf-8")
        current = parse_atoms(text)
        _check_atoms(current, fragment, name)
        texts.append(text.rstrip("\n") + "\n")
        atoms.extend(current)
    _check_atoms(atoms, manifest, "assembled verifier")
    text = "".join(texts)
    if not atoms_equal(atoms, parse_atoms(text)):
        raise ValueError("Fragment concatenation changed a token boundary")
    return Assembly(text, tuple(atoms), manifest)


def compare_verifier(assembly: Assembly, path: str | Path, *, prefix: bool = False) -> dict:
    candidates = read_atoms(path)
    compared = candidates[:len(assembly.atoms)] if prefix else candidates
    if not atoms_equal(assembly.atoms, compared):
        raise ValueError(f"Parsed verifier identity failed for {path}")
    return {
        "path": str(path),
        "comparison": "verifier-prefix" if prefix else "whole-verifier",
        "candidate_forms": len(candidates),
        "compared_forms": len(compared),
        "parsed_sha256": atom_digest(compared),
        "equal": True,
    }


def write_atomic(path: str | Path, text: str) -> None:
    """Publish a generated output only once its complete contents are ready."""
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=destination.parent, prefix=".mm2-output-", delete=False) as output:
        output.write(text)
        temporary = output.name
    os.replace(temporary, destination)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true", help="Check assembly without printing the verifier")
    parser.add_argument("--compare", type=Path, action="append", default=[], help="Require whole parsed identity with a prior verifier")
    parser.add_argument("--compare-prefix", type=Path, action="append", default=[], help="Require identity with a prior program's verifier prefix")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args(argv)
    try:
        assembly = load_verifier(args.manifest)
        comparisons = [compare_verifier(assembly, path) for path in args.compare]
        comparisons.extend(compare_verifier(assembly, path, prefix=True) for path in args.compare_prefix)
        receipt = {
            "schema": "mm2-assembly-receipt-v1",
            "profile": assembly.manifest["profile"],
            "forms": len(assembly.atoms),
            "top_level_exec": assembly.manifest["top_level_exec"],
            "parsed_sha256": atom_digest(assembly.atoms),
            "comparisons": comparisons,
        }
        if args.output:
            write_atomic(args.output, assembly.text)
        elif not args.check:
            sys.stdout.write(assembly.text)
        encoded = json.dumps(receipt, indent=2) + "\n"
        if args.receipt:
            write_atomic(args.receipt, encoded)
        sys.stderr.write(encoded)
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f"Assembly failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
