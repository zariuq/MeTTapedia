#!/usr/bin/env python3
"""Prepare A + native B without executing the verifier."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from assemble import load_verifier, write_atomic
from mm2_atoms import atom_digest, parse_atoms
from protocol import validate_passive_data
from run import executable, translator_identity


def validate_output_paths(outputs: list[Path], protected: list[Path],
                          source_identities: set[tuple[int, int]] | None = None) -> None:
    """Check aliases before publication, including hard links and symlinks."""
    destinations: list[Path] = []
    for output in outputs:
        resolved = output.resolve()
        if resolved in destinations or any(
                prior.exists() and output.exists() and os.path.samefile(prior, output)
                for prior in outputs[:len(destinations)]):
            raise ValueError("Output paths must be distinct")
        if any(resolved == item.resolve() or
               (item.exists() and output.exists() and os.path.samefile(item, output))
               for item in protected):
            raise ValueError("Output path aliases a source or runtime input")
        if output.exists() and source_identities is not None:
            status = output.stat()
            if (status.st_dev, status.st_ino) in source_identities:
                raise ValueError("Output path aliases an expanded source file")
        destinations.append(resolved)


def read_source_identities(translator: Path, source: Path, root_name: str,
                           timeout: float) -> set[tuple[int, int]]:
    reply = subprocess.run([str(translator), str(source.resolve()), "--source-identities",
                            "--profile", "zar", "--root-name", root_name],
                           capture_output=True, text=True, timeout=timeout)
    if reply.returncode:
        raise ValueError("Cannot validate expanded source identities: " + reply.stderr.strip())
    value = json.loads(reply.stdout)
    if not isinstance(value, dict) or value.get("schema") != "mm2-source-identities-v1":
        raise ValueError("Unsupported source identity receipt")
    files = value.get("files")
    if not isinstance(files, list) or not files:
        raise ValueError("Missing expanded source identities")
    identities = set()
    for item in files:
        if (not isinstance(item, dict) or type(item.get("device")) is not int or
                type(item.get("inode")) is not int or item["device"] < 0 or item["inode"] < 0):
            raise ValueError("Malformed source identity receipt")
        identities.add((item["device"], item["inode"]))
    source_status = source.stat()
    if (source_status.st_dev, source_status.st_ino) not in identities:
        raise ValueError("Source identity receipt omits the root source")
    return identities


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--translator", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verifier-output", type=Path)
    parser.add_argument("--data-output", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--owner", default="metamath-test-unit")
    parser.add_argument("--root-name", default="unit.mm")
    parser.add_argument("--timeout", type=float, default=300.0)
    args = parser.parse_args(argv)
    directory: Path | None = None
    try:
        if not any((args.output, args.verifier_output, args.data_output)):
            raise ValueError("At least one output is required")
        if args.timeout <= 0:
            raise ValueError("Timeout must be positive")
        assembly = load_verifier() if args.manifest is None else load_verifier(args.manifest)
        translator = executable(args.translator)
        outputs = [path for path in (args.output, args.verifier_output, args.data_output) if path]
        manifest = args.manifest or Path(__file__).resolve().parents[1] / "verifier" / "manifest.json"
        protected = [args.input, translator, manifest]
        protected.extend(manifest.parent / row["file"] for row in assembly.manifest["fragments"])
        validate_output_paths(outputs, protected)
        identity = translator_identity(translator, args.timeout)
        destination = args.output or args.data_output or args.verifier_output
        destination.parent.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="native-prepare-", dir=destination.parent))
        data_path = directory / "source-data.mm2"
        reply = subprocess.run([str(translator), str(args.input.resolve()), "--output", str(data_path),
                                "--profile", "zar", "--owner", args.owner, "--root-name", args.root_name],
                               capture_output=True, text=True, timeout=args.timeout)
        write_atomic(directory / "translator.stdout", reply.stdout)
        write_atomic(directory / "translator.stderr", reply.stderr)
        if reply.returncode:
            if reply.returncode == 1 and not data_path.exists():
                print(reply.stderr.strip(), file=sys.stderr)
                print(f"Preparation staging retained: {directory}", file=sys.stderr)
                return 1
            raise ValueError("Native translator failed or left output on rejection: " + reply.stderr.strip())
        data = data_path.read_text(encoding="utf-8")
        data_atoms = parse_atoms(data)
        source = validate_passive_data(data_atoms, owner=args.owner)
        identities = read_source_identities(translator, args.input, args.root_name, args.timeout)
        validate_output_paths(outputs, protected, identities)
        if args.output:
            write_atomic(args.output, assembly.text + data.rstrip("\n") + "\n")
        if args.verifier_output:
            write_atomic(args.verifier_output, assembly.text)
        if args.data_output:
            write_atomic(args.data_output, data)
        print(json.dumps({"schema": "mm2-prepare-receipt-v1", "translator": identity,
                          "verifier_parsed_sha256": assembly.manifest["parsed_sha256"],
                          "data_parsed_sha256": atom_digest(data_atoms), "statements": source.end,
                          "source_files": len(identities), "staging": str(directory)}))
        return 0
    except (OSError, ValueError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"Native preparation failed: {error}", file=sys.stderr)
        if directory is not None:
            print(f"Preparation staging retained: {directory}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
