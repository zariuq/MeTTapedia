#!/usr/bin/env python3
"""Create one fail-closed rule mutation in a pure DTT process bundle."""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path


ORIGINAL = '"lf-fo-conversion-refl"'
MUTATED = '"lf-fo-unknown-rule"'


def bundle_files(directory: Path) -> list[Path]:
    fixed = [
        directory / "manifest.tsv",
        directory / "common.metta",
        directory / "final.template.metta",
    ]
    chunks = sorted(directory.glob("term_chunk_*.template.metta"))
    chunks.extend(sorted(directory.glob("type_chunk_*.template.metta")))
    paths = [*fixed, *chunks]
    missing = [path.name for path in paths if not path.is_file()]
    if missing:
        raise FileNotFoundError(
            "bundle files are missing: " + ", ".join(missing)
        )
    return paths


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_directory", type=Path)
    parser.add_argument("output_directory", type=Path)
    arguments = parser.parse_args()

    source = arguments.source_directory.resolve()
    output = arguments.output_directory.resolve()
    if source == output:
        raise ValueError("source and output bundle directories must differ")

    paths = bundle_files(source)
    output.mkdir(parents=True, exist_ok=True)
    for path in paths:
        shutil.copy2(path, output / path.name)

    candidates = [
        path
        for path in paths
        if path.name.endswith(".template.metta")
        and ORIGINAL in path.read_text(encoding="utf-8")
    ]
    if not candidates:
        raise ValueError("no reflexive conversion rule is present")
    selected = candidates[0]
    target = output / selected.name
    text = target.read_text(encoding="utf-8")
    offset = text.find(ORIGINAL)
    mutated = text[:offset] + MUTATED + text[offset + len(ORIGINAL) :]
    if mutated.count(MUTATED) != text.count(MUTATED) + 1:
        raise ValueError("mutation cardinality is not exactly one")
    target.write_text(mutated, encoding="utf-8")


if __name__ == "__main__":
    main()
