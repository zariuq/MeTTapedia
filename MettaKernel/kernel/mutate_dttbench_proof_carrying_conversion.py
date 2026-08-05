#!/usr/bin/env python3
"""Mutate exactly one rule in the first generated DTT conversion proof."""

from __future__ import annotations

import argparse
from pathlib import Path


MARKER = "(= (dtt-pc-witness-0)"
ORIGINAL = '"lf-fo-conversion-refl"'
MUTATED = '"lf-fo-unknown-rule"'


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    arguments = parser.parse_args()

    text = arguments.source.read_text()
    marker_index = text.find(MARKER)
    if marker_index < 0:
        raise ValueError("first generated DTT witness marker is absent")
    proof_index = text.find(ORIGINAL, marker_index)
    if proof_index < 0:
        raise ValueError("first generated reflexive conversion rule is absent")
    mutated = text[:proof_index] + MUTATED + text[proof_index + len(ORIGINAL) :]
    if mutated.count(MUTATED) != text.count(MUTATED) + 1:
        raise ValueError("mutation cardinality is not exactly one")
    arguments.output.write_text(mutated)


if __name__ == "__main__":
    main()
