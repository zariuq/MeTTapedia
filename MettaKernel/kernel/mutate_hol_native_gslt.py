#!/usr/bin/env python3
"""Mutate one native HOL proof constructor use for gate-sensitivity testing."""

from pathlib import Path
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: mutate_hol_native_gslt.py INPUT OUTPUT", file=sys.stderr)
        return 2

    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    lines = source.read_text(encoding="utf-8").splitlines(keepends=True)
    target_indices = [
        index for index, line in enumerate(lines)
        if line.startswith("(= (hl-native-proof)")
    ]
    if len(target_indices) != 1:
        print("expected exactly one HOL Light positive-proof definition", file=sys.stderr)
        return 1

    index = target_indices[0]
    old = 'GRuleInst "HL_EQ_MP"'
    new = 'GRuleInst "HL_ASSUME"'
    if lines[index].count(old) != 1:
        print("expected exactly one root HOL Light rule identifier", file=sys.stderr)
        return 1
    lines[index] = lines[index].replace(old, new, 1)
    output.write_text("".join(lines), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
