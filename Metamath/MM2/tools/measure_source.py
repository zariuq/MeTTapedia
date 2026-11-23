#!/usr/bin/env python3
"""Advisory source-payload and current-encoding bounds, without proof execution.

This lexical measurement assumes structurally valid Zar-profile Metamath. It
does not duplicate the native declaration model, check proofs, or expand
includes. For a single file, mandatory hypothesis counts lie between zero
and the active hypothesis count; those bounds size the current four successor
families. Includes invalidate the expanded-source upper bound, not the lower
bound contributed by the measured file. Neither bound measures MORK memory.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import re


def tokens(source: bytes):
    comment = False
    for match in re.finditer(rb"[^\x09\x0a\x0c\x0d\x20]+", source):
        word = match.group()
        if any(byte < 33 or byte > 126 for byte in word):
            raise ValueError("byte outside the Zar profile")
        if comment:
            if word == b"$)":
                comment = False
            elif b"$(" in word or b"$)" in word:
                raise ValueError("embedded comment delimiter")
        elif word == b"$(":
            comment = True
        elif word == b"$)":
            raise ValueError("comment close without comment open")
        else:
            yield word
    if comment:
        raise ValueError("unterminated comment")


def nat_length(value: int) -> int:
    return len(f"(mm-nat {value})")


def string_length(value: str) -> int:
    return (len("(mm-string ") + len("(mm-char-nil)") + 1 +
            sum(len("(mm-char-cons ") + nat_length(ord(char)) + 2 for char in value))


def index_length(value: int) -> int:
    prefix, digits = value // 20, 0
    while prefix:
        digit = (prefix - 1) % 5 + 1
        prefix = (prefix - digit) // 5
        digits += 1
    return (len("(mm-compressed-index-code ") + len("(mm-nil)") + 2 +
            nat_length(value % 20) + 21 * digits)


@lru_cache(maxsize=None)
def index_length_sum(count: int) -> int:
    """Sum current wire-index sizes for 0 <= value < count, without rows."""
    base = len("(mm-compressed-index-code ") + len("(mm-nil)") + 2 + nat_length(0)
    total = count * base + (count // 20) * 10 + max(0, count % 20 - 10)
    low, high, digits = 1, 5, 1
    while 20 * low < count:
        total += max(0, min(count, 20 * (high + 1)) - 20 * low) * 21 * digits
        low, high, digits = high + 1, 5 * high + 5, digits + 1
    return total


def successor_bytes(count: int, position: int, tag: str | None, owner: str) -> int:
    proof_owner = (len("(mm-source-proof-owner ") + string_length(owner) +
                   1 + nat_length(position) + 1)
    prefix = len("(mm-compressed-index-successor " if tag else "(mm-index-successor ")
    wrapped_owner = len("(" + tag + " ") + proof_owner + 1 if tag else proof_owner
    return (count * (prefix + wrapped_owner + 4) + 2 * index_length_sum(count) -
            index_length(0) + index_length(count))


def measure(source: bytes, owner: str = "metamath-test-unit") -> dict:
    owner.encode("utf-8")
    words = iter(tokens(source))
    counts, payload = Counter(), Counter()
    lower_rows, upper_rows, lower_bytes, upper_bytes = (Counter() for _ in range(4))
    position, assertions, active_hypotheses = 0, 0, 0
    scopes = []
    for directive in words:
        if directive == b"${":
            scopes.append(active_hypotheses)
            counts["scope_open"] += 1
            position += 1
            continue
        if directive == b"$}":
            if not scopes:
                raise ValueError("scope underflow in lexical measurement")
            active_hypotheses = scopes.pop()
            counts["scope_close"] += 1
            position += 1
            continue
        if directive == b"$[":
            counts["include"] += 1
            while next(words) != b"$]":
                pass
            continue
        if directive not in (b"$c", b"$v", b"$d", b"$f", b"$e", b"$a", b"$p"):
            continue
        counts[directive.decode()] += 1
        formula = []
        for word in words:
            if word in (b"$.", b"$="):
                break
            formula.append(word)
        payload["statement_formula_tokens"] += len(formula)
        if directive in (b"$f", b"$e"):
            active_hypotheses += 1
        if directive == b"$d":
            payload["declared_dv_pairs"] += len(formula) * (len(formula) - 1) // 2
        if directive == b"$p":
            first = next(words)
            if first == b"(":
                counts["compressed_theorems"] += 1
                header = 0
                for word in words:
                    if word == b")":
                        break
                    header += 1
                body_bytes = 0
                for word in words:
                    if word == b"$.":
                        break
                    payload["compressed_body_words"] += 1
                    body_bytes += len(word)
                payload["compressed_header_labels"] += header
                payload["compressed_body_bytes"] += body_bytes
                for family, minimum, maximum, tag in (
                    ("heap", header + body_bytes, header + body_bytes + active_hypotheses,
                     "mm-compressed-heap-owner"),
                    ("node", body_bytes, body_bytes + active_hypotheses,
                     "mm-compressed-node-owner"),
                    ("stack", body_bytes + 1, body_bytes + 1, "mm-compressed-stack-owner"),
                    ("plain", body_bytes + 1, body_bytes + 1, None),
                ):
                    lower_rows[family] += minimum
                    upper_rows[family] += maximum
                    lower_bytes[family] += successor_bytes(minimum, position, tag, owner)
                    upper_bytes[family] += successor_bytes(maximum, position, tag, owner)
            else:
                counts["normal_theorems"] += 1
                steps = 1
                for word in words:
                    if word == b"$.":
                        break
                    steps += 1
                payload["normal_proof_labels"] += steps
                payload["normal_prefix_inventory_rows"] += assertions + active_hypotheses
            assertions += 1
        elif directive == b"$a":
            assertions += 1
        position += 1
    if scopes:
        raise ValueError("unclosed scope in lexical measurement")
    no_includes = not counts["include"]
    return {
        "schema": "mm2-source-size-bounds-v1",
        "assumption": "structurally valid Zar-profile source; no proof checking",
        "expanded_includes_measured": False,
        "native_mandatory_frames_measured": False,
        "source_bytes": len(source), "source_forms_in_file": position,
        "counts": dict(counts), "payload": dict(payload),
        "successor_rows_lower": dict(lower_rows),
        "successor_rows_upper": dict(upper_rows) if no_includes else None,
        "successor_encoded_bytes_lower": sum(lower_bytes.values()),
        "successor_encoded_bytes_upper": sum(upper_bytes.values()) if no_includes else None,
        "other_passive_rows_included_in_bounds": False,
        "normal_inventory_exact_for_no_includes": no_includes,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--owner", default="metamath-test-unit")
    args = parser.parse_args()
    try:
        print(json.dumps(measure(args.source.read_bytes(), args.owner), indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, UnicodeError, StopIteration) as error:
        parser.exit(2, f"Source measurement failed: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
