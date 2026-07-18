#!/usr/bin/env python3
"""Create reproducible ``set.mm`` inputs centered on ``ax5d``.

The window is a transport optimization for the grammar-derived source ledger:
it preserves the original bytes from the start of the pinned database through
the scope containing ``ax5d``.  All Metamath parsing and scope interpretation
remain the responsibility of the checked GSLT frontend.

The compact database contains the source assertions needed to check ``ax5d``
and its proof.  Each assertion and proof payload is checked against the pinned
database before the compact input is emitted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


SOURCE_REVISION = "47e6e06b87581cd630d210dc41cf83b02eea78ea"
SOURCE_SHA256 = "3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a"


class WindowError(ValueError):
    pass


AX5D_MANDATORY = ("wph", "wps", "vx")
AX5D_HEADER = ("wal", "wi", "ax-5", "a1i")
AX5D_CODE = "BBCDEABCFG"
AX5D_DECODED = (
    "wps", "wps", "vx", "wal", "wi",
    "wph", "wps", "vx", "ax-5", "a1i",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def ax5d_window(source: bytes) -> bytes:
    target = re.search(rb"(?m)^[ \t]*ax5d[ \t]+\$p[ \t]+", source)
    if target is None:
        raise WindowError("ax5d theorem declaration not found")
    scope_close = re.search(rb"(?m)^[ \t]*\$\}[ \t]*(?:\r?\n|$)", source[target.end():])
    if scope_close is None:
        raise WindowError("scope close following ax5d not found")
    end = target.end() + scope_close.end()
    window = source[:end]
    if not window.endswith(b"\n"):
        window += b"\n"

    anchors = (
        b"a1i $p |- ( ps -> ph ) $=",
        b"wal $a wff A. x ph $.",
        b"ax-5 $a |- ( ph -> A. x ph ) $.",
        b"$d x ps $.",
        b"ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=",
        b"( wal wi ax-5 a1i ) BBCDEABCFG $.",
    )
    missing = [anchor.decode("ascii") for anchor in anchors if anchor not in window]
    if missing:
        raise WindowError(f"ax5d source-window anchors missing: {missing}")
    return window


def require_source_fragments(source: bytes, fragments: tuple[bytes, ...]) -> None:
    missing = [fragment.decode("ascii") for fragment in fragments if fragment not in source]
    if missing:
        raise WindowError(f"set.mm source fragments missing: {missing}")


def decode_compressed_references(
    mandatory: tuple[str, ...], header: tuple[str, ...], code: str
) -> tuple[str, ...]:
    """Decode a compressed proof with no saved-step or unknown-step actions.

    Metamath's A--T characters terminate a base-20 reference index, while
    U--Y extend its base-5 prefix.  The ax5d proof has neither Z saves nor ?
    unknowns, so its reference stream can be checked without interpreting
    proof-stack formulae.
    """

    references = mandatory + header
    accumulator = 0
    decoded: list[str] = []
    for character in code:
        if "A" <= character <= "T":
            index = 20 * accumulator + ord(character) - ord("A")
            if index >= len(references):
                raise WindowError(
                    f"compressed proof reference {index} outside {len(references)} entries"
                )
            decoded.append(references[index])
            accumulator = 0
        elif "U" <= character <= "Y":
            accumulator = 5 * accumulator + ord(character) - ord("T")
        elif character == "Z":
            raise WindowError("saved compressed-proof steps are not expected in ax5d")
        elif character == "?":
            raise WindowError("unknown compressed-proof steps are not permitted in ax5d")
        else:
            raise WindowError(f"invalid compressed-proof character {character!r}")
    if accumulator != 0:
        raise WindowError("unterminated compressed-proof reference")
    return tuple(decoded)


def compact_ax5d_database(source: bytes) -> bytes:
    """Return a self-contained database with the authentic ``ax5d`` proof."""

    fragments = (
        b"wi $a wff ( ph -> ps ) $.",
        b"min $e |- ph $.",
        b"maj $e |- ( ph -> ps ) $.",
        b"ax-mp $a |- ps $.",
        b"ax-1 $a |- ( ph -> ( ps -> ph ) ) $.",
        b"a1i.1 $e |- ph $.",
        b"a1i $p |- ( ps -> ph ) $=\n      ( wi ax-1 ax-mp ) ABADCABEF $.",
        b"wal $a wff A. x ph $.",
        b"vy $f setvar y $.",
        b"$d x ph $.",
        b"ax-5 $a |- ( ph -> A. x ph ) $.",
        b"$d x ps $.",
        b"ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=\n"
        b"      ( wal wi ax-5 a1i ) BBCDEABCFG $.",
    )
    require_source_fragments(source, fragments)

    return b"""$c ( ) -> wff |- A. setvar $.
$v ph ps x y $.
wph $f wff ph $.
wps $f wff ps $.
vx $f setvar x $.
vy $f setvar y $.

wi $a wff ( ph -> ps ) $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $=
    ( wi ax-1 ax-mp ) ABADCABEF $.
$}

wal $a wff A. x ph $.

${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}

${
  $d x ps $.
  ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=
    ( wal wi ax-5 a1i ) BBCDEABCFG $.
$}
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--setmm", required=True, type=Path)
    parser.add_argument("--output-prefix", required=True, type=Path)
    parser.add_argument("--output-slice", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    source = args.setmm.read_bytes()
    actual_source_hash = sha256(source)
    if actual_source_hash != SOURCE_SHA256:
        raise WindowError(
            f"expected set.mm SHA-256 {SOURCE_SHA256}, found {actual_source_hash}"
        )
    window = ax5d_window(source)
    compact = compact_ax5d_database(source)
    decoded = decode_compressed_references(
        AX5D_MANDATORY, AX5D_HEADER, AX5D_CODE
    )
    if decoded != AX5D_DECODED:
        raise WindowError(
            f"ax5d compressed proof changed: expected {AX5D_DECODED}, found {decoded}"
        )
    manifest = {
        "source": {
            "revision": SOURCE_REVISION,
            "sha256": SOURCE_SHA256,
            "bytes": len(source),
        },
        "window": {
            "target": "ax5d",
            "sha256": sha256(window),
            "bytes": len(window),
            "lines": len(window.splitlines()),
        },
        "compact_database": {
            "target": "ax5d",
            "sha256": sha256(compact),
            "bytes": len(compact),
            "lines": len(compact.splitlines()),
        },
        "compressed_proof": {
            "mandatory": list(AX5D_MANDATORY),
            "header": list(AX5D_HEADER),
            "code": AX5D_CODE,
            "decoded_references": list(decoded),
            "logical_assertions": [
                reference for reference in decoded if reference in {"ax-5", "a1i"}
            ],
        },
    }
    manifest_bytes = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()

    if args.check:
        if not args.output_prefix.exists() or args.output_prefix.read_bytes() != window:
            raise WindowError("generated ax5d source window is stale")
        if not args.output_slice.exists() or args.output_slice.read_bytes() != compact:
            raise WindowError("generated compact ax5d database is stale")
        if not args.manifest.exists() or args.manifest.read_bytes() != manifest_bytes:
            raise WindowError("generated ax5d source-window manifest is stale")
    else:
        args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
        args.output_slice.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.output_prefix.write_bytes(window)
        args.output_slice.write_bytes(compact)
        args.manifest.write_bytes(manifest_bytes)

    print(
        "SET.MM AX5D SOURCE WINDOW: PASS "
        f"(window {len(window)} bytes/{len(window.splitlines())} lines; "
        f"compact {len(compact)} bytes/{len(compact.splitlines())} lines; "
        "compressed proof decodes to ax-5,a1i)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
