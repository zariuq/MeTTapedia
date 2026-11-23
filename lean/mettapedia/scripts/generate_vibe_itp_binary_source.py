#!/usr/bin/env python3
"""Export the actual authored guest text and binary descriptor for Lean checks.

The exported descriptor is evidence to be checked by independent Lean source
admission and decoder correspondence. Artifact hashes only identify inputs.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from vibe_itp_source_slices import (
    GuestSourceSlices,
    SLICE_FILE,
    VIEW_IMPORTS,
    assembly_theorem,
    component_span,
    snapshot_identity,
)

LEAN_ROOT = Path(__file__).resolve().parents[1]
NATIVE_ROOT = LEAN_ROOT.parents[2] / "hyperon/cetta-prime-nik-20260811"
OUTPUT = LEAN_ROOT / "Mettapedia/Languages/VibeITP/Native/GeneratedBinarySource.lean"
BINARY_VIEWS = ("authoredSourceChars", "authoredPrefixChars", "authoredBinaryChars", "authoredSuffixChars")


def quoted(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def character_list(value: str) -> str:
    """Snapshot source characters independently of every parsed candidate."""
    return "[" + ", ".join("Char.ofNat %d" % ord(character) for character in value) + "]"


def character_definitions(name: str, value: str) -> list[str]:
    """Emit a standalone character view for the operational source snapshot."""
    chunks = [value[position:position + 256] for position in range(0, len(value), 256)]
    definitions = [f"def {name}_{index:03d} : List Char := {character_list(chunk)}"
                   for index, chunk in enumerate(chunks)]
    joined = "[]"
    for index in reversed(range(len(chunks))):
        joined = f"{name}_{index:03d} ++ ({joined})"
    definitions.append(f"def {name} : List Char := {joined}")
    return definitions


def source_character_definitions(text: str, start: int, end: int) -> list[str]:
    """Share the common refinement of the checked source and component slices."""
    views = (
        ("authoredSourceChars", 0, len(text)),
        ("authoredPrefixChars", 0, start),
        ("authoredBinaryChars", start, end),
        ("authoredSuffixChars", end, len(text)),
    )
    intervals = {
        name: [(pos, min(pos + 256, upper)) for pos in range(lower, upper, 256)]
        for name, lower, upper in views
    }
    boundaries = sorted({cut for ranges in intervals.values() for interval in ranges for cut in interval})
    offsets = {cut: index for index, cut in enumerate(boundaries)}
    character_names = {char: f"character_{ord(char)}" for char in sorted(set(text))}
    definitions = [
        f"private def {name} : Char := Char.ofNat {ord(char)}"
        for char, name in character_names.items()
    ]
    sections = []
    for index, (left, right) in enumerate(zip(boundaries, boundaries[1:])):
        name = f"sourceSlice_{index:03d}"
        contents = ", ".join(character_names[char] for char in text[left:right])
        definitions.append(f"private def {name} : List Char := [{contents}]")
        sections.append(name)
    definitions.append("")
    for name, lower, upper in views:
        for index, (left, right) in enumerate(intervals[name]):
            field = f"{name}_{index:03d}"
            trunk = " ++ ".join(sections[offsets[left]:offsets[right]])
            definitions.append(f"def {field} : List Char := {trunk}")
        view = name.removesuffix("Chars") + "Slices"
        entries = ", ".join(sections[offsets[lower]:offsets[upper]])
        definitions.extend([
            f"private def {view} : List (List Char) := [{entries}]",
            f"def {name} : List Char := {view}.flatten",
            "",
        ])
    definitions.extend([
        "private theorem authored_slices_factorization : authoredSourceSlices =",
        "    authoredPrefixSlices ++ authoredBinarySlices ++ authoredSuffixSlices := rfl",
        "",
        "/-- Concatenating the three views recovers the complete source text. -/",
        "theorem authored_characters_factorization : authoredSourceChars =",
        "    authoredPrefixChars ++ authoredBinaryChars ++ authoredSuffixChars := by",
        "  unfold authoredSourceChars authoredPrefixChars authoredBinaryChars authoredSuffixChars",
        "  rw [authored_slices_factorization, List.flatten_append, List.flatten_append]",
        "",
    ])
    return definitions


def source_expression(value) -> str:
    if isinstance(value, tuple):
        return ".list [" + ", ".join(source_expression(child) for child in value) + "]"
    token = str(value) if isinstance(value, int) else value.text
    return ".atom " + quoted(token)



def render(native: Path, slices: GuestSourceSlices | None = None) -> str:
    sys.path.insert(0, str(native / "tools"))
    from compile_gslt_binary_reader_v1 import load
    from gslt2parse_schema_v1 import parse_sexprs, Symbol

    authored = native / "langdef/vibe-itp/vibe_itp_native_guest_v1.metta"
    projected = native / "langdef/vibe-itp/vibe_itp_binary_reader_v1.metta"
    text = slices.text if slices is not None else authored.read_text(encoding="utf-8")
    packages = parse_sexprs(text)
    if len(packages) != 1:
        raise ValueError("expected exactly one authored guest package")
    package = packages[0]
    if not isinstance(package, tuple) or len(package) != 4 or package[0] != Symbol("gslt-native-guest-v1"):
        raise ValueError("unexpected authored package schema")
    components = {part[0].text: part[1] for part in package[2:]}
    if set(components) != {"binary-reader", "operations"}:
        raise ValueError("unexpected guest components")
    if parse_sexprs(projected.read_text(encoding="utf-8")) != [components["binary-reader"]]:
        raise ValueError("generated binary projection differs from authored syntax")
    start, end = component_span(text, text.index("(gslt-presentation-v1"))
    binary_text = text[start:end]
    if parse_sexprs(binary_text) != [components["binary-reader"]]:
        raise ValueError("verbatim binary span differs from authored syntax")
    grammar = load(projected)
    metadata = {
        "authoredSourceSHA256": slices.digest if slices is not None else sha256(authored.read_bytes()).hexdigest(),
        "binaryProjectionSHA256": sha256(projected.read_bytes()).hexdigest(),
        "generatedReaderSHA256": sha256((native / "src/generated/vibe_itp_binary_reader_v1.generated.c").read_bytes()).hexdigest(),
        "binaryRuntimeSHA256": sha256((native / "src/gslt_binary_reader_v1.c").read_bytes()).hexdigest(),
        "binaryCompilerSHA256": sha256((native / "tools/compile_gslt_binary_reader_v1.py").read_bytes()).hexdigest(),
    }
    if slices is None:
        character_views = source_character_definitions(text, start, end)
    else:
        if (start, end) != slices.binary:
            raise ValueError("binary span differs from shared source view")
        character_views = slices.render_views(BINARY_VIEWS, slices.binary)
        character_views += assembly_theorem("authored_characters_factorization", BINARY_VIEWS)
    lines = [
        *(VIEW_IMPORTS if slices is not None else []),
        "import Mettapedia.GSLT.Parsing.BinaryRecordCodec",
        "import Algorithms.MeTTa.Simple.Parser",
        "import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT",
        "",
        "/-! Exact authored input and exported binary descriptor. Generated by",
        "`scripts/generate_vibe_itp_binary_source.py`; proof checks live separately. -/",
        "",
        "namespace Mettapedia.Languages.VibeITP.Native.GeneratedBinarySource",
        "",
        "set_option maxRecDepth 100000",
        "",
        "open Mettapedia.GSLT.Parsing.BinaryRecordCodec",
        "",
        *character_views,
        "def authoredSourceText : String := String.ofList authoredSourceChars",
        "def authoredPrefixText : String := String.ofList authoredPrefixChars",
        "def authoredBinaryText : String := String.ofList authoredBinaryChars",
        "def authoredSuffixText : String := String.ofList authoredSuffixChars",
        "",
        "def binarySyntax : Algorithms.MeTTa.Simple.Parser.SExpr := " + source_expression(components["binary-reader"]),
        "",
    ]
    binary = components["binary-reader"]
    lines += [
        "def canonicalSource : Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.Source := {",
        "  name := " + quoted(binary[1].text),
        "  operators := [" + ", ".join(
            "{ name := %s, arity := %d }" % (quoted(operator[1].text), operator[2])
            for operator in binary[2][1:]) + "]",
        "  equations := [" + ", ".join(source_expression(equation) for equation in binary[3][1:]) + "]",
        "  rewrites := [",
    ]
    for index, rewrite in enumerate(binary[4][1:]):
        comma = "," if index + 1 < len(binary[4][1:]) else ""
        lines.append("    { name := %s, head := %s, body := [%s] }%s" % (
            quoted(rewrite[1].text), source_expression(rewrite[2][1]),
            ", ".join(source_expression(body) for body in rewrite[3][1:]), comma))
    lines += ["  ]", "}", ""]
    for name, value in metadata.items():
        lines.append(f'def {name} : String := {quoted(value)}')
        if name == "authoredSourceSHA256" and slices is not None:
            lines += ["", *snapshot_identity()]
    lines += [
        "",
        "def grammar : Grammar := {",
        "  codec := { inlineMax := %d, payloadMax := %d, requireShortest := %s }" % (
            grammar.codec.inline_max, grammar.codec.payload_max,
            "true" if grammar.codec.require_shortest else "false"),
        "  opcodes := [",
    ]
    kinds = {"word": "word", "counted-bytes": "countedBytes", "counted-words": "countedWords"}
    for index, layout in enumerate(grammar.opcodes):
        operands = ", ".join("{ kind := .%s, role := %s }" % (kinds[field.kind], quoted(field.role)) for field in layout.operands)
        comma = "," if index + 1 < len(grammar.opcodes) else ""
        lines.append(f"    {{ opcode := {layout.byte}, label := {quoted(layout.label)}, operands := [{operands}] }}{comma}")
    lines += ["  ]", "}", "", "end Mettapedia.Languages.VibeITP.Native.GeneratedBinarySource", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--slices-output", type=Path, help="path to the shared character store")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    table_output = args.slices_output
    if table_output is None and args.output.resolve() == OUTPUT.resolve():
        table_output = LEAN_ROOT / SLICE_FILE
    outputs = {}
    slices = None
    if table_output is not None:
        if table_output.resolve() == args.output.resolve():
            parser.error("the source wrapper and character store require distinct paths")
        source = args.native_root / "langdef/vibe-itp/vibe_itp_native_guest_v1.metta"
        slices = GuestSourceSlices.read(source)
        outputs[table_output] = slices.render_table()
    outputs[args.output] = render(args.native_root, slices)
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != content:
                parser.error(f"generated binary source input is missing or stale in {path.name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    print("checked" if args.check else "generated", args.output.name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
