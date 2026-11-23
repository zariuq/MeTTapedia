"""Shared character slices of the authored VibeITP guest package."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path


SLICE_MODULE = "Mettapedia.GSLT.Parsing.VibeGuestSourceSlices"
SLICE_FILE = Path(*SLICE_MODULE.split(".")).with_suffix(".lean")
VIEW_IMPORTS = [
    "import Mettapedia.GSLT.Parsing.SourceCharacterViews",
    "import " + SLICE_MODULE,
]
CHUNK_SIZE = 256


def component_span(text: str, start: int) -> tuple[int, int]:
    """Locate a balanced source span; Lean checks the exported text separately."""
    depth = 0
    quoted_string = escaped = comment = False
    for position in range(start, len(text)):
        character = text[position]
        if comment:
            comment = character != "\n"
        elif quoted_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                quoted_string = False
        elif character == ";":
            comment = True
        elif character == '"':
            quoted_string = True
        elif character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                return start, position + 1
    raise ValueError("unclosed binary source component")


@dataclass(frozen=True)
class GuestSourceSlices:
    text: str
    digest: str
    binary: tuple[int, int]
    operations: tuple[int, int]
    cuts: tuple[int, ...]

    @classmethod
    def read(cls, source: Path) -> GuestSourceSlices:
        raw = source.read_bytes()
        text = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        binary = component_span(text, text.index("(gslt-presentation-v1"))
        operations = component_span(text, text.index("(gslt-native-ops-v1"))
        cuts = {0, len(text), *binary, *operations}
        for first, last in (binary, operations):
            cuts.update(range(0, first, CHUNK_SIZE))
            cuts.update(range(first, last, CHUNK_SIZE))
            cuts.update(range(last, len(text), CHUNK_SIZE))
        cuts.update(range(0, len(text), CHUNK_SIZE))
        return cls(text, sha256(raw).hexdigest(), binary, operations, tuple(sorted(cuts)))

    def render_table(self) -> str:
        lines = [
            "import Init", "",
            "/-! Character slices of the authored VibeITP guest source. The cuts refine",
            "both the binary reader and the operational reader's source views. -/", "",
            f"namespace {SLICE_MODULE}", "",
        ]
        for char in sorted(set(self.text)):
            code = ord(char)
            lines.append(f"private def character_{code} : Char := Char.ofNat {code}")
        lines.append("")
        for index, (start, end) in enumerate(zip(self.cuts, self.cuts[1:])):
            values = ", ".join(f"character_{ord(c)}" for c in self.text[start:end])
            lines.append(f"def sourceSlice_{index:03d} : List Char := [{values}]")
        lines += ["", f'def sourceSHA256 : String := "{self.digest}"',
                  "", f"end {SLICE_MODULE}", ""]
        return "\n".join(lines)

    def render_views(self, names: tuple[str, str, str, str],
                     span: tuple[int, int]) -> list[str]:
        offsets = {position: index for index, position in enumerate(self.cuts)}
        start, end = span
        extent = len(self.text)
        ranges = ((0, extent), (0, start), (start, end), (end, extent))
        lines = [f"open {SLICE_MODULE}", ""]
        for name, (first, last) in zip(names, ranges, strict=True):
            cuts = [str(offsets[min(pos + CHUNK_SIZE, last)])
                    for pos in range(first, last, CHUNK_SIZE)]
            prefix = f"source_character_view {name} from {offsets[first]} cuts"
            if len(cuts) <= 32:
                lines.append(prefix + f" [{', '.join(cuts)}]")
            else:
                lines.append(prefix + " [")
                for row in range(0, len(cuts), 32):
                    group = cuts[row:row + 32]
                    suffix = "," if row + len(group) < len(cuts) else ""
                    lines.append("  " + ", ".join(group) + suffix)
                lines.append("]")
            lines.append("")
        whole, leading, component, trailing = (name + "Slices" for name in names)
        return lines + [
            f"private theorem source_slices_assemble : {whole} =",
            f"    {leading} ++ {component} ++ {trailing} := rfl", "",
        ]


def assembly_theorem(name: str, views: tuple[str, str, str, str]) -> list[str]:
    whole, leading, component, trailing = views
    return [
        f"theorem {name} : {whole} = {leading} ++ {component} ++ {trailing} := by",
        f"  rw [{whole}FromSlices, {leading}FromSlices, {component}FromSlices, {trailing}FromSlices,",
        "    source_slices_assemble, List.flatten_append, List.flatten_append]", "",
    ]


def snapshot_identity() -> list[str]:
    return [
        "theorem source_snapshot_matches :",
        f"    {SLICE_MODULE}.sourceSHA256 = authoredSourceSHA256 := rfl", "",
    ]
