#!/usr/bin/env python3
"""Generate kernel-checked replay of the existing scanner and quoted lexer.

Candidates retain exact source characters and quote tokens. Transitions keep
quoted state and arbitrary prior history. No production parser rules change.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

from generate_vibe_itp_binary_source import (
    LEAN_ROOT,
    NATIVE_ROOT,
    character_list,
    component_span,
    quoted,
)
from generate_vibe_itp_binary_scan import REPLAY_BLOCK_ROWS, format_rows, suffix_blocks

DESTINATION = LEAN_ROOT / "Mettapedia/GSLT/LanguageDef"
NAMESPACE = "Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot"
SCAN_NAMESPACE = NAMESPACE.replace("Snapshot", "Scan")
LEX_NAMESPACE = NAMESPACE.replace("Snapshot", "Lex")


def chunks(text: str) -> list[str]:
    if ";" in text or "\\" in text:
        raise ValueError("replay candidates require a comment-free component without escapes")
    result = []
    position = 0
    while position < len(text) - 1:
        end = min(position + 32, len(text) - 1)
        in_string = False
        for c in text[position:end]:
            if c == '"':
                in_string = not in_string
        while in_string and end < len(text) - 1:
            if text[end] == '"':
                in_string = False
            end += 1
        if in_string:
            raise ValueError("unclosed quoted token")
        result.append(text[position:end])
        position = end
    if not text.endswith(")"):
        raise ValueError("source form must end with closing parenthesis")
    return result + [text[-1:]]


def scan_block_data(text):
    """Candidate positions contain no historical source accumulator."""
    blocks = [text[position:position + 256] for position in range(0, len(text), 256)]
    if not blocks or not blocks[-1].endswith(")"):
        raise ValueError("source form must end with closing parenthesis")
    prefix_blocks = blocks[:-1] + [blocks[-1][:-1]]
    positions = [(1, 0, False, False)]
    line, depth, quoted, started = positions[0]
    for block in prefix_blocks:
        for c in block:
            line += c == "\n"
            if c == '"':
                quoted = not quoted
                started = True
            elif not quoted:
                depth += (c == "(") - (c == ")")
                if not c.isspace():
                    started = True
        positions.append((line, depth, quoted, started))
    if positions[-1][1:] != (1, False, True):
        raise ValueError("unexpected final scanner position")
    return blocks, prefix_blocks, positions


def render_scan_probe(text, count=4):
    blocks, prefix_blocks, positions = scan_block_data(text)
    lines = ["import Mettapedia.GSLT.Parsing.SourceAccumulatorScan",
             "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot", "",
             "set_option maxRecDepth 1000000", "set_option maxHeartbeats 4000000",
             "set_option Elab.async false", "",
             "open Mettapedia.GSLT.Parsing.SourceAccumulatorScan",
             "open Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot", ""]
    for index in range(min(count, len(blocks) - 1) + 1):
        line, depth, quoted, started = positions[index]
        lines.append(f"def point_{index:03d} : Point := ⟨{line}, {depth}, false, "
                     f"{str(quoted).lower()}, false, {str(started).lower()}, 1⟩")
    for index in range(min(count, len(blocks) - 1)):
        sid, nxt = f"{index:03d}", f"{index + 1:03d}"
        lines += [f"theorem step_{sid} : Agreement point_{sid} point_{nxt}",
                  f"    componentChars_{sid} componentChars_{sid} := by",
                  "  intro current forms", "  cbv", f"#check step_{sid}", ""]
    return "\n".join(lines)


def render_scan(text, pieces):
    blocks, prefix_blocks, positions = scan_block_data(text)
    count = len(blocks)
    line = positions[-1][0]
    final = f"{count:03d}"
    lines = [
        "import Mettapedia.GSLT.Parsing.SourceAccumulatorReplay",
        "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot",
        "import Batteries.Tactic.OpenPrivate", "",
        "/-! Original-scanner transitions over arbitrary accumulated source history. -/", "",
        "set_option autoImplicit false", "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
        "namespace " + SCAN_NAMESPACE, "",
        "open Mettapedia.GSLT.Parsing.SourceScanSegments",
        "open Mettapedia.GSLT.Parsing.SourceAccumulatorScan",
        "open NativeOpsSourceGuestSnapshot",
        "open private splitProgramForms parserDialectOf from Algorithms.MeTTa.Simple.Parser", "",
    ]
    rows = [f"  {at_line} {depth} {str(quoted).lower()} {str(started).lower()}"
            for at_line, depth, quoted, started in positions[:-1]]
    lines.extend(format_rows("accumulator_scan_points", rows))
    lines += [
        f"def point_{final} := closingPoint {line}",
        "def lastPrefixChars : List Char := " + character_list(prefix_blocks[-1]), "",
    ]
    lines.extend(
        f"accumulator_scan_rows {start} to {min(start + REPLAY_BLOCK_ROWS, count)} ending {count}"
        for start in range(0, count, REPLAY_BLOCK_ROWS)
    )
    lines += ["", f"def prefix_{final} : List Char := []",
              f"theorem replay_{final} : Agreement point_{final} point_{final}",
              f"    prefix_{final} prefix_{final} := agreement_empty point_{final}",
              f"def sourceSuffix_{final} : List Char := []", ""]
    lines.extend(suffix_blocks("accumulator_scan_suffix", count))
    lines.append("")
    lines += [
        "theorem source_suffix_exact : sourceSuffix_000 = componentChars := rfl", "",
        "theorem source_characters_exact : prefix_000 ++ [')'] = componentChars :=",
        "  closing_000.trans source_suffix_exact", "",
        "theorem source_last : componentChars.getLast? = some ')' := by",
        "  rw [← source_characters_exact]", "  exact retained_last_boundary prefix_000", "",
        "theorem source_trimmed : componentText.trimAscii.toString = componentText := by",
        "  apply trimAscii_of_boundary",
        "  · rw [componentText, String.toList_ofList]",
        "    have head : componentChars.head? = some '(' := by rfl",
        "    rw [head]", "    rfl",
        "  · rw [componentText, String.toList_ofList, source_last]", "    rfl", "",
        "theorem source_nonempty : componentText.isEmpty = false := by",
        "  apply ofList_nonempty", "  intro equal",
        "  have heads := congrArg List.head? equal",
        "  change some '(' = none at heads", "  contradiction", "",
        "theorem scanned_exact : componentText.toList.foldl step initialScanState =",
        f"    makeScanState {line} 0 false false false false {line} [] [(1, componentText)] none := by",
        "  have input : componentText.toList = prefix_000 ++ [')'] :=",
        "    (@String.toList_ofList componentChars).trans source_characters_exact.symm",
        "  exact (congrArg (fun chars => chars.foldl step initialScanState) input).trans",
        f"    (scanned_single_form {line} prefix_000 prefix_000 componentText",
        "      replay_000 (congrArg String.ofList source_characters_exact) source_trimmed source_nonempty)", "",
        "theorem split_forms_exact : splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta)",
        "    componentText = .ok [(1, componentText)] :=",
        f"  splitProgramForms_of_scanned componentText {line} scanned_exact", "",
    ]
    # The lexer uses its own quote-safe segmentation. No scanner transition
    # refers to these strings or to a growing historical accumulator.
    lines.extend(f"def segment_{index:04d} : String := {quoted(piece)}" for index, piece in enumerate(pieces))
    lines += ["", "end " + SCAN_NAMESPACE, ""]
    return "\n".join(lines)


def lex_block_data(text):
    """Boundary candidates retain only quoted state and an unfinished token."""
    if ";" in text or "\\" in text:
        raise ValueError("current replay candidate has unsupported comments or escapes")
    blocks = [text[position:position + 256] for position in range(0, len(text), 256)]
    points = [(False, "")]
    emissions = []
    quoted, current = points[0]
    for block in blocks:
        emitted = []
        for character in block:
            if quoted:
                current += character
                if character == '"':
                    quoted = False
                    emitted.append(current)
                    current = ""
            elif character == '"':
                if current:
                    emitted.append(current)
                current = character
                quoted = True
            elif character.isspace() or character in "()":
                if current:
                    emitted.append(current)
                    current = ""
                if character in "()":
                    emitted.append(character)
            else:
                current += character
        points.append((quoted, current))
        emissions.append(emitted)
    if points[-1] != (False, ""):
        raise ValueError("component ends inside a token")
    return blocks, points, emissions


def lex_point(index, point):
    quoted, current = point
    return f"def point_{index:03d} : Point := ⟨{str(quoted).lower()}, false, " + \
        character_list(current[::-1]) + "⟩"


def lex_step(index, emitted):
    sid, nxt = f"{index:03d}", f"{index + 1:03d}"
    return [f"def emitted_{sid} : List String := [" +
            ", ".join(quoted(token) for token in emitted) + "]",
            f"theorem step_{sid} : Agreement point_{sid} point_{nxt}",
            f"    componentChars_{sid} emitted_{sid} := by",
            "  intro rest priorTokens", "  cbv", ""]


def render_lex_probe(text, count=4):
    blocks, points, emissions = lex_block_data(text)
    count = min(count, len(blocks))
    lines = ["import Mettapedia.GSLT.Parsing.SourceAccumulatorLex",
             "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot", "",
             "set_option maxRecDepth 1000000", "set_option maxHeartbeats 4000000",
             "set_option Elab.async false", "",
             "open Mettapedia.GSLT.Parsing.SourceAccumulatorLex",
             "open Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot", ""]
    lines.extend(lex_point(index, point) for index, point in enumerate(points[:count + 1]))
    for index in range(count):
        lines.extend(lex_step(index, emissions[index]))
    return "\n".join(lines)


def render_lex(text):
    blocks, points, emissions = lex_block_data(text)
    final = f"{len(blocks):03d}"
    lines = [
        "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot",
        "import Mettapedia.GSLT.Parsing.SourceAccumulatorReplay",
        "import Mettapedia.GSLT.Parsing.SExprTokenRoundTrip",
        "import Batteries.Tactic.OpenPrivate", "",
        "/-! Original quoted-lexer transitions over arbitrary preceding tokens. -/", "",
        "set_option autoImplicit false", "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
        "namespace " + LEX_NAMESPACE, "",
        "open Mettapedia.GSLT.Parsing.SourceAccumulatorLex",
        "open NativeOpsSourceGuestSnapshot",
        "open private tokenizeWith parserDialectOf from Algorithms.MeTTa.Simple.Parser", "",
    ]
    lines.append("def point_000 : Point := initialPoint")
    lines.append("")
    rows = []
    for (in_string, current), emitted in zip(points[1:], emissions, strict=True):
        tokens = ", ".join(quoted(token) for token in emitted)
        rows.append(f"  {str(in_string).lower()} false {quoted(current)} [{tokens}]")
    lines.extend(format_rows("accumulator_lex_rows", rows))
    lines += [f"def input_{final} : List Char := []",
              f"def tokens_{final} : List String := []",
              f"theorem replay_{final} : Agreement point_{final} point_{final}",
              f"    input_{final} tokens_{final} := agreement_empty point_{final}", ""]
    lines.extend(suffix_blocks("accumulator_lex_suffix", len(blocks)))
    lines.append("")
    lines += ["theorem input_characters_exact : input_000 = componentChars := rfl", "",
              "theorem tokens_exact : tokens_000 =",
              "    Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax := by rfl", "",
              "theorem lexed_exact : Mettapedia.GSLT.Parsing.SourceLexSegments.lex input_000 [] [] =",
              "    Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax := by",
              "  exact (original_lexer_replay input_000 tokens_000 replay_000).trans tokens_exact", "",
              "theorem tokenized_exact : tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta)",
              "    componentText = Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax :=",
              "  Mettapedia.GSLT.Parsing.SourceLexSegments.tokenized_of_initial",
              "    componentText componentChars input_000 [] []",
              "    (Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax)",
              "    rfl input_characters_exact rfl rfl lexed_exact", "",
              "end " + LEX_NAMESPACE, ""]
    return "\n".join(lines)


def render_admission(module_name, declaration_count):
    lines = [
        "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestLex",
        "import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestScan",
        "import Mettapedia.GSLT.LanguageDef.NativeOpsText",
        "import Mettapedia.GSLT.Parsing.SourceSExprAdmission", "",
        "import Mettapedia.GSLT.Parsing.SourceSExprSafety", "",
        "/-! Actual operational component admitted through the existing complete carrier parser. -/", "",
        "set_option autoImplicit false", "set_option maxHeartbeats 4000000",
        "set_option maxRecDepth 1000000", "set_option Elab.async false", "",
        "namespace " + NAMESPACE.replace("Snapshot", "Admission"), "",
        "open Mettapedia.GSLT.Parsing", "open NativeOps NativeOpsSourceGuestSnapshot", "",
    ]
    for index in range(declaration_count):
        lines += [f"theorem syntax_{index:03d}_safe : SExprTokenRoundTrip.safe syntax_{index:03d} :=",
                  f"  (SourceSExprSafety.safeBool_iff syntax_{index:03d}).mp (by decide +kernel)", ""]
    last = f"{declaration_count:03d}"
    lines += [f"theorem tail_{last}_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_{last} := trivial", ""]
    for index in reversed(range(declaration_count)):
        sid, nxt = f"{index:03d}", f"{index+1:03d}"
        lines += [f"theorem tail_{sid}_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_{sid} :=",
                  f"  ⟨syntax_{sid}_safe, tail_{nxt}_safe⟩", ""]
    lines += [
        "theorem source_syntax_safe : SExprTokenRoundTrip.safe sourceSyntax := by",
        '  change SExprTokenRoundTrip.safe (.atom "gslt-native-ops-v1") ∧',
        "    SExprTokenRoundTrip.safe (.atom " + quoted(module_name) + ") ∧",
        "    SExprTokenRoundTrip.childrenSafe syntaxTail_000",
        "  exact ⟨by simp [SExprTokenRoundTrip.safe], by simp [SExprTokenRoundTrip.safe],",
        "    tail_000_safe⟩", "",
        "theorem source_parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed",
        "    MeTTailCore.MeTTaSyntax.petta componentText = .ok sourceSyntax :=",
        "  SourceSExprAdmission.parsed_of_forms componentText sourceSyntax",
        "    NativeOpsSourceGuestScan.split_forms_exact",
        "    (SourceSExprAdmission.single_of_tokens componentText sourceSyntax source_syntax_safe",
        "      NativeOpsSourceGuestLex.tokenized_exact)", "",
        "theorem source_text_admitted : admitProgramText? primitiveCatalogue componentText =",
        "    some expectedProgram :=",
        "  admitProgramText?_of_parsed primitiveCatalogue componentText sourceSyntax expectedProgram",
        "    source_parsed source_admitted", "",
        "theorem source_text_no_extra_program (program : Program) :",
        "    admitProgramText? primitiveCatalogue componentText = some program ↔ program = expectedProgram := by",
        "  rw [source_text_admitted, Option.some.injEq]", "  exact eq_comm", "",
        "theorem source_text_factorization : sourceText =",
        "    String.ofList leadingChars ++ componentText ++ String.ofList trailingChars := by",
        "  rw [sourceText, source_character_factorization, String.ofList_append, String.ofList_append]",
        "  rfl", "",
        "end " + NAMESPACE.replace("Snapshot", "Admission"), "",
    ]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--output-dir", type=Path, default=DESTINATION)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = args.source or args.native_root / "langdef/vibe-itp/vibe_itp_native_guest_v1.metta"
    text = source.read_text()
    start, end = component_span(text, text.index("(gslt-native-ops-v1"))
    component = text[start:end]
    pieces = chunks(component)
    sys.path.insert(0, str(args.native_root / "tools"))
    from gslt2parse_schema_v1 import parse_sexprs
    expression = parse_sexprs(component)[0]
    outputs = {"NativeOpsSourceGuestScan.lean": render_scan(component, pieces),
               "NativeOpsSourceGuestLex.lean": render_lex(component),
               "NativeOpsSourceGuestAdmission.lean": render_admission(expression[1].text, len(expression)-2)}
    for name, content in outputs.items():
        path = args.output_dir / name
        if args.check:
            if not path.exists() or path.read_text() != content:
                parser.error("stale source replay candidates: " + name)
        else:
            path.write_text(content)
    print("checked" if args.check else "generated", len(scan_block_data(component)[0]),
          "scanner and quoted-state lexer blocks")


if __name__ == "__main__":
    main()
