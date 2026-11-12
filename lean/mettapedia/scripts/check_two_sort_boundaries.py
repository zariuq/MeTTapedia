#!/usr/bin/env python3
"""Read-only source audit for the two-sort calculus and its MeTTa adapters.

Run from any directory with Python 3; no build, cache, or manifest is required.
The default source scope is Mettapedia/**/*.lean, scripts/**/*.lean, and all
root-level Lean files, including standalone probes. --include-scratch also
scans other source directories. Archive, MessyWIP, and generated dependency
caches are excluded.

Historical mentions in comments or papers are allowed. Active references,
including string-valued module names, are not. This lexical/import-graph audit
does not replace Lean compilation or certify the mathematical claims.
"""

from __future__ import annotations

import argparse
from collections import deque
from pathlib import Path
import os
import re


ROOT = Path(__file__).resolve().parents[1]
CALCULUS = "Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId"
EXPERIMENT = "Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId"
RETIRED = "Mettapedia.Languages.MeTTa.Pure"
CORE_ROOTS = tuple(
    f"{CALCULUS}.Regular.{name}"
    for name in ("Typing", "Normalization", "BidirectionalCompleteness", "SyntacticCwf")
)
YONEDA_ROOTS = (
    "Mettapedia.TypeTheory.CwfYoneda",
    "Mettapedia.TypeTheory.CwfYonedaCoherence",
)
RELATION_ROOTS = (
    "Mettapedia.Logic.Relation.Normalization",
    "Mettapedia.Logic.Relation.NormalizationExamples",
    "Mettapedia.Logic.Relation.PathConfluence",
    "Mettapedia.Logic.Relation.PathConfluenceExamples",
    "Mettapedia.Logic.Relation.DecodedPath",
    "Mettapedia.Data.List.FiniteLookup",
)
TYPING = CORE_ROOTS[0]
ADAPTER = f"{EXPERIMENT}.Adapters.PresentationBoundary"
EXCLUDED = {".lake", ".git", "__pycache__", "Archive", "MessyWIP", "_archive"}

# The prefix deliberately includes retired siblings such as PureCheckingService,
# not only the old Pure.* subtree. Unrelated uses of the word 'pure' are allowed.
RETIRED_REFERENCE = re.compile(r"(?<![\w'])" + re.escape(RETIRED) + r"[\w'.]*")
IDENTIFIER = r"(?:«[^»\n]+»|[A-Za-z_][\w']*)(?:\.(?:«[^»\n]+»|[A-Za-z_][\w']*))*"
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b", re.M)
NAME = re.compile(IDENTIFIER)
HEADER_COMMANDS = {
    "import", "prelude", "public", "private", "meta", "open", "namespace",
    "section", "end", "set_option", "universe", "universes", "variable",
    "variables", "noncomputable", "def", "abbrev", "opaque", "theorem", "lemma",
    "structure", "inductive", "class", "instance", "example", "initialize",
    "syntax", "macro", "macro_rules", "elab", "elab_rules", "attribute", "export",
}
TOKEN = re.compile(
    r"/-|--|(?<![\w'])r(#+)\"|\"(?:\\.|[^\"\\])*\"|"
    r"(?<![\w'])'(?:\\.|[^'\\\n])'|«[^»]*»",
    re.S,
)
BLOCK_MARKER = re.compile(r"/-|-/")
COMMAND = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)[ \t]+)*"
    r"(namespace|section|end|def|abbrev|opaque|theorem|lemma|inductive|structure|class)"
    r"\b(?:[ \t]+(" + IDENTIFIER + r"))?",
    re.M,
)


def mask_lean(source: str) -> tuple[str, str]:
    """Return comment-free and comment/string-free views, retaining line offsets.

    Nested block comments, escaped/ordinary/raw strings, character literals, and
    escaped identifiers are recognized. Lean syntax extensions are not parsed.
    """
    comments, code = [], []
    cursor = 0
    while match := TOKEN.search(source, cursor):
        start, end = match.span()
        comments.append(source[cursor:start])
        code.append(source[cursor:start])
        token = match.group()
        is_comment = token in ("/-", "--")
        if token == "/-":
            depth = 1
            while depth:
                marker = BLOCK_MARKER.search(source, end)
                if marker is None:
                    raise ValueError("unterminated block comment")
                depth += 1 if marker.group() == "/-" else -1
                end = marker.end()
        elif token == "--":
            newline = source.find("\n", end)
            end = len(source) if newline < 0 else newline
        elif match.group(1) is not None:
            delimiter = '"' + match.group(1)
            closing = source.find(delimiter, end)
            if closing < 0:
                raise ValueError("unterminated raw string")
            end = closing + len(delimiter)
        original = source[start:end]
        masked = re.sub(r"[^\n]", " ", original)
        comments.append(masked if is_comment else original)
        code.append(original if token.startswith("«") else masked)
        cursor = end
    comments.append(source[cursor:])
    code.append(source[cursor:])
    return "".join(comments), "".join(code)


def imports(code: str) -> tuple[str, ...]:
    """Read ordinary Lean import commands, including multiline module lists."""
    result = []
    for command in IMPORT.finditer(code):
        cursor = command.end()
        while True:
            whitespace = re.match(r"\s+", code[cursor:])
            if whitespace is None:
                break
            cursor += whitespace.end()
            module = NAME.match(code, cursor)
            if module is None or module.group() in HEADER_COMMANDS:
                break
            result.append(module.group())
            cursor = module.end()
    return tuple(dict.fromkeys(result))


def under(module: str, prefix: str) -> bool:
    return module == prefix or module.startswith(prefix + ".")


def source_files(include_scratch: bool) -> list[Path]:
    trees = [ROOT] if include_scratch else [ROOT / "Mettapedia", ROOT / "scripts"]
    files = set()
    for tree in trees:
        for directory, folders, names in os.walk(tree):
            folders[:] = sorted(name for name in folders if name not in EXCLUDED)
            files.update(Path(directory) / name for name in names if name.endswith(".lean"))
    files.update(path for path in ROOT.glob("*.lean") if path.is_file())
    return sorted(files)


def closure_paths(graph: dict[str, tuple[str, ...]], root: str) -> dict[str, tuple[str, ...]]:
    """Retain shortest witness paths, including missing/external import leaves."""
    paths = {root: (root,)}
    pending = deque([root])
    while pending:
        module = pending.popleft()
        for dependency in graph.get(module, ()):
            if dependency not in paths:
                paths[dependency] = paths[module] + (dependency,)
                pending.append(dependency)
    return paths


def declarations(code: str) -> dict[str, list[tuple[str, int]]]:
    """Collect named declaration authorities with ordinary namespace scopes."""
    result: dict[str, list[tuple[str, int]]] = {}
    namespace = ""
    scopes = []
    for command in COMMAND.finditer(code):
        kind, name = command.groups()
        if kind in ("namespace", "section"):
            scopes.append(namespace)
            if kind == "namespace" and name:
                namespace = (name.removeprefix("_root_.") if name.startswith("_root_.")
                             else ".".join(part for part in (namespace, name) if part))
        elif kind == "end":
            if scopes:
                namespace = scopes.pop()
        elif name:
            full = (name.removeprefix("_root_.") if name.startswith("_root_.")
                    else ".".join(part for part in (namespace, name) if part))
            result.setdefault(full, []).append((kind, code.count("\n", 0, command.start()) + 1))
    return result


def self_test() -> None:
    """Positive/negative parser and graph controls, entirely in memory."""
    sample = ('/- historical ' + RETIRED + '.Core /- nested -/ -/\n'
              'import A.B C.D\n  E.F\n'
              'namespace Test\n'
              'def label := "-- /- ' + RETIRED + '.Core"\n'
              'def raw := r#"a " /- b"#\n'
              '-- import Hidden\nend Test\n')
    comments, code = mask_lean(sample)
    assert imports(code) == ("A.B", "C.D", "E.F")
    assert len(RETIRED_REFERENCE.findall(comments)) == 1
    assert not RETIRED_REFERENCE.search(code)
    assert comments.count("\n") == code.count("\n") == sample.count("\n")
    assert RETIRED_REFERENCE.search("open " + RETIRED + "CheckingService")
    assert not RETIRED_REFERENCE.search("open Mettapedia.Languages.MeTTa.OtherPure")
    assert not under(CALCULUS + "Comparison", CALCULUS)
    graph = {"A": ("B",), "B": ("A", "C")}
    assert closure_paths(graph, "A")["C"] == ("A", "B", "C")
    owners = declarations("namespace N\nsection\ninductive T where\nend\n"
                          "namespace T\ntheorem law : True := by trivial\nend T\nend N\n")
    assert set(owners) == {"N.T", "N.T.law"}
    duplicate = declarations("namespace N\ninductive T where\nabbrev T := Nat\nend N\n")
    assert len(duplicate["N.T"]) == 2


def audit(include_scratch: bool) -> int:
    failures = []
    graph = {}
    retained_code = {}
    files = source_files(include_scratch)
    for path in files:
        relative = path.relative_to(ROOT)
        module = ".".join(relative.with_suffix("").parts)
        try:
            comments, code = mask_lean(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            failures.append(f"{relative}: cannot inspect source ({type(error).__name__})")
            continue
        graph[module] = imports(code)
        if module in (TYPING, ADAPTER):
            retained_code[module] = code
        if module.startswith(RETIRED):
            failures.append(f"{relative}: source remains under a retired module name")
        for match in RETIRED_REFERENCE.finditer(comments):
            line = comments.count("\n", 0, match.start()) + 1
            failures.append(f"{relative}:{line}: active retired reference {match.group()}")
        if (under(module, "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId")
                or under(module, "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased")):
            for match in re.finditer(r"\b\w*(?:toPure|ofPure)\w*\b", code):
                line = code.count("\n", 0, match.start()) + 1
                failures.append(f"{relative}:{line}: ambiguous two-sort translation {match.group()}")

    print(f"Scanned {len(files)} Lean sources; historical comments are excluded.")
    if not include_scratch:
        print("Scope: library, scripts, and all root-level Lean files (including scratch probes).")

    for root in CORE_ROOTS + YONEDA_ROOTS + RELATION_ROOTS:
        paths = closure_paths(graph, root)
        errors = []
        for module, witness in paths.items():
            if module.startswith("Mettapedia.") and module not in graph:
                errors.append("missing active local source: " + " -> ".join(witness))
            if root in CORE_ROOTS:
                forbidden = (under(module, "Mettapedia.Languages.MeTTa")
                             or "Adapters" in module.split("."))
            elif root in RELATION_ROOTS:
                forbidden = (under(module, "Mettapedia.TypeTheory.Calculi")
                             or under(module, "Mettapedia.Languages")
                             or under(module, "Mettapedia.GSLT")
                             or under(module, "Mettapedia.OSLF"))
            else:
                forbidden = under(module, CALCULUS) or under(module, EXPERIMENT)
            if forbidden:
                errors.append("forbidden dependency: " + " -> ".join(witness))
        failures.extend(errors)
        if not errors:
            print(f"PASS {root}: {sum(module in graph for module in paths)} local modules;")
            print("     no MeTTa/adapters" if root in CORE_ROOTS else "     no concrete calculus dependency")

    if TYPING not in retained_code or ADAPTER not in retained_code:
        failures.append("cannot inspect both regular typing and presentation adapter authorities")
    else:
        core = declarations(retained_code[TYPING])
        adapter = declarations(retained_code[ADAPTER])
        authority_failures = []
        required = {
            "ConstantFree": "inductive", "ConstantFreeRed": "def",
            "ConstantFreeConv": "inductive", "RegularHasType": "inductive",
            "RegularCtx": "inductive", "RegularJudgment": "structure",
        }
        for name, kind in required.items():
            full = f"{CALCULUS}.Regular.{name}"
            owners = core.get(full, [])
            if len(owners) != 1 or owners[0][0] != kind:
                authority_failures.append(f"{TYPING}: expected one {kind} authority for {name}")
            for declared in adapter:
                if declared.rsplit(".", 1)[-1] == name:
                    authority_failures.append(f"{ADAPTER}: redeclares extracted authority {declared}")
        for name in sorted(core.keys() & adapter.keys()):
            authority_failures.append(f"duplicate declaration authority across core/adapter: {name}")
        for module, owners in ((TYPING, core), (ADAPTER, adapter)):
            for name, entries in owners.items():
                if len(entries) > 1:
                    authority_failures.append(f"{module}: duplicate declaration {name}")
        if TYPING not in graph.get(ADAPTER, ()):
            authority_failures.append(f"{ADAPTER}: does not directly import the regular typing authority")
        failures.extend(authority_failures)
        if not authority_failures:
            print("PASS extracted typing authorities are unique; adapter imports the core.")

    for failure in failures:
        print("FAIL " + failure)
    print(f"Two-sort boundary audit: {'FAIL' if failures else 'PASS'} ({len(failures)} findings).")
    return int(bool(failures))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-scratch", action="store_true",
                        help="also inspect other Lean source directories outside the default trees")
    parser.add_argument("--self-test", action="store_true",
                        help="run only the in-memory lexical and dependency regression controls")
    args = parser.parse_args()
    self_test()
    if args.self_test:
        print("Two-sort audit self-tests: PASS")
        return 0
    return audit(args.include_scratch)


if __name__ == "__main__":
    raise SystemExit(main())
