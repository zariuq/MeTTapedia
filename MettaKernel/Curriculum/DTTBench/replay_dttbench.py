#!/usr/bin/env python3

import argparse
import re
import subprocess
import sys
from pathlib import Path


CORPUS_FILES = ("Eq.lean", "Leq.lean", "Logic.lean", "Relation.lean", "Set.lean")
DECL_RE = re.compile(r"(?m)^def\s+([A-Za-z0-9_]+)\s*:")
TACTIC_RE = re.compile(r"\bby[ \t]*(?:\n[ \t]*)?canonical_min(?:[ \t]+\d+)?")
SUGGESTION_RE = re.compile(
    r"Try this:\n(?P<body>.*?)(?=\n[^\n]+:\d+:\d+: warning: declaration uses `sorry`)",
    re.DOTALL,
)
FORBIDDEN_RE = re.compile(r"\b(?:sorry|admit|theorem_wanted)\b")
AXIOM_FREE_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def fail(message: str, output: str = "") -> None:
    print(f"DTTBENCH-FAIL: {message}", file=sys.stderr)
    if output:
        print(output, file=sys.stderr)
    raise SystemExit(1)


def extract_suggestions(output: str) -> list[str]:
    suggestions: list[str] = []
    for match in SUGGESTION_RE.finditer(output):
        body = match.group("body").strip()
        if not re.match(r"^\[apply\]\s+exact\b", body):
            fail("unexpected Canonical suggestion format", body)
        suggestions.append(body.removeprefix("[apply]").lstrip())
    return suggestions


def replace_tactics(source: str, suggestions: list[str]) -> str:
    sites = list(TACTIC_RE.finditer(source))
    if len(sites) != len(suggestions):
        fail("suggestion count does not match canonical_min sites")

    suggestion_iter = iter(suggestions)

    def replacement(_match: re.Match[str]) -> str:
        suggestion = next(suggestion_iter)
        indented = suggestion.replace("\n", "\n  ")
        return f"by\n  {indented}"

    return TACTIC_RE.sub(replacement, source)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--negative", required=True, type=Path)
    parser.add_argument("--expected-files", required=True, type=int)
    parser.add_argument("--expected-declarations", required=True, type=int)
    args = parser.parse_args()

    repo = args.repo.resolve()
    work_dir = args.work_dir.resolve()
    work_dir.mkdir(parents=True, exist_ok=True)

    if args.expected_files != len(CORPUS_FILES):
        fail("pinned file count disagrees with the replay driver")

    build = run(["lake", "build", "CanonicalMin"], repo)
    if build.returncode != 0:
        fail("CanonicalMin build failed", build.stdout)

    total = 0
    for filename in CORPUS_FILES:
        source_path = repo / "DTTBench-lean" / filename
        if not source_path.is_file():
            fail(f"missing corpus file {filename}")

        source = source_path.read_text(encoding="utf-8")
        names = DECL_RE.findall(source)
        sites = len(TACTIC_RE.findall(source))
        if not names or len(names) != sites:
            fail(f"{filename}: declarations and canonical_min sites disagree")

        generated = run(["lake", "env", "lean", str(source_path)], repo)
        if generated.returncode != 0:
            fail(f"{filename}: Canonical generation failed", generated.stdout)

        suggestions = extract_suggestions(generated.stdout)
        if len(suggestions) != len(names):
            fail(f"{filename}: expected {len(names)} suggestions, found {len(suggestions)}", generated.stdout)

        replay = replace_tactics(source, suggestions)
        if FORBIDDEN_RE.search(replay):
            fail(f"{filename}: replay source contains an admitted-proof marker")
        replay += "\n" + "\n".join(f"#print axioms {name}" for name in names) + "\n"

        replay_path = work_dir / filename
        replay_path.write_text(replay, encoding="utf-8")
        checked = run(["lake", "env", "lean", str(replay_path)], repo)
        if checked.returncode != 0:
            fail(f"{filename}: generated exact terms failed kernel replay", checked.stdout)
        if "declaration uses `sorry`" in checked.stdout or "depends on axioms:" in checked.stdout:
            fail(f"{filename}: replay retained an admitted or axiomatic dependency", checked.stdout)

        audited = set(AXIOM_FREE_RE.findall(checked.stdout))
        missing = [name for name in names if name not in audited]
        if missing:
            fail(f"{filename}: missing axiom-free audit for {', '.join(missing)}", checked.stdout)

        total += len(names)
        print(f"DTTBENCH-FILE {filename} declarations={len(names)} replay=kernel-checked axioms=none")

    if total != args.expected_declarations:
        fail(f"expected {args.expected_declarations} declarations, found {total}")

    negative = run(["lake", "env", "lean", str(args.negative.resolve())], repo)
    if negative.returncode == 0:
        fail("uninhabited-arrow negative was accepted", negative.stdout)
    if "No proof found" not in negative.stdout:
        fail("uninhabited-arrow negative failed for an unrelated reason", negative.stdout)

    print(
        f"DTTBENCH-GATE files={len(CORPUS_FILES)} declarations={total} "
        "kernel_replay=pass axiom_audit=pass negative=pass"
    )


if __name__ == "__main__":
    main()
