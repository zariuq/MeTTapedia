from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
from typing import Sequence


DEFAULT_PAPERS = (
    "OEIS.tex",
    "PC.tex",
    "neural_networks.tex",
    "gslt2gslt.tex",
)

COMMIT_PATTERN = re.compile(
    r"\\newcommand\{\\(?:formalcommit|leancommit)\}"
    r"\{(?P<commit>[0-9a-f]{40})\}"
)
FORMAL_BLOB_PATTERN = re.compile(
    r"\\newcommand\{\\formalblob\}"
    r"\{https://github\.com/zariuq/MeTTapedia/blob/"
    r"\\formalcommit/(?P<prefix>[^}]+)\}"
)
LEAN_SOURCE_PATTERN = re.compile(
    r"\\leansource\{(?P<path>[^}]+)\}"
    r"\{(?P<start>[0-9]+)(?:-L(?P<end>[0-9]+))?\}"
    r"\{(?P<name>[^}]+)\}"
)
LEAN_SIGNATURE_PATTERN = re.compile(
    r"\\leansignaturelink\{(?P<path>[^}]+)\}"
    r"\{(?P<start>[0-9]+)(?:-L(?P<end>[0-9]+))?\}",
    re.DOTALL,
)
STATIC_PINNED_PATTERN = re.compile(
    r"https://github\.com/zariuq/MeTTapedia/(?:blob|tree)/"
    r"\\(?:formalcommit|leancommit)/(?P<path>[^}\s#]+)"
)


class PinnedLeanLinkError(ValueError):
    pass


@dataclass(frozen=True)
class LinkFailure:
    paper: str
    kind: str
    detail: str


def _git(repo: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ("git", *arguments),
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )


def _repo_root(start: Path) -> Path:
    result = _git(start, "rev-parse", "--show-toplevel")
    if result.returncode != 0:
        raise PinnedLeanLinkError("paper directory is not in a Git repository")
    return Path(result.stdout.strip()).resolve()


def _source_at(repo: Path, commit: str, path: str) -> str | None:
    result = _git(repo, "show", f"{commit}:{path}")
    return result.stdout if result.returncode == 0 else None


def _normalized_identifier(value: str) -> str:
    normalized = value.replace(r"\_", "_").replace(r"\allowbreak", "")
    return normalized.rsplit(".", maxsplit=1)[-1].strip()


def _normalized_path(value: str) -> str:
    without_line_continuations = re.sub(
        r"%[ \t]*\r?\n[ \t]*", "", value
    )
    return "".join(without_line_continuations.split())


def _resolved_source_path(path: str, formal_prefix: str | None) -> str:
    if path.startswith("lean/") or formal_prefix is None:
        return path
    return f"{formal_prefix.rstrip('/')}/{path}"


def audit_paper(repo: Path, paper: Path) -> tuple[int, list[LinkFailure]]:
    text = paper.read_text(encoding="utf-8")
    commit_match = COMMIT_PATTERN.search(text)
    if commit_match is None:
        return 0, [
            LinkFailure(paper.name, "commit", "missing pinned 40-hex commit")
        ]
    commit = commit_match.group("commit")
    if _git(repo, "cat-file", "-e", f"{commit}^{{commit}}").returncode != 0:
        return 0, [
            LinkFailure(paper.name, "commit", f"unknown commit {commit}")
        ]
    blob_match = FORMAL_BLOB_PATTERN.search(text)
    formal_prefix = blob_match.group("prefix") if blob_match else None
    failures: list[LinkFailure] = []
    checked = 0
    for match in LEAN_SOURCE_PATTERN.finditer(text):
        checked += 1
        path = _resolved_source_path(
            _normalized_path(match.group("path")), formal_prefix
        )
        source = _source_at(repo, commit, path)
        if source is None:
            failures.append(LinkFailure(paper.name, "source", path))
            continue
        lines = source.splitlines()
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if start < 1 or end < start or end > len(lines):
            failures.append(
                LinkFailure(
                    paper.name,
                    "line-range",
                    f"{path}:{start}-L{end} outside 1-L{len(lines)}",
                )
            )
            continue
        identifier = _normalized_identifier(match.group("name"))
        snippet = "\n".join(lines[start - 1 : end])
        if identifier not in snippet:
            failures.append(
                LinkFailure(
                    paper.name,
                    "declaration",
                    f"{identifier} absent from {path}:{start}-L{end}",
                )
            )
    for match in LEAN_SIGNATURE_PATTERN.finditer(text):
        checked += 1
        path = _resolved_source_path(
            _normalized_path(match.group("path")), formal_prefix
        )
        source = _source_at(repo, commit, path)
        if source is None:
            failures.append(
                LinkFailure(paper.name, "signature-source", path)
            )
            continue
        lines = source.splitlines()
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if start < 1 or end < start or end > len(lines):
            failures.append(
                LinkFailure(
                    paper.name,
                    "signature-line-range",
                    f"{path}:{start}-L{end} outside 1-L{len(lines)}",
                )
            )
    for path in sorted(
        {
            match.group("path").rstrip(".,")
            for match in STATIC_PINNED_PATTERN.finditer(text)
        }
    ):
        checked += 1
        if _source_at(repo, commit, path) is None:
            failures.append(LinkFailure(paper.name, "static-source", path))
    return checked, failures


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Check commit-pinned Lean links in selected TeX papers"
    )
    parser.add_argument("papers", nargs="*", default=DEFAULT_PAPERS)
    args = parser.parse_args(argv)
    paper_root = Path(__file__).resolve().parent
    repo = _repo_root(paper_root)
    total = 0
    failures: list[LinkFailure] = []
    for value in args.papers:
        paper = (paper_root / value).resolve()
        try:
            paper.relative_to(paper_root)
        except ValueError as error:
            raise PinnedLeanLinkError(
                f"paper lies outside the paper directory: {value}"
            ) from error
        if not paper.is_file():
            failures.append(LinkFailure(value, "paper", "file is missing"))
            continue
        checked, paper_failures = audit_paper(repo, paper)
        total += checked
        failures.extend(paper_failures)
    if failures:
        for failure in failures:
            print(f"FAIL {failure.paper} {failure.kind}: {failure.detail}")
        print(f"FAIL checked={total} failures={len(failures)}")
        raise SystemExit(1)
    print(f"PASS checked={total} papers={len(args.papers)}")


if __name__ == "__main__":
    main()
